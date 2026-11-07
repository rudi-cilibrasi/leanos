#!/usr/bin/env python3
"""Run the xHCI keyboard, mouse or mass-storage device program under QEMU q35 (issues #449, #607, #619, #623).

Builds the q35 device-lab kernel (`build-qotom-recovery-lab.py
--q35-device-lab`) around the `kbd-q35` program, boots it from a GRUB ISO on
q35 with a `qemu-xhci` controller at 00:02.0, a hub on root port 1 and a USB
keyboard behind it, waits for the driver's ready record, types a string
through QMP `input-send-event` addressed to the USB keyboard, and checks the
serial transcript: every typed character must come back as a
`LEANOS-LAB/1 KBD key=` record, in order, and the program must end with
status 0.

With `--service` the program yields each key instead of printing it and runs
through the lab device service (ADR 0022): subject 1 is granted the device,
an ungranted subject is denied, the driver is invoked in fixed step budgets,
each yielded key comes back as a `SERVICE subject=1 key=` record, and after
revocation the former holder is denied.

With `--mouse` the `mouse-q35` program runs instead, with a USB mouse behind
the hub. QMP `input-send-event` moves it, presses and releases its buttons
and turns its wheel. QEMU's mouse merges motion between two polls and splits
motion beyond 127 counts over several reports, so the check is on runs of
records with equal buttons: their button states, in order, must be the states
the button events produced, and each run's dx, dy and wheel must sum to the
motion sent in that state. The ready record must name QEMU's mouse.

`--mouse --keyboard-first` puts a USB keyboard on hub port 1 and the mouse on
port 2, so the driver must pass over the keyboard's boot interface (protocol
1) and address the mouse in the driver context the keyboard used. The ready
record must still name the mouse: a regression check that the reused EP0
ring holds none of the keyboard's transfer descriptors (`Xhci.ringInit`).

With `--msc` the `msc-q35` program runs instead, with a QEMU `usb-storage`
behind the hub whose raw image (`MSC_BLOCKS` blocks of 512 bytes) the script
writes first: each block's content derives from its LBA, so a misread block
or offset shows. The INQUIRY record must name QEMU's disk, the capacity must
be the image's, every block record (LBA, first 16 bytes, FNV-1a of the block)
must match the image, LBA 0, the middle LBA and the last LBA among them, and
the READ(10) past the end must fail with an illegal-request sense.
`--msc --root-port` puts the storage on QEMU's root port 2 instead, where it
attaches at SuperSpeed to the port's USB 3 half (qemu-xhci numbers its USB 3
ports 1-4 and its USB 2 ports 5-8, so the hub is xHCI port 5 and the storage
xHCI port 2), and a USB keyboard alone behind the hub, which the driver must
pass over.

`--hub-port N` (2-8, with the keyboard, `--mouse` or `--msc`) puts the device
under test on hub port N, and a decoy on hub port 1 that the driver must
pass over: a mouse for the keyboard, a keyboard for the mouse and the
storage. Besides the program's own records it checks the `HUB`
records (docs/usb-hub.md): QEMU's full-speed hub on xHCI port 5 with 8
ports, a status record for each port up to N, connected only at 1 and N, and
both devices' slot contexts with the hub port as route string, full speed,
root port 5 and no TT fields, as behind any full-speed hub.

usage: run-q35-device-lab.py [--service | --mouse [--keyboard-first] | --msc [--root-port]]
                             [--hub-port N] [--text hello] [--output DIR] [--no-build]
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import socket
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# QMP qcodes for the characters the check types (US layout).
QCODES = {c: c for c in "abcdefghijklmnopqrstuvwxyz"}
QCODES.update({str(d): str(d) for d in range(10)})
QCODES.update({" ": "spc", "\n": "ret"})
RECORD = {" ": "space", "\n": "enter"}

# The mouse scenario: moves (dx, dy), button presses and releases, wheel
# clicks. dx -150 needs two reports; the wheel is QEMU's "wheel-up" (+1) and
# "wheel-down" (-1) button.
MOUSE_PLAN = [
    ("move", 10, 5), ("move", -3, 20),
    ("press", "left"), ("move", 40, -7), ("release", "left"),
    ("move", -150, 0),
    ("press", "right"), ("release", "right"),
    ("wheel", "up"), ("wheel", "up"), ("wheel", "down"),
    ("press", "middle"), ("press", "left"), ("move", 1, -1),
    ("release", "left"), ("release", "middle"),
    ("move", 0, 3),
]
BUTTON_BITS = {"left": 1, "right": 2, "middle": 4}
MOUSE_RECORD = "LEANOS-LAB/1 MOUSE buttons="


def mouse_runs_expected(plan: list[tuple]) -> list[list[int]]:
    """[buttons, dx, dy, wheel] of each run of records the plan must produce."""
    runs = [[0, 0, 0, 0]]
    for step in plan:
        kind, *args = step
        if kind in ("press", "release"):
            bit = BUTTON_BITS[args[0]]
            state = runs[-1][0] | bit if kind == "press" else runs[-1][0] & ~bit
            runs.append([state, 0, 0, 0])
        elif kind == "move":
            runs[-1][1] += args[0]
            runs[-1][2] += args[1]
        else:
            runs[-1][3] += 1 if args[0] == "up" else -1
    # Only a report that moves or changes the buttons becomes a record: the
    # initial state has records only if it moved.
    if runs[0][1:] == [0, 0, 0]:
        runs.pop(0)
    return runs


def mouse_runs(records: list[dict]) -> list[list[int]]:
    runs: list[list[int]] = []
    for r in records:
        if not runs or runs[-1][0] != r["buttons"]:
            runs.append([r["buttons"], 0, 0, 0])
        runs[-1][1] += r["dx"]
        runs[-1][2] += r["dy"]
        runs[-1][3] += r["wheel"]
    return runs


def parse_mouse(line: str) -> dict:
    fields = dict(f.split("=", 1) for f in line.split()[2:])
    return {k: int(fields[k]) for k in ("buttons", "dx", "dy", "wheel")}


# The mass-storage scenario's disk: 4 MiB of 512-byte blocks.
MSC_BLOCKS = 8192
MSC_BLOCK_BYTES = 512
# The LBAs the program reads: 0-3 in one command, the middle one, the last
# two in one command.
MSC_LBAS = [0, 1, 2, 3, MSC_BLOCKS // 2, MSC_BLOCKS - 2, MSC_BLOCKS - 1]


def msc_block(lba: int) -> bytes:
    """Block `lba` of the disk: a readable 16-byte head naming the LBA, then
    bytes hashed from the LBA and their position."""
    head = f"LBA{lba:08x}-MSC\n".encode()
    body = b"".join(hashlib.sha256(b"leanos-msc %d %d" % (lba, k)).digest() for k in range(16))
    return (head + body)[:MSC_BLOCK_BYTES]


def fnv1a32(data: bytes) -> int:
    h = 0x811C9DC5
    for b in data:
        h = ((h ^ b) * 0x01000193) & 0xFFFFFFFF
    return h


def write_msc_disk(path: Path) -> None:
    with path.open("wb") as f:
        for lba in range(MSC_BLOCKS):
            f.write(msc_block(lba))


def run(cmd: list[str], **kw) -> None:
    subprocess.run(cmd, check=True, cwd=ROOT, **kw)


def build(output: Path, seconds: int, service: bool, mouse: bool, msc: bool) -> Path:
    program = ("msc-q35" if msc else "mouse-q35" if mouse else
               "kbd-q35-service" if service else "kbd-q35")
    image = output / f"{program}.bin"
    env = dict(os.environ, LEANOS_KBD_SECONDS=str(seconds), LEANOS_MOUSE_SECONDS=str(seconds))
    run(["lake", "build", "leanos-wifi-gen"], stdout=subprocess.DEVNULL)
    run([".lake/build/bin/leanos-wifi-gen", program, str(image)], env=env,
        stdout=subprocess.DEVNULL)
    run(["python3", "scripts/build-qotom-recovery-lab.py", "--prepared-repo", ".",
         "--q35-device-lab", "--lab-program", str(image)] +
        (["--device-service"] if service else []), stdout=subprocess.DEVNULL)
    elf = ROOT / "build/q35-device-lab/leanos-q35-device-lab.elf"
    iso_root = output / "iso"
    (iso_root / "boot/grub").mkdir(parents=True, exist_ok=True)
    shutil.copy2(elf, iso_root / "boot/leanos.elf")
    (iso_root / "boot/grub/grub.cfg").write_text(
        "set timeout=0\nset default=0\n"
        "menuentry \"LeanOS q35 device lab\" {\n"
        "  multiboot2 /boot/leanos.elf\n  boot\n}\n")
    iso = output / "q35-device-lab.iso"
    run(["grub-mkrescue", "-d", "/usr/lib/grub/i386-pc", "-o", str(iso), str(iso_root)],
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    return iso


class Qmp:
    def __init__(self, path: Path) -> None:
        self.sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        for _ in range(100):
            try:
                self.sock.connect(str(path))
                break
            except (FileNotFoundError, ConnectionRefusedError):
                time.sleep(0.05)
        self.file = self.sock.makefile("rw")
        self.read()                      # greeting
        self.command("qmp_capabilities")

    def read(self) -> dict:
        while True:
            message = json.loads(self.file.readline())
            if "event" not in message:
                return message

    def command(self, name: str, **arguments) -> dict:
        self.file.write(json.dumps({"execute": name, "arguments": arguments}) + "\n")
        self.file.flush()
        reply = self.read()
        if "error" in reply:
            raise SystemExit(f"QMP {name} failed: {reply['error']}")
        return reply

    def key(self, qcode: str) -> None:
        for down in (True, False):
            self.command("input-send-event", device="vga0", events=[
                {"type": "key", "data": {"down": down, "key": {"type": "qcode", "data": qcode}}}])
            time.sleep(0.05)

    def mouse(self, step: tuple) -> None:
        kind, *args = step
        if kind == "move":
            events = [{"type": "rel", "data": {"axis": axis, "value": value}}
                      for axis, value in zip(("x", "y"), args) if value]
        elif kind == "wheel":
            button = "wheel-up" if args[0] == "up" else "wheel-down"
            events = [{"type": "btn", "data": {"down": down, "button": button}}
                      for down in (True, False)]
        else:
            events = [{"type": "btn", "data": {"down": kind == "press", "button": args[0]}}]
        # One command, one sync: QEMU's mouse queues one report per button
        # state. The mouse is bound to no display; the events reach it once
        # the driver has polled it (QEMU then activates its input handler).
        self.command("input-send-event", events=events)
        time.sleep(0.05)


def wait_for(log: Path, needle: str, timeout: float) -> bool:
    deadline = time.time() + timeout
    while time.time() < deadline:
        if log.exists() and needle in log.read_text(errors="replace"):
            return True
        time.sleep(0.1)
    return False


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--text", default="hello lean\n")
    parser.add_argument("--seconds", type=int, default=6, help="keyboard session length")
    parser.add_argument("--output", type=Path, default=ROOT / "build/q35-device-lab/run")
    parser.add_argument("--no-build", action="store_true")
    parser.add_argument("--service", action="store_true", help="run through the lab device service")
    parser.add_argument("--mouse", action="store_true",
                        help="run the USB mouse program, a mouse behind the hub")
    parser.add_argument("--keyboard-first", action="store_true",
                        help="with --mouse: a keyboard on hub port 1, the mouse on port 2")
    parser.add_argument("--msc", action="store_true",
                        help="run the USB mass-storage program, a usb-storage behind the hub")
    parser.add_argument("--root-port", action="store_true",
                        help="with --msc: the usb-storage on root port 2, a keyboard behind the hub")
    parser.add_argument("--hub-port", type=int, metavar="N",
                        help="the device under test on hub port N (2-8), a decoy device on hub "
                             "port 1")
    a = parser.parse_args()
    if a.mouse and a.service:
        raise SystemExit("--mouse runs without the device service")
    if a.keyboard_first and not a.mouse:
        raise SystemExit("--keyboard-first needs --mouse")
    if a.msc and (a.mouse or a.service):
        raise SystemExit("--msc runs alone, without the device service")
    if a.root_port and not a.msc:
        raise SystemExit("--root-port needs --msc")
    if a.hub_port is not None:
        if not 2 <= a.hub_port <= 8:
            raise SystemExit("--hub-port needs 2..8 (QEMU's usb-hub has 8 ports; 1 holds the decoy)")
        if a.service or a.keyboard_first or a.root_port:
            raise SystemExit("--hub-port runs without --service, --keyboard-first and --root-port")
    if any(c not in QCODES for c in a.text):
        raise SystemExit("--text may use lower-case letters, digits, space and newline")
    if a.output == parser.get_default("output"):
        if a.service:
            a.output = ROOT / "build/q35-device-lab/run-service"
        elif a.mouse:
            a.output = ROOT / ("build/q35-device-lab/run-mouse-keyboard-first" if a.keyboard_first
                               else "build/q35-device-lab/run-mouse")
        elif a.msc:
            a.output = ROOT / ("build/q35-device-lab/run-msc-root-port" if a.root_port
                               else "build/q35-device-lab/run-msc")
        if a.hub_port is not None:
            a.output = a.output.with_name(a.output.name + f"-hub-port-{a.hub_port}")
    a.output.mkdir(parents=True, exist_ok=True)
    iso = (a.output / "q35-device-lab.iso" if a.no_build else
           build(a.output, a.seconds, a.service, a.mouse, a.msc))
    if a.msc:
        disk = a.output / "msc-disk.raw"
        write_msc_disk(disk)
        usb = (["-device", "usb-kbd,id=kbd0,bus=xhci.0,port=1.1,display=vga0"]
               if a.root_port or a.hub_port else []) + [
            "-drive", f"id=msc0,if=none,format=raw,readonly=on,file={disk}",
            "-device", "usb-storage,id=msc,bus=xhci.0,port="
                       f"{2 if a.root_port else f'1.{a.hub_port or 1}'},drive=msc0"]
    elif a.hub_port:
        # The keyboard is bound to the display QMP types on, as elsewhere.
        kbd, mouse = "usb-kbd,id=kbd0,bus=xhci.0,port=1.{},display=vga0", \
            "usb-mouse,id=mouse0,bus=xhci.0,port=1.{}"
        usb = (["-device", kbd.format(1), "-device", mouse.format(a.hub_port)] if a.mouse else
               ["-device", mouse.format(1), "-device", kbd.format(a.hub_port)])
    else:
        usb = (["-device", "usb-kbd,id=kbd0,bus=xhci.0,port=1.1,display=vga0"]
               if not a.mouse or a.keyboard_first else []) + (
            ["-device", f"usb-mouse,id=mouse0,bus=xhci.0,port=1.{2 if a.keyboard_first else 1}"]
            if a.mouse else [])
    serial = a.output / "serial.log"
    serial.unlink(missing_ok=True)
    qmp_path = Path(tempfile.mkdtemp()) / "qmp.sock"
    qemu = subprocess.Popen([
        "qemu-system-x86_64", "-machine", "q35,accel=tcg", "-nodefaults", "-cpu", "max",
        "-m", "512M", "-display", "none", "-monitor", "none", "-no-reboot",
        "-serial", f"file:{serial}", "-qmp", f"unix:{qmp_path},server=on,wait=off",
        "-device", "VGA,id=vga0,bus=pcie.0,addr=0x1",
        "-device", "isa-debug-exit,iobase=0xf4,iosize=0x04",
        "-device", "qemu-xhci,id=xhci,bus=pcie.0,addr=0x2",
        "-device", "usb-hub,id=hub,bus=xhci.0,port=1",
    ] + usb + [
        "-drive", f"id=cd,if=none,format=raw,media=cdrom,readonly=on,file={iso}",
        "-device", "ide-cd,drive=cd,bus=ide.0",
    ], cwd=ROOT)
    try:
        qmp = Qmp(qmp_path)
        if a.msc:
            # Nothing to send: the program reads the disk on its own.
            qemu.wait(timeout=180)
            return check_msc(serial.read_text(errors="replace").replace("\r", ""), a.root_port,
                             a.hub_port)
        ready = "MOUSE ready" if a.mouse else "KBD ready"
        if not wait_for(serial, ready, 120):
            print(serial.read_text(errors="replace") if serial.exists() else "(no serial)")
            raise SystemExit(f"error: {'mouse' if a.mouse else 'keyboard'} driver never reported ready")
        time.sleep(0.5)
        if a.mouse:
            for step in MOUSE_PLAN:
                qmp.mouse(step)
        else:
            for c in a.text:
                qmp.key(QCODES[c])
        qemu.wait(timeout=120)
    finally:
        if qemu.poll() is None:
            qemu.kill()
    transcript = serial.read_text(errors="replace").replace("\r", "")
    if a.mouse:
        return check_mouse(transcript, a.keyboard_first, a.hub_port)
    prefix = "LEANOS-LAB/1 SERVICE subject=1 key=" if a.service else "LEANOS-LAB/1 KBD key="
    keys = [l.split("key=", 1)[1] for l in transcript.splitlines() if l.startswith(prefix)]
    want = [RECORD.get(c, c) for c in a.text]
    print("\n".join(l for l in transcript.splitlines() if l.startswith("LEANOS-LAB/1")))
    if keys != want:
        print(f"error: typed {want}, driver reported {keys}", file=sys.stderr)
        return 1
    if "LEANOS-LAB/1 WIFI-END status=0 " not in transcript:
        print("error: device program did not end with status 0", file=sys.stderr)
        return 1
    if a.hub_port and check_hub(transcript.splitlines(), a.hub_port):
        return 1
    if a.service:
        lines = transcript.splitlines()
        order = ["LEANOS-LAB/1 SERVICE grant subject=1 bind=accepted",
                 "LEANOS-LAB/1 SERVICE invoke subject=2 denied",
                 "LEANOS-LAB/1 SERVICE revoke subject=1 invocations=",
                 "LEANOS-LAB/1 SERVICE invoke subject=1 denied"]
        at = [next((i for i, l in enumerate(lines) if l.startswith(o)), -1) for o in order]
        if -1 in at or at != sorted(at) or any("KBD key=" in l for l in lines):
            print("error: service grant/deny/revoke records missing or out of order", file=sys.stderr)
            return 1
    via = "the device service (yield per key)" if a.service else "the Lean xHCI driver"
    where = f" on hub port {a.hub_port}" if a.hub_port else ""
    print(f"q35 device lab: {len(keys)} keys typed through QMP came back from {via}{where}")
    return 0


# QEMU's usb-hub: full speed, 8 ports, attached to qemu-xhci's USB 2 port 5
# (QEMU port 1; ports 1-4 are the USB 3 halves).
HUB_ROOT_PORT = 5
HUB_PORTS = 8


def check_hub(lines: list[str], port: int) -> list[str]:
    """Errors in the HUB records of a --hub-port run (docs/usb-hub.md),
    printed; an empty list if they are as required."""
    errors = []
    hub = [l for l in lines if l.startswith("LEANOS-LAB/1 HUB ")]
    found = [l for l in hub if l.startswith("LEANOS-LAB/1 HUB found ")]
    if len(found) != 1 or not found[0].startswith(
            f"LEANOS-LAB/1 HUB found root-port={HUB_ROOT_PORT} speed=full slot="):
        errors.append(f"hub found records {found}, expected one on root port {HUB_ROOT_PORT} "
                      "at full speed")
    # QEMU's hub reports a bPwrOn2PwrGood of at most 75 (150 ms), so the 250 ms
    # floor applies; a full-speed hub has no TT think time.
    want = (f"LEANOS-LAB/1 HUB configured ports={HUB_PORTS} power-on-wait-ms=250 "
            "tt-think-time=0")
    if want not in hub:
        errors.append(f"no line {want!r}")
    # Each port up to the device's: one status record when first read, and
    # one more after the reset of each connected port.
    status: dict[int, list[int]] = {}
    for l in hub:
        if l.startswith("LEANOS-LAB/1 HUB port=") and " status=" in l:
            f = dict(x.split("=", 1) for x in l.split()[2:])
            status.setdefault(int(f["port"]), []).append(int(f["status"], 16))
    if sorted(status) != list(range(1, port + 1)):
        errors.append(f"status records for hub ports {sorted(status)}, expected 1..{port}")
    for k, words in sorted(status.items()):
        connected = k in (1, port)
        # first read: powered (bit 8), connected (bit 0) only where a device is
        if not words or words[0] & 0x101 != (0x101 if connected else 0x100):
            errors.append(f"hub port {k} first status {words[:1]}, expected "
                          f"{'connected and ' if connected else ''}powered")
        # after the reset: connected and enabled (bits 0, 1), full speed
        if connected and (len(words) != 2 or words[1] & 0x603 != 0x003):
            errors.append(f"hub port {k} statuses {words}, expected a second one "
                          "connected, enabled, full speed")
        if not connected and len(words) != 1:
            errors.append(f"empty hub port {k} statuses {words}, expected one")
    for k in (1, port):
        want = (f"LEANOS-LAB/1 HUB device route=0x{k:05x} speed=full root-port={HUB_ROOT_PORT} "
                "tt-slot=0 tt-port=0")
        if want not in hub:
            errors.append(f"no line {want!r}")
    if any(" skipped=" in l for l in hub):
        errors.append("a connected hub port was given up")
    # The decoy on hub port 1 was addressed and passed over (Hid.Tag.rejected).
    if "WIFI 2019 0x00000001" not in lines:
        errors.append("the decoy on hub port 1 was not passed over")
    for e in errors:
        print(f"error: {e}", file=sys.stderr)
    return errors


def check_mouse(transcript: str, keyboard_first: bool, hub_port: int | None) -> int:
    lines = transcript.splitlines()
    print("\n".join(l for l in lines if l.startswith("LEANOS-LAB/1")))
    records = [parse_mouse(l) for l in lines if l.startswith(MOUSE_RECORD)]
    got, want = mouse_runs(records), mouse_runs_expected(MOUSE_PLAN)
    if got != want:
        print(f"error: sent runs [buttons, dx, dy, wheel] {want}, driver reported {got}",
              file=sys.stderr)
        return 1
    if any(not (-127 <= r[k] <= 127) for r in records for k in ("dx", "dy", "wheel")):
        print("error: a mouse record is outside the boot report's range", file=sys.stderr)
        return 1
    # The device descriptor read back is the mouse's (QEMU's HID devices are
    # 0627:0001).
    if "LEANOS-LAB/1 MOUSE ready vendor=0x0627 product=0x0001 move-now" not in lines:
        print("error: the ready record does not name QEMU's mouse (0627:0001)", file=sys.stderr)
        return 1
    # The keyboard on hub port 1 was addressed and passed over (Hid.Tag.rejected).
    if keyboard_first and "WIFI 2019 0x00000001" not in lines:
        print("error: the keyboard on hub port 1 was not rejected", file=sys.stderr)
        return 1
    if hub_port and check_hub(lines, hub_port):
        return 1
    if f"LEANOS-LAB/1 MOUSE session-end records={len(records)}" not in lines:
        print("error: session-end record count missing or wrong", file=sys.stderr)
        return 1
    if "LEANOS-LAB/1 WIFI-END status=0 " not in transcript:
        print("error: device program did not end with status 0", file=sys.stderr)
        return 1
    where = f" on hub port {hub_port}" if hub_port else ""
    print(f"q35 device lab: {len(MOUSE_PLAN)} mouse events through QMP came back from the "
          f"Lean xHCI driver{where} as {len(records)} MOUSE records in {len(want)} button runs")
    return 0


def check_msc(transcript: str, root_port: bool, hub_port: int | None) -> int:
    lines = transcript.splitlines()
    print("\n".join(l for l in lines if l.startswith("LEANOS-LAB/1")))
    errors = []

    def need(line: str, what: str) -> None:
        if line not in lines:
            errors.append(f"{what}: no line {line!r}")

    # QEMU's usb-storage is 46f4:0001, its SCSI disk "QEMU" / "QEMU HARDDISK".
    need("LEANOS-LAB/1 MSC ready vendor=0x46f4 product=0x0001", "device descriptor")
    # Full speed behind QEMU's full-speed hub (bulk max packet 64); SuperSpeed
    # (1024) on a root port, where qemu-xhci attaches it to the USB 3 port.
    mps = 1024 if root_port else 64
    need(f"LEANOS-LAB/1 MSC configured bulk-in=0x81 in-max-packet={mps} "
         f"bulk-out=0x02 out-max-packet={mps}", "bulk endpoints")
    inquiry = [l for l in lines if l.startswith("LEANOS-LAB/1 MSC inquiry ")]
    if (len(inquiry) != 1 or not inquiry[0].startswith(
            'LEANOS-LAB/1 MSC inquiry type=0x00 removable=0 vendor="QEMU" '
            'product="QEMU HARDDISK" revision="')):
        errors.append(f"INQUIRY record {inquiry} does not name QEMU's disk")
    if not any(l.startswith("LEANOS-LAB/1 MSC unit-ready attempts=") for l in lines):
        errors.append("no unit-ready record")
    need(f"LEANOS-LAB/1 MSC capacity blocks={MSC_BLOCKS} block-bytes={MSC_BLOCK_BYTES}",
         "capacity")
    reads = []
    for l in lines:
        if l.startswith("LEANOS-LAB/1 MSC block "):
            fields = dict(f.split("=", 1) for f in l.split()[3:])
            reads.append((int(fields["lba"]), fields["head"], int(fields["fnv1a"], 16)))
    if [r[0] for r in reads] != MSC_LBAS:
        errors.append(f"blocks read {[r[0] for r in reads]}, expected {MSC_LBAS}")
    for lba, head, fnv in reads:
        block = msc_block(lba) if 0 <= lba < MSC_BLOCKS else b""
        if head != block[:16].hex() or fnv != fnv1a32(block):
            errors.append(f"block {lba}: head={head} fnv1a=0x{fnv:08x}, the image has "
                          f"head={block[:16].hex()} fnv1a=0x{fnv1a32(block):08x}")
    # READ(10) of LBA MSC_BLOCKS: a failed CSW, then ILLEGAL REQUEST, LBA out of range.
    if not any(l.startswith("LEANOS-LAB/1 MSC csw step=read-past-end status=1 ") for l in lines):
        errors.append("the read past the end did not report a failed CSW")
    if not any(l.startswith("LEANOS-LAB/1 MSC sense after=read-past-end key=0x05 asc=0x21 ")
               for l in lines):
        errors.append("the read past the end did not report ILLEGAL REQUEST / LBA out of range")
    need(f"LEANOS-LAB/1 MSC done blocks-read={len(MSC_LBAS)}", "done record")
    if any(l.startswith("LEANOS-LAB/1 MSC error=") for l in lines):
        errors.append("the program stopped with an error record")
    # The keyboard behind the hub was addressed and passed over (Hid.Tag.rejected).
    if root_port and "WIFI 2019 0x00000001" not in lines:
        errors.append("the keyboard on hub port 1 was not rejected")
    if "LEANOS-LAB/1 WIFI-END status=0 " not in transcript:
        errors.append("device program did not end with status 0")
    for e in errors:
        print(f"error: {e}", file=sys.stderr)
    if hub_port and check_hub(lines, hub_port):
        return 1
    if errors:
        return 1
    where = ("on root port 2" if root_port else f"on hub port {hub_port}" if hub_port
             else "behind the hub")
    print(f"q35 device lab: the Lean xHCI driver read {len(reads)} blocks of the usb-storage "
          f"{where} through bulk-only transport, all matching the image")
    return 0


if __name__ == "__main__":
    sys.exit(main())
