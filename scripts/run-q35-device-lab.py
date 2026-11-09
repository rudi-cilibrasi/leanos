#!/usr/bin/env python3
"""Run the xHCI keyboard or mouse device program under QEMU q35 (issues #449, #607).

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

usage: run-q35-device-lab.py [--service | --mouse [--keyboard-first]] [--text hello]
                             [--output DIR] [--no-build]
"""

from __future__ import annotations

import argparse
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


def run(cmd: list[str], **kw) -> None:
    subprocess.run(cmd, check=True, cwd=ROOT, **kw)


def build(output: Path, seconds: int, service: bool, mouse: bool) -> Path:
    program = "mouse-q35" if mouse else "kbd-q35-service" if service else "kbd-q35"
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
    a = parser.parse_args()
    if a.mouse and a.service:
        raise SystemExit("--mouse runs without the device service")
    if a.keyboard_first and not a.mouse:
        raise SystemExit("--keyboard-first needs --mouse")
    if any(c not in QCODES for c in a.text):
        raise SystemExit("--text may use lower-case letters, digits, space and newline")
    if a.output == parser.get_default("output"):
        if a.service:
            a.output = ROOT / "build/q35-device-lab/run-service"
        elif a.mouse:
            a.output = ROOT / ("build/q35-device-lab/run-mouse-keyboard-first" if a.keyboard_first
                               else "build/q35-device-lab/run-mouse")
    a.output.mkdir(parents=True, exist_ok=True)
    iso = (a.output / "q35-device-lab.iso" if a.no_build else
           build(a.output, a.seconds, a.service, a.mouse))
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
    ] + (["-device", "usb-kbd,id=kbd0,bus=xhci.0,port=1.1,display=vga0"]
         if not a.mouse or a.keyboard_first else []) + (
        ["-device", f"usb-mouse,id=mouse0,bus=xhci.0,port=1.{2 if a.keyboard_first else 1}"]
        if a.mouse else []) + [
        "-drive", f"id=cd,if=none,format=raw,media=cdrom,readonly=on,file={iso}",
        "-device", "ide-cd,drive=cd,bus=ide.0",
    ], cwd=ROOT)
    try:
        qmp = Qmp(qmp_path)
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
        return check_mouse(transcript, a.keyboard_first)
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
    print(f"q35 device lab: {len(keys)} keys typed through QMP came back from {via}")
    return 0


def check_mouse(transcript: str, keyboard_first: bool) -> int:
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
    if f"LEANOS-LAB/1 MOUSE session-end records={len(records)}" not in lines:
        print("error: session-end record count missing or wrong", file=sys.stderr)
        return 1
    if "LEANOS-LAB/1 WIFI-END status=0 " not in transcript:
        print("error: device program did not end with status 0", file=sys.stderr)
        return 1
    print(f"q35 device lab: {len(MOUSE_PLAN)} mouse events through QMP came back from the "
          f"Lean xHCI driver as {len(records)} MOUSE records in {len(want)} button runs")
    return 0


if __name__ == "__main__":
    sys.exit(main())
