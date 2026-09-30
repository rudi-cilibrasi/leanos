#!/usr/bin/env python3
"""Run the xHCI keyboard device program under QEMU q35 (issue #449, stage 2a).

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

usage: run-q35-device-lab.py [--service] [--text hello] [--output DIR] [--no-build]
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


def run(cmd: list[str], **kw) -> None:
    subprocess.run(cmd, check=True, cwd=ROOT, **kw)


def build(output: Path, seconds: int, service: bool) -> Path:
    program = "kbd-q35-service" if service else "kbd-q35"
    image = output / f"{program}.bin"
    env = dict(os.environ, LEANOS_KBD_SECONDS=str(seconds))
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
    a = parser.parse_args()
    if any(c not in QCODES for c in a.text):
        raise SystemExit("--text may use lower-case letters, digits, space and newline")
    if a.service and a.output == parser.get_default("output"):
        a.output = ROOT / "build/q35-device-lab/run-service"
    a.output.mkdir(parents=True, exist_ok=True)
    iso = a.output / "q35-device-lab.iso" if a.no_build else build(a.output, a.seconds, a.service)
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
        "-device", "usb-kbd,id=kbd0,bus=xhci.0,port=1.1,display=vga0",
        "-drive", f"id=cd,if=none,format=raw,media=cdrom,readonly=on,file={iso}",
        "-device", "ide-cd,drive=cd,bus=ide.0",
    ], cwd=ROOT)
    try:
        qmp = Qmp(qmp_path)
        if not wait_for(serial, "KBD ready", 120):
            print(serial.read_text(errors="replace") if serial.exists() else "(no serial)")
            raise SystemExit("error: keyboard driver never reported ready")
        time.sleep(0.5)
        for c in a.text:
            qmp.key(QCODES[c])
        qemu.wait(timeout=120)
    finally:
        if qemu.poll() is None:
            qemu.kill()
    transcript = serial.read_text(errors="replace").replace("\r", "")
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


if __name__ == "__main__":
    sys.exit(main())
