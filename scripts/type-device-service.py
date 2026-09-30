#!/usr/bin/env python3
"""Type a fixed text into the device-service scenario's USB keyboard.

Waits until the guest's xHCI program reports the keyboard ready on the serial
log, then sends each character as a QMP `input-send-event` key press and
release. The guest echoes every key through the blocking IPC, so the typed
text is part of the scenario's exact transcript (issue #449).

usage: type-device-service.py --ready PREFIX SERIAL_LOG QMP_SOCKET [--text TEXT]
"""

from __future__ import annotations

import argparse
import json
import socket
import sys
import time
from pathlib import Path

QCODES = {c: c for c in "abcdefghijklmnopqrstuvwxyz"}
QCODES.update({str(d): str(d) for d in range(10)})
QCODES.update({" ": "spc", "\n": "ret"})


class Qmp:
    def __init__(self, path: Path, timeout: float) -> None:
        self.sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        deadline = time.time() + timeout
        while True:
            try:
                self.sock.connect(str(path))
                break
            except (FileNotFoundError, ConnectionRefusedError):
                if time.time() > deadline:
                    raise SystemExit(f"error: QMP socket {path} never accepted")
                time.sleep(0.05)
        self.file = self.sock.makefile("rw")
        self.read()
        self.command("qmp_capabilities")

    def read(self) -> dict:
        while True:
            line = self.file.readline()
            if not line:
                raise SystemExit("error: QMP connection closed")
            message = json.loads(line)
            if "event" not in message:
                return message

    def command(self, name: str, **arguments) -> dict:
        self.file.write(json.dumps({"execute": name, "arguments": arguments}) + "\n")
        self.file.flush()
        reply = self.read()
        if "error" in reply:
            raise SystemExit(f"error: QMP {name} failed: {reply['error']}")
        return reply

    def key(self, qcode: str) -> None:
        for down in (True, False):
            self.command("input-send-event", events=[
                {"type": "key", "data": {"down": down, "key": {"type": "qcode", "data": qcode}}}])
            time.sleep(0.05)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("serial", type=Path)
    parser.add_argument("qmp", type=Path)
    parser.add_argument("--text", default="lean ipc\n")
    parser.add_argument("--timeout", type=float, default=120.0)
    parser.add_argument("--ready", required=True,
                        help="the generated DEVICE ready-record prefix to wait for")
    a = parser.parse_args()
    if any(c not in QCODES for c in a.text):
        raise SystemExit("error: --text may use lower-case letters, digits, space and newline")
    qmp = Qmp(a.qmp, a.timeout)
    deadline = time.time() + a.timeout
    while True:
        if a.serial.exists() and a.ready in a.serial.read_text(errors="replace"):
            break
        if time.time() > deadline:
            print("error: the device program never reported the keyboard ready", file=sys.stderr)
            return 1
        time.sleep(0.1)
    time.sleep(0.5)
    for c in a.text:
        qmp.key(QCODES[c])
    return 0


if __name__ == "__main__":
    sys.exit(main())
