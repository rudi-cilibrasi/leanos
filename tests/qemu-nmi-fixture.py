#!/usr/bin/env python3
import os
from pathlib import Path
import socket
import sys

if "--version" in sys.argv:
    print("QEMU emulator version fixture")
    raise SystemExit(0)

mode = os.environ.get("LEANOS_QEMU_FIXTURE_MODE", "success")
serial_arg = sys.argv[sys.argv.index("-serial") + 1]
monitor_arg = sys.argv[sys.argv.index("-qmp") + 1]
log = Path(serial_arg.removeprefix("file:"))
monitor = Path(monitor_arg.removeprefix("unix:").split(",", 1)[0])
ready = "LEANOS/17 NMI-READY origin=cpl0 prior=handling if=0 gate=2 ist=2 result=PASS\n"
terminal = "LEANOS/17 NMI reason=non-maskable-interrupt vector=2 error=none ist=2 frame=rip,cs,rflags,rsp,ss origin=cpl0 prior=handling terminal=latched return=none\n"

if mode == "missing-ready":
    raise SystemExit(0)
log.write_text(ready, encoding="utf-8")
with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as server:
    server.bind(str(monitor))
    server.listen(1)
    connection, _ = server.accept()
    with connection:
        connection.sendall(b'{"QMP":{"version":{},"capabilities":[]}}\n')
        capabilities = connection.recv(128)
        connection.sendall(b'{"return":{}}\n')
        command = connection.recv(128)
        connection.sendall(b'{"return":{}}\n')
if b"qmp_capabilities" not in capabilities or b"inject-nmi" not in command:
    raise SystemExit(1)
if mode == "hang":
    while True:
        pass
if mode == "reject":
    log.write_text(ready + "LEANOS/17 NMI status=FAIL reason=terminal-frame-policy\n", encoding="utf-8")
    raise SystemExit(43)
if mode == "wrong-record":
    terminal = terminal.replace("ist=2", "ist=1")
log.write_text(ready + terminal, encoding="utf-8")
raise SystemExit(41 if mode != "reset" else 0)
