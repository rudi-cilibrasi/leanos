#!/usr/bin/env python3
import os
from pathlib import Path
import sys

if "--version" in sys.argv:
    print("QEMU emulator version fixture")
    raise SystemExit(0)

mode = os.environ.get("LEANOS_QEMU_FIXTURE_MODE", "success")
serial_arg = sys.argv[sys.argv.index("-serial") + 1]
log = Path(serial_arg.removeprefix("file:"))
terminal = ("LEANOS/18 EARLY-TERMINAL phase=bootstrap32 table=bootstrap32 "
            "width=legacy8 vector=6 reason=invalid-opcode error=none "
            "frame=eip,cs,eflags stack=boot target=stub32 latch=terminal "
            "return=none\n")

if mode == "hang":
    while True:
        pass
if mode == "reject":
    log.write_text("LEANOS/18 EARLY-TERMINAL status=FAIL phase=bootstrap32 "
                   "reason=probe-frame-policy\n", encoding="utf-8")
    raise SystemExit(49)
if mode == "missing-record":
    log.write_text("", encoding="utf-8")
    raise SystemExit(45)
if mode == "wrong-record":
    terminal = terminal.replace("vector=6", "vector=13")
if mode == "duplicate":
    terminal = terminal + terminal
if mode == "long-mode-escape":
    terminal = terminal + (
        "LEANOS/18 EARLY64-READY phase=bootstrap64 table=bootstrap64 "
        "width=long16 stack=boot if=0 tss=none runtime-idt=unpublished "
        "result=PASS\n")
if mode == "ordinary-boot":
    terminal = ("LEANOS/10 BOOT target=x86_64-q35 subjects=2 "
                "schedule=blocking-ipc controls=wp,smep,smap\n") + terminal
log.write_text(terminal, encoding="utf-8")
raise SystemExit(45 if mode != "reset" else 0)
