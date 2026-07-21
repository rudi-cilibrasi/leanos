#!/usr/bin/env python3
"""Reject control-flow edges that can escape a terminal assembly stub."""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path


def fail(message: str) -> None:
    print(f"error: {message}", file=sys.stderr)
    raise SystemExit(1)


def symbol_address(elf: Path, name: str) -> int:
    output = subprocess.check_output(["nm", "-n", str(elf)], text=True)
    for line in output.splitlines():
        fields = line.split()
        if len(fields) >= 3 and fields[2] == name:
            return int(fields[0], 16)
    fail(f"terminal CFG symbol missing: {name}")


def direct_target(operand: str) -> int | None:
    match = re.match(r"(?:0x)?([0-9a-fA-F]+)(?:\s|$|\s*<)", operand.strip())
    return int(match.group(1), 16) if match else None


def main() -> None:
    if len(sys.argv) != 4:
        fail("usage: check-terminal-cfg.py ELF START-SYMBOL END-SYMBOL")
    elf = Path(sys.argv[1])
    start_name, end_name = sys.argv[2], sys.argv[3]
    if not elf.is_file():
        fail(f"missing terminal CFG ELF: {elf}")

    start = symbol_address(elf, start_name)
    end = symbol_address(elf, end_name)
    if start >= end:
        fail(f"terminal CFG range is empty: {start_name}..{end_name}")

    output = subprocess.check_output(
        ["objdump", "-d", "--no-show-raw-insn", str(elf)], text=True
    )
    instruction_re = re.compile(
        r"^\s*([0-9a-fA-F]+):\s+([A-Za-z][A-Za-z0-9.]*)\s*(.*?)\s*$"
    )
    instructions: list[tuple[int, str, str]] = []
    for line in output.splitlines():
        match = instruction_re.match(line)
        if not match:
            continue
        address = int(match.group(1), 16)
        if start <= address < end:
            instructions.append((address, match.group(2).lower(), match.group(3)))

    if not instructions or instructions[0][0] != start:
        fail(f"could not disassemble terminal CFG at {start_name}")

    for address, mnemonic, operand in instructions:
        site = f"0x{address:x} ({mnemonic} {operand})".rstrip()
        if mnemonic.startswith("call"):
            fail(f"terminal CFG contains a call at {site}")
        if mnemonic.startswith(("ret", "lret", "iret", "sysret")):
            fail(f"terminal CFG contains a return at {site}")
        if mnemonic in {"int", "int1", "int3", "into", "syscall", "sysenter"}:
            fail(f"terminal CFG contains a software entry at {site}")
        is_branch = mnemonic.startswith("j") or mnemonic.startswith("loop")
        if is_branch:
            target = direct_target(operand)
            if target is None:
                fail(f"terminal CFG contains an indirect or unparsed branch at {site}")
            if not start <= target < end:
                fail(
                    f"terminal CFG branch escapes {start_name}..{end_name} "
                    f"at {site} to 0x{target:x}"
                )

    last_address, last_mnemonic, last_operand = instructions[-1]
    last_target = direct_target(last_operand)
    if last_mnemonic != "jmp" or last_target is None or not start <= last_target < end:
        fail(
            f"terminal CFG can fall through past {end_name} after "
            f"0x{last_address:x} ({last_mnemonic} {last_operand})"
        )

    print(
        f"Terminal CFG containment passed ({start_name}..{end_name}, "
        f"{len(instructions)} instructions)"
    )


if __name__ == "__main__":
    main()
