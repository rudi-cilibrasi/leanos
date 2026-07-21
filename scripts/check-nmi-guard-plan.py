#!/usr/bin/env python3
"""Audit the linked NMI guard/IST2 leaves in an accepted generated plan."""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

PAGE_BYTES = 4096
PTE_PRESENT = 1
PTE_WRITABLE = 2
PTE_USER = 4
PTE_NX = 1 << 63


def fail(message: str) -> None:
    raise SystemExit(f"error: {message}")


def symbols(elf: Path) -> dict[str, int]:
    output = subprocess.run(
        ["nm", "-n", str(elf)], check=True, capture_output=True, text=True
    ).stdout
    result: dict[str, int] = {}
    for line in output.splitlines():
        fields = line.split()
        if len(fields) == 3:
            result[fields[2]] = int(fields[0], 16)
    return result


def array(header: str, name: str) -> list[int]:
    match = re.search(
        rf"static const unsigned long long {name}\[4096\] = \{{\n(.*?)\n\}};",
        header,
        re.DOTALL,
    )
    if match is None:
        fail(f"NMI boot plan lacks exact array {name}[4096]")
    entries = [int(value) for value in re.findall(r"([0-9]+)ULL", match.group(1))]
    if len(entries) != 4096:
        fail(f"NMI boot plan array {name} has {len(entries)} leaves, expected 4096")
    return entries


def main() -> None:
    if len(sys.argv) != 3:
        fail(f"usage: {sys.argv[0]} ELF GENERATED_PLAN_HEADER")
    elf = Path(sys.argv[1])
    plan = Path(sys.argv[2])
    if not elf.is_file() or not plan.is_file():
        fail("NMI ELF and generated plan header must both exist")

    linked = symbols(elf)
    required = (
        "__nmi_ist_guard_start",
        "__nmi_ist_guard_end",
        "__nmi_ist_stack_start",
        "__nmi_ist_stack_end",
    )
    missing = [name for name in required if name not in linked]
    if missing:
        fail(f"NMI boot plan ELF lacks symbol {missing[0]}")

    guard_start = linked[required[0]]
    guard_end = linked[required[1]]
    stack_start = linked[required[2]]
    stack_end = linked[required[3]]
    if (
        guard_start % PAGE_BYTES != 0
        or guard_end - guard_start != PAGE_BYTES
        or guard_end != stack_start
        or stack_end - stack_start != 4 * PAGE_BYTES
    ):
        fail("NMI boot plan received invalid linked guard/IST2 intervals")

    text = plan.read_text(encoding="utf-8")
    for name in ("leanos_boot_plan_a", "leanos_boot_plan_b"):
        entries = array(text, name)
        guard_page = guard_start // PAGE_BYTES
        if entries[guard_page] != 0:
            fail(f"NMI guard is mapped in {name}")
        for page in range(stack_start // PAGE_BYTES, stack_end // PAGE_BYTES):
            expected = page * PAGE_BYTES | PTE_PRESENT | PTE_WRITABLE | PTE_NX
            if entries[page] != expected or entries[page] & PTE_USER:
                fail(f"NMI IST2 leaf policy mismatch in {name} at page {page}")

    print("NMI generated boot plan keeps the guard absent and IST2 supervisor-writable NX")


if __name__ == "__main__":
    main()
