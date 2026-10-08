#!/usr/bin/env python3
"""Keep the ring-3 syscall vocabulary in one table (issue #483).

scripts/syscall-numbers.tsv lists every syscall number boot/kernel.c accepts,
per scenario. This check fails if the kernel compares the syscall number
against a value the table does not list, if the table lists a number the
kernel never handles, or if the table in docs/userspace-abi.md is not the
rendering of the TSV. `--render` prints that rendering.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TABLE = ROOT / "scripts/syscall-numbers.tsv"
DOC = ROOT / "docs/userspace-abi.md"
BEGIN, END = "<!-- syscall-table:start -->", "<!-- syscall-table:end -->"


def table_rows() -> list[list[str]]:
    rows = []
    for line in TABLE.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) != 4 or not fields[0].isdigit() or not all(fields):
            raise SystemExit(f"error: malformed syscall row: {line!r}")
        rows.append(fields)
    return rows


def kernel_numbers() -> set[int]:
    source = (ROOT / "boot/kernel.c").read_text()
    numbers = {int(n) for n in re.findall(r"\bnumber == (\d+)", source)}
    for low, high in re.findall(r"\bnumber >= (\d+) && number <= (\d+)", source):
        numbers |= set(range(int(low), int(high) + 1))
    return numbers


def render(rows: list[list[str]]) -> str:
    lines = ["| Number | Scenario image | Subject | Meaning |", "| --- | --- | --- | --- |"]
    lines += [f"| {n} | {scenario} | {subject} | {meaning} |"
              for n, scenario, subject, meaning in rows]
    return "\n".join(lines)


def main() -> int:
    rows = table_rows()
    if sys.argv[1:] == ["--render"]:
        print(render(rows))
        return 0
    listed = {int(row[0]) for row in rows}
    handled = kernel_numbers()
    if handled - listed:
        print(f"error: boot/kernel.c handles syscall {min(handled - listed)}, "
              f"which {TABLE.relative_to(ROOT)} does not list", file=sys.stderr)
        return 1
    if listed - handled:
        print(f"error: {TABLE.relative_to(ROOT)} lists syscall {min(listed - handled)}, "
              "which boot/kernel.c never handles", file=sys.stderr)
        return 1
    doc = DOC.read_text()
    if BEGIN not in doc or END not in doc:
        print(f"error: {DOC.relative_to(ROOT)} lacks the syscall table markers", file=sys.stderr)
        return 1
    current = doc.split(BEGIN, 1)[1].split(END, 1)[0].strip()
    if current != render(rows):
        print(f"error: the syscall table in {DOC.relative_to(ROOT)} is stale; "
              "regenerate it with scripts/check-userspace-abi.py --render", file=sys.stderr)
        return 1
    print(f"userspace ABI: {len(handled)} syscall numbers, table and doc agree")
    return 0


if __name__ == "__main__":
    sys.exit(main())
