#!/usr/bin/env python3
"""Inventory of handwritten assembly windows at the CPL boundary (issue #477).

A *window* is a global code symbol defined in boot/boot.S whose assembled
range contains a privileged or CPL-boundary instruction: iretq, sysret,
sysexit, swapgs, stac, clac, lidt, lgdt, ltr, wrmsr, hlt, cli, sti, or a
write to CR0, CR3 or CR4. Sizes are symbol ranges in the lane's assembled
boot object (the object linked into the final ELF), each running to the next
symbol or the end of its input section: in the final ELF the linker merges
input sections, so a range there would absorb alignment padding. Every window
must also be present in the final ELF.

scripts/asm-windows.tsv holds one row per window, with the symbol, source
file, byte sizes in each toolchain lane, the images that contain it, the
policy checks that constrain it, what is assumed, the failure impact, and an
owner. The check fails when a window has no row, when a window's size differs
from its row for the selected lane, or when a row names a symbol that is no
longer a window.

usage: check-asm-windows.py [--lane gcc|clang] [--table TSV] BOOT_OBJECT FINAL_ELF
       check-asm-windows.py --measure BOOT_OBJECT     (print windows)
The lane defaults from LEANOS_TOOLCHAIN_PROFILE (clang-reference -> clang).
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PRIVILEGED = re.compile(
    r"^(iretq?|sysretq?|sysexit|swapgs|stac|clac|lidt|lgdt|ltr|wrmsr|hlt|cli|sti)$")
CR_WRITE = re.compile(r",%cr[034]$")
COLUMNS = ("symbol", "source", "gcc_bytes", "clang_bytes", "images", "checks",
           "assumes", "impact", "owner")


def source_globals(source_path: str = "boot/boot.S") -> set[str]:
    source = (ROOT / source_path).read_text() if not Path(source_path).is_absolute() \
        else Path(source_path).read_text()
    return set(re.findall(r"^\s*\.globa?l\s+(\w+)", source, re.M))


def sections(binary: str) -> list[tuple[str, int, int]]:
    """(name, start, end) of allocated executable sections."""
    out = subprocess.check_output(["readelf", "-SW", binary], text=True)
    result = []
    for line in out.splitlines():
        m = re.match(r"\s*\[\s*\d+\]\s+(\S+)\s+\S+\s+([0-9a-f]+)\s+([0-9a-f]+)\s+([0-9a-f]+)"
                     r"\s+\S+\s+(\S*)", line)
        if m and "X" in m.group(5):
            start, size = int(m.group(2), 16), int(m.group(4), 16)
            result.append((m.group(1), start, start + size))
    return result


def measure(binary: str, source_path: str = "boot/boot.S") -> dict[str, tuple[int, str]]:
    """Windows of `binary`: symbol -> (bytes, privileged instructions)."""
    wanted = source_globals(source_path)
    is_object = binary.endswith(".o")
    symbols = []
    for line in subprocess.check_output(
            ["nm", "-n", "--defined-only", binary], text=True).splitlines():
        fields = line.split()
        if len(fields) == 3 and fields[1] in "Tt":
            symbols.append((int(fields[0], 16), fields[2]))
    # In a relocatable object each section starts at 0: resolve per section.
    section_of: dict[str, str] = {}
    if is_object:
        for line in subprocess.check_output(["objdump", "-t", binary], text=True).splitlines():
            m = re.match(r"([0-9a-f]+)\s.{7}\s(\S+)\s+[0-9a-f]+\s+(\S+)$", line)
            if m:
                section_of[m.group(3)] = m.group(2)
    disassembly = subprocess.check_output(
        ["objdump", "-d", "--no-show-raw-insn", binary], text=True)
    instructions: dict[str, list[tuple[int, str, str]]] = {}
    current = None
    for line in disassembly.splitlines():
        m = re.match(r"Disassembly of section (\S+):", line)
        if m:
            current = m.group(1)
            instructions.setdefault(current, [])
            continue
        m = re.match(r"\s*([0-9a-f]+):\s+(\S+)\s*(.*)", line)
        if m and current:
            instructions[current].append((int(m.group(1), 16), m.group(2), m.group(3)))
    executable = sections(binary)
    windows = {}
    for address, name in symbols:
        if name not in wanted:
            continue
        if is_object:
            section = section_of.get(name)
            if section is None or section not in instructions:
                continue
            same = sorted(a for a, n in symbols if section_of.get(n) == section and a > address)
            end_candidates = same + [max((a for a, _, _ in instructions[section]), default=address) + 16]
            sect_end = next((e for s, st, e in executable if s == section), None)
            end = min(same[0] if same else (sect_end - 0 if sect_end else end_candidates[-1]),
                      sect_end if sect_end else 1 << 62)
            body = [x for x in instructions[section] if address <= x[0] < end]
        else:
            containing = [(s, st, e) for s, st, e in executable if st <= address < e]
            if not containing:
                continue
            section, _, sect_end = containing[0]
            later = [a for a, _ in symbols if a > address]
            end = min(later[0] if later else sect_end, sect_end)
            body = [x for x in instructions.get(section, []) if address <= x[0] < end]
        hits = sorted({x[1] for x in body if PRIVILEGED.match(x[1])} |
                      {"mov-cr" for x in body if x[1] == "mov" and CR_WRITE.search(x[2])})
        if hits:
            windows[name] = (end - address, ",".join(hits))
    return windows


def load_table(path: Path) -> dict[str, dict[str, str]]:
    rows = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) != len(COLUMNS):
            raise SystemExit(f"error: malformed asm-window row: {line!r}")
        row = dict(zip(COLUMNS, fields))
        for column in COLUMNS:
            if not row[column]:
                raise SystemExit(f"error: asm-window row {row['symbol']} lacks {column}")
        if row["symbol"] in rows:
            raise SystemExit(f"error: duplicate asm-window row {row['symbol']}")
        rows[row["symbol"]] = row
    return rows


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("binary", help="the lane's assembled boot object")
    parser.add_argument("elf", nargs="?", help="the final ELF that must contain every window")
    parser.add_argument("--measure", action="store_true")
    parser.add_argument("--lane", choices=("gcc", "clang"))
    parser.add_argument("--table", type=Path, default=ROOT / "scripts/asm-windows.tsv")
    parser.add_argument("--source", default="boot/boot.S",
                        help="the assembly source whose globals are candidate windows")
    parser.add_argument("--lab", nargs=2, action="append", default=[],
                        metavar=("SOURCE", "OBJECT"),
                        help="a Qotom lab assembly source and its assembled object (lab-only rows)")
    args = parser.parse_args()
    windows = measure(args.binary, args.source)
    lab_windows: dict[str, tuple[int, str]] = {}
    for source, obj in args.lab:
        lab_windows.update(measure(obj, source))
    if args.measure:
        for name, (size, hits) in windows.items():
            print(f"{name}\t{size}\t{hits}")
        return 0
    lane = args.lane or ("clang" if "clang" in os.environ.get("LEANOS_TOOLCHAIN_PROFILE", "")
                         else "gcc")
    rows = load_table(args.table)
    lab_rows = {name for name, row in rows.items() if row["images"] == "lab-only"}
    if args.lab:
        windows_to_check = {**windows, **lab_windows}
    else:
        windows_to_check = windows
        rows = {name: row for name, row in rows.items() if name not in lab_rows}
    for name, (size, _) in windows_to_check.items():
        if name not in rows:
            print(f"error: assembly window {name} has no row in {args.table}", file=sys.stderr)
            return 1
        if name in lab_rows and lane != "gcc":
            continue  # the Qotom lab assembles with GCC only
        recorded = int(rows[name][f"{lane}_bytes"])
        if recorded != size:
            print(f"error: assembly window {name} is {size} bytes in the {lane} lane, "
                  f"but its row records {recorded}", file=sys.stderr)
            return 1
    if args.elf:
        linked = {line.split()[2] for line in subprocess.check_output(
            ["nm", "--defined-only", args.elf], text=True).splitlines()
            if len(line.split()) == 3}
        missing = sorted(set(windows) - linked)
        if missing:
            print(f"error: assembly window {missing[0]} is absent from {args.elf}",
                  file=sys.stderr)
            return 1
    stale = sorted(set(rows) - set(windows_to_check))
    if stale:
        print(f"error: asm-window row names {stale[0]}, which is not a window", file=sys.stderr)
        return 1
    print(f"ASM-WINDOWS lane={lane} windows={len(windows)} lab-windows={len(lab_windows)} "
          "result=PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
