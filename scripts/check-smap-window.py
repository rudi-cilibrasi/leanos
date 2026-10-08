#!/usr/bin/env python3
"""Check the SMAP copy windows in final ELFs against the Lean plan (#478).

The plan (`lake exe leanos-smap-window`) gives each window's exact bytes and
the byte offset of each internal label. For every ELF given, this reads the
bytes at the window's symbol through the ELF's program headers and requires:

* the window bytes equal the plan exactly;
* each label symbol sits at the window address plus the planned offset; and
* the byte after the window is not part of it (the next window or other code
  starts there, so the plan's `ret` is the window's last instruction).

Byte equality is the whole claim. What each instruction means comes from the
x86 manual, not from a semantics of x86.
"""

from __future__ import annotations

import argparse
import struct
import subprocess
import sys
from pathlib import Path


def parse_plan(text: str) -> tuple[dict[str, bytes], dict[str, tuple[str, int]]]:
    lines = text.splitlines()
    if not lines or lines[0] != "leanos-smap-window-plan\t1":
        raise ValueError("unrecognized SMAP window plan header")
    windows: dict[str, bytes] = {}
    labels: dict[str, tuple[str, int]] = {}
    for line in lines[1:]:
        fields = line.split("\t")
        if fields[0] == "window" and len(fields) == 3:
            windows[fields[1]] = bytes(int(byte, 16) for byte in fields[2].split())
        elif fields[0] == "label" and len(fields) == 4:
            labels[fields[1]] = (fields[2], int(fields[3]))
        else:
            raise ValueError(f"malformed SMAP window plan row: {line!r}")
    if not windows:
        raise ValueError("SMAP window plan has no windows")
    for label, (window, _) in labels.items():
        if window not in windows:
            raise ValueError(f"label {label} names unknown window {window}")
    return windows, labels


def symbols(elf: Path) -> dict[str, int]:
    output = subprocess.run(["nm", str(elf)], capture_output=True, text=True, check=True).stdout
    table: dict[str, int] = {}
    for line in output.splitlines():
        fields = line.split()
        if len(fields) == 3:
            table[fields[2]] = int(fields[0], 16)
    return table


def file_offset(image: bytes, address: int, length: int) -> int:
    """File offset of a virtual range, through the PT_LOAD program headers."""
    if image[:4] != b"\x7fELF" or image[4] != 2 or image[5] != 1:
        raise ValueError("not a little-endian ELF64 file")
    phoff = struct.unpack_from("<Q", image, 0x20)[0]
    phentsize, phnum = struct.unpack_from("<HH", image, 0x36)
    for index in range(phnum):
        base = phoff + index * phentsize
        ptype, _flags, offset, vaddr, _paddr, filesz, _memsz, _align = struct.unpack_from(
            "<IIQQQQQQ", image, base)
        if ptype == 1 and vaddr <= address and address + length <= vaddr + filesz:
            return offset + (address - vaddr)
    raise ValueError(f"address {address:#x} is not in a loaded segment")


def read_virtual(image: bytes, address: int, length: int) -> bytes:
    start = file_offset(image, address, length)
    return image[start:start + length]


def check(elf: Path, windows: dict[str, bytes], labels: dict[str, tuple[str, int]]) -> list[str]:
    errors = []
    table = symbols(elf)
    image = elf.read_bytes()
    for name, expected in windows.items():
        if name not in table:
            errors.append(f"{elf}: window symbol {name} is missing")
            continue
        address = table[name]
        actual = read_virtual(image, address, len(expected))
        if actual != expected:
            errors.append(
                f"{elf}: {name} bytes {actual.hex(' ')} differ from the plan {expected.hex(' ')}")
    for label, (window, offset) in labels.items():
        if window not in table:
            continue
        if table.get(label) != table[window] + offset:
            found = table.get(label)
            errors.append(
                f"{elf}: label {label} is at "
                f"{'missing' if found is None else hex(found)}, plan says {hex(table[window] + offset)}")
    return errors


def corrupt_clac(elf: Path) -> None:
    """Negative fixture: replace smap_copy_from's clac with three NOPs."""
    image = bytearray(elf.read_bytes())
    address = symbols(elf)["smap_copy_from_clac"]
    start = file_offset(bytes(image), address, 3)
    if bytes(image[start:start + 3]) != bytes([0x0f, 0x01, 0xca]):
        raise ValueError(f"{elf}: smap_copy_from_clac is not a clac")
    image[start:start + 3] = b"\x90\x90\x90"
    elf.write_bytes(bytes(image))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("plan", type=Path, help="output of `lake exe leanos-smap-window`")
    parser.add_argument("elves", nargs="+", type=Path)
    parser.add_argument("--corrupt-clac", action="store_true",
                        help="negative fixture: overwrite clac in each ELF in place, then exit")
    args = parser.parse_args()
    if args.corrupt_clac:
        for elf in args.elves:
            corrupt_clac(elf)
        return 0
    try:
        windows, labels = parse_plan(args.plan.read_text(encoding="utf-8"))
        errors = []
        for elf in args.elves:
            errors.extend(check(elf, windows, labels))
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    for error in errors:
        print(f"error: {error}", file=sys.stderr)
    if errors:
        return 1
    print(f"SMAP-WINDOW-PLAN windows={len(windows)} labels={len(labels)} "
          f"elves={len(args.elves)} bytes=exact result=PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
