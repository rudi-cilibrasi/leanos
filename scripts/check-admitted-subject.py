#!/usr/bin/env python3
"""Check the admitted subject ELF embedded in a linked boot image (issue #492).

    check-admitted-subject.py IMAGE_ELF ADMITTED_ELF ADMITTED_PLAN ADMIT_TOOL OUT_DIR

ADMITTED_ELF is the separate subject executable scripts/build-subject.sh
linked, and ADMITTED_PLAN the plan the Lean checker (ADMIT_TOOL,
leanos-elf-admit) printed for it at build time.  This script

1. reads the image's .user_admitted section and the symbols around it, and
   requires it to be the range [__user_admitted_start, __user_admitted_end):
   page aligned, after the last subject slot, read-only and non-executable,
   and loaded from file bytes by an identity (paddr == vaddr) PT_LOAD, so the
   boot loader puts exactly these bytes at these physical frames;
2. byte-compares those booted bytes with ADMITTED_ELF;
3. re-runs the Lean checker over the bytes read back from the image, with
   the range and the embedded-user reservation [__user_a_text_start,
   __boot_image_end), and requires the same admitted plan plus a placement
   (LeanOS.ElfAdmission.place); and
4. runs the checker over mutated copies of ADMITTED_ELF, one per rejection
   reason the issue lists, and requires each to be rejected for that reason.

It writes OUT_DIR/admitted-subject-plan.tsv (the placed plan) and prints one
summary line.  It parses only ELF64 little-endian headers with `struct`.
"""

from __future__ import annotations

import hashlib
import struct
import subprocess
import sys
from pathlib import Path

PAGE = 4096
PT_LOAD = 1
SHF_WRITE = 1
SHF_ALLOC = 2
SHF_EXECINSTR = 4


def fail(message: str) -> None:
    raise SystemExit(f"error: check-admitted-subject: {message}")


def elf_tables(data: bytes):
    if data[:4] != b"\x7fELF" or data[4] != 2 or data[5] != 1:
        fail("image is not a little-endian ELF64 file")
    (phoff, shoff) = struct.unpack_from("<QQ", data, 32)
    (phentsize, phnum, shentsize, shnum, shstrndx) = struct.unpack_from("<HHHHH", data, 54)
    segments = [struct.unpack_from("<IIQQQQQQ", data, phoff + i * phentsize) for i in range(phnum)]
    raw = [struct.unpack_from("<IIQQQQIIQQ", data, shoff + i * shentsize) for i in range(shnum)]
    strtab = raw[shstrndx]
    names = data[strtab[4]:strtab[4] + strtab[5]]

    def name(offset: int) -> str:
        return names[offset:names.index(b"\0", offset)].decode()

    sections = {name(s[0]): s for s in raw}
    return segments, sections


def symbols(elf: Path) -> dict[str, int]:
    table: dict[str, int] = {}
    for line in subprocess.run(["nm", str(elf)], check=True, capture_output=True,
                               text=True).stdout.splitlines():
        fields = line.split()
        if len(fields) == 3:
            table[fields[2]] = int(fields[0], 16)
    return table


def run_tool(tool: str, *args: str) -> tuple[int, str]:
    result = subprocess.run([tool, *args], capture_output=True, text=True)
    return result.returncode, result.stdout


def plan_rows(text: str) -> list[str]:
    return [row for row in text.splitlines()
            if row.startswith("elf\t") or row.startswith("segment\t")]


def mutate(original: bytes, edits: list[tuple[int, str, int]], size: int | None = None) -> bytes:
    data = bytearray(original if size is None else original[:size])
    for offset, fmt, value in edits:
        struct.pack_into(fmt, data, offset, value)
    return bytes(data)


def main() -> None:
    if len(sys.argv) != 6:
        fail("usage: IMAGE_ELF ADMITTED_ELF ADMITTED_PLAN ADMIT_TOOL OUT_DIR")
    image, admitted, plan_path, tool, out_dir = sys.argv[1:]
    out = Path(out_dir)
    out.mkdir(parents=True, exist_ok=True)
    image_bytes = Path(image).read_bytes()
    admitted_bytes = Path(admitted).read_bytes()
    plan = Path(plan_path).read_text()

    # 1. The reserved range and how the boot loader fills it.
    segments, sections = elf_tables(image_bytes)
    symbol = symbols(Path(image))
    for required in ("__user_admitted_start", "__user_admitted_end", "__user_a_text_start",
                     "__user_c_stack_end", "__boot_image_end"):
        if required not in symbol:
            fail(f"image lacks symbol {required}")
    start, stop = symbol["__user_admitted_start"], symbol["__user_admitted_end"]
    section = sections.get(".user_admitted")
    if section is None:
        fail("image has no .user_admitted section")
    (_, kind, flags, address, offset, size, *_rest) = section
    if address != start or size != len(admitted_bytes):
        fail(f".user_admitted @{address:#x}+{size:#x} is not the admitted file at {start:#x}")
    if start % PAGE or stop % PAGE or stop != start + -(-size // PAGE) * PAGE:
        fail(f"reserved range {start:#x}..{stop:#x} is not the page-rounded file")
    if start < symbol["__user_c_stack_end"] or stop != symbol["__boot_image_end"]:
        fail("reserved range does not follow the last subject slot and end the image")
    if not flags & SHF_ALLOC or flags & (SHF_WRITE | SHF_EXECINSTR):
        fail(".user_admitted must be allocated, read-only and non-executable")
    covering = [s for s in segments if s[0] == PT_LOAD and s[2] <= offset
                and offset + size <= s[2] + s[5]]
    if len(covering) != 1:
        fail(".user_admitted is not loaded from file bytes by exactly one PT_LOAD")
    load = covering[0]
    if load[3] != load[4] or load[3] + (offset - load[2]) != start:
        fail(".user_admitted is not identity-loaded at its reserved frames")
    booted = image_bytes[offset:offset + size]

    # 2. The booted bytes are the admitted file.
    if booted != admitted_bytes:
        fail("booted .user_admitted bytes differ from the admitted ELF")
    (out / "booted-admitted.elf").write_bytes(booted)

    # 3. The Lean checker admits the booted bytes with the same plan and places
    #    them in the embedded-user reservation.
    status, placed = run_tool(tool, "place", str(out / "booted-admitted.elf"), str(start),
                              str(stop), str(symbol["__user_a_text_start"]),
                              str(symbol["__boot_image_end"]))
    if status != 0:
        fail(f"Lean checker rejected the booted bytes: {placed.strip()}")
    if plan_rows(placed) != plan_rows(plan) or not plan_rows(plan):
        fail("admitted plan of the booted bytes differs from the build-time plan")
    sources = [row for row in placed.splitlines() if row.startswith("source\t")]
    if len(sources) != len(plan_rows(plan)) - 1:
        fail("placement does not list one source per admitted segment")
    (out / "admitted-subject-plan.tsv").write_text(placed)

    # 4. One mutated copy per rejection reason the issue lists.
    (phoff,) = struct.unpack_from("<Q", admitted_bytes, 32)
    (phnum,) = struct.unpack_from("<H", admitted_bytes, 56)
    loads = [i for i in range(phnum)
             if struct.unpack_from("<I", admitted_bytes, phoff + i * 56)[0] == PT_LOAD]
    text, data = (phoff + loads[0] * 56, phoff + loads[1] * 56)
    (text_vaddr,) = struct.unpack_from("<Q", admitted_bytes, text + 16)
    (data_vaddr,) = struct.unpack_from("<Q", admitted_bytes, data + 16)
    vectors = {
        "wrong-machine": mutate(admitted_bytes, [(18, "<H", 3)]),
        "not-executable": mutate(admitted_bytes, [(16, "<H", 3)]),
        "too-many-program-headers": mutate(admitted_bytes, [(56, "<H", 9)]),
        "misaligned-segment": mutate(admitted_bytes, [(data + 16, "<Q", data_vaddr + 16)]),
        "writable-executable": mutate(admitted_bytes, [(text + 4, "<I", 7)]),
        "oversize-segment": mutate(admitted_bytes, [(data + 40, "<Q", 17 * PAGE)]),
        "outside-user-range": mutate(admitted_bytes, [(data + 16, "<Q", 0x200000)]),
        "overlapping-segments": mutate(admitted_bytes, [(data + 16, "<Q", text_vaddr)]),
        "entry-outside-text": mutate(admitted_bytes, [(24, "<Q", data_vaddr)]),
        "truncated-header": admitted_bytes[:40],
    }
    for reason, vector in vectors.items():
        path = out / f"reject-{reason}.elf"
        path.write_bytes(vector)
        status, output = run_tool(tool, "admit", str(path))
        if status != 1 or output.strip() != f"rejected\t{reason}":
            fail(f"vector {reason} was not rejected for that reason: {output.strip()!r}")

    digest = hashlib.sha256(booted).hexdigest()
    print(f"admitted-subject range={start:#x}..{stop:#x} bytes={size} sha256={digest} "
          f"segments={len(sources)} booted=exact negatives={len(vectors)} result=PASS")


if __name__ == "__main__":
    main()
