#!/usr/bin/env python3
"""Reject unreviewed boot-interrupt ownership in the final ELF.

The entry prologue must publish the first kernel-owned IDT before any other
boot work, the long-mode IDTR handoff must be the single reviewed instruction
boundary, both static bootstrap tables must decode exactly, every bootstrap
stub must be a contained non-returning terminal CFG, and the only later lidt
must be the runtime publication inside privilege_init.
"""

from __future__ import annotations

import argparse
import re
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

EARLY_TRAP_BASE = 0x101000
EARLY_SLOTS = {
    "boot_early_isr2_32": EARLY_TRAP_BASE + 0x000,
    "boot_early_catchall_32": EARLY_TRAP_BASE + 0x080,
    "boot_early_isr2_64": EARLY_TRAP_BASE + 0x100,
    "boot_early_catchall_64": EARLY_TRAP_BASE + 0x180,
}
REQUIRED_SYMBOLS = [
    "multiboot_entry", "long_mode_entry", "kernel_main",
    "boot_idt32", "boot_idt32_end", "boot_idt32_pointer",
    "boot_idt64", "boot_idt64_end", "boot_idt64_pointer",
    "boot_idt32_published", "boot_stack", "boot_stack_top", "idt",
    "boot_early_isr2_32", "boot_early_isr2_32_end",
    "boot_early_catchall_32", "boot_early_catchall_32_end",
    "boot_early_isr2_64", "boot_early_isr2_64_end",
    "boot_early_catchall_64", "boot_early_catchall_64_end",
]
INSTRUCTION_RE = re.compile(r"^\s*([0-9a-f]+):\s+([a-z][a-z0-9.]*)\s*(.*?)\s*$")
PROLOGUE_ALLOWED = {"cli", "lgdt", "lgdtl", "ljmp", "mov", "movw", "movl", "xor"}
PROLOGUE_LIMIT = 16


def fail(message: str) -> None:
    print(f"error: {message}", file=sys.stderr)
    raise SystemExit(1)


def tool_output(*command: str) -> str:
    try:
        return subprocess.run(command, check=True, text=True,
                              capture_output=True).stdout
    except (OSError, subprocess.CalledProcessError) as error:
        print(f"error: early-IDT policy tool failed: {' '.join(command)}",
              file=sys.stderr)
        raise SystemExit(1) from error


def read_symbols(elf: Path) -> dict[str, int]:
    symbols: dict[str, int] = {}
    for line in tool_output("nm", "-n", str(elf)).splitlines():
        fields = line.split()
        if len(fields) >= 3:
            symbols[fields[2]] = int(fields[0], 16)
    return symbols


def read_sections(elf: Path) -> list[tuple[int, int, int]]:
    sections: list[tuple[int, int, int]] = []
    header_re = re.compile(
        r"^\s*\[\s*\d+\]\s+(\S+)\s+\S+\s+([0-9a-f]+)\s+([0-9a-f]+)\s+([0-9a-f]+)")
    for line in tool_output("readelf", "-SW", str(elf)).splitlines():
        match = header_re.match(line)
        if match and match.group(1) != "NULL":
            address = int(match.group(2), 16)
            offset = int(match.group(3), 16)
            size = int(match.group(4), 16)
            if address:
                sections.append((address, offset, size))
    return sections


def read_virtual(elf: Path, sections: list[tuple[int, int, int]],
                 address: int, size: int) -> bytes:
    for base, offset, section_size in sections:
        if base <= address and address + size <= base + section_size:
            data = elf.read_bytes()
            return data[offset + (address - base):offset + (address - base) + size]
    fail(f"virtual range 0x{address:x}+0x{size:x} is not in any loaded section")


def parse_instructions(disassembly: str,
                       first: int, past: int) -> list[tuple[int, str, str]]:
    instructions: list[tuple[int, str, str]] = []
    for line in disassembly.splitlines():
        match = INSTRUCTION_RE.match(line)
        if not match:
            continue
        address = int(match.group(1), 16)
        if first <= address < past:
            instructions.append((address, match.group(2), match.group(3)))
    return instructions


def disassemble_i386(elf: Path, sections: list[tuple[int, int, int]],
                     first: int, past: int) -> list[tuple[int, str, str]]:
    data = read_virtual(elf, sections, first, past - first)
    with tempfile.NamedTemporaryFile(suffix=".bin") as raw:
        raw.write(data)
        raw.flush()
        disassembly = tool_output(
            "objdump", "-D", "-b", "binary", "-m", "i386", "-M", "att",
            "--no-show-raw-insn", f"--adjust-vma=0x{first:x}", raw.name)
    instructions = parse_instructions(disassembly, first, past)
    if not instructions or instructions[0][0] != first:
        fail(f"could not decode 32-bit region at 0x{first:x}")
    return instructions


def operand_address(operands: str) -> int | None:
    match = re.match(r"(?:0x)?([0-9a-f]+)(?:\s|$|\s*<|\(|,)", operands.strip())
    return int(match.group(1), 16) if match else None


def check_terminal_stub(name: str, instructions: list[tuple[int, str, str]],
                        first: int, past: int) -> None:
    if not instructions or instructions[0][0] != first:
        fail(f"could not decode terminal stub {name}")
    for address, mnemonic, operands in instructions:
        site = f"{name} 0x{address:x} ({mnemonic} {operands})".rstrip()
        if mnemonic.startswith("call"):
            fail(f"terminal CFG contains a call at {site}")
        if mnemonic.startswith(("ret", "lret", "iret", "sysret")):
            fail(f"terminal CFG contains a return at {site}")
        if mnemonic in {"int", "int1", "int3", "into", "syscall", "sysenter"}:
            fail(f"terminal CFG contains a software entry at {site}")
        if mnemonic.startswith("push"):
            fail(f"terminal CFG pushes at {site}")
        if mnemonic.startswith("j") or mnemonic.startswith("loop"):
            target = operand_address(operands)
            if target is None:
                fail(f"terminal CFG contains an indirect branch at {site}")
            if not first <= target < past:
                fail(f"terminal CFG branch escapes {name} at {site}")
    last_address, last_mnemonic, last_operands = instructions[-1]
    last_target = operand_address(last_operands)
    if last_mnemonic != "jmp" or last_target is None or \
            not first <= last_target < past:
        fail(f"terminal CFG can fall through past {name} after 0x{last_address:x}")


def check_gate_tables(elf: Path, sections: list[tuple[int, int, int]],
                      symbols: dict[str, int]) -> None:
    table32 = read_virtual(elf, sections, symbols["boot_idt32"], 256 * 8)
    if symbols["boot_idt32_end"] - symbols["boot_idt32"] != 256 * 8:
        fail("bootstrap32 table is not 256 8-byte gates")
    for vector in range(256):
        low, selector, zero, attributes, high = struct.unpack_from(
            "<HHBBH", table32, vector * 8)
        target = low | high << 16
        expected = symbols["boot_early_isr2_32"] if vector == 2 else \
            symbols["boot_early_catchall_32"]
        if selector != 0x38:
            fail(f"bootstrap32 gate selector drifted vector={vector} "
                 f"selector=0x{selector:x}")
        if attributes != 0x8e or zero != 0:
            fail(f"bootstrap32 gate attributes drifted vector={vector} "
                 f"attributes=0x{attributes:x}")
        if target != expected:
            kind = "vector-2" if vector == 2 else "catch-all"
            fail(f"bootstrap32 {kind} gate target drifted vector={vector} "
                 f"target=0x{target:x}")
    limit, base = struct.unpack_from(
        "<HI", read_virtual(elf, sections, symbols["boot_idt32_pointer"], 6))
    if limit != 256 * 8 - 1 or base != symbols["boot_idt32"]:
        fail("bootstrap32 IDTR pointer drifted")

    table64 = read_virtual(elf, sections, symbols["boot_idt64"], 256 * 16)
    if symbols["boot_idt64_end"] - symbols["boot_idt64"] != 256 * 16:
        fail("bootstrap64 table is not 256 16-byte gates")
    for vector in range(256):
        low, selector, ist, attributes, middle, upper, reserved = \
            struct.unpack_from("<HHBBHII", table64, vector * 16)
        target = low | middle << 16 | upper << 32
        expected = symbols["boot_early_isr2_64"] if vector == 2 else \
            symbols["boot_early_catchall_64"]
        if selector != 0x08:
            fail(f"bootstrap64 gate selector drifted vector={vector} "
                 f"selector=0x{selector:x}")
        if ist != 0:
            fail(f"bootstrap64 gate uses IST before the TSS exists "
                 f"vector={vector} ist={ist}")
        if attributes != 0x8e or reserved != 0:
            fail(f"bootstrap64 gate attributes drifted vector={vector} "
                 f"attributes=0x{attributes:x}")
        if target != expected:
            kind = "vector-2" if vector == 2 else "catch-all"
            fail(f"bootstrap64 {kind} gate target drifted vector={vector} "
                 f"target=0x{target:x}")
    limit, base = struct.unpack_from(
        "<HI", read_virtual(elf, sections, symbols["boot_idt64_pointer"], 6))
    if limit != 256 * 16 - 1 or base != symbols["boot_idt64"]:
        fail("bootstrap64 IDTR pointer drifted")


def check_prologue(instructions: list[tuple[int, str, str]],
                   symbols: dict[str, int]) -> None:
    lidt_sites = [(address, operands) for address, mnemonic, operands in
                  instructions if mnemonic in {"lidt", "lidtl"}]
    if len(lidt_sites) != 2:
        fail(f"bootstrap lidt inventory drifted: expected two bootstrap lidt "
             f"publications, found {len(lidt_sites)}")
    first_lidt, first_operand = lidt_sites[0]
    second_lidt, second_operand = lidt_sites[1]
    if operand_address(first_operand) != symbols["boot_idt32_pointer"]:
        fail("first kernel lidt must publish boot_idt32_pointer")
    if operand_address(second_operand) != symbols["boot_idt64_pointer"]:
        fail("second kernel lidt must publish boot_idt64_pointer")

    before = [entry for entry in instructions if entry[0] < first_lidt]
    if len(before) > PROLOGUE_LIMIT:
        fail(f"first kernel lidt is published late: {len(before)} instructions "
             f"precede it")
    lgdt_seen = 0
    for address, mnemonic, operands in before:
        site = f"0x{address:x} ({mnemonic} {operands})".rstrip()
        if mnemonic not in PROLOGUE_ALLOWED:
            fail(f"unreviewed instruction before first kernel lidt at {site}")
        if mnemonic in {"lgdt", "lgdtl"}:
            lgdt_seen += 1
            if operand_address(operands) is None:
                fail(f"pre-lidt lgdt operand is unreviewed at {site}")
            continue
        if mnemonic.startswith("mov") or mnemonic == "xor":
            destination = operands.split(",")[-1].strip()
            if not destination.startswith("%"):
                fail(f"unreviewed instruction before first kernel lidt at {site}")
    if lgdt_seen != 1:
        fail("prologue must own the GDT exactly once before the first lidt")

    banned_re = re.compile(r"^(sti|in[bwl]?|ins[bwl]?|out[bwl]?|outs[bwl]?|"
                           r"int|int1|int3|into|call[a-z]*|iret[a-z]*|"
                           r"ret[a-z]*|sidt[a-z]*|hlt)$")
    for address, mnemonic, operands in instructions:
        site = f"0x{address:x} ({mnemonic} {operands})".rstrip()
        if banned_re.match(mnemonic):
            fail(f"forbidden instruction in the boot-entry interval at {site}")

    cr0_writes = [address for address, mnemonic, operands in instructions
                  if mnemonic.startswith("mov") and operands.endswith("%cr0")]
    if len(cr0_writes) != 1:
        fail("expected exactly one CR0 write in the 32-bit prologue")
    ordered = [entry for entry in instructions if entry[0] >= cr0_writes[0]]
    if len(ordered) < 3:
        fail("long-mode handoff is truncated")
    handoff = ordered[1]
    far_jump = ordered[2]
    if handoff[0] != second_lidt:
        fail("long-mode IDTR handoff must immediately follow the CR0 write")
    if far_jump[1] != "ljmp" or "$0x8," not in far_jump[2].replace(" ", ""):
        fail("long-mode far jump must immediately follow the IDTR handoff")
    if cr0_writes[0] <= first_lidt:
        fail("first kernel lidt must precede the paging CR0 write")


def check_long_mode_region(elf: Path, symbols: dict[str, int],
                           sorted_symbols: list[tuple[int, str]]) -> None:
    disassembly = tool_output("objdump", "-d", "--no-show-raw-insn", str(elf))
    prologue_first = symbols["multiboot_entry"]
    prologue_past = symbols["long_mode_entry"]
    early_first = EARLY_TRAP_BASE
    early_past = EARLY_TRAP_BASE + 0x200
    # privilege_init is a static single-call C function and is inlined into
    # kernel_main by the pinned compiler; bound the runtime publication there.
    runtime_first = symbols["kernel_main"]
    runtime_past = next(address for address, _ in sorted_symbols
                        if address > runtime_first)

    lidt_sites = []
    sidt_sites = []
    sti_sites = []
    for line in disassembly.splitlines():
        match = INSTRUCTION_RE.match(line)
        if not match:
            continue
        address = int(match.group(1), 16)
        mnemonic = match.group(2)
        if mnemonic in {"lidt", "lidtl"}:
            lidt_sites.append(address)
        if mnemonic in {"sidt", "sidtl"}:
            sidt_sites.append(address)
        if mnemonic == "sti" and not prologue_first <= address < prologue_past:
            sti_sites.append(address)
    if sidt_sites:
        fail(f"sidt is not a reviewed instruction (0x{sidt_sites[0]:x})")
    if sti_sites:
        fail(f"sti outside the reviewed prologue at 0x{sti_sites[0]:x}")
    runtime_lidt = [address for address in lidt_sites
                    if not prologue_first <= address < prologue_past]
    if len(runtime_lidt) != 1 or not \
            runtime_first <= runtime_lidt[0] < runtime_past:
        fail("the runtime IDT publication must be the single lidt inside "
             "privilege_init/kernel_main")

    for name in ("boot_early_isr2_64", "boot_early_catchall_64"):
        first = symbols[name]
        past = symbols[f"{name}_end"]
        instructions = parse_instructions(disassembly, first, past)
        check_terminal_stub(name, instructions, first, past)
    if not parse_instructions(disassembly, early_first, early_past):
        fail("bootstrap stubs are missing from the final ELF text")


def check_sources(boot_source: Path, kernel_source: Path) -> None:
    boot_text = boot_source.read_text()
    if boot_text.count("lidt boot_idt32_pointer") != 1 or \
            boot_text.count("lidt boot_idt64_pointer") != 1 or \
            len(re.findall(r"^\s+lidt\s", boot_text, re.MULTILINE)) != 2:
        fail("boot.S bootstrap lidt source inventory drifted")
    if re.search(r"^\s+(sti|sidt)\b", boot_text, re.MULTILINE):
        fail("boot.S contains an unreviewed sti/sidt site")
    kernel_text = kernel_source.read_text()
    if kernel_text.count("lidt") != 1 or \
            '__asm__ volatile ("lidt %0" : : "m"(idtr));' not in kernel_text:
        fail("kernel.c runtime lidt source inventory drifted")
    if "sidt" in kernel_text:
        fail("kernel.c contains an unreviewed sidt site")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("elf", type=Path)
    parser.add_argument("--boot-source", type=Path, default=Path("boot/boot.S"))
    parser.add_argument("--kernel-source", type=Path,
                        default=Path("boot/kernel.c"))
    args = parser.parse_args()
    if not args.elf.is_file():
        fail(f"missing early-IDT policy ELF: {args.elf}")

    check_sources(args.boot_source, args.kernel_source)
    symbols = read_symbols(args.elf)
    for name in REQUIRED_SYMBOLS:
        if name not in symbols:
            fail(f"early-IDT policy symbol missing: {name}")
    for name, expected in EARLY_SLOTS.items():
        if symbols[name] != expected:
            fail(f"bootstrap stub moved: {name}=0x{symbols[name]:x} "
                 f"expected=0x{expected:x}")

    sections = read_sections(args.elf)
    check_gate_tables(args.elf, sections, symbols)

    prologue = disassemble_i386(args.elf, sections, symbols["multiboot_entry"],
                                symbols["long_mode_entry"])
    check_prologue(prologue, symbols)

    for name in ("boot_early_isr2_32", "boot_early_catchall_32"):
        first = symbols[name]
        past = symbols[f"{name}_end"]
        instructions = disassemble_i386(args.elf, sections, first, past)
        check_terminal_stub(name, instructions, first, past)

    sorted_symbols = sorted((address, name) for name, address in symbols.items())
    check_long_mode_region(args.elf, symbols, sorted_symbols)

    print("EARLY-IDT-POLICY tables=2 gates=512 stubs=4 lidt=3 sidt=0 "
          "prologue=reviewed handoff=one-instruction result=PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
