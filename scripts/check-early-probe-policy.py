#!/usr/bin/env python3
"""Bind the early-IDT injection probes to their reviewed final-ELF shape.

The bootstrap32-ud image must place one real ud2 as the first instruction
after the first kernel lidt, before any page-table/CR/MSR/PCI/generated-code
work, and its catch-all stub must attest the exact no-error #UD frame before
emitting the probe terminal record.  The bootstrap64-nmi image must publish
the early readiness record only after the 64-bit early table and boot stack
are live, dominate the unreachable kernel_main call with a halt loop, and its
vector-2 stub must attest the exact IST-0 boot-stack frame with IF clear.
Every instruction of the probe-touched regions is matched exactly, so a
synthetic int substitute, a moved probe or readiness site, a duplicated
output site, a wrong exit code, a forged record, or any added escape edge is
rejected.  This is final-ELF evidence, not a proof of x86 delivery.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

def load_serial_protocol(path):
    """Map "<family>/<TAG>" to the exact guest line prefix from the generated
    serial vocabulary; the checker never spells a record identity itself."""
    records = {}
    for line in Path(path).read_text(encoding="utf-8").splitlines():
        fields = line.split("\t")
        if fields[0] == "record":
            records[f"{fields[1]}/{fields[2]}"] = fields[4]
        elif fields[0] == "family":
            records[fields[1]] = fields[3]
    if not records:
        raise SystemExit(f"error: empty serial protocol vocabulary: {path}")
    return records


SERIAL = load_serial_protocol(
    os.environ.get("LEANOS_SERIAL_PROTOCOL_TSV", "build/boot/serial-protocol.tsv")
)


INSTRUCTION_RE = re.compile(r"^\s*([0-9a-f]+):\s+([a-z][a-z0-9.]*)\s*(.*?)\s*$")
UD_TERMINAL_RECORD = (
    SERIAL["18/EARLY-TERMINAL"] + " phase=bootstrap32 table=bootstrap32 "
    "width=legacy8 vector=6 reason=invalid-opcode error=none "
    "frame=eip,cs,eflags stack=boot target=stub32 latch=terminal return=none\n"
)
UD_FAILURE_RECORD = (
    SERIAL["18/EARLY-TERMINAL"] + " status=FAIL phase=bootstrap32 "
    "reason=probe-frame-policy\n"
)
NMI_TERMINAL_RECORD = (
    SERIAL["18/EARLY-TERMINAL"] + " phase=bootstrap64 table=bootstrap64 "
    "width=long16 vector=2 reason=non-maskable-interrupt error=none "
    "frame=rip,cs,rflags,rsp,ss stack=boot target=stub64 latch=terminal "
    "return=none\n"
)
NMI_FAILURE_RECORD = (
    SERIAL["18/EARLY-TERMINAL"] + " status=FAIL phase=bootstrap64 "
    "reason=probe-frame-policy\n"
)
NMI_READY_RECORD = (
    SERIAL["18/EARLY64-READY"] + " phase=bootstrap64 table=bootstrap64 "
    "width=long16 stack=boot if=0 tss=none runtime-idt=unpublished "
    "result=PASS\n"
)
CATCHALL32_PRODUCTION_RECORD = (
    SERIAL["18/EARLY-TERMINAL"] + " phase=bootstrap32 table=bootstrap32 "
    "width=legacy8 vector=other class=exception stack=boot target=stub32 "
    "latch=terminal return=none\n"
)
ISR2_64_PRODUCTION_RECORD = (
    SERIAL["18/EARLY-TERMINAL"] + " phase=bootstrap64 table=bootstrap64 "
    "width=long16 vector=2 class=nmi stack=boot target=stub64 "
    "latch=terminal return=none\n"
)


def fail(message: str) -> None:
    print(f"error: {message}", file=sys.stderr)
    raise SystemExit(1)


def tool_output(*command: str) -> str:
    try:
        return subprocess.run(command, check=True, text=True,
                              capture_output=True).stdout
    except (OSError, subprocess.CalledProcessError) as error:
        print(f"error: early-probe policy tool failed: {' '.join(command)}",
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


def normalize(operands: str) -> str:
    text = operands.split("#", 1)[0]
    text = re.sub(r"<[^>]*>", "", text)
    return text.replace(" ", "")


def parse_instructions(disassembly: str,
                       first: int, past: int) -> list[tuple[int, str, str]]:
    instructions: list[tuple[int, str, str]] = []
    for line in disassembly.splitlines():
        match = INSTRUCTION_RE.match(line)
        if not match:
            continue
        address = int(match.group(1), 16)
        if first <= address < past:
            instructions.append(
                (address, match.group(2), normalize(match.group(3))))
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


def check_record(elf: Path, sections: list[tuple[int, int, int]],
                 symbols: dict[str, int], name: str, expected: str) -> None:
    if name not in symbols or f"{name}_end" not in symbols:
        fail(f"early-probe record symbol missing: {name}")
    first = symbols[name]
    past = symbols[f"{name}_end"]
    if past - first != len(expected.encode()):
        fail(f"early-probe record {name} length drifted")
    observed = read_virtual(elf, sections, first, past - first)
    if observed != expected.encode():
        fail(f"early-probe record {name} content drifted")


class Matcher:
    """Match one decoded region against an exact expected instruction list."""

    def __init__(self, name: str,
                 instructions: list[tuple[int, str, str]]) -> None:
        self.name = name
        self.instructions = instructions
        self.index = 0
        self.labels: dict[str, int] = {}

    def current_address(self) -> int:
        if self.index >= len(self.instructions):
            fail(f"{self.name} region is truncated")
        return self.instructions[self.index][0]

    def label(self, name: str) -> None:
        self.labels[name] = self.current_address()

    def expect(self, mnemonic: str, operands: str = "") -> None:
        if self.index >= len(self.instructions):
            fail(f"{self.name} region is truncated before {mnemonic}")
        address, observed_mnemonic, observed_operands = \
            self.instructions[self.index]
        template = operands.replace(" ", "")
        accepted = {template}
        for label, value in self.labels.items():
            token = "{" + label + "}"
            accepted = {
                candidate.replace(token, spelling)
                for candidate in accepted
                for spelling in (f"{value:x}", f"0x{value:x}")
            }
        if observed_mnemonic != mnemonic or observed_operands not in accepted:
            fail(f"{self.name} instruction drifted at 0x{address:x}: "
                 f"observed '{observed_mnemonic} {observed_operands}' "
                 f"expected '{mnemonic} {template}'")
        self.index += 1

    def finish(self) -> None:
        if self.index != len(self.instructions):
            address = self.instructions[self.index][0]
            fail(f"{self.name} contains unreviewed trailing instructions "
                 f"at 0x{address:x}")


def serial_loop32(matcher: Matcher, record: int, length: int) -> None:
    matcher.expect("mov", f"$0x{record:x},%esi")
    matcher.expect("mov", f"$0x{length:x},%ecx")
    matcher.label("poll")
    matcher.expect("mov", "$0x3fd,%dx")
    matcher.label("wait")
    matcher.expect("in", "(%dx),%al")
    matcher.expect("test", "$0x20,%al")
    matcher.expect("je", "{wait}")
    matcher.expect("mov", "(%esi),%al")
    matcher.expect("mov", "$0x3f8,%dx")
    matcher.expect("out", "%al,(%dx)")
    matcher.expect("add", "$0x1,%esi")
    matcher.expect("sub", "$0x1,%ecx")
    matcher.expect("jne", "{poll}")


def serial_loop64(matcher: Matcher, record: int, length: int) -> None:
    address = matcher.current_address()
    displacement = record - (address + 7)
    prefix = "-" if displacement < 0 else ""
    matcher.expect("lea", f"{prefix}0x{abs(displacement):x}(%rip),%rsi")
    matcher.expect("mov", f"$0x{length:x},%ecx")
    matcher.label("poll")
    matcher.expect("mov", "$0x3fd,%dx")
    matcher.label("wait")
    matcher.expect("in", "(%dx),%al")
    matcher.expect("test", "$0x20,%al")
    matcher.expect("je", "{wait}")
    matcher.expect("mov", "(%rsi),%al")
    matcher.expect("mov", "$0x3f8,%dx")
    matcher.expect("out", "%al,(%dx)")
    matcher.expect("inc", "%rsi")
    matcher.expect("dec", "%ecx")
    matcher.expect("jne", "{poll}")


def debug_exit(matcher: Matcher, value: int) -> None:
    matcher.expect("mov", f"$0x{value:x},%al")
    matcher.expect("mov", "$0xf4,%dx")
    matcher.expect("out", "%al,(%dx)")
    matcher.label("halt")
    matcher.expect("hlt")
    matcher.expect("jmp", "{halt}")


def match_catchall32(instructions: list[tuple[int, str, str]],
                     symbols: dict[str, int], probe: bool) -> None:
    matcher = Matcher("bootstrap32 catch-all stub", instructions)
    record = symbols["early32_fault_record"]
    length = symbols["early32_fault_record_end"] - record
    matcher.expect("cli")
    matcher.expect("cld")
    if probe:
        failure = symbols["early32_probe_failure_record"]
        failure_length = symbols["early32_probe_failure_record_end"] - failure
        matcher.labels["fail"] = _probe32_failure_address(instructions)
        matcher.expect("cmp",
                       f"$0x{symbols['boot_stack_top'] - 12:x},%esp")
        matcher.expect("jne", "{fail}")
        matcher.expect("cmpl",
                       f"$0x{symbols['boot_bootstrap32_ud_probe']:x},(%esp)")
        matcher.expect("jne", "{fail}")
        matcher.expect("cmpl", "$0x38,0x4(%esp)")
        matcher.expect("jne", "{fail}")
        matcher.expect("testl", "$0x200,0x8(%esp)")
        matcher.expect("jne", "{fail}")
    serial_loop32(matcher, record, length)
    debug_exit(matcher, 0x16)
    if probe:
        if matcher.current_address() != matcher.labels["fail"]:
            fail("bootstrap32 probe failure path is misplaced")
        serial_loop32(matcher, failure, failure_length)
        debug_exit(matcher, 0x18)
    matcher.finish()


def _probe32_failure_address(
        instructions: list[tuple[int, str, str]]) -> int:
    # The failure path begins at the target every guard branch shares; it is
    # re-verified positionally after the success path is matched.
    for _address, mnemonic, operands in instructions:
        if mnemonic == "jne" and re.fullmatch(r"0x?[0-9a-f]+|[0-9a-f]+",
                                              operands):
            return int(operands.removeprefix("0x"), 16)
    fail("bootstrap32 probe stub has no frame-guard branch")


def match_isr2_32(instructions: list[tuple[int, str, str]],
                  symbols: dict[str, int]) -> None:
    matcher = Matcher("bootstrap32 vector-2 stub", instructions)
    record = symbols["early32_nmi_record"]
    length = symbols["early32_nmi_record_end"] - record
    matcher.expect("cli")
    matcher.expect("cld")
    serial_loop32(matcher, record, length)
    debug_exit(matcher, 0x16)
    matcher.finish()


def match_isr2_64(instructions: list[tuple[int, str, str]],
                  symbols: dict[str, int], probe: bool) -> None:
    matcher = Matcher("bootstrap64 vector-2 stub", instructions)
    record = symbols["early64_nmi_record"]
    length = symbols["early64_nmi_record_end"] - record
    matcher.expect("cli")
    matcher.expect("cld")
    if probe:
        failure = symbols["early64_probe_failure_record"]
        failure_length = symbols["early64_probe_failure_record_end"] - failure
        matcher.labels["fail"] = _probe64_failure_address(instructions)
        matcher.expect("cmp",
                       f"$0x{symbols['boot_stack_top'] - 40:x},%rsp")
        matcher.expect("jne", "{fail}")
        matcher.expect("cmpq", "$0x8,0x8(%rsp)")
        matcher.expect("jne", "{fail}")
        matcher.expect("testl", "$0x200,0x10(%rsp)")
        matcher.expect("jne", "{fail}")
    serial_loop64(matcher, record, length)
    debug_exit(matcher, 0x17)
    if probe:
        if matcher.current_address() != matcher.labels["fail"]:
            fail("bootstrap64 probe failure path is misplaced")
        serial_loop64(matcher, failure, failure_length)
        debug_exit(matcher, 0x18)
    matcher.finish()


def _probe64_failure_address(
        instructions: list[tuple[int, str, str]]) -> int:
    for _address, mnemonic, operands in instructions:
        if mnemonic == "jne" and re.fullmatch(r"0x?[0-9a-f]+|[0-9a-f]+",
                                              operands):
            return int(operands.removeprefix("0x"), 16)
    fail("bootstrap64 probe stub has no frame-guard branch")


def match_catchall64(instructions: list[tuple[int, str, str]],
                     symbols: dict[str, int]) -> None:
    matcher = Matcher("bootstrap64 catch-all stub", instructions)
    record = symbols["early64_fault_record"]
    length = symbols["early64_fault_record_end"] - record
    matcher.expect("cli")
    matcher.expect("cld")
    serial_loop64(matcher, record, length)
    debug_exit(matcher, 0x17)
    matcher.finish()


def match_tail(instructions: list[tuple[int, str, str]],
               symbols: dict[str, int], probe: bool) -> None:
    """Exact-match long_mode_entry with RIP-relative displacements resolved."""
    matcher = Matcher("long-mode entry", instructions)
    fixed = [
        ("mov", "$0x10,%ax"), ("mov", "%eax,%ds"), ("mov", "%eax,%es"),
        ("mov", "%eax,%ss"), ("xor", "%ax,%ax"), ("mov", "%eax,%fs"),
        ("mov", "%eax,%gs"),
        ("mov", f"$0x{symbols['boot_stack_top']:x},%rsp"),
        ("xor", "%rbp,%rbp"),
    ]
    for mnemonic, operands in fixed:
        matcher.expect(mnemonic, operands)
    if probe:
        # The readiness site must begin exactly at the exported checkpoint
        # symbol, after the stack publication, and its halt loop must
        # dominate the otherwise-unreachable kernel_main call below.
        if matcher.current_address() != symbols["boot_bootstrap64_nmi_ready"]:
            fail("long-mode readiness site drifted from its exported symbol")
        record = symbols["early64_ready_record"]
        length = symbols["early64_ready_record_end"] - record
        serial_loop64(matcher, record, length)
        matcher.label("halt")
        matcher.expect("hlt")
        matcher.expect("jmp", "{halt}")
    address = matcher.current_address()
    magic = symbols["multiboot_magic"] - (address + 6)
    matcher.expect("mov", _rip_operand(magic, "%edi"))
    address = matcher.current_address()
    info = symbols["multiboot_info"] - (address + 6)
    matcher.expect("mov", _rip_operand(info, "%esi"))
    matcher.labels["kernel_main"] = symbols["kernel_main"]
    matcher.expect("call", "{kernel_main}")
    matcher.label("stop")
    matcher.expect("cli")
    matcher.expect("hlt")
    matcher.expect("jmp", "{stop}")
    matcher.finish()


def _rip_operand(displacement: int, register: str) -> str:
    prefix = "-" if displacement < 0 else ""
    return f"{prefix}0x{abs(displacement):x}(%rip),{register}"


def check_prologue_probe(instructions: list[tuple[int, str, str]],
                         symbols: dict[str, int], expected: bool) -> None:
    ud_sites = [address for address, mnemonic, _ in instructions
                if mnemonic in {"ud2", "ud2a"}]
    if not expected:
        if ud_sites:
            fail(f"unreviewed ud2 in the entry prologue at 0x{ud_sites[0]:x}")
        return
    if len(ud_sites) != 1:
        fail(f"bootstrap32 probe requires exactly one prologue ud2, "
             f"found {len(ud_sites)}")
    probe_address = symbols["boot_bootstrap32_ud_probe"]
    if ud_sites[0] != probe_address or \
            probe_address != symbols["boot_idt32_published"]:
        fail("bootstrap32 ud2 probe site moved from the publication boundary")
    lidt_indices = [index for index, (_, mnemonic, _) in
                    enumerate(instructions) if mnemonic in {"lidt", "lidtl"}]
    if not lidt_indices:
        fail("bootstrap32 probe is not preceded by the bootstrap32 lidt")
    first_lidt = lidt_indices[0]
    if first_lidt + 1 >= len(instructions) or \
            instructions[first_lidt + 1][0] != probe_address or \
            instructions[first_lidt + 1][1] not in {"ud2", "ud2a"}:
        fail("bootstrap32 ud2 is not the first instruction after the first "
             "bootstrap lidt")


def check_sources(boot_source: Path) -> None:
    text = boot_source.read_text()
    ud_site = ("boot_idt32_published:\n"
               "#ifdef LEANOS_BOOTSTRAP32_UD_PROBE")
    if ud_site not in text:
        fail("boot.S bootstrap32 probe must sit at the publication label")
    if text.count("\nboot_bootstrap32_ud_probe:\n    ud2\n") != 1:
        fail("boot.S bootstrap32 probe is not a single real ud2 opcode")
    if text.count("\nboot_bootstrap64_nmi_ready:\n") != 1:
        fail("boot.S bootstrap64 readiness site inventory drifted")
    ready_site = ("    xor %rbp, %rbp\n"
                  "#ifdef LEANOS_BOOTSTRAP64_NMI_PROBE")
    if ready_site not in text:
        fail("boot.S bootstrap64 readiness site must follow the boot-stack "
             "publication")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("elf", type=Path)
    parser.add_argument("probe", choices=["bootstrap32-ud", "bootstrap64-nmi"])
    parser.add_argument("--boot-source", type=Path, default=Path("boot/boot.S"))
    args = parser.parse_args()
    if not args.elf.is_file():
        fail(f"missing early-probe policy ELF: {args.elf}")

    check_sources(args.boot_source)
    symbols = read_symbols(args.elf)
    sections = read_sections(args.elf)
    required = [
        "multiboot_entry", "long_mode_entry", "kernel_main", "boot_stack_top",
        "multiboot_magic", "multiboot_info", "boot_idt32_published",
        "boot_early_isr2_32", "boot_early_isr2_32_end",
        "boot_early_catchall_32", "boot_early_catchall_32_end",
        "boot_early_isr2_64", "boot_early_isr2_64_end",
        "boot_early_catchall_64", "boot_early_catchall_64_end",
        "early32_nmi_record", "early32_nmi_record_end",
        "early32_fault_record", "early32_fault_record_end",
        "early64_nmi_record", "early64_nmi_record_end",
        "early64_fault_record", "early64_fault_record_end",
    ]
    if args.probe == "bootstrap32-ud":
        required += ["boot_bootstrap32_ud_probe",
                     "early32_probe_failure_record",
                     "early32_probe_failure_record_end"]
        forbidden = ["boot_bootstrap64_nmi_ready", "early64_ready_record",
                     "early64_probe_failure_record"]
    else:
        required += ["boot_bootstrap64_nmi_ready",
                     "early64_ready_record", "early64_ready_record_end",
                     "early64_probe_failure_record",
                     "early64_probe_failure_record_end"]
        forbidden = ["boot_bootstrap32_ud_probe",
                     "early32_probe_failure_record"]
    for name in required:
        if name not in symbols:
            fail(f"early-probe policy symbol missing: {name}")
    for name in forbidden:
        if name in symbols:
            fail(f"foreign probe symbol present in this image: {name}")

    prologue = disassemble_i386(args.elf, sections, symbols["multiboot_entry"],
                                symbols["long_mode_entry"])
    check_prologue_probe(prologue, symbols,
                         expected=args.probe == "bootstrap32-ud")

    stub32_nmi = disassemble_i386(
        args.elf, sections, symbols["boot_early_isr2_32"],
        symbols["boot_early_isr2_32_end"])
    match_isr2_32(stub32_nmi, symbols)
    stub32_catchall = disassemble_i386(
        args.elf, sections, symbols["boot_early_catchall_32"],
        symbols["boot_early_catchall_32_end"])
    match_catchall32(stub32_catchall, symbols,
                     probe=args.probe == "bootstrap32-ud")

    disassembly = tool_output("objdump", "-d", "--no-show-raw-insn",
                              str(args.elf))
    stub64_nmi = parse_instructions(disassembly, symbols["boot_early_isr2_64"],
                                    symbols["boot_early_isr2_64_end"])
    match_isr2_64(stub64_nmi, symbols, probe=args.probe == "bootstrap64-nmi")
    stub64_catchall = parse_instructions(
        disassembly, symbols["boot_early_catchall_64"],
        symbols["boot_early_catchall_64_end"])
    match_catchall64(stub64_catchall, symbols)

    for name in ("long_mode_entry", "long_mode_entry_end"):
        if name not in symbols:
            fail(f"long-mode entry boundary symbol missing: {name}")
    tail = parse_instructions(disassembly, symbols["long_mode_entry"],
                              symbols["long_mode_entry_end"])
    if not tail:
        fail("could not decode long-mode entry region")
    match_tail(tail, symbols, probe=args.probe == "bootstrap64-nmi")

    check_record(args.elf, sections, symbols, "early32_nmi_record",
                 SERIAL["18/EARLY-TERMINAL"] + " phase=bootstrap32 "
                 "table=bootstrap32 width=legacy8 vector=2 class=nmi "
                 "stack=boot target=stub32 latch=terminal return=none\n")
    check_record(args.elf, sections, symbols, "early64_fault_record",
                 SERIAL["18/EARLY-TERMINAL"] + " phase=bootstrap64 "
                 "table=bootstrap64 width=long16 vector=other "
                 "class=exception stack=boot target=stub64 latch=terminal "
                 "return=none\n")
    if args.probe == "bootstrap32-ud":
        check_record(args.elf, sections, symbols, "early32_fault_record",
                     UD_TERMINAL_RECORD)
        check_record(args.elf, sections, symbols,
                     "early32_probe_failure_record", UD_FAILURE_RECORD)
        check_record(args.elf, sections, symbols, "early64_nmi_record",
                     ISR2_64_PRODUCTION_RECORD)
    else:
        check_record(args.elf, sections, symbols, "early32_fault_record",
                     CATCHALL32_PRODUCTION_RECORD)
        check_record(args.elf, sections, symbols, "early64_nmi_record",
                     NMI_TERMINAL_RECORD)
        check_record(args.elf, sections, symbols,
                     "early64_probe_failure_record", NMI_FAILURE_RECORD)
        check_record(args.elf, sections, symbols, "early64_ready_record",
                     NMI_READY_RECORD)

    print(f"EARLY-PROBE-POLICY probe={args.probe} placement=exact "
          f"frame-guards=verified records=exact result=PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
