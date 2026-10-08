#!/usr/bin/env python3
"""Check a subject built from subjects/ against the ring-3 assembly policy (#484).

Two modes share one instruction policy:

  object OBJ    the relocatable object scripts/build-subject.sh links with
                subjects/subject.ld, before it is renamed to its slot;
  elf ELF SLOT  a final image ELF, re-checking the slot's linked text, so the
                policy covers the bytes that actually boot.

The policy: every executable byte of the subject is decodable code; no
privileged or system instruction (cli, sti, hlt, port I/O, MSR and control- or
debug-register access, descriptor-table loads, TLB and cache control, iret,
sysret, swapgs, stac/clac, ...); no segment-register loads or far transfers;
no x87, MMX, SSE or AVX register use (extended state is denied at CPL3); and
the kernel is entered only through `int $0x80` (no syscall, sysenter, int3,
into or any other vector).  The object mode also requires a self-contained
object (no undefined symbols, so no libc) whose sections and sizes match the
slot layout of subjects/subject.ld.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys

PAGE_BYTES = 4096
STACK_BYTES = 2048

PREFIXES = {
    "rep", "repe", "repz", "repne", "repnz", "lock", "data16", "data32",
    "addr16", "addr32", "cs", "ds", "es", "ss", "fs", "gs", "notrack", "bnd",
    "rex", "rex.w", "rex.wb", "rex.wr", "rex.wx", "rex.b", "rex.r", "rex.x",
    "rex.rb", "rex.rx", "rex.xb", "rex.rxb", "rex.wrb", "rex.wrx", "rex.wxb",
    "rex.wrxb", "{disp32}", "{disp8}", "{vex}", "{vex3}", "{evex}",
}

# Mnemonics (AT&T, with or without a size suffix) a subject may never contain.
DENIED = {
    # interrupt flag, halt
    "cli", "sti", "hlt",
    # MSRs and performance counters
    "rdmsr", "wrmsr", "wrmsrns", "rdmsrlist", "wrmsrlist", "rdpmc",
    # descriptor tables and task state
    "lgdt", "lidt", "lldt", "ltr", "sgdt", "sidt", "sldt", "str", "smsw",
    "lmsw", "clts", "arpl", "lar", "lsl", "verr", "verw",
    # TLB and cache control
    "invlpg", "invlpga", "invpcid", "invd", "wbinvd", "wbnoinvd",
    # privileged returns and fast entry
    "iret", "iretw", "iretl", "iretd", "iretq", "sysret", "sysretl",
    "sysretq", "sysexit", "sysexitl", "sysexitq", "swapgs", "syscall",
    "sysenter", "int3", "int1", "icebp", "into", "rsm",
    # SMAP override
    "stac", "clac",
    # extended state and its control
    "xsetbv", "xgetbv", "xsave", "xsavec", "xsaveopt", "xsaves", "xsave64",
    "xsavec64", "xsaveopt64", "xsaves64", "xrstor", "xrstors", "xrstor64",
    "xrstors64", "fxsave", "fxsave64", "fxrstor", "fxrstor64", "emms",
    "ldmxcsr", "stmxcsr", "vldmxcsr", "vstmxcsr",
    # monitor/wait, virtualization, enclaves, SMX
    "monitor", "mwait", "monitorx", "mwaitx", "umonitor", "umwait",
    "tpause", "vmcall", "vmmcall", "vmfunc", "vmlaunch", "vmresume", "vmxon",
    "vmxoff", "vmread", "vmwrite", "vmptrld", "vmptrst", "vmclear", "vmrun",
    "vmload", "vmsave", "stgi", "clgi", "skinit", "getsec", "encls",
    "enclu", "enclv", "pconfig", "seamcall", "seamops", "seamret", "tdcall",
    # segment bases and far transfers
    "rdfsbase", "rdgsbase", "wrfsbase", "wrgsbase", "lds", "les", "lfs",
    "lgs", "lss", "ljmp", "ljmpl", "ljmpq", "ljmpw", "lcall", "lcalll",
    "lcallq", "lcallw", "lret", "lretl", "lretq", "lretw",
    # undecodable bytes
    "(bad)",
}
PORT_IO = re.compile(r"^(?:in|ins|out|outs)[bwld]?$")
SEGMENT_REGISTER = re.compile(r"%(?:cs|ds|es|fs|gs|ss)")
SYSTEM_REGISTER = re.compile(r"%(?:cr|db|dr|tr)\d+\b")
EXTENDED_REGISTER = re.compile(r"%(?:[xyz]mm\d+|mm\d|st(?:\(\d\))?|k[0-7])\b")
LINE = re.compile(r"^\s*([0-9a-f]+):\s+(.*?)\s*$")


class PolicyError(Exception):
    pass


def run(*argv: str) -> str:
    result = subprocess.run(argv, check=False, capture_output=True, text=True)
    if result.returncode != 0:
        raise PolicyError(f"{argv[0]} failed: {result.stderr.strip()}")
    return result.stdout


def instruction_violations(path: str, section: str) -> tuple[list[str], int]:
    """Return (violations, instruction count) for one executable section."""
    listing = run("objdump", "-d", "-w", "-z", "--no-show-raw-insn",
                  "-j", section, path)
    violations: list[str] = []
    count = 0
    for line in listing.splitlines():
        match = LINE.match(line)
        if not match:
            continue
        text = match.group(2).split("#", 1)[0].strip()
        if not text:
            continue
        tokens = text.split()
        while tokens and tokens[0] in PREFIXES:
            tokens.pop(0)
        if not tokens:
            continue
        count += 1
        mnemonic = tokens[0]
        operands = " ".join(tokens[1:])
        where = f"{section} @0x{match.group(1)}: {text}"
        reason = None
        if mnemonic in DENIED:
            reason = "privileged or system instruction"
        elif PORT_IO.match(mnemonic):
            reason = "port I/O"
        elif mnemonic.startswith("int"):
            if mnemonic == "int" and operands == "$0x80":
                continue
            reason = "kernel entry other than int $0x80"
        elif SYSTEM_REGISTER.search(operands):
            reason = "control, debug or test register access"
        elif mnemonic.startswith("mov") and SEGMENT_REGISTER.fullmatch(
                operands.rsplit(",", 1)[-1]):
            reason = "segment register load"
        elif mnemonic.startswith("pop") and SEGMENT_REGISTER.fullmatch(operands):
            reason = "segment register load"
        elif mnemonic.startswith("f") or EXTENDED_REGISTER.search(operands):
            reason = "x87/MMX/SSE/AVX state (denied at CPL3)"
        if reason:
            violations.append(f"{where}  [{reason}]")
    return violations, count


def sections(path: str) -> dict[str, tuple[str, int, str, int]]:
    """name -> (type, size, flags, index) for every section header."""
    table: dict[str, tuple[str, int, str, int]] = {}
    for line in run("readelf", "-SW", path).splitlines():
        match = re.match(
            r"^\s*\[\s*(\d+)\]\s+(\S+)\s+(\S+)\s+[0-9a-f]+\s+[0-9a-f]+\s+"
            r"([0-9a-f]+)\s+[0-9a-f]+\s+([A-Za-z]*)\s", line)
        if match:
            table[match.group(2)] = (match.group(3), int(match.group(4), 16),
                                     match.group(5), int(match.group(1)))
    return table


def symbols(path: str) -> dict[str, tuple[int, str]]:
    """name -> (value, section index) from the symbol table.  In a relocatable
    object the value is the offset within the symbol's section."""
    table: dict[str, tuple[int, str]] = {}
    for line in run("readelf", "-sW", path).splitlines():
        fields = line.split()
        if len(fields) == 8 and fields[0][:-1].isdigit() and fields[0].endswith(":"):
            table[fields[7]] = (int(fields[1], 16), fields[6])
    return table


def check_object(path: str) -> list[str]:
    errors: list[str] = []
    undefined = [line.split()[-1] for line in run("nm", "-u", path).splitlines()
                 if line.strip()]
    if undefined:
        errors.append("undefined symbols (no libc, no kernel symbols): "
                      + ", ".join(sorted(undefined)))
    table = sections(path)
    allocated = sorted(name for name, (_, _, flags, _) in table.items() if "A" in flags)
    if allocated != [".subject.bss", ".subject.text"]:
        errors.append("allocated sections must be exactly .subject.text and "
                      f".subject.bss, found: {', '.join(allocated) or 'none'}")
        return errors
    _, text_size, text_flags, text_index = table[".subject.text"]
    _, data_size, data_flags, data_index = table[".subject.bss"]
    if "X" not in text_flags or "W" in text_flags:
        errors.append(".subject.text must be executable and not writable")
    if "X" in data_flags or "W" not in data_flags:
        errors.append(".subject.bss must be writable and not executable")
    if not 0 < text_size <= PAGE_BYTES:
        errors.append(f".subject.text is {text_size} bytes; the slot maps one "
                      f"{PAGE_BYTES}-byte text page")
    if data_size != PAGE_BYTES:
        errors.append(f".subject.bss is {data_size} bytes; the slot's stack page "
                      f"is exactly {PAGE_BYTES}")
    names = symbols(path)
    expected = {
        "subject_template_text": (".subject.text", text_index, 0),
        "subject_entry": (".subject.text", text_index, 0),
        "subject_stack": (".subject.bss", data_index, 0),
        "subject_stack_top": (".subject.bss", data_index, STACK_BYTES),
    }
    for name, (section, index, offset) in expected.items():
        if names.get(name) != (offset, str(index)):
            errors.append(f"{name} must be defined at {section}+{offset}")
    violations, count = instruction_violations(path, ".subject.text")
    errors.extend(violations)
    if count == 0:
        errors.append(".subject.text disassembles to no instructions")
    return errors


def check_elf(path: str, slot: str) -> list[str]:
    errors: list[str] = []
    section = f".user_{slot}_text"
    table = sections(path)
    if section not in table:
        return [f"final ELF lacks {section}"]
    names = symbols(path)
    for left, right in ((f"user_{slot}_entry", f"__user_{slot}_text_start"),
                        (f"user_{slot}_template_text", f"__user_{slot}_text_start"),
                        (f"user_{slot}_stack", f"__user_{slot}_stack_start")):
        if left not in names or right not in names or names[left][0] != names[right][0]:
            errors.append(f"{left} must equal {right}")
    if (f"user_{slot}_stack_top" not in names or f"user_{slot}_stack" not in names
            or names[f"user_{slot}_stack_top"][0] - names[f"user_{slot}_stack"][0]
            != STACK_BYTES):
        errors.append(f"user_{slot}_stack_top must be {STACK_BYTES} bytes above "
                      f"user_{slot}_stack")
    violations, count = instruction_violations(path, section)
    errors.extend(violations)
    if count == 0:
        errors.append(f"{section} disassembles to no instructions")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="mode", required=True)
    obj = sub.add_parser("object")
    obj.add_argument("path")
    elf = sub.add_parser("elf")
    elf.add_argument("path")
    elf.add_argument("slot", choices=["c"])
    args = parser.parse_args()
    try:
        errors = (check_object(args.path) if args.mode == "object"
                  else check_elf(args.path, args.slot))
    except PolicyError as error:
        errors = [str(error)]
    if errors:
        for error in errors:
            print(f"error: subject policy: {args.path}: {error}", file=sys.stderr)
        return 1
    print(f"subject-policy\t{args.mode}\t{args.path}\tPASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
