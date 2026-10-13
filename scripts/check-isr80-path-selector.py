#!/usr/bin/env python3
"""Check isr80's typed return-path selector (#560).

`isr80` in boot/boot.S picks its path after `syscall_handler` from the
kernel-owned word `isr80_return_path`, never from the reply word in RAX.  The
Lean model `LeanOS.Isr80PathSelector` proves that a ladder of
`cmp $code, %rdx; je label` rungs depends on the selector alone.  This check
ties that model to the sources and to a final ELF:

* the Lean table (`Path.code`, `Path.macroName`, `Path.label`) equals
  include/leanos/isr80-path.h;
* in boot.S, isr80 stores LEANOS_ISR80_PATH_REPLY before the call, loads the
  selector into RDX once after it, and then runs only reviewed
  `cmp $LEANOS_ISR80_PATH_*, %rdx; je <label>` rungs before `ud2`; no
  instruction in isr80 compares RAX;
* in kernel.c, `isr80_select` is the only writer of the selector, every call
  selects a path macro, and no handler returns a former magic value;
* in the ELF (when given), the store precedes `call syscall_handler`, the
  first instruction after the selector load is the ladder, every rung
  compares RDX with a model code, and nothing in isr80 compares RAX.

Every failure prints `error: vector=128 field=typed-path-selector
violated=<reason>` and exits 1.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

FORMER_MAGIC = re.compile(
    r"\b0x(?:beef|cafe|feed|a55a|3c0[1-7]|5c0[12])u?\b", re.IGNORECASE)


def fail(reason: str) -> None:
    print(f"error: vector=128 field=typed-path-selector violated={reason}",
          file=sys.stderr)
    sys.exit(1)


def lean_table(text: str) -> dict[str, tuple[int, str, int]]:
    def arms(definition: str) -> dict[str, str]:
        match = re.search(
            rf"^def Path\.{definition} : Path → \S+\n((?:  \| \.\w+ => .+\n)+)",
            text, re.MULTILINE)
        if not match:
            fail(f"lean-table-missing-{definition}")
        return dict(re.findall(r"^  \| \.(\w+) => (.+)$", match.group(1),
                               re.MULTILINE))

    codes, names, labels = arms("code"), arms("macroName"), arms("label")
    if not codes or set(codes) != set(names) or set(codes) != set(labels):
        fail("lean-table-shape")
    table = {}
    for path in codes:
        name = names[path].strip()
        if not re.fullmatch(r'"LEANOS_ISR80_PATH_[A-Z0-9_]+"', name):
            fail(f"lean-macro-name-{path}")
        table[name.strip('"')] = (int(codes[path], 0), path,
                                  int(labels[path], 0))
    values = [entry[0] for entry in table.values()]
    label_values = [entry[2] for entry in table.values()]
    if (len(set(values)) != len(values) or len(set(label_values)) != len(label_values)
            or len(table) != len(codes)):
        fail("lean-table-not-injective")
    if table.get("LEANOS_ISR80_PATH_REPLY", (None,))[0] != 0:
        fail("lean-reply-code")
    return table


def check_header(text: str, table: dict[str, tuple[int, str, int]]) -> None:
    defines = {name: int(value, 0) for name, value in re.findall(
        r"^#define (LEANOS_ISR80_PATH_\w+) (\S+)$", text, re.MULTILINE)}
    if defines != {name: entry[0] for name, entry in table.items()}:
        fail("header-differs-from-lean-model")


def instruction_lines(lines: list[str]) -> list[str]:
    """Strip comments and preprocessor lines from assembler source lines."""
    text = "\n".join(lines)
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.DOTALL)
    text = text.replace("\\\n", " ")
    result = []
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        result.append(stripped)
    return result


def check_boot(text: str, table: dict[str, tuple[int, str, int]]) -> None:
    match = re.search(r"^isr80:\n(.*?)^\.global isr14\n", text,
                      re.MULTILINE | re.DOTALL)
    if not match:
        fail("isr80-source-missing")
    raw = match.group(1).splitlines()
    lines = instruction_lines(raw)
    store = "movq $LEANOS_ISR80_PATH_REPLY, isr80_return_path(%rip)"
    load = "mov isr80_return_path(%rip), %rdx"
    calls = [i for i, line in enumerate(lines) if line == "call syscall_handler"]
    stores = [i for i, line in enumerate(lines) if line == store]
    loads = [i for i, line in enumerate(lines) if line == load]
    mentions = [i for i, line in enumerate(lines) if "isr80_return_path" in line]
    if len(calls) != 1 or len(stores) != 1 or stores[0] > calls[0]:
        fail("source-selector-not-reset-before-call")
    if len(loads) != 1 or loads[0] < calls[0]:
        fail("source-selector-not-loaded-after-call")
    if sorted(mentions) != sorted(stores + loads):
        fail("source-extra-selector-access")
    for line in lines:
        if re.match(r"(cmp|test)[a-z]*\s.*%[re]?ax$", line) or \
                re.match(r"(cmp|test)[a-z]*\s+%[re]?ax,", line):
            fail("source-reply-word-compared")
    defined_labels = {int(label) for label in re.findall(
        r"^(\d+):", "\n".join(raw), re.MULTILINE)}
    rungs = lines[loads[0] + 1:]
    seen = set()
    index = 0
    while index < len(rungs) and rungs[index] != "ud2":
        compare = re.fullmatch(r"cmp \$(LEANOS_ISR80_PATH_\w+), %rdx",
                               rungs[index])
        jump = (re.fullmatch(r"je (\d+)f", rungs[index + 1])
                if index + 1 < len(rungs) else None)
        if not compare or not jump:
            fail(f"source-unreviewed-ladder-instruction:{rungs[index]}")
        name = compare.group(1)
        if name not in table or name in seen:
            fail(f"source-unknown-or-repeated-selector:{name}")
        if int(jump.group(1)) != table[name][2]:
            fail(f"source-selector-label:{name}")
        if table[name][2] not in defined_labels:
            fail(f"source-selector-label-missing:{name}")
        seen.add(name)
        index += 2
    if index >= len(rungs) or "LEANOS_ISR80_PATH_REPLY" not in seen:
        fail("source-ladder-not-closed-by-ud2")


def check_kernel(text: str, table: dict[str, tuple[int, str, int]]) -> None:
    writes = re.findall(r"\bisr80_return_path\s*=(?!=)", text)
    selector = re.search(
        r"^isr80_select\(uint64_t path\) \{\n    isr80_return_path = path;\n"
        r"    return 0;\n\}$", text, re.MULTILINE)
    if len(writes) != 1 or not selector:
        fail("kernel-selector-writer")
    for statement in re.findall(r"\breturn\b[^;]*;", text):
        if FORMER_MAGIC.search(statement):
            fail("kernel-former-magic-reply")
    macros = dict(re.findall(r"^#define (\w+) (LEANOS_ISR80_PATH_\w+)$", text,
                             re.MULTILINE))
    for name, value in macros.items():
        if value not in table:
            fail(f"kernel-unknown-selector-macro:{name}")

    def resolves(token: str) -> bool:
        return token in table or macros.get(token) in table

    calls = re.findall(r"\bisr80_select\(((?:[^()]|\([^()]*\))*)\)", text)
    if not calls:
        fail("kernel-no-selector-call")
    for argument in calls:
        argument = " ".join(argument.split())
        if argument == "uint64_t path":
            continue
        shape = re.fullmatch(r"(?:[^?:]+\? )?(\w+)(?: : (\w+))?", argument)
        if not shape or not all(resolves(token) for token in shape.groups()
                                if token is not None):
            fail(f"kernel-selector-argument:{argument}")


def check_elf(elf: Path, table: dict[str, tuple[int, str, int]]) -> None:
    symbols = {}
    for line in subprocess.run(["nm", "-n", str(elf)], capture_output=True,
                               text=True, check=True).stdout.splitlines():
        fields = line.split()
        if len(fields) == 3:
            symbols[fields[2]] = fields[0]
    for name in ("isr80", "isr14", "isr80_return_path", "syscall_handler"):
        if name not in symbols:
            fail(f"elf-symbol-missing:{name}")
    disassembly = subprocess.run(
        ["objdump", "-d", "--no-show-raw-insn",
         f"--start-address=0x{symbols['isr80']}",
         f"--stop-address=0x{symbols['isr14']}", str(elf)],
        capture_output=True, text=True, check=True).stdout
    instructions = []
    for line in disassembly.splitlines():
        parsed = re.match(r"^\s*([0-9a-f]+):\s+(\S+)\s*(.*)$", line)
        if parsed:
            instructions.append((int(parsed.group(1), 16), parsed.group(2),
                                 parsed.group(3).strip()))
    calls = [i for i, (_, op, args) in enumerate(instructions)
             if op.startswith("call") and args.endswith("<syscall_handler>")]
    stores = [i for i, (_, op, args) in enumerate(instructions)
              if op == "movq" and args.startswith("$0x0,")
              and args.endswith("<isr80_return_path>")]
    loads = [i for i, (_, op, args) in enumerate(instructions)
             if op == "mov" and args.endswith("<isr80_return_path>")
             and re.search(r",%rdx\s", args)]
    mentions = [i for i, (_, _, args) in enumerate(instructions)
                if args.endswith("<isr80_return_path>")]
    if len(calls) != 1 or len(stores) != 1 or stores[0] > calls[0]:
        fail("elf-selector-not-reset-before-call")
    if len(loads) != 1 or loads[0] < calls[0]:
        fail("elf-selector-not-loaded-after-call")
    if sorted(mentions) != sorted(stores + loads):
        fail("elf-extra-selector-access")
    for _, op, args in instructions:
        if re.match(r"(cmp|test)", op) and re.search(r"%[re]?ax\b|%al\b", args):
            fail("elf-reply-word-compared")
    codes = {entry[0] for entry in table.values()}
    start, stop = int(symbols["isr80"], 16), int(symbols["isr14"], 16)
    index = loads[0] + 1
    seen = set()
    while index < len(instructions) and instructions[index][1] != "ud2":
        compare = instructions[index]
        jump = instructions[index + 1] if index + 1 < len(instructions) else None
        immediate = re.fullmatch(r"\$0x([0-9a-f]+),%rdx", compare[2])
        if not compare[1].startswith("cmp") or not immediate or jump is None \
                or jump[1] != "je":
            fail(f"elf-unreviewed-ladder-instruction:{compare[1]} {compare[2]}")
        code = int(immediate.group(1), 16)
        target = re.match(r"([0-9a-f]+)\b", jump[2])
        if code not in codes or code in seen or not target or \
                not start <= int(target.group(1), 16) < stop:
            fail(f"elf-unknown-or-repeated-selector:{code}")
        seen.add(code)
        index += 2
    if index >= len(instructions) or 0 not in seen:
        fail("elf-ladder-not-closed-by-ud2")
    print(f"ISR80-PATH-SELECTOR elf={elf} rungs={len(seen)} operand=rdx "
          "source=isr80_return_path reply-compared=0 result=PASS")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--lean", default="LeanOS/Isr80PathSelector.lean")
    parser.add_argument("--header", default="include/leanos/isr80-path.h")
    parser.add_argument("--boot", default="boot/boot.S")
    parser.add_argument("--kernel", default="boot/kernel.c")
    parser.add_argument("--elf")
    options = parser.parse_args()
    table = lean_table(Path(options.lean).read_text())
    check_header(Path(options.header).read_text(), table)
    check_boot(Path(options.boot).read_text(), table)
    check_kernel(Path(options.kernel).read_text(), table)
    print(f"ISR80-PATH-SELECTOR source paths={len(table)} model=LeanOS.Isr80PathSelector "
          "header=agrees ladder=rdx-only kernel-writer=isr80_select result=PASS")
    if options.elf:
        check_elf(Path(options.elf), table)
    return 0


if __name__ == "__main__":
    sys.exit(main())
