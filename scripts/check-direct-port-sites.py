#!/usr/bin/env python3
"""Reject final-ELF port-I/O sites outside the reviewed manifest."""

from __future__ import annotations

import argparse
from collections import Counter
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path


SITE_RE = re.compile(r"^\s*([0-9a-f]+):\s+(\S+)(?:\s+(.*?))?\s*$")
SYMBOL_RE = re.compile(r"^[0-9a-f]+ <([^>]+)>:$")
PORT_OPCODE_RE = re.compile(r"^(?:in|out)(?:b|w|l|s[bwl]?)?$")
CALL_TARGET_RE = re.compile(r"<([^>+]+)(?:\+0x[0-9a-f]+)?>")
BRANCH_TARGET_RE = re.compile(r"^\s*([0-9a-f]+)\s+<")
C_TOKEN_RE = re.compile(
    r"//[^\n]*|/\*.*?\*/|\"(?:\\.|[^\"\\])*\"|'(?:\\.|[^'\\])*'|"
    r"[A-Za-z_]\w*|0[xX][0-9a-fA-F]+[uUlL]*|[0-9]+[uUlL]*|[{}(),+]",
    re.DOTALL,
)
OWNERS = {
    "DirectPortIO.serial",
    "DirectPortIO.debug-exit",
    "DirectPortIO.pic",
    "DirectPortIO.pit",
    "DirectPortIO.byte-wrapper",
    "DMAQuarantine.boot-pci-config",
}
BYTE_OWNERS = {
    ("out8", 0x3F8): "DirectPortIO.serial",
    ("out8", 0x3F9): "DirectPortIO.serial",
    ("out8", 0x3FA): "DirectPortIO.serial",
    ("out8", 0x3FB): "DirectPortIO.serial",
    ("out8", 0x3FC): "DirectPortIO.serial",
    ("in8", 0x3FD): "DirectPortIO.serial",
    ("out8", 0x20): "DirectPortIO.pic",
    ("out8", 0x21): "DirectPortIO.pic",
    ("out8", 0xA0): "DirectPortIO.pic",
    ("out8", 0xA1): "DirectPortIO.pic",
    ("out8", 0x40): "DirectPortIO.pit",
    ("out8", 0x43): "DirectPortIO.pit",
    ("out8", 0xF4): "DirectPortIO.debug-exit",
}


@dataclass(frozen=True, order=True)
class Site:
    symbol: str
    offset: int
    opcode: str
    operands: str

    def fields(self) -> tuple[str, str, str, str]:
        return self.symbol, f"0x{self.offset:x}", self.opcode, self.operands


@dataclass(frozen=True, order=True)
class Instruction:
    address: int
    opcode: str
    operands: str


@dataclass(frozen=True, order=True)
class ByteOperation:
    caller: str
    wrapper: str
    port: int

    def fields(self) -> tuple[str, str, str]:
        return self.caller, self.wrapper, f"0x{self.port:x}"


def tool_output(*command: str) -> str:
    try:
        return subprocess.run(command, check=True, text=True, capture_output=True).stdout
    except (OSError, subprocess.CalledProcessError) as error:
        print(f"error: direct-port site tool failed: {' '.join(command)}", file=sys.stderr)
        raise SystemExit(1) from error


def elf_inventory(elf: Path) -> tuple[list[Site], dict[str, set[str]],
                                      dict[tuple[str, str], list[int]],
                                      dict[str, list[Instruction]]]:
    disassembly = tool_output("objdump", "-d", "--no-show-raw-insn", str(elf))
    symbol = ""
    symbol_address = 0
    sites: list[Site] = []
    callers: dict[str, set[str]] = {}
    calls: dict[tuple[str, str], list[int]] = {}
    functions: dict[str, list[Instruction]] = {}
    for line in disassembly.splitlines():
        match = SYMBOL_RE.match(line)
        if match:
            symbol = match.group(1)
            symbol_address = int(line.split()[0], 16)
            functions.setdefault(symbol, [])
            continue
        match = SITE_RE.match(line)
        if not match:
            continue
        address = int(match.group(1), 16)
        opcode = match.group(2)
        operands = match.group(3) or "-"
        if symbol:
            functions[symbol].append(Instruction(address, opcode, operands))
        if opcode in {"call", "callq", "jmp", "jmpq"}:
            target = CALL_TARGET_RE.search(operands)
            if target and target.group(1) != symbol:
                callee = target.group(1)
                callers.setdefault(callee, set()).add(symbol)
                calls.setdefault((symbol, callee), []).append(address)
        if not PORT_OPCODE_RE.fullmatch(opcode):
            continue
        if not symbol:
            print("error: final-ELF port-I/O instruction has no owning symbol", file=sys.stderr)
            raise SystemExit(1)
        sites.append(Site(symbol, address - symbol_address, opcode, operands))
    return sites, callers, calls, functions


def kernel_main_cfg(instructions: list[Instruction]) -> dict[int, set[int]]:
    addresses = {instruction.address for instruction in instructions}
    successors: dict[int, set[int]] = {}
    for index, instruction in enumerate(instructions):
        next_address = instructions[index + 1].address \
            if index + 1 < len(instructions) else None
        opcode = instruction.opcode
        branch = BRANCH_TARGET_RE.match(instruction.operands)

        if opcode in {"call", "callq"}:
            if not CALL_TARGET_RE.search(instruction.operands):
                print("error: kernel_main contains an indirect call", file=sys.stderr)
                raise SystemExit(1)
            successors[instruction.address] = ({next_address}
                                               if next_address is not None else set())
        elif opcode in {"jmp", "jmpq"}:
            if not branch:
                print("error: kernel_main contains an indirect jump", file=sys.stderr)
                raise SystemExit(1)
            target = int(branch.group(1), 16)
            successors[instruction.address] = {target} if target in addresses else set()
        elif opcode.startswith("j") or opcode.startswith("loop"):
            if not branch or next_address is None:
                print("error: kernel_main conditional control flow is unreviewed",
                      file=sys.stderr)
                raise SystemExit(1)
            target = int(branch.group(1), 16)
            if target not in addresses:
                print("error: kernel_main conditional branch leaves the audited symbol",
                      file=sys.stderr)
                raise SystemExit(1)
            successors[instruction.address] = {next_address, target}
        elif opcode in {"ret", "retq", "iret", "iretq", "ud2", "hlt"}:
            successors[instruction.address] = set()
        else:
            successors[instruction.address] = ({next_address}
                                               if next_address is not None else set())
    return successors


def reachable_addresses(start: int, successors: dict[int, set[int]],
                        blocked: int | None = None) -> set[int]:
    if start == blocked:
        return set()
    reached: set[int] = set()
    pending = [start]
    while pending:
        address = pending.pop()
        if address in reached or address == blocked:
            continue
        reached.add(address)
        pending.extend(successors.get(address, set()) - reached)
    return reached


def validate_pci_call_graph(callers: dict[str, set[str]],
                            calls: dict[tuple[str, str], list[int]],
                            functions: dict[str, list[Instruction]]) -> None:
    expected = {
        "out16": {"pci_config_command"},
        "out32": {"pci_config_command", "pci_config_dword"},
        "in32": {"pci_config_dword"},
        "pci_config_dword": {"quarantine_q35_pci_dma"},
        "pci_config_command": {"quarantine_q35_pci_dma"},
        "quarantine_q35_pci_dma": {"kernel_main"},
        "enter_user": {"kernel_main"},
    }
    for callee, expected_callers in expected.items():
        observed = callers.get(callee, set())
        if observed != expected_callers:
            print("error: boot-only PCI final-ELF call graph drifted " +
                  f"callee={callee} callers={','.join(sorted(observed)) or '-'}",
                  file=sys.stderr)
            raise SystemExit(1)

    quarantine_calls = calls.get(("kernel_main", "quarantine_q35_pci_dma"), [])
    user_calls = calls.get(("kernel_main", "enter_user"), [])
    if len(quarantine_calls) != 1 or len(user_calls) != 1:
        print("error: boot-only PCI quarantine/CPL3 call count drifted",
              file=sys.stderr)
        raise SystemExit(1)

    kernel_main = functions.get("kernel_main", [])
    if not kernel_main:
        print("error: final ELF has no auditable kernel_main body", file=sys.stderr)
        raise SystemExit(1)
    successors = kernel_main_cfg(kernel_main)
    reached = reachable_addresses(kernel_main[0].address, successors)
    quarantine_call = quarantine_calls[0]
    user_call = user_calls[0]
    if quarantine_call not in reached:
        print("error: boot-only PCI quarantine is unreachable from kernel_main entry",
              file=sys.stderr)
        raise SystemExit(1)
    if user_call not in reached:
        print("error: first CPL3 return is unreachable from kernel_main entry",
              file=sys.stderr)
        raise SystemExit(1)
    without_quarantine = reachable_addresses(
        kernel_main[0].address, successors, blocked=quarantine_call)
    if user_call in without_quarantine:
        print("error: boot-only PCI quarantine does not dominate first CPL3 return",
              file=sys.stderr)
        raise SystemExit(1)


def read_manifest(path: Path) -> dict[Site, str]:
    result: dict[Site, str] = {}
    for number, line in enumerate(path.read_text().splitlines(), 1):
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) != 5:
            print(f"error: direct-port manifest malformed line={number}", file=sys.stderr)
            raise SystemExit(1)
        symbol, offset, opcode, operands, owner = fields
        if owner not in OWNERS:
            print(f"error: direct-port manifest owner unreviewed line={number} owner={owner}",
                  file=sys.stderr)
            raise SystemExit(1)
        site = Site(symbol, int(offset, 0), opcode, operands)
        if site in result:
            print(f"error: duplicate direct-port manifest site line={number}", file=sys.stderr)
            raise SystemExit(1)
        result[site] = owner
    return result


def read_byte_manifest(path: Path) -> Counter[ByteOperation]:
    result: Counter[ByteOperation] = Counter()
    for number, line in enumerate(path.read_text().splitlines(), 1):
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) != 5:
            print(f"error: byte-operation manifest malformed line={number}",
                  file=sys.stderr)
            raise SystemExit(1)
        caller, wrapper, port_text, owner, count_text = fields
        try:
            operation = ByteOperation(caller, wrapper, int(port_text, 0))
            count = int(count_text, 0)
        except ValueError:
            print(f"error: byte-operation manifest value malformed line={number}",
                  file=sys.stderr)
            raise SystemExit(1)
        if count <= 0 or operation in result:
            print(f"error: byte-operation manifest count/entry invalid line={number}",
                  file=sys.stderr)
            raise SystemExit(1)
        expected_owner = BYTE_OWNERS.get((wrapper, operation.port))
        if owner != expected_owner:
            print("error: byte-operation manifest is outside modeled authority " +
                  f"line={number} owner={owner}", file=sys.stderr)
            raise SystemExit(1)
        result[operation] = count
    return result


def parse_constant_port(tokens: list[str]) -> int | None:
    constants = {"COM1": 0x3F8, "DEBUG_EXIT": 0xF4}
    value = 0
    expect_term = True
    for term in tokens:
        if not expect_term:
            if term != "+":
                return None
            expect_term = True
            continue
        if term in constants:
            value += constants[term]
        else:
            match = re.fullmatch(r"(0[xX][0-9a-fA-F]+|[0-9]+)[uUlL]*", term)
            if not match:
                return None
            value += int(match.group(1), 0)
        expect_term = False
    return value if tokens and not expect_term else None


def source_byte_operations(
        text: str) -> tuple[Counter[ByteOperation], Counter[str]]:
    tokens = [match.group(0) for match in C_TOKEN_RE.finditer(text)
              if not match.group(0).startswith(("//", "/*", "\"", "'"))]
    result: Counter[ByteOperation] = Counter()
    references: Counter[str] = Counter(
        token for token in tokens if token in {"out8", "in8"})
    caller = ""
    depth = 0
    for index, token in enumerate(tokens):
        if token == "{":
            if depth == 0 and index > 0 and tokens[index - 1] == ")":
                parentheses = 1
                opening = index - 2
                while opening >= 0 and parentheses:
                    if tokens[opening] == ")":
                        parentheses += 1
                    elif tokens[opening] == "(":
                        parentheses -= 1
                    opening -= 1
                if parentheses == 0 and opening >= 0 and \
                        re.fullmatch(r"[A-Za-z_]\w*", tokens[opening]):
                    caller = tokens[opening]
            depth += 1
            continue
        if token == "}":
            depth -= 1
            if depth == 0:
                caller = ""
            if depth < 0:
                print("error: source brace structure is malformed", file=sys.stderr)
                raise SystemExit(1)
            continue
        if not caller or token not in {"out8", "in8"}:
            continue
        if index + 1 >= len(tokens) or tokens[index + 1] != "(":
            print("error: byte wrapper has a non-call source reference " +
                  f"caller={caller} wrapper={token}", file=sys.stderr)
            raise SystemExit(1)
        argument: list[str] = []
        parentheses = 1
        cursor = index + 2
        while cursor < len(tokens) and parentheses:
            current = tokens[cursor]
            if current == "(":
                parentheses += 1
            elif current == ")":
                parentheses -= 1
                if parentheses == 0:
                    break
            elif current == "," and parentheses == 1:
                break
            argument.append(current)
            cursor += 1
        if cursor >= len(tokens) or (parentheses == 0 and token == "out8"):
            print("error: byte-wrapper call argument structure is malformed " +
                  f"caller={caller} wrapper={token}", file=sys.stderr)
            raise SystemExit(1)
        port = parse_constant_port(argument)
        if port is None:
            print("error: byte-wrapper call does not use an audited constant port " +
                  f"caller={caller} wrapper={token}", file=sys.stderr)
            raise SystemExit(1)
        result[ByteOperation(caller, token, port)] += 1
    if depth != 0:
        print("error: source brace structure ended unbalanced", file=sys.stderr)
        raise SystemExit(1)
    return result, references


def validate_source(source: Path, byte_manifest: Path) -> None:
    text = source.read_text()
    contracts = (
        "#define COM1 0x3f8u",
        "#define DEBUG_EXIT 0xf4u",
        "static __attribute__((noinline, noipa)) void out8(uint16_t port, uint8_t value) {",
        "static __attribute__((noinline, noipa)) uint8_t in8(uint16_t port) {",
        "#define PCI_CONFIG_ADDRESS 0xcf8u",
        "#define PCI_CONFIG_DATA 0xcfcu",
        "out32(PCI_CONFIG_ADDRESS, address);",
        "return in32(PCI_CONFIG_DATA);",
        "out16(PCI_CONFIG_DATA, command);",
    )
    for contract in contracts:
        if contract not in text:
            print(f"error: DMA-quarantine PCI configuration contract drifted: {contract}",
                  file=sys.stderr)
            raise SystemExit(1)

    # The final ELF deliberately funnels these three instructions through one
    # wrapper each.  Also pin every source-level invocation so a later caller
    # cannot reuse a boot-only PCI wrapper for ambient port authority while
    # leaving the final instruction inventory unchanged.
    expected_invocations = Counter({
        "static __attribute__((noinline, noipa)) void out16(uint16_t port, uint16_t value) {": 1,
        "static __attribute__((noinline, noipa)) void out32(uint16_t port, uint32_t value) {": 1,
        "static __attribute__((noinline, noipa)) uint32_t in32(uint16_t port) {": 1,
        "out32(PCI_CONFIG_ADDRESS, address);": 2,
        "return in32(PCI_CONFIG_DATA);": 1,
        "out16(PCI_CONFIG_DATA, command);": 1,
    })
    observed_invocations = Counter(
        line.strip() for line in text.splitlines()
        if re.search(r"\b(?:out16|out32|in32)\s*\(", line)
    )
    if observed_invocations != expected_invocations:
        print("error: boot-only PCI configuration wrapper call contract drifted",
              file=sys.stderr)
        raise SystemExit(1)

    expected_byte_operations = read_byte_manifest(byte_manifest)
    observed_byte_operations, observed_byte_references = source_byte_operations(text)
    unexpected = observed_byte_operations - expected_byte_operations
    missing = expected_byte_operations - observed_byte_operations
    if unexpected:
        operation = sorted(unexpected)[0]
        print("error: unauthorized byte-wrapper operation " +
              " ".join(operation.fields()), file=sys.stderr)
        raise SystemExit(1)
    if missing:
        operation = sorted(missing)[0]
        print("error: reviewed byte-wrapper operation missing " +
              " ".join(operation.fields()), file=sys.stderr)
        raise SystemExit(1)
    expected_byte_references = Counter({"out8": 1, "in8": 1})
    for operation, count in expected_byte_operations.items():
        expected_byte_references[operation.wrapper] += count
    if observed_byte_references != expected_byte_references:
        print("error: byte-wrapper source reference contract drifted", file=sys.stderr)
        raise SystemExit(1)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("elf", type=Path)
    parser.add_argument("manifest", nargs="?", type=Path,
                        default=Path("scripts/direct-port-sites.tsv"))
    parser.add_argument("--source", type=Path, default=Path("boot/kernel.c"))
    parser.add_argument("--byte-manifest", type=Path,
                        default=Path("scripts/direct-port-byte-operations.tsv"))
    args = parser.parse_args()
    if not args.elf.is_file() or not args.manifest.is_file() or \
            not args.source.is_file() or not args.byte_manifest.is_file():
        print("error: missing direct-port policy input", file=sys.stderr)
        return 1

    validate_source(args.source, args.byte_manifest)
    sites, callers, calls, functions = elf_inventory(args.elf)
    observed = set(sites)
    manifest = read_manifest(args.manifest)
    expected = set(manifest)
    unexpected = sorted(observed - expected)
    missing = sorted(expected - observed)
    if unexpected:
        site = unexpected[0]
        print("error: unauthorized final-ELF port-I/O site " +
              " ".join(site.fields()), file=sys.stderr)
        return 1
    if missing:
        site = missing[0]
        print("error: reviewed final-ELF port-I/O site missing " +
              " ".join(site.fields()), file=sys.stderr)
        return 1

    validate_pci_call_graph(callers, calls, functions)

    dma_symbols = {site.symbol for site, owner in manifest.items()
                   if owner == "DMAQuarantine.boot-pci-config"}
    if dma_symbols != {"out16", "out32", "in32"}:
        print("error: boot-only PCI configuration site classification drifted", file=sys.stderr)
        return 1
    for site, owner in manifest.items():
        if site.symbol in {"out16", "out32", "in32"} and \
                owner != "DMAQuarantine.boot-pci-config":
            print(f"error: PCI configuration wrapper has wrong owner symbol={site.symbol}",
                  file=sys.stderr)
            return 1

    print(f"DIRECT-PORT-SITES sites={len(observed)} dma-exceptions=3 result=PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
