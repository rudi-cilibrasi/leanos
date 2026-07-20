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
OWNERS = {
    "DirectPortIO.serial",
    "DirectPortIO.debug-exit",
    "DirectPortIO.pic",
    "DirectPortIO.pit",
    "DirectPortIO.byte-wrapper",
    "DMAQuarantine.boot-pci-config",
}


@dataclass(frozen=True, order=True)
class Site:
    symbol: str
    offset: int
    opcode: str
    operands: str

    def fields(self) -> tuple[str, str, str, str]:
        return self.symbol, f"0x{self.offset:x}", self.opcode, self.operands


def tool_output(*command: str) -> str:
    try:
        return subprocess.run(command, check=True, text=True, capture_output=True).stdout
    except (OSError, subprocess.CalledProcessError) as error:
        print(f"error: direct-port site tool failed: {' '.join(command)}", file=sys.stderr)
        raise SystemExit(1) from error


def elf_sites(elf: Path) -> list[Site]:
    disassembly = tool_output("objdump", "-d", "--no-show-raw-insn", str(elf))
    symbol = ""
    symbol_address = 0
    sites: list[Site] = []
    for line in disassembly.splitlines():
        match = SYMBOL_RE.match(line)
        if match:
            symbol = match.group(1)
            symbol_address = int(line.split()[0], 16)
            continue
        match = SITE_RE.match(line)
        if not match or not PORT_OPCODE_RE.fullmatch(match.group(2)):
            continue
        if not symbol:
            print("error: final-ELF port-I/O instruction has no owning symbol", file=sys.stderr)
            raise SystemExit(1)
        sites.append(Site(symbol, int(match.group(1), 16) - symbol_address,
                          match.group(2), match.group(3) or "-"))
    return sites


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


def validate_source(source: Path) -> None:
    text = source.read_text()
    contracts = (
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


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("elf", type=Path)
    parser.add_argument("manifest", nargs="?", type=Path,
                        default=Path("scripts/direct-port-sites.tsv"))
    parser.add_argument("--source", type=Path, default=Path("boot/kernel.c"))
    args = parser.parse_args()
    if not args.elf.is_file() or not args.manifest.is_file() or not args.source.is_file():
        print("error: missing direct-port policy input", file=sys.stderr)
        return 1

    validate_source(args.source)
    observed = set(elf_sites(args.elf))
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
