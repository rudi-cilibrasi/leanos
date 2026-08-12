#!/usr/bin/env python3
"""Validate guest PCI records and retain one canonical machine snapshot."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
import re


TOPOLOGY = "0001000800020002"
BUS_MASTER = 1 << 2
COMMAND_MASK = 0x7FF
FUNCTION_RE = re.compile(
    rf"^LEANOS/15 DMA-FUNCTION manifest=1 topology={TOPOLOGY} "
    r"bdf=(\d+):(\d+)\.(\d+) present=([01]) vendor=(\d+) device=(\d+) "
    r"class=(\d+) command-before=(\d+) command-after=(\d+) assigned=0 "
    r"bridge=([01]) multifunction=([01]) policy=accepted$"
)
SUMMARY_RE = re.compile(
    rf"^LEANOS/15 DMA snapshot=1 topology={TOPOLOGY} bus=0 scanned=256 "
    r"present=5 optional-absent=1 writes=5 readbacks=5 "
    r"initial-bus-masters=1 initial-bus-master-mask=16 bus-master=disabled "
    r"readback=exact generated-result=0 "
    r"stage=pre-cpl3 result=PASS$"
)
EXPECTED = {
    (0, 0, 0): (1, 0x8086, 0x29C0, 0x060000, 0, 0),
    (0, 1, 0): (1, 0x1234, 0x1111, 0x030000, 0, 0),
    (0, 3, 0): (0, 0, 0, 0, 0, 0),
    (0, 31, 0): (1, 0x8086, 0x2918, 0x060100, 1, 1),
    (0, 31, 2): (1, 0x8086, 0x2922, 0x010601, 0, 1),
    (0, 31, 3): (1, 0x8086, 0x2930, 0x0C0500, 0, 1),
}


@dataclass(frozen=True)
class Function:
    bdf: tuple[int, int, int]
    present: int
    vendor: int
    device: int
    class_code: int
    command_before: int
    command_after: int
    bridge: int
    multifunction: int


def parse(text: str) -> list[Function]:
    functions: list[Function] = []
    summaries = 0
    for line in text.splitlines():
        match = FUNCTION_RE.fullmatch(line)
        if match:
            values = [int(value) for value in match.groups()]
            functions.append(
                Function(
                    tuple(values[0:3]), values[3], values[4], values[5],
                    values[6], values[7], values[8], values[9], values[10],
                )
            )
        elif SUMMARY_RE.fullmatch(line):
            summaries += 1
    if summaries != 1:
        raise ValueError("exactly one accepted DMA summary is required")
    if [function.bdf for function in functions] != list(EXPECTED):
        raise ValueError("DMA function inventory is missing, duplicated, or noncanonical")
    initially_enabled = 0
    initial_mask = 0
    for index, function in enumerate(functions):
        expected = EXPECTED[function.bdf]
        observed = (
            function.present, function.vendor, function.device,
            function.class_code, function.bridge, function.multifunction,
        )
        if observed != expected:
            raise ValueError(f"DMA identity/status mismatch at {function.bdf}")
        if function.command_before & ~COMMAND_MASK:
            raise ValueError(f"noncanonical initial Command word at {function.bdf}")
        if function.command_after != 0:
            raise ValueError(f"noncanonical deny-all Command read-back at {function.bdf}")
        if not function.present and (
            function.command_before != 0 or function.command_after != 0
        ):
            raise ValueError(f"absent function carries Command state at {function.bdf}")
        if function.command_before & BUS_MASTER:
            initially_enabled += 1
            initial_mask |= 1 << index
    if (initially_enabled, initial_mask) != (1, 16):
        raise ValueError("initial bus-master state disagrees with accepted q35 fixture")
    return functions


def write_snapshot(
    output: Path, functions: list[Function], qemu_version: str, revision: str
) -> None:
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("source revision must be a full lowercase Git commit")
    if "\t" in qemu_version or "\n" in qemu_version or not qemu_version:
        raise ValueError("QEMU version must be one nonempty TSV-safe line")
    lines = [
        "# leanos-dma-quarantine-snapshot-v1",
        f"meta\tqemu-version\t{qemu_version}",
        "meta\tmachine\tq35",
        "meta\taccelerator\ttcg",
        "meta\tsnapshot-version\t1",
        f"meta\ttopology-version\t{TOPOLOGY}",
        "meta\tmanifest-version\t1",
        "meta\tgenerated-policy-result\t0",
        f"meta\tsource-revision\t{revision}",
        "bdf\tpresent\tvendor\tdevice\tclass\tcommand-before\tcommand-after"
        "\tassigned\tbridge\tmultifunction\tpolicy-result",
    ]
    for function in functions:
        bdf = f"{function.bdf[0]}:{function.bdf[1]}.{function.bdf[2]}"
        lines.append(
            f"{bdf}\t{function.present}\t{function.vendor}\t{function.device}"
            f"\t{function.class_code}\t{function.command_before}"
            f"\t{function.command_after}\t0\t{function.bridge}"
            f"\t{function.multifunction}\taccepted:0"
        )
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--serial-log", type=Path, required=True)
    parser.add_argument("--source-revision", type=Path, required=True)
    parser.add_argument("--qemu-version", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    functions = parse(args.serial_log.read_text(encoding="utf-8"))
    revision = args.source_revision.read_text(encoding="utf-8").strip()
    write_snapshot(args.output, functions, args.qemu_version, revision)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
