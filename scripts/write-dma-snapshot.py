#!/usr/bin/env python3
"""Validate guest PCI records and retain one canonical machine snapshot."""

from __future__ import annotations

import argparse
import os
from dataclasses import dataclass
from pathlib import Path
import re


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


BUS_MASTER = 1 << 2
COMMAND_MASK = 0x7FF
PRODUCTION_EXPECTED = {
    (0, 0, 0): (1, 0x8086, 0x29C0, 0x060000, 0, 0, 0),
    (0, 1, 0): (1, 0x1234, 0x1111, 0x030000, 0, 0, 0),
    (0, 3, 0): (0, 0, 0, 0, 0, 0, 0),
    (0, 31, 0): (1, 0x8086, 0x2918, 0x060100, 1, 1, 0),
    (0, 31, 2): (1, 0x8086, 0x2922, 0x010601, 0, 1, 0),
    (0, 31, 3): (1, 0x8086, 0x2930, 0x0C0500, 0, 1, 0),
}


@dataclass(frozen=True)
class Profile:
    """One pinned q35 construction: its topology, inventory and the
    firmware bus-mastering state its quarantine must observe."""
    topology: str
    present: int
    initial_masters: int
    initial_mask: int
    expected: dict


PROFILES = {
    "production": Profile("0001000800020002", 5, 1, 16, PRODUCTION_EXPECTED),
    # The device-service construction (issue #449) appends the assigned
    # qemu-xhci at 00:02.0, which SeaBIOS leaves bus-mastering; the
    # quarantine still reads back Command=0 before VT-d is enabled.
    "device-service": Profile(
        "0001000800020004", 6, 2, 80,
        {**PRODUCTION_EXPECTED, (0, 2, 0): (1, 0x1B36, 0x000D, 0x0C0330, 0, 0, 1)},
    ),
    # The ahci-service construction (issue #496) adds only a disk behind the
    # built-in AHCI's port 1: the production PCI inventory, quarantined
    # unassigned; the kernel assigns the AHCI only after VT-d is enabled.
    "ahci-service": Profile("0001000800020005", 5, 1, 16, PRODUCTION_EXPECTED),
}


def function_re(profile: Profile) -> re.Pattern:
    return re.compile(
        "^" + re.escape(SERIAL["15/DMA-FUNCTION"])
        + rf" manifest=1 topology={profile.topology} "
        r"bdf=(\d+):(\d+)\.(\d+) present=([01]) vendor=(\d+) device=(\d+) "
        r"class=(\d+) command-before=(\d+) command-after=(\d+) assigned=([01]) "
        r"bridge=([01]) multifunction=([01]) policy=accepted$"
    )


def summary_re(profile: Profile) -> re.Pattern:
    count = profile.present
    return re.compile(
        "^" + re.escape(SERIAL["15/DMA"])
        + rf" snapshot=1 topology={profile.topology} bus=0 scanned=256 "
        rf"present={count} optional-absent=1 writes={count} readbacks={count} "
        rf"initial-bus-masters={profile.initial_masters} "
        rf"initial-bus-master-mask={profile.initial_mask} bus-master=disabled "
        r"readback=exact generated-result=0 "
        r"stage=pre-cpl3 result=PASS$"
    )


@dataclass(frozen=True)
class Function:
    bdf: tuple[int, int, int]
    present: int
    vendor: int
    device: int
    class_code: int
    command_before: int
    command_after: int
    assigned: int
    bridge: int
    multifunction: int


def parse(text: str, profile: Profile = PROFILES["production"]) -> list[Function]:
    functions: list[Function] = []
    summaries = 0
    function_pattern = function_re(profile)
    summary_pattern = summary_re(profile)
    for line in text.splitlines():
        match = function_pattern.fullmatch(line)
        if match:
            values = [int(value) for value in match.groups()]
            functions.append(
                Function(
                    tuple(values[0:3]), values[3], values[4], values[5],
                    values[6], values[7], values[8], values[9], values[10],
                    values[11],
                )
            )
        elif summary_pattern.fullmatch(line):
            summaries += 1
    if summaries != 1:
        raise ValueError("exactly one accepted DMA summary is required")
    if [function.bdf for function in functions] != list(profile.expected):
        raise ValueError("DMA function inventory is missing, duplicated, or noncanonical")
    initially_enabled = 0
    initial_mask = 0
    for index, function in enumerate(functions):
        expected = profile.expected[function.bdf]
        observed = (
            function.present, function.vendor, function.device,
            function.class_code, function.bridge, function.multifunction,
            function.assigned,
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
    if (initially_enabled, initial_mask) != (profile.initial_masters, profile.initial_mask):
        raise ValueError("initial bus-master state disagrees with accepted q35 fixture")
    return functions


def write_snapshot(
    output: Path, functions: list[Function], qemu_version: str, revision: str,
    profile: Profile = PROFILES["production"],
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
        f"meta\ttopology-version\t{profile.topology}",
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
            f"\t{function.command_after}\t{function.assigned}\t{function.bridge}"
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
    parser.add_argument("--profile", choices=tuple(PROFILES), default="production")
    args = parser.parse_args()
    profile = PROFILES[args.profile]
    functions = parse(args.serial_log.read_text(encoding="utf-8"), profile)
    revision = args.source_revision.read_text(encoding="utf-8").strip()
    write_snapshot(args.output, functions, args.qemu_version, revision, profile)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
