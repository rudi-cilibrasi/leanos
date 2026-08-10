#!/usr/bin/env python3
"""Validate guest VT-d activation records and retain one canonical snapshot."""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys


TOPOLOGY = "0001000800020002"
PAGE_BYTES = 4096
UNIT_RE = re.compile(
    r"^LEANOS/21 VTD unit=0 mmio=4275634176 version=16 "
    r"cap=59110346977575430 ecap=3842 gsts=0 fsts=0 rtaddr=0 "
    r"stage=pre-activation result=PASS$"
)
PLAN_RE = re.compile(
    r"^LEANOS/21 VTD-PLAN root-frame=([1-9]\d*) context-frame=([1-9]\d*) "
    r"root-words=512 context-words=512 present-root-entries=1 "
    r"present-context-entries=0 translation=disabled deny-all=1 result=PASS$"
)
TABLES_RE = re.compile(
    r"^LEANOS/21 VTD-TABLES root-frame=([1-9]\d*) context-frame=([1-9]\d*) "
    r"scrub=verified construct=verified root-words=512 context-words=512 "
    r"result=PASS$"
)
ACTIVATE_RE = re.compile(
    r"^LEANOS/21 VTD-ACTIVATE order=validate,scrub,construct,publish,"
    r"invalidate-context,invalidate-iotlb,enable,verify journal=2271560481 "
    r"gsts=3221225472 fsts=0 rtaddr=([1-9]\d*) generated-result=0 "
    r"stage=pre-cpl3 result=PASS$"
)


def parse(serial_log: Path) -> tuple[int, int, int]:
    lines = [
        line
        for line in serial_log.read_text(encoding="utf-8", errors="strict").splitlines()
        if line.startswith("LEANOS/21 ")
    ]
    if len(lines) != 4:
        raise ValueError(f"expected exactly 4 VT-d records, found {len(lines)}")
    if UNIT_RE.match(lines[0]) is None:
        raise ValueError(f"invalid quiescent-unit record: {lines[0]!r}")
    plan = PLAN_RE.match(lines[1])
    if plan is None:
        raise ValueError(f"invalid plan record: {lines[1]!r}")
    tables = TABLES_RE.match(lines[2])
    if tables is None:
        raise ValueError(f"invalid table-construction record: {lines[2]!r}")
    activate = ACTIVATE_RE.match(lines[3])
    if activate is None:
        raise ValueError(f"invalid activation record: {lines[3]!r}")
    root_frame = int(plan.group(1))
    context_frame = int(plan.group(2))
    if context_frame != root_frame + 1:
        raise ValueError("plan table frames are not adjacent")
    if (int(tables.group(1)), int(tables.group(2))) != (root_frame, context_frame):
        raise ValueError("construction frames disagree with the plan frames")
    root_address = int(activate.group(1))
    if root_address != root_frame * PAGE_BYTES:
        raise ValueError("published root pointer disagrees with the plan frame")
    return root_frame, context_frame, root_address


def write_snapshot(
    output: Path,
    root_frame: int,
    context_frame: int,
    root_address: int,
    qemu_version: str,
    revision: str,
) -> None:
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("source revision must be a full lowercase Git commit")
    if "\t" in qemu_version or "\n" in qemu_version or not qemu_version:
        raise ValueError("QEMU version must be one nonempty TSV-safe line")
    lines = [
        "# leanos-vtd-activation-snapshot-v1",
        f"meta\tqemu-version\t{qemu_version}",
        "meta\tmachine\tq35",
        "meta\taccelerator\ttcg",
        "meta\tplan-version\t1",
        f"meta\ttopology-version\t{TOPOLOGY}",
        "meta\tunit-version\t16",
        "meta\tcapability\t59110346977575430",
        "meta\textended-capability\t3842",
        "meta\tenabled-global-status\t3221225472",
        "meta\tfault-status\t0",
        "meta\tjournal\t2271560481",
        "meta\tgenerated-result\t0",
        f"meta\tsource-revision\t{revision}",
        "table\troot-frame\t" + str(root_frame),
        "table\tcontext-frame\t" + str(context_frame),
        "table\troot-address\t" + str(root_address),
    ]
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--serial-log", type=Path, required=True)
    parser.add_argument("--source-revision", type=Path, required=True)
    parser.add_argument("--qemu-version", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        revision = args.source_revision.read_text(encoding="ascii").strip()
        root_frame, context_frame, root_address = parse(args.serial_log)
        write_snapshot(
            args.output, root_frame, context_frame, root_address,
            args.qemu_version, revision,
        )
    except (OSError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
