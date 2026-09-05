#!/usr/bin/env python3
"""Validate one successful aggregate-check phase timing record."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys

HEADER = "phase\tphase_seconds\ttotal_seconds"
FAILURE_HEADER = "phase\tphase_seconds\ttotal_seconds\texit_code"
PHASES = (
    "lean-and-generated-contracts",
    "security-and-platform-contracts",
    "hosted-boundary-and-boot-contracts",
    "image-and-emulator-contracts",
    "proof-integrity-and-negative-fixtures",
)


def validate(path: Path) -> int:
    lines = path.read_text(encoding="utf-8").splitlines()
    if not lines or lines[0] != HEADER:
        raise ValueError("timing header is missing or unrecognized")
    if len(lines) != len(PHASES) + 1:
        raise ValueError(f"expected {len(PHASES)} phases, found {len(lines) - 1}")
    previous_total = 0
    for number, (line, expected) in enumerate(zip(lines[1:], PHASES, strict=True), 2):
        fields = line.split("\t")
        if len(fields) != 3 or fields[0] != expected:
            raise ValueError(f"line {number}: expected phase {expected}")
        try:
            phase_seconds, total_seconds = map(int, fields[1:])
        except ValueError as error:
            raise ValueError(f"line {number}: timing values must be integers") from error
        if phase_seconds < 0 or total_seconds != previous_total + phase_seconds:
            raise ValueError(f"line {number}: invalid cumulative timing")
        previous_total = total_seconds
    return previous_total


def validate_failure(path: Path) -> tuple[str, int, int, int]:
    lines = path.read_text(encoding="utf-8").splitlines()
    if len(lines) != 2 or lines[0] != FAILURE_HEADER:
        raise ValueError("failure timing header or row count is invalid")
    fields = lines[1].split("\t")
    if len(fields) != 4 or fields[0] not in PHASES:
        raise ValueError("failure timing phase is unrecognized")
    try:
        phase_seconds, total_seconds, exit_code = map(int, fields[1:])
    except ValueError as error:
        raise ValueError("failure timing values must be integers") from error
    if (
        phase_seconds < 0
        or total_seconds < phase_seconds
        or exit_code < 1
        or exit_code > 255
    ):
        raise ValueError("failure timing values are out of range")
    return fields[0], phase_seconds, total_seconds, exit_code


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("timing_file", type=Path)
    args = parser.parse_args()
    try:
        total = validate(args.timing_file)
    except (OSError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    print(f"Aggregate check phase timing evidence passed (total={total}s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
