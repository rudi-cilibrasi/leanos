#!/usr/bin/env python3
"""Validate one complete LeanOS image-build phase timing record."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
import sys


HEADER = "phase\tphase_seconds\ttotal_seconds"
PHASES = (
    "bootstrap-and-lean-generation",
    "object-graph-prelinks",
    "boot-plans-and-final-links",
    "policy-and-fixture-validation",
    "iso-packaging",
    "manifests-and-completion",
)


class TimingError(RuntimeError):
    pass


@dataclass(frozen=True)
class Timing:
    phase: str
    phase_seconds: int
    total_seconds: int


def parse_timing(path: Path) -> list[Timing]:
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError as error:
        raise TimingError(f"cannot read build timing evidence {path}: {error}") from error
    if not lines or lines[0] != HEADER:
        raise TimingError(f"{path}: build timing header is missing or unrecognized")
    if len(lines) != len(PHASES) + 1:
        raise TimingError(
            f"{path}: expected {len(PHASES)} build phases, found {len(lines) - 1}"
        )

    timings: list[Timing] = []
    previous_total = 0
    for line_number, (line, expected_phase) in enumerate(
        zip(lines[1:], PHASES, strict=True), 2
    ):
        fields = line.split("\t")
        if len(fields) != 3:
            raise TimingError(f"{path}:{line_number}: expected three tab-separated fields")
        phase, phase_text, total_text = fields
        if phase != expected_phase:
            raise TimingError(
                f"{path}:{line_number}: expected phase {expected_phase}, found {phase}"
            )
        try:
            phase_seconds = int(phase_text)
            total_seconds = int(total_text)
        except ValueError as error:
            raise TimingError(f"{path}:{line_number}: timing values must be integers") from error
        if phase_seconds < 0 or total_seconds < 0:
            raise TimingError(f"{path}:{line_number}: timing values must be nonnegative")
        if total_seconds != previous_total + phase_seconds:
            raise TimingError(
                f"{path}:{line_number}: cumulative time is inconsistent "
                f"({previous_total} + {phase_seconds} != {total_seconds})"
            )
        timings.append(Timing(phase, phase_seconds, total_seconds))
        previous_total = total_seconds
    return timings


def github_summary(timings: list[Timing]) -> str:
    """Render every validated phase for the GitHub job summary."""

    rows = [
        "### Image-build phase timing",
        "",
        "| Phase | Duration (s) | Cumulative (s) |",
        "| --- | ---: | ---: |",
    ]
    rows.extend(
        f"| `{timing.phase}` | {timing.phase_seconds} | {timing.total_seconds} |"
        for timing in timings
    )
    slowest = max(timings, key=lambda timing: timing.phase_seconds)
    rows.extend(
        (
            "",
            f"Total: **{timings[-1].total_seconds}s**; "
            f"slowest phase: `{slowest.phase}` (**{slowest.phase_seconds}s**).",
        )
    )
    return "\n".join(rows)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("timing_file", type=Path)
    parser.add_argument(
        "--format",
        choices=("text", "github"),
        default="text",
        help="render a concise text result or a complete GitHub summary table",
    )
    args = parser.parse_args()
    try:
        timings = parse_timing(args.timing_file)
    except TimingError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    if args.format == "github":
        print(github_summary(timings))
    else:
        slowest = max(timings, key=lambda timing: timing.phase_seconds)
        print(
            "Build phase timing evidence passed "
            f"(total={timings[-1].total_seconds}s, "
            f"slowest={slowest.phase}:{slowest.phase_seconds}s)"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
