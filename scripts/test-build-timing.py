#!/usr/bin/env python3
"""Controlled-positive and negative fixtures for image-build timing evidence."""

from __future__ import annotations

import importlib.util
from pathlib import Path
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "scripts" / "check-build-timing.py"
SPEC = importlib.util.spec_from_file_location("check_build_timing", CHECKER)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot import {CHECKER}")
checker = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = checker
SPEC.loader.exec_module(checker)


def render(rows: list[tuple[str, int, int]], header: str = checker.HEADER) -> str:
    return header + "\n" + "".join(
        f"{phase}\t{phase_seconds}\t{total_seconds}\n"
        for phase, phase_seconds, total_seconds in rows
    )


def expect_failure(path: Path, content: str, needle: str) -> None:
    path.write_text(content, encoding="utf-8")
    try:
        checker.parse_timing(path)
    except checker.TimingError as error:
        if needle not in str(error):
            raise AssertionError(f"missing diagnostic {needle!r}: {error}") from error
    else:
        raise AssertionError(f"invalid timing evidence unexpectedly passed: {needle}")


def main() -> None:
    durations = (3, 5, 0, 11, 2, 1)
    total = 0
    rows: list[tuple[str, int, int]] = []
    for phase, duration in zip(checker.PHASES, durations, strict=True):
        total += duration
        rows.append((phase, duration, total))

    with tempfile.TemporaryDirectory(prefix="leanos-build-timing-") as directory:
        path = Path(directory) / "timing.tsv"
        path.write_text(render(rows), encoding="utf-8")
        observed = checker.parse_timing(path)
        if observed[-1].total_seconds != sum(durations):
            raise AssertionError("valid timing evidence lost its cumulative duration")

        expect_failure(path, render(rows, "phase,duration,total"), "header")
        expect_failure(path, render(rows[:-1]), "expected 6 build phases")
        reordered = rows.copy()
        reordered[1], reordered[2] = reordered[2], reordered[1]
        expect_failure(path, render(reordered), "expected phase")
        negative = rows.copy()
        negative[0] = (negative[0][0], -1, -1)
        expect_failure(path, render(negative), "nonnegative")
        inconsistent = rows.copy()
        inconsistent[3] = (inconsistent[3][0], inconsistent[3][1], 999)
        expect_failure(path, render(inconsistent), "cumulative time is inconsistent")
        malformed = render(rows).replace("\t3\t3", "\tthree\t3", 1)
        expect_failure(path, malformed, "must be integers")

    build = (ROOT / "scripts" / "build-image.sh").read_text(encoding="utf-8")
    if 'check-build-timing.py "$LEANOS_BUILD_TIMING_FILE"' not in build:
        raise AssertionError("image build does not validate completed timing evidence")
    reproducibility = (ROOT / "scripts" / "test-reproducible-build.sh").read_text(
        encoding="utf-8"
    )
    for contract in (
        "LEANOS_REPRO_BUILD_TIMING_DIR",
        "${name}-build-phases.tsv",
        "run_timed_build reproducibility-first",
        "run_timed_build reproducibility-second",
    ):
        if contract not in reproducibility:
            raise AssertionError(f"reproducibility timing contract is missing: {contract}")
    print("Build phase timing evidence fixtures passed")


if __name__ == "__main__":
    main()
