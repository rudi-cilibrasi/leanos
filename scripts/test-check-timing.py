#!/usr/bin/env python3
"""Positive and negative fixtures for aggregate-check timing evidence."""

from __future__ import annotations

import importlib.util
from pathlib import Path
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "scripts" / "check-check-timing.py"
SPEC = importlib.util.spec_from_file_location("check_check_timing", CHECKER)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot import {CHECKER}")
checker = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = checker
SPEC.loader.exec_module(checker)


def render(phases: tuple[str, ...] = checker.PHASES) -> str:
    total = 0
    rows = [checker.HEADER]
    for index, phase in enumerate(phases, 1):
        total += index
        rows.append(f"{phase}\t{index}\t{total}")
    return "\n".join(rows) + "\n"


def main() -> None:
    aggregate_check = (ROOT / "scripts" / "check.sh").read_text(encoding="utf-8")
    timing_header = "printf 'phase\\tphase_seconds\\ttotal_seconds\\n'"
    first_check = "./scripts/test-generate-oracle-adapter-map.sh"
    if aggregate_check.index(timing_header) > aggregate_check.index(first_check):
        raise AssertionError("timing evidence must exist before the first aggregate check")

    with tempfile.TemporaryDirectory(prefix="leanos-check-timing-") as directory:
        path = Path(directory) / "timing.tsv"
        path.write_text(render(), encoding="utf-8")
        if checker.validate(path) != 15:
            raise AssertionError("valid timing evidence lost its total")
        for content, needle in (
            (render()[6:], "header"),
            (render(checker.PHASES[:-1]), "expected 5 phases"),
            (render().replace("\t2\t3", "\ttwo\t3"), "integers"),
            (render().replace("\t3\t6", "\t3\t99"), "cumulative"),
        ):
            path.write_text(content, encoding="utf-8")
            try:
                checker.validate(path)
            except ValueError as error:
                if needle not in str(error):
                    raise AssertionError(f"missing diagnostic {needle!r}: {error}") from error
            else:
                raise AssertionError(f"invalid fixture passed: {needle}")
    print("Aggregate check timing evidence fixtures passed")


if __name__ == "__main__":
    main()
