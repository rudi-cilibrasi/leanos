#!/usr/bin/env python3
"""Positive and negative fixtures for aggregate-check timing evidence."""

from __future__ import annotations

import importlib.util
import os
from pathlib import Path
import subprocess
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
    for contract in (
        "trap record_check_failure EXIT",
        "check-failure.tsv",
        "phase\\tphase_seconds\\ttotal_seconds\\texit_code",
        "trap - EXIT",
    ):
        if contract not in aggregate_check:
            raise AssertionError(f"aggregate check failure timing contract is missing: {contract}")

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

        failure = Path(directory) / "failure.tsv"
        failure.write_text(
            checker.FAILURE_HEADER
            + "\nimage-and-emulator-contracts\t7\t19\t2\n",
            encoding="utf-8",
        )
        if checker.validate_failure(failure) != (
            "image-and-emulator-contracts",
            7,
            19,
            2,
        ):
            raise AssertionError("valid failure timing evidence changed")
        for content, needle in (
            (failure.read_text().replace("\t2\n", "\t0\n"), "range"),
            (failure.read_text().replace("image-and-emulator-contracts", "unknown"), "phase"),
            (failure.read_text().replace("\t7\t19", "\t20\t19"), "range"),
        ):
            failure.write_text(content, encoding="utf-8")
            try:
                checker.validate_failure(failure)
            except ValueError as error:
                if needle not in str(error):
                    raise AssertionError(
                        f"missing failure diagnostic {needle!r}: {error}"
                    ) from error
            else:
                raise AssertionError(f"invalid failure fixture passed: {needle}")

        injected_log = Path(directory) / "negative-fixture.log"
        injected_log.write_text("sentinel\n", encoding="utf-8")
        injected_failure = Path(directory) / "injected-failure.tsv"
        injected_phases = Path(directory) / "injected-phases.tsv"
        injected = aggregate_check.replace(
            first_check,
            "\n".join(
                (
                    f'negative_log={str(injected_log)!r}',
                    'check_phase="proof-integrity-and-negative-fixtures"',
                    "exit 37",
                )
            ),
            1,
        )
        injected_script = ROOT / "scripts" / ".check-timing-injected.sh"
        try:
            injected_script.write_text(injected, encoding="utf-8")
            result = subprocess.run(
                ["bash", str(injected_script)],
                cwd=ROOT,
                env={
                    **os.environ,
                    "LEANOS_CHECK_TIMING_FILE": str(injected_phases),
                    "LEANOS_CHECK_FAILURE_TIMING_FILE": str(injected_failure),
                },
                check=False,
                capture_output=True,
                text=True,
            )
        finally:
            injected_script.unlink(missing_ok=True)
        if result.returncode != 37:
            raise AssertionError(
                f"injected aggregate failure returned {result.returncode}: {result.stderr}"
            )
        if injected_log.exists():
            raise AssertionError("aggregate failure handler left its negative log behind")
        phase, _phase_seconds, _total_seconds, exit_code = checker.validate_failure(
            injected_failure
        )
        if phase != "proof-integrity-and-negative-fixtures" or exit_code != 37:
            raise AssertionError("final-phase failure timing lost its phase or exit code")
    print("Aggregate check timing evidence fixtures passed")


if __name__ == "__main__":
    main()
