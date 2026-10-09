#!/usr/bin/env python3
"""Record per-module Lean elaboration time and gate regressions (issue #498).

Lake prints `Built <Module> (<time>)` for every module it rebuilds when ANSI
output is off. GitHub runners differ in speed by up to 2x between runs, so a
run is first normalized by its speed factor: the median, over the rebuilt
modules whose baseline time is at least MIN_FACTOR_SECONDS, of current time
over baseline time. Measured over four full main/PR runs, the normalized
top-15 module times stayed within 16% of their medians.

A run fails when, after normalization, either
  * a module among the TOP_N slowest baseline modules regresses by more than
    REGRESSION_FRACTION and by more than FLOOR_SECONDS; or
  * a module outside that set (or new) exceeds both the TOP_N-th baseline
    time and CEILING_SECONDS, i.e. it enters the slowest set above a ceiling.

Only rebuilt modules are compared, since Lake replays cached modules without
elaborating them. A run with fewer than MIN_SAMPLE rebuilt reference modules
cannot estimate its speed factor and is reported as skipped.

The baseline may be raised only by editing scripts/proof-time-baseline.tsv in
the same PR; its `# reason:` line must say why.
"""

from __future__ import annotations

import argparse
import os
import re
import statistics
import sys
from pathlib import Path

TOP_N = 15
REGRESSION_FRACTION = 0.35
FLOOR_SECONDS = 15.0
CEILING_SECONDS = 60.0
MIN_FACTOR_SECONDS = 2.0
MIN_SAMPLE = 20

BUILT = re.compile(r"Built (LeanOS(?:\.[A-Za-z0-9_]+)*) \(([0-9.]+)(ms|s)\)$")
MODULE = re.compile(r"LeanOS(?:\.[A-Za-z0-9_]+)*")
HEADER = "module\tseconds"


def parse_log(text: str) -> dict[str, float]:
    times: dict[str, float] = {}
    for line in text.splitlines():
        match = BUILT.search(line.rstrip())
        if not match:
            continue
        value = float(match.group(2))
        times[match.group(1)] = value / 1000 if match.group(3) == "ms" else value
    return times


def read_tsv(path: Path, *, baseline: bool) -> tuple[dict[str, float], str]:
    times: dict[str, float] = {}
    reason = ""
    lines = path.read_text(encoding="utf-8").splitlines()
    body = [line for line in lines if not line.startswith("#")]
    for line in lines:
        if line.startswith("# reason:"):
            reason = line[len("# reason:"):].strip()
    if not body or body[0] != HEADER:
        raise ValueError(f"{path}: header must be '{HEADER}'")
    for number, line in enumerate(body[1:], 2):
        fields = line.split("\t")
        if len(fields) != 2 or not MODULE.fullmatch(fields[0]):
            raise ValueError(f"{path}: malformed row {number}")
        try:
            seconds = float(fields[1])
        except ValueError as error:
            raise ValueError(f"{path}: row {number} has a non-numeric time") from error
        if seconds < 0 or fields[0] in times:
            raise ValueError(f"{path}: row {number} is negative or duplicated")
        times[fields[0]] = seconds
    if baseline and not reason:
        raise ValueError(f"{path}: baseline needs a non-empty '# reason:' line")
    return times, reason


def write_tsv(path: Path, times: dict[str, float], reason: str | None) -> None:
    lines = []
    if reason is not None:
        lines.append(f"# reason: {reason}")
    lines.append(HEADER)
    for module in sorted(times, key=lambda name: (-times[name], name)):
        lines.append(f"{module}\t{times[module]:.1f}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def speed_factor(current: dict[str, float], baseline: dict[str, float]) -> tuple[float, int]:
    ratios = [
        current[module] / baseline[module]
        for module in current
        if baseline.get(module, 0) >= MIN_FACTOR_SECONDS
    ]
    if len(ratios) < MIN_SAMPLE:
        return 1.0, len(ratios)
    return statistics.median(ratios), len(ratios)


def evaluate(current: dict[str, float], baseline: dict[str, float]) -> tuple[list[str], list[str], bool]:
    factor, sample = speed_factor(current, baseline)
    report = [f"proof-time sample={sample} factor={factor:.2f}"]
    if sample < MIN_SAMPLE:
        report.append(f"proof-time result=SKIPPED rebuilt-reference-modules={sample} minimum={MIN_SAMPLE}")
        return report, [], True
    ranked = sorted(baseline, key=lambda name: (-baseline[name], name))
    slowest = ranked[:TOP_N]
    threshold = baseline[slowest[-1]] if slowest else 0.0
    failures = []
    report.append("| module | baseline s | normalized s | delta |")
    report.append("| --- | ---: | ---: | ---: |")
    for module in slowest:
        if module not in current:
            report.append(f"| {module} | {baseline[module]:.1f} | cached | |")
            continue
        normalized = current[module] / factor
        delta = normalized - baseline[module]
        report.append(
            f"| {module} | {baseline[module]:.1f} | {normalized:.1f} | {delta / baseline[module]:+.0%} |"
        )
        if delta > FLOOR_SECONDS and delta > REGRESSION_FRACTION * baseline[module]:
            failures.append(
                f"module={module} baseline={baseline[module]:.1f} normalized={normalized:.1f} "
                f"regression>{REGRESSION_FRACTION:.0%}+{FLOOR_SECONDS:.0f}s"
            )
    for module in sorted(set(current) - set(slowest)):
        normalized = current[module] / factor
        if normalized > threshold and normalized > CEILING_SECONDS:
            failures.append(
                f"module={module} normalized={normalized:.1f} entered-top-{TOP_N} "
                f"above-ceiling={CEILING_SECONDS:.0f}s"
            )
    report.append(f"proof-time result={'FAIL' if failures else 'PASS'}")
    return report, failures, False


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("logs", nargs="+", type=Path, help="lake build --no-ansi output")
    parser.add_argument("--baseline", type=Path, default=Path("scripts/proof-time-baseline.tsv"))
    parser.add_argument("--record", type=Path, help="write this run's raw module times as TSV")
    parser.add_argument("--write-baseline", type=Path,
                        help="write the normalized median of LOGS as a new baseline")
    parser.add_argument("--reason", help="one-line reason recorded with --write-baseline")
    args = parser.parse_args()

    runs = [parse_log(path.read_text(encoding="utf-8", errors="replace")) for path in args.logs]
    if args.write_baseline:
        if not args.reason or "\n" in args.reason:
            parser.error("--write-baseline needs a one-line --reason")
        # Normalize every run against the first-pass median, then take medians.
        modules = set.intersection(*(set(run) for run in runs))
        first = {module: statistics.median(run[module] for run in runs) for module in modules}
        normalized = []
        for run in runs:
            factor, _ = speed_factor({m: run[m] for m in modules}, first)
            normalized.append({module: run[module] / factor for module in modules})
        write_tsv(args.write_baseline,
                  {module: statistics.median(run[module] for run in normalized) for module in modules},
                  args.reason)
        return 0

    if len(runs) != 1:
        parser.error("checking takes exactly one log")
    current = runs[0]
    if args.record:
        write_tsv(args.record, current, None)
    try:
        baseline, reason = read_tsv(args.baseline, baseline=True)
    except (OSError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    report, failures, _ = evaluate(current, baseline)
    print(f"proof-time baseline reason: {reason}")
    print("\n".join(report))
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a", encoding="utf-8") as handle:
            handle.write("### Lean proof-time budget\n\n" + "\n".join(report) + "\n")
    for failure in failures:
        print(f"error: proof-time {failure}", file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
