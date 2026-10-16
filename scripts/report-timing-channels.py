#!/usr/bin/env python3
"""Report the timing-channels image's cycle counts (issue #576, ADR 0028).

The timing-channels image times each path ADR 0028 names with the
time-stamp counter at CPL0 and prints one `CYCLES` record per path, plus the
refusal overrun count.  scripts/run-image.sh keeps those records out of the
exact transcript (the counts vary from run to run) and passes them here.

Checked, so a malformed or regressed run fails:

* exactly the named paths, in order, each with its sample count and
  `min <= median <= max`;
* the closed refusal paths: their reported budget is the image's, and no
  refused reply left before it (`min >= budget`).

Reported, for regression visibility (failing only with `--strict`):

* each path's median beside the median recorded in
  scripts/timing-channels-baseline.tsv, and their ratio; `--strict` fails a
  ratio above `--tolerance` (default 4) or a refusal overrun;
* the spread of the two closed refusal paths' medians, which padding keeps
  near zero, beside the spread of their unpadded work;
* the declared channels' differences: 16-byte against 1-byte copy, and the
  wake round trip with the receiver busy against idle.

The counts come from whatever counter the machine has: under QEMU's TCG the
counter follows the host's, so they move with host load.  `--write-baseline`
records the medians of the given run (with a `# reason:` line) for the
platform it ran on.

usage: report-timing-channels.py [--strict] [--tolerance X]
           [--baseline TSV] [--write-baseline REASON] CYCLES_FILE
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BASELINE = ROOT / "scripts/timing-channels-baseline.tsv"
PREFIX = "LEANOS/26 CYCLES "
SAMPLES = 64
BUDGET = 100000
PATHS = (
    ("refusal.peer", "closed", None),
    ("refusal.unissued", "closed", None),
    ("refusal.peer.work", "unpadded", None),
    ("refusal.unissued.work", "unpadded", None),
    ("own-request", "baseline", None),
    ("copy-in.1", "declared", "caller-length"),
    ("copy-in.16", "declared", "caller-length"),
    ("ipc.wake.idle", "declared", "receiver-run"),
    ("ipc.wake.busy", "declared", "receiver-run"),
)
RECORD = re.compile(
    r"path=(?P<path>[a-z0-9.-]+) class=(?P<class>[a-z]+)"
    r"(?: source=(?P<source>[a-z-]+))? samples=(?P<samples>[0-9]+)"
    r" min=(?P<min>[0-9]+) median=(?P<median>[0-9]+) max=(?P<max>[0-9]+)"
    r"(?: budget=(?P<budget>[0-9]+))?")
OVERRUNS = re.compile(r"path=refusal class=closed overruns=(?P<overruns>[0-9]+)")


class ReportError(Exception):
    pass


def parse(text: str) -> tuple[dict[str, dict[str, int]], int]:
    lines = [line for line in text.splitlines() if line]
    if len(lines) != len(PATHS) + 1:
        raise ReportError(f"expected {len(PATHS) + 1} cycle records, found {len(lines)}")
    paths: dict[str, dict[str, int]] = {}
    for line, (name, klass, source) in zip(lines, PATHS):
        if not line.startswith(PREFIX):
            raise ReportError(f"not a cycle record: {line!r}")
        match = RECORD.fullmatch(line[len(PREFIX):])
        if (not match or match["path"] != name or match["class"] != klass or
                match["source"] != source):
            raise ReportError(f"expected path {name} ({klass}), found {line!r}")
        row = {key: int(match[key]) for key in ("samples", "min", "median", "max")}
        if row["samples"] != SAMPLES:
            raise ReportError(f"{name}: {row['samples']} samples, expected {SAMPLES}")
        if not row["min"] <= row["median"] <= row["max"]:
            raise ReportError(f"{name}: min, median and max out of order")
        if klass == "closed":
            if match["budget"] is None or int(match["budget"]) != BUDGET:
                raise ReportError(f"{name}: budget is not {BUDGET}")
            if row["min"] < BUDGET:
                raise ReportError(f"{name}: a refused reply left before its budget")
        elif match["budget"] is not None:
            raise ReportError(f"{name}: only closed paths carry a budget")
        paths[name] = row
    if not lines[-1].startswith(PREFIX):
        raise ReportError("missing refusal overrun record")
    match = OVERRUNS.fullmatch(lines[-1][len(PREFIX):])
    if not match:
        raise ReportError(f"malformed refusal overrun record: {lines[-1]!r}")
    return paths, int(match["overruns"])


def read_baseline(path: Path) -> dict[str, int]:
    if not path.is_file():
        return {}
    baseline = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) != 2 or not fields[1].isdigit():
            raise ReportError(f"malformed baseline row: {line!r}")
        baseline[fields[0]] = int(fields[1])
    return baseline


def write_baseline(path: Path, paths: dict[str, dict[str, int]], reason: str) -> None:
    if not reason.strip():
        raise ReportError("a baseline needs a reason")
    lines = ["# path\tmedian-cycles",
             "# Medians of one timing-channels run (scripts/report-timing-channels.py",
             "# --write-baseline); a regression report compares each run's medians",
             "# with these.",
             f"# reason: {reason.strip()}"]
    lines += [f"{name}\t{paths[name]['median']}" for name, _, _ in PATHS]
    path.write_text("\n".join(lines) + "\n")


def spread(left: int, right: int) -> float:
    return abs(left - right) / max(left, right, 1)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("cycles")
    parser.add_argument("--baseline", type=Path, default=BASELINE)
    parser.add_argument("--strict", action="store_true")
    parser.add_argument("--tolerance", type=float, default=4.0)
    parser.add_argument("--write-baseline", metavar="REASON")
    args = parser.parse_args()
    try:
        paths, overruns = parse(Path(args.cycles).read_text())
        if args.write_baseline is not None:
            write_baseline(args.baseline, paths, args.write_baseline)
        baseline = read_baseline(args.baseline)
    except (OSError, ReportError) as error:
        print(f"error: timing-channels: {error}", file=sys.stderr)
        return 1

    regressions = []
    print("timing-channels cycle counts (ADR 0028)")
    print(f"{'path':<24}{'class':<10}{'min':>10}{'median':>10}{'max':>12}"
          f"{'baseline':>10}{'ratio':>8}")
    for name, klass, _ in PATHS:
        row = paths[name]
        recorded = baseline.get(name)
        ratio = row["median"] / recorded if recorded else None
        if ratio is not None and ratio > args.tolerance:
            regressions.append(f"{name} median {row['median']} is {ratio:.2f}x "
                               f"the baseline {recorded}")
        print(f"{name:<24}{klass:<10}{row['min']:>10}{row['median']:>10}{row['max']:>12}"
              f"{recorded if recorded else '-':>10}"
              f"{f'{ratio:.2f}' if ratio is not None else '-':>8}")
    peer, unissued = paths["refusal.peer"], paths["refusal.unissued"]
    peer_work, unissued_work = paths["refusal.peer.work"], paths["refusal.unissued.work"]
    print(f"closed: refusal budget {BUDGET} cycles, overruns {overruns}; median spread "
          f"padded {spread(peer['median'], unissued['median']):.4f}, unpadded "
          f"{spread(peer_work['median'], unissued_work['median']):.4f}")
    print(f"declared: copy-in 16 - 1 bytes = "
          f"{paths['copy-in.16']['median'] - paths['copy-in.1']['median']} cycles (median); "
          f"wake round trip busy - idle = "
          f"{paths['ipc.wake.busy']['median'] - paths['ipc.wake.idle']['median']} cycles "
          f"(median; the receiver ran 4096 iterations)")
    if overruns:
        regressions.append(f"{overruns} refused replies overran the {BUDGET}-cycle budget")
    for regression in regressions:
        print(f"{'error' if args.strict else 'warning'}: timing-channels: {regression}",
              file=sys.stderr)
    return 1 if args.strict and regressions else 0


if __name__ == "__main__":
    sys.exit(main())
