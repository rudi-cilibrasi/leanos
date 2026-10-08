#!/usr/bin/env python3
"""Fixture tests for check-proof-time-budget.py (issue #498)."""

from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "scripts" / "check-proof-time-budget.py"

# Thirty reference modules plus three slow ones, so the speed factor has a
# sample and the slowest set has a well-defined threshold.
BASE = {f"LeanOS.Ref{index}": 4.0 + index for index in range(30)}
BASE.update({"LeanOS.Slow": 120.0, "LeanOS.Medium": 80.0, "LeanOS.Small": 40.0})


def log(times: dict[str, float]) -> str:
    lines = ["⚠ [1/2] Replayed LeanOS.Cached"]
    for number, (module, seconds) in enumerate(sorted(times.items()), 2):
        stamp = f"{int(seconds * 1000)}ms" if seconds < 1 else f"{seconds:.1f}s"
        lines.append(f"✔ [{number}/99] Built {module} ({stamp})")
        lines.append(f"✔ [{number}/99] Built {module}:c.o (1.0s)")
    return "\n".join(lines) + "\n"


def baseline(reason: str = "fixture") -> str:
    rows = [f"# reason: {reason}" if reason else "# no reason", "module\tseconds"]
    rows += [f"{module}\t{seconds:.1f}" for module, seconds in BASE.items()]
    return "\n".join(rows) + "\n"


def run(directory: Path, times: dict[str, float], base: str | None = None) -> subprocess.CompletedProcess:
    (directory / "lake.log").write_text(log(times), encoding="utf-8")
    (directory / "baseline.tsv").write_text(base or baseline(), encoding="utf-8")
    return subprocess.run(
        [sys.executable, str(CHECKER), str(directory / "lake.log"),
         "--baseline", str(directory / "baseline.tsv"),
         "--record", str(directory / "record.tsv")],
        capture_output=True, text=True, check=False,
    )


def expect(name: str, result: subprocess.CompletedProcess, status: int, needle: str) -> None:
    output = result.stdout + result.stderr
    if result.returncode != status or needle not in output:
        raise SystemExit(f"{name}: status={result.returncode} expected={status} "
                         f"missing '{needle}'\n{output}")
    print(f"PASS {name}")


def main() -> int:
    with tempfile.TemporaryDirectory() as raw:
        directory = Path(raw)
        expect("identity", run(directory, BASE), 0, "result=PASS")
        recorded = (directory / "record.tsv").read_text(encoding="utf-8").splitlines()
        if recorded[0] != "module\tseconds" or recorded[1] != "LeanOS.Slow\t120.0":
            raise SystemExit(f"record: unexpected TSV head {recorded[:2]}")
        print("PASS record")
        slower = {module: seconds * 1.9 for module, seconds in BASE.items()}
        expect("uniform-slow-runner", run(directory, slower), 0, "factor=1.90")
        regressed = dict(BASE, **{"LeanOS.Slow": 120.0 * 1.5})
        expect("top-module-regression", run(directory, regressed), 1,
               "module=LeanOS.Slow baseline=120.0 normalized=180.0")
        expect("regression-below-fraction", run(directory, dict(BASE, **{"LeanOS.Slow": 155.0})), 0,
               "result=PASS")
        expect("regression-below-floor", run(directory, dict(BASE, **{"LeanOS.Ref0": 18.0})), 0,
               "result=PASS")
        expect("new-module-above-ceiling", run(directory, dict(BASE, **{"LeanOS.New": 90.0})), 1,
               "module=LeanOS.New normalized=90.0 entered-top-15")
        expect("new-module-below-ceiling", run(directory, dict(BASE, **{"LeanOS.New": 50.0})), 0,
               "result=PASS")
        partial = {module: BASE[module] * 3 for module in ("LeanOS.Slow", "LeanOS.Ref1")}
        expect("partial-rebuild-skipped", run(directory, partial), 0, "result=SKIPPED")
        expect("baseline-needs-reason", run(directory, BASE, baseline("")), 1,
               "needs a non-empty '# reason:' line")
        expect("ms-times-parse", run(directory, dict(BASE, **{"LeanOS.Tiny": 0.25})), 0,
               "result=PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
