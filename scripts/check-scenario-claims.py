#!/usr/bin/env python3
"""Every emulator scenario names the claims it tests and what it does not
prove (issue #497).

Fails if a scenario in scripts/scenario-manifest.json lacks a non-empty
`does_not_prove`, if its `claims` cite an ID missing from
docs/security-claims.md, if a Tested claim row cites a scenario that does not
exist (as `scenario:<name>`), or if the README's generated scenario index is
stale. `--render` prints that index.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
import os
MANIFEST = Path(os.environ.get("LEANOS_SCENARIO_MANIFEST", ROOT / "scripts/scenario-manifest.json"))
CLAIMS = Path(os.environ.get("LEANOS_CLAIM_INDEX", ROOT / "docs/security-claims.md"))
README = ROOT / "README.md"
BEGIN, END = "<!-- scenario-index:start -->", "<!-- scenario-index:end -->"


def render(scenarios: dict) -> str:
    lines = ["| Scenario | Tier | Tested evidence for |", "| --- | --- | --- |"]
    for name, entry in scenarios.items():
        claims = ", ".join(entry["claims"]) or "none (integration only)"
        lines.append(f"| `{name}` | {entry.get('tier', '-')} | {claims} |")
    return "\n".join(lines)


def main() -> int:
    scenarios = json.loads(MANIFEST.read_text())["scenarios"]
    if sys.argv[1:] == ["--render"]:
        print(render(scenarios))
        return 0
    index = CLAIMS.read_text()
    known = set(re.findall(r"^\| (SC-[A-Z0-9-]+) \|", index, re.M))
    for name, entry in scenarios.items():
        statement = entry.get("does_not_prove")
        if not isinstance(statement, str) or not statement.strip():
            print(f"error: scenario {name} lacks a does_not_prove statement", file=sys.stderr)
            return 1
        claims = entry.get("claims")
        if not isinstance(claims, list):
            print(f"error: scenario {name} lacks a claims list", file=sys.stderr)
            return 1
        unknown = [claim for claim in claims if claim not in known]
        if unknown:
            print(f"error: scenario {name} cites unknown claim {unknown[0]}", file=sys.stderr)
            return 1
    for row in re.findall(r"^\| SC-[^\n]*$", index, re.M):
        if "Tested" not in row:
            continue
        for cited in re.findall(r"scenario:([a-z0-9-]+)", row):
            if cited not in scenarios:
                print(f"error: a Tested claim row cites unknown scenario {cited}", file=sys.stderr)
                return 1
    readme = README.read_text()
    if BEGIN not in readme or END not in readme:
        print("error: README.md lacks the scenario index markers", file=sys.stderr)
        return 1
    if readme.split(BEGIN, 1)[1].split(END, 1)[0].strip() != render(scenarios):
        print("error: the README scenario index is stale; regenerate it with "
              "scripts/check-scenario-claims.py --render", file=sys.stderr)
        return 1
    print(f"scenario claims: {len(scenarios)} scenarios, all with does_not_prove; README index current")
    return 0


if __name__ == "__main__":
    sys.exit(main())
