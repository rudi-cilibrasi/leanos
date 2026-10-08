#!/usr/bin/env bash
# check-scenario-claims.py (issue #497) passes on the repository and rejects
# a scenario without does_not_prove, an unknown claim, and a Tested row that
# cites a missing scenario.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
python3 scripts/check-scenario-claims.py >/dev/null
reject() {
  local name="$1" expected="$2"
  if LEANOS_SCENARIO_MANIFEST="$tmp/$name.json" LEANOS_CLAIM_INDEX="$tmp/$name.md" \
      python3 scripts/check-scenario-claims.py >"$tmp/$name.log" 2>&1; then
    echo "error: scenario-claims check accepted $name" >&2; exit 1
  fi
  grep -q "$expected" "$tmp/$name.log" || { cat "$tmp/$name.log" >&2; exit 1; }
}
python3 - "$tmp" <<'PY'
import json, sys
from pathlib import Path
tmp = Path(sys.argv[1])
manifest = json.loads(Path("scripts/scenario-manifest.json").read_text())
claims = Path("docs/security-claims.md").read_text()
missing = json.loads(json.dumps(manifest)); del missing["scenarios"]["blocking-ipc"]["does_not_prove"]
unknown = json.loads(json.dumps(manifest)); unknown["scenarios"]["blocking-ipc"]["claims"] = ["SC-NOT-A-CLAIM"]
for name, data in (("missing", missing), ("unknown", unknown), ("tested", manifest)):
    (tmp / f"{name}.json").write_text(json.dumps(data))
    (tmp / f"{name}.md").write_text(claims)
(tmp / "tested.md").write_text(claims.replace("<!-- claim-index:end -->",
    "| SC-FIXTURE | `x` | x | x | x | Tested by `scripts/x.sh` on scenario:no-such-scenario | x |\n<!-- claim-index:end -->"))
PY
reject missing "lacks a does_not_prove statement"
reject unknown "cites unknown claim SC-NOT-A-CLAIM"
reject tested "cites unknown scenario no-such-scenario"
echo "scenario-claims check rejects 3 malformed inputs"
