#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
index="${1:-$root/docs/security-claims.md}"
contract="$root/LeanOS/SecurityClaims.lean"

fail() { echo "security-claim index error: $*" >&2; exit 1; }
[[ -f "$index" ]] || fail "missing index: $index"

rows="$(sed -n '/claim-index:start/,/claim-index:end/p' "$index" | grep '^| SC-' || true)"
[[ -n "$rows" ]] || fail "no claim entries"

ids="$(printf '%s\n' "$rows" | awk -F'|' '{gsub(/^ +| +$/, "", $2); print $2}')"
duplicate="$(printf '%s\n' "$ids" | sort | uniq -d | head -1)"
[[ -z "$duplicate" ]] || fail "duplicate ID: $duplicate"

while IFS='|' read -r _ id declaration source model assumptions evidence exclusions _; do
  id="${id# }"; id="${id% }"
  for field in id declaration source model assumptions evidence exclusions; do
    value="${!field}"; value="${value# }"; value="${value% }"
    [[ -n "$value" ]] || fail "$id has missing $field"
  done
  decl="$(printf '%s' "$declaration" | tr -d '` ' )"
  case "$evidence" in
    *Proved*) rg -q "^theorem ${decl}([[:space:]]|$)" "$contract" ||
      fail "$id names unknown contract theorem: $decl" ;;
    *Tested*) [[ "$evidence" == *scripts/* ]] || fail "$id Tested evidence lacks repository script" ;;
    *) fail "$id has unknown evidence classification: $evidence" ;;
  esac
done <<< "$rows"

if [[ "${LEANOS_CLAIM_INDEX_SELF_TEST:-1}" == 1 ]]; then
  fixtures="$root/tests/negative/security-claims"
  while IFS='|' read -r fixture expected; do
    log="$(mktemp)"
    if LEANOS_CLAIM_INDEX_SELF_TEST=0 "$0" "$fixtures/$fixture" >"$log" 2>&1; then
      rm -f "$log"
      fail "negative fixture unexpectedly passed: $fixture"
    fi
    if ! grep -Fq "$expected" "$log"; then
      cat "$log" >&2
      rm -f "$log"
      fail "negative fixture lacked expected diagnostic: $fixture"
    fi
    rm -f "$log"
  done <<'EOF'
Duplicate.md|duplicate ID: SC-DUPLICATE
UnknownTheorem.md|names unknown contract theorem: theorem_that_does_not_exist
MissingEvidence.md|SC-MISSING-EVIDENCE has missing evidence
ScriptAsProof.md|names unknown contract theorem: scripts/check.sh
EOF
fi

echo "Security claim index consistency checks passed"
