#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

lake build

./scripts/test-run-image.sh

lake env lean -DwarningAsError=true -R experiments/freestanding-boundary \
  experiments/freestanding-boundary/Boundary.lean
lake env lean -DwarningAsError=true -R experiments/hosted-boundary \
  experiments/hosted-boundary/Hosted.lean

declaration_escape_pattern='^[[:space:]]*((private|protected|local|noncomputable)[[:space:]]+)*(axiom|constant|unsafe|extern)[[:space:]]'
ffi_attribute_pattern='^[[:space:]]*@\[[^]]*(extern|implemented_by)([[:space:],(]|\])'

if rg -n --glob '*.lean' \
  -e "$declaration_escape_pattern" \
  -e "$ffi_attribute_pattern" \
  LeanOS.lean LeanOS experiments; then
  echo "error: unapproved axiom or trusted-code declaration in Lean sources" >&2
  echo "document and explicitly allowlist required TCB declarations" >&2
  exit 1
fi

negative_log="$(mktemp)"
trap 'rm -f "$negative_log"' EXIT

if lake env lean tests/negative/InvalidBound.lean >"$negative_log" 2>&1; then
  echo "error: negative proof fixture unexpectedly type-checked" >&2
  exit 1
fi

if ! grep -q 'tests/negative/InvalidBound.lean.*error:' "$negative_log"; then
  echo "error: negative proof fixture failed without the expected Lean diagnostic" >&2
  cat "$negative_log" >&2
  exit 1
fi

if lake env lean -DwarningAsError=true tests/negative/Sorry.lean \
    >"$negative_log" 2>&1; then
  echo "error: a declaration using sorry unexpectedly type-checked" >&2
  exit 1
fi

if ! grep -q 'declaration uses `sorry`' "$negative_log"; then
  echo "error: sorry fixture failed without the expected Lean diagnostic" >&2
  cat "$negative_log" >&2
  exit 1
fi

echo "Lean build, proof-integrity, and negative regression checks passed"
