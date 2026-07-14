#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

lake build

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

echo "Lean build and negative proof regression check passed"
