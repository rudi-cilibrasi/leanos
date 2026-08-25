#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
first="$(mktemp)"
second="$(mktemp)"
trap 'rm -f "$first" "$second"' EXIT

./scripts/build-image.sh
./scripts/write-reproducibility-manifest.sh "$first"
./scripts/build-image.sh
./scripts/write-reproducibility-manifest.sh "$second"

if ! cmp -s "$first" "$second"; then
  echo "error: repeated build changed the reproducibility manifest" >&2
  diff -u "$first" "$second" >&2 || true
  exit 1
fi

echo "Repeated base/reason-sensitive fault images, including stale-translation artifacts, ELFs, maps, plans, policies, and revision are byte-identical"
