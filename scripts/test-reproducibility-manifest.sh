#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
fixture="$(mktemp -d)"
trap 'rm -rf "$fixture"' EXIT
mapfile -t artifacts < <("$repo_root/scripts/write-reproducibility-manifest.sh" --list)

for artifact in "${artifacts[@]}"; do
  printf 'stable:%s\n' "$artifact" >"$fixture/$artifact"
done
"$repo_root/scripts/write-reproducibility-manifest.sh" "$fixture/first" "$fixture"
"$repo_root/scripts/write-reproducibility-manifest.sh" "$fixture/second" "$fixture"
cmp "$fixture/first" "$fixture/second"

printf 'nondeterministic\n' >>"$fixture/${artifacts[0]}"
"$repo_root/scripts/write-reproducibility-manifest.sh" "$fixture/changed" "$fixture"
! cmp -s "$fixture/first" "$fixture/changed"

rm "$fixture/${artifacts[1]}"
if "$repo_root/scripts/write-reproducibility-manifest.sh" \
  "$fixture/missing" "$fixture" 2>/dev/null; then
  echo "error: missing artifact was accepted" >&2
  exit 1
fi
echo "Reproducibility manifest is stable, complete, and change-sensitive"
