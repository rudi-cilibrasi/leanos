#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

scripts=(
  scripts/check-boundary-experiments.sh
  scripts/check-boot-handoff-stream.sh
  scripts/check-boot-memory-full-projection.sh
)

for script in "${scripts[@]}"; do
  log="$tmp/${script##*/}.log"
  set +e
  LEANOS_CC="$repo_root/tests/failing-cc-fixture.sh" \
    "$script" >"$log" 2>&1
  status=$?
  set -e
  if [[ $status -ne 86 ]] || \
      ! grep -Fq 'controlled compiler failure fixture' "$log"; then
    echo "error: $script did not propagate the selected compiler failure" >&2
    cat "$log" >&2
    exit 1
  fi
done

echo "Selected-compiler propagation fixtures passed"
