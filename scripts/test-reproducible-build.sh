#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
first="$(mktemp)"
second="$(mktemp)"
trap 'rm -f "$first" "$second"' EXIT

run_timed_build() {
  local name="$1"
  if [[ -n "${LEANOS_REPRO_BUILD_TIMING_DIR:-}" ]]; then
    mkdir -p "$LEANOS_REPRO_BUILD_TIMING_DIR"
    LEANOS_BUILD_TIMING_FILE="$LEANOS_REPRO_BUILD_TIMING_DIR/${name}-build-phases.tsv" \
      ./scripts/build-image.sh
  else
    ./scripts/build-image.sh
  fi
}

run_timed_build reproducibility-first
./scripts/write-reproducibility-manifest.sh "$first"
run_timed_build reproducibility-second
./scripts/write-reproducibility-manifest.sh "$second"

if ! cmp -s "$first" "$second"; then
  echo "error: repeated build changed the reproducibility manifest" >&2
  diff -u "$first" "$second" >&2 || true
  exit 1
fi

echo "Repeated base/reason-sensitive fault images, including stale-translation artifacts, ELFs, maps, plans, policies, and revision are byte-identical"
