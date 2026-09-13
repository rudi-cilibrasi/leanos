#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

log="$(mktemp)"
fixture_build="$(mktemp -d "$repo_root/build/image-failure-fixture.XXXXXX")"
trap 'rm -f "$log"; rm -rf "$fixture_build"' EXIT
set +e
LEANOS_IMAGE_BUILD_DIR="$fixture_build" \
  LEANOS_CC="$repo_root/tests/failing-cc-fixture.sh" \
  ./scripts/build-image.sh >"$log" 2>&1
status=$?
set -e

if [[ $status -eq 0 ]] || ! grep -q 'controlled compiler failure fixture' "$log"; then
  echo "error: controlled image-build failure did not propagate" >&2
  cat "$log" >&2
  exit 1
fi

echo "Image-build failure regression check passed"
