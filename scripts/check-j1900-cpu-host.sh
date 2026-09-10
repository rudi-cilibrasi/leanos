#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
python3 scripts/test-j1900-cpu-profile.py
export LEANOS_HOSTED_BOUNDARY_ID=j1900-cpu
mode="${1:-ordinary}"
./scripts/check-boot-handoff-host.sh "$mode"
suffix=""
if [[ "$mode" == sanitized ]]; then
  suffix="-sanitized"
  source scripts/hosted-sanitizer-config.sh
  export ASAN_OPTIONS="$leanos_host_asan_options"
  export UBSAN_OPTIONS="$leanos_host_ubsan_options"
fi
python3 scripts/test-j1900-diagnostic.py --replay "build/j1900-cpu-host${suffix}/host"
