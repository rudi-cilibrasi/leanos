#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
python3 scripts/test-j1900-cpu-profile.py
export LEANOS_HOSTED_BOUNDARY_ID=j1900-cpu
exec ./scripts/check-boot-handoff-host.sh "${1:-ordinary}"
