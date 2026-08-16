#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

if [[ "${LEANOS_REQUIRE_CURRENT_INVARIANTS:-1}" != "1" ]]; then
  echo "check-invariants: skipped (LEANOS_REQUIRE_CURRENT_INVARIANTS=${LEANOS_REQUIRE_CURRENT_INVARIANTS})"
  exit 0
fi

python3 "$root/scripts/generate-invariants.py" verify
