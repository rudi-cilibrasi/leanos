#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
lake build LeanOS.QotomPCIQuarantineTransition
python3 scripts/test-qotom-quarantine-transition.py
python3 scripts/test-qotom-quarantine-transition-abi.py
export LEANOS_HOSTED_BOUNDARY_ID=qotom-quarantine-transition
./scripts/check-boot-handoff-host.sh "${1:-ordinary}"
