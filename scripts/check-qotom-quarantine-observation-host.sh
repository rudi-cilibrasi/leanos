#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
lake build LeanOS.QotomPCIQuarantineObservation
python3 scripts/test-qotom-quarantine-observation.py
python3 scripts/test-qotom-quarantine-abi.py
export LEANOS_HOSTED_BOUNDARY_ID=qotom-quarantine-observation
./scripts/check-boot-handoff-host.sh "${1:-ordinary}"
