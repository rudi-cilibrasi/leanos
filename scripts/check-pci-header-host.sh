#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
lake build LeanOS.PCIHeaderObservation
./scripts/check-pci-header-scalar.sh
python3 scripts/test-pci-header-capture.py
python3 scripts/test-pci-header-abi.py
export LEANOS_HOSTED_BOUNDARY_ID=pci-header
./scripts/check-boot-handoff-host.sh "${1:-ordinary}"
