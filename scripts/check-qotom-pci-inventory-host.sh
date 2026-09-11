#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
lake build LeanOS.QotomPCIInventory
python3 scripts/test-qotom-pci-inventory.py
python3 scripts/test-qotom-pci-abi.py
export LEANOS_HOSTED_BOUNDARY_ID=qotom-pci-inventory
./scripts/check-boot-handoff-host.sh "${1:-ordinary}"
suffix=""
if [[ "${1:-ordinary}" == sanitized ]]; then
  suffix="-sanitized"
  source scripts/hosted-sanitizer-config.sh
  export ASAN_OPTIONS="$leanos_host_asan_options"
  export UBSAN_OPTIONS="$leanos_host_ubsan_options"
fi
python3 scripts/test-qotom-pci-replay-cli.py --replay "build/qotom-pci-inventory-host${suffix}/host"
