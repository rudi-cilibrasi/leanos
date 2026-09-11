#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build LeanOS.QotomNativePCIInventory
./scripts/check-qotom-native-fields.sh
if [[ "${1:-ordinary}" == sanitized ]]; then
  ./scripts/check-qotom-native-snapshot-sanitizers.sh
fi
lake env python3 scripts/test-qotom-native-inventory.py
export LEANOS_HOSTED_BOUNDARY_ID=qotom-native-inventory
./scripts/check-boot-handoff-host.sh "${1:-ordinary}"
suffix=""
if [[ "${1:-ordinary}" == sanitized ]]; then
  suffix="-sanitized"
  source scripts/hosted-sanitizer-config.sh
  export ASAN_OPTIONS="$leanos_host_asan_options" UBSAN_OPTIONS="$leanos_host_ubsan_options"
fi
python3 scripts/test-qotom-native-inventory-cli.py --replay "build/qotom-native-inventory-host${suffix}/host"
