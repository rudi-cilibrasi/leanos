#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
fixture="$repo_root/tests/qemu-multivcpu-rejection-fixture.py"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
./scripts/generate-oracle.sh "$tmp/oracle" > /dev/null
export LEANOS_SERIAL_PROTOCOL="$tmp/oracle/serial-protocol.sh"
export LEANOS_SERIAL_PROTOCOL_TSV="$tmp/oracle/serial-protocol.tsv"
touch "$tmp/image.iso"

run() {
  local mode="$1"
  LEANOS_QEMU="$fixture" \
  LEANOS_QEMU_FIXTURE_MODE="$mode" \
  LEANOS_SERIAL_LOG="$tmp/$mode.serial.log" \
  LEANOS_QMP_LOG="$tmp/$mode.qmp.jsonl" \
  LEANOS_MULTIVCPU_INVENTORY="$tmp/$mode.qmp.tsv" \
    ./scripts/run-multivcpu-rejection.sh "$tmp/image.iso"
}

run success >/dev/null
grep -Fqx '# leanos-q35-multivcpu-inventory-v1' "$tmp/success.qmp.tsv"
for mode in missing authority-leak reset; do
  if run "$mode" >/dev/null 2>&1; then
    echo "error: multi-vCPU runner accepted controlled failure '$mode'" >&2
    exit 1
  fi
done

echo "Multi-vCPU rejection runner positive and controlled-negative checks passed"
