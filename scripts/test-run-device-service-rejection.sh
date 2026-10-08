#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
./scripts/generate-oracle.sh "$tmp/oracle" > /dev/null
export LEANOS_SERIAL_PROTOCOL="$tmp/oracle/serial-protocol.sh"
export LEANOS_SERIAL_PROTOCOL_TSV="$tmp/oracle/serial-protocol.tsv"
touch "$tmp/image.iso"

invoke() {
  local mode="$1"
  LEANOS_QEMU="$root/tests/qemu-device-service-rejection-fixture.sh" \
    LEANOS_QEMU_DEVICE_SERVICE_FIXTURE_MODE="$mode" \
    LEANOS_DEVICE_SERVICE_REJECTION_REASON=dma-live-assignment-command \
    LEANOS_QEMU_TIMEOUT_SECONDS=2 \
    LEANOS_SERIAL_LOG="$tmp/${mode}.serial" \
    ./scripts/run-device-service-rejection.sh "$tmp/image.iso"
}

invoke rejected >/dev/null

for spec in \
  'pre-assignment failed before its assigned tables were live' \
  'wrong-reason lacked its exact rejection' \
  'passed exited 33 instead of typed guest failure 35' \
  'hang failure_class=timeout'; do
  read -r mode diagnostic <<< "$spec"
  set +e
  invoke "$mode" >"$tmp/${mode}.output" 2>&1
  status=$?
  set -e
  if [[ $status -eq 0 ]] || ! grep -Fq "$diagnostic" "$tmp/${mode}.output"; then
    cat "$tmp/${mode}.output" >&2
    exit 1
  fi
done

echo "Device-service post-assignment rejection runner checks passed"
