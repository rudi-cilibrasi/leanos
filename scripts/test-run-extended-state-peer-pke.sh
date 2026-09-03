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
  local accelerator="$1" mode="$2"
  LEANOS_QEMU="$root/tests/qemu-extended-state-peer-control-fixture.sh" \
    LEANOS_QEMU_ACCELERATOR="$accelerator" \
    LEANOS_QEMU_PEER_CONTROL_FIXTURE_MODE="$mode" \
    LEANOS_QEMU_TIMEOUT_SECONDS=5 \
    LEANOS_SERIAL_LOG="$tmp/${accelerator}-${mode}.serial" \
    ./scripts/run-extended-state-peer-pke.sh "$tmp/image.iso"
}

invoke tcg pke >/dev/null
invoke kvm pke >/dev/null
invoke kvm osxsave >/dev/null

for spec in \
  'tcg osxsave pinned TCG' \
  'tcg missing one exact live-control witness' \
  'tcg duplicate one exact live-control witness' \
  'kvm wrong unreviewed control' \
  'tcg peer-entry entered CPL3'; do
  read -r accelerator mode diagnostic <<< "$spec"
  set +e
  invoke "$accelerator" "$mode" >"$tmp/${accelerator}-${mode}.output" 2>&1
  status=$?
  set -e
  if [[ $status -eq 0 ]] ||
     ! grep -Fq "$diagnostic" "$tmp/${accelerator}-${mode}.output"; then
    cat "$tmp/${accelerator}-${mode}.output" >&2
    exit 1
  fi
done

echo "Peer-return adaptive forbidden-control runner checks passed"
