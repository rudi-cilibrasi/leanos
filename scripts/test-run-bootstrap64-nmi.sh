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
  LEANOS_QEMU="$root/tests/qemu-bootstrap64-nmi-fixture.py" \
    LEANOS_QEMU_FIXTURE_MODE="$1" LEANOS_QEMU_TIMEOUT_SECONDS=5 \
    LEANOS_SERIAL_LOG="$tmp/$1.serial" \
    ./scripts/run-bootstrap64-nmi.sh "$tmp/image.iso"
}

invoke success >/dev/null 2>&1
invoke disconnect-after-inject >/dev/null 2>&1
for spec in \
  'missing-ready early64-ready' \
  'wrong-record terminal-record' \
  'runtime-delivery terminal-record' \
  'reordered terminal-record' \
  'reject guest-evidence' \
  'reset qemu-error' \
  'hang timeout'; do
  read -r mode class <<< "$spec"
  set +e
  invoke "$mode" >"$tmp/$mode.output" 2>&1
  status=$?
  set -e
  if [[ $status -eq 0 ]] || ! grep -q "failure_class=$class" "$tmp/$mode.output"; then
    cat "$tmp/$mode.output" >&2
    exit 1
  fi
done

echo "bootstrap64-nmi runner success and negative fixture checks passed"
