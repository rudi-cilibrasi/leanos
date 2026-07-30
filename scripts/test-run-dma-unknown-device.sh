#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
touch "$tmp/image.iso"

invoke() {
  LEANOS_QEMU="$repo_root/tests/qemu-dma-unknown-device-fixture.sh" \
    LEANOS_QEMU_FIXTURE_MODE="$1" \
    LEANOS_QEMU_TIMEOUT_SECONDS=1 \
    LEANOS_SERIAL_LOG="$tmp/$1.serial" \
    ./scripts/run-dma-unknown-device.sh "$tmp/image.iso"
}

invoke success >/dev/null 2>&1
for spec in \
  'missing controlled-negative' \
  'duplicate controlled-negative' \
  'wrong-reason controlled-negative' \
  'reached-cpl3 controlled-negative' \
  'forged-pass controlled-negative' \
  'unrelated-guest-error guest-error' \
  'reset qemu-error' \
  'hang timeout'
do
  read -r mode failure_class <<<"$spec"
  set +e
  invoke "$mode" >"$tmp/$mode.output" 2>&1
  status=$?
  set -e
  if [[ $status -eq 0 ]] ||
      ! grep -q "failure_class=$failure_class" "$tmp/$mode.output"; then
    cat "$tmp/$mode.output" >&2
    exit 1
  fi
done

echo "DMA unknown-device runner success and controlled-negative checks passed"
