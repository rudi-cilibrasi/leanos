#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
touch "$tmp/image.iso"
printf '%040d\n' 0 > "$tmp/SOURCE_REVISION"
./scripts/generate-oracle.sh "$tmp/oracle" >/dev/null
invoke() {
  LEANOS_BOOT_SCENARIO=frame-budget \
    LEANOS_ORACLE_CORPUS="$tmp/oracle/corpus.tsv" \
    LEANOS_QEMU="$root/tests/qemu-fixture.sh" \
    LEANOS_QEMU_FIXTURE_MODE="$1" \
    LEANOS_QEMU_TIMEOUT_SECONDS=1 \
    LEANOS_SERIAL_LOG="$tmp/$1.serial" \
    LEANOS_DMA_SNAPSHOT="$tmp/$1.dma.tsv" \
    LEANOS_SOURCE_REVISION_FILE="$tmp/SOURCE_REVISION" \
    ./scripts/run-image.sh "$tmp/image.iso"
}
invoke success >/dev/null 2>&1
for mode in \
    frame-budget-global-counter frame-budget-cross-charge \
    frame-budget-owner-forgery frame-budget-relabel-success \
    frame-budget-partial-publication frame-budget-double-credit \
    frame-budget-double-publication \
    frame-budget-canary frame-budget-stale-authorized \
    frame-budget-static-buffer frame-budget-wrong-frame \
    frame-budget-non-ring3 \
    frame-budget-missing frame-budget-reordered frame-budget-forged; do
  set +e
  invoke "$mode" >"$tmp/$mode.output" 2>&1
  status=$?
  set -e
  if [[ $status -eq 0 ]] || ! grep -q 'failure_class=serial-protocol' "$tmp/$mode.output"; then
    cat "$tmp/$mode.output" >&2
    exit 1
  fi
done
echo "Frame-budget QEMU runner success and controlled negative fixtures passed"
