#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
evidence="${LEANOS_FRAME_BUDGET_NEGATIVE_EVIDENCE_DIR:-build/boot/frame-budget-negatives}"
# The fixture recursively builds the canonical serial trace before mutating it.
# Leave headroom for hosted-runner contention without weakening protocol checks.
fixture_timeout="${LEANOS_FRAME_BUDGET_FIXTURE_TIMEOUT_SECONDS:-5}"
mkdir -p "$evidence"
find "$evidence" -mindepth 1 -maxdepth 1 -type f -delete
manifest="$evidence/manifest.tsv"
printf 'mode\texit_status\tfailure_class\tserial_log\toutput_log\n' >"$manifest"
touch "$tmp/image.iso"
printf '%040d\n' 0 > "$tmp/SOURCE_REVISION"
./scripts/generate-oracle.sh "$tmp/oracle" >/dev/null
invoke() {
  LEANOS_BOOT_SCENARIO=frame-budget \
    LEANOS_ORACLE_CORPUS="$tmp/oracle/corpus.tsv" \
    LEANOS_QEMU="$root/tests/qemu-fixture.sh" \
    LEANOS_QEMU_FIXTURE_MODE="$1" \
    LEANOS_QEMU_TIMEOUT_SECONDS="$fixture_timeout" \
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
    frame-budget-register-leak \
    frame-budget-canary frame-budget-stale-authorized \
    frame-budget-static-buffer frame-budget-wrong-frame \
    frame-budget-non-ring3 \
    frame-budget-missing frame-budget-reordered frame-budget-forged; do
  set +e
  invoke "$mode" >"$tmp/$mode.output" 2>&1
  status=$?
  set -e
  serial="$evidence/$mode.serial.log"
  output="$evidence/$mode.output.log"
  cp "$tmp/$mode.output" "$output"
  if [[ ! -s "$tmp/$mode.serial" ]]; then
    echo "error: $mode controlled negative produced no serial evidence" >&2
    exit 1
  fi
  cp "$tmp/$mode.serial" "$serial"
  failure_class=unexpected
  grep -q 'failure_class=serial-protocol' "$output" &&
    failure_class=serial-protocol
  printf '%s\t%s\t%s\t%s\t%s\n' \
    "$mode" "$status" "$failure_class" \
    "$(basename "$serial")" "$(basename "$output")" \
    >>"$manifest"
  if [[ $status -eq 0 || "$failure_class" != serial-protocol ]]; then
    cat "$output" >&2
    exit 1
  fi
done
echo "Frame-budget QEMU runner success and controlled negative fixtures passed"
