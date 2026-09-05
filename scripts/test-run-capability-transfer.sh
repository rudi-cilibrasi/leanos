#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
evidence="${LEANOS_CAPABILITY_TRANSFER_NEGATIVE_EVIDENCE_DIR:-build/boot/capability-transfer-negatives}"
fixture_timeout="${LEANOS_CAPABILITY_TRANSFER_FIXTURE_TIMEOUT_SECONDS:-5}"
mkdir -p "$evidence"
find "$evidence" -mindepth 1 -maxdepth 1 -type f -delete
manifest="$evidence/manifest.tsv"
printf 'mode\texit_status\tfailure_class\tserial_log\toutput_log\n' >"$manifest"
touch "$tmp/image.iso"
printf '%040d\n' 0 > "$tmp/SOURCE_REVISION"
./scripts/generate-oracle.sh "$tmp/oracle" >/dev/null

invoke() {
  LEANOS_BOOT_SCENARIO=capability-transfer \
    LEANOS_ORACLE_CORPUS="$tmp/oracle/corpus.tsv" \
    LEANOS_QEMU="$root/tests/qemu-capability-transfer-fixture.sh" \
    LEANOS_CAPABILITY_TRANSFER_FIXTURE_MODE="$1" \
    LEANOS_QEMU_TIMEOUT_SECONDS="$fixture_timeout" \
    LEANOS_SERIAL_LOG="$tmp/$1.serial" \
    LEANOS_DMA_SNAPSHOT="$tmp/$1.dma.tsv" \
    LEANOS_VTD_SNAPSHOT="$tmp/$1.vtd.tsv" \
    LEANOS_SOURCE_REVISION_FILE="$tmp/SOURCE_REVISION" \
    ./scripts/run-image.sh "$tmp/image.iso"
}

invoke success >/dev/null 2>&1
for spec in \
  'payload-authority serial-protocol' \
  'rights-widened serial-protocol' \
  'installed-early serial-protocol' \
  'truncated-handle serial-protocol' \
  'replaced-return serial-protocol' \
  'stale-a-context serial-protocol' \
  'old-adapter serial-protocol' \
  'state-splice serial-protocol' \
  'missing serial-protocol' \
  'reordered serial-protocol' \
  'forged-final serial-protocol' \
  'guest-error guest-error' \
  'hang timeout'; do
  read -r mode failure_class <<< "$spec"
  set +e
  invoke "$mode" > "$tmp/$mode.output" 2>&1
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
  observed_failure_class=unexpected
  grep -q "failure_class=${failure_class}" "$output" &&
    observed_failure_class="$failure_class"
  printf '%s\t%s\t%s\t%s\t%s\n' \
    "$mode" "$status" "$observed_failure_class" \
    "$(basename "$serial")" "$(basename "$output")" \
    >>"$manifest"
  if [[ $status -eq 0 || "$observed_failure_class" != "$failure_class" ]]; then
    cat "$output" >&2
    exit 1
  fi
done
echo "Capability-transfer runner success and 13 controlled negatives passed"
