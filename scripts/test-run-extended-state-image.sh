#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
touch "$tmp/image.iso"
./scripts/generate-oracle.sh "$tmp/oracle" >/dev/null

invoke() {
  LEANOS_BOOT_SCENARIO=extended-state \
    LEANOS_ORACLE_CORPUS="$tmp/oracle/corpus.tsv" \
    LEANOS_QEMU="$root/tests/qemu-extended-state-fixture.sh" \
    LEANOS_QEMU_FIXTURE_MODE="$1" \
    LEANOS_QEMU_TIMEOUT_SECONDS=1 \
    LEANOS_SERIAL_LOG="$tmp/$1.serial" \
    LEANOS_EXTENDED_STATE_SNAPSHOT="$tmp/$1.snapshot" \
    ./scripts/run-image.sh "$tmp/image.iso"
}

invoke success >/dev/null 2>&1
for spec in \
    'missing-cpuid serial-protocol' \
    'missing-control serial-protocol' \
    'missing-deny serial-protocol' \
    'missing-peer serial-protocol' \
    'reordered-records serial-protocol' \
    'forged-record serial-protocol' \
    'resumed-a serial-protocol' \
    'seeded-peer serial-protocol' \
    'kernel-contained serial-protocol' \
    'direct-handler serial-protocol' \
    'reset qemu-error' \
    'triple-fault qemu-error' \
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

echo "Extended-state QEMU runner success and negative fixture checks passed"
