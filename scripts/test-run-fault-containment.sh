#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$root"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT; touch "$tmp/image.iso"
./scripts/generate-oracle.sh "$tmp/oracle" >/dev/null
invoke() {
  LEANOS_BOOT_SCENARIO=fault-containment \
  LEANOS_ORACLE_CORPUS="$tmp/oracle/corpus.tsv" \
  LEANOS_QEMU="$root/tests/qemu-fixture.sh" LEANOS_QEMU_FIXTURE_MODE="$1" \
  LEANOS_QEMU_TIMEOUT_SECONDS=1 LEANOS_SERIAL_LOG="$tmp/$1.serial" \
  ./scripts/run-image.sh "$tmp/image.iso"
}
invoke success >/dev/null 2>&1
for spec in \
  'fault-direct-call serial-protocol' \
  'fault-old-recovery serial-protocol' \
  'fault-stale-cr3 serial-protocol' \
  'fault-cleanup-missing serial-protocol' \
  'fault-a-queued serial-protocol' \
  'fault-attacker-selection serial-protocol' \
  'fault-return-unvalidated serial-protocol' \
  'fault-peer-corrupt serial-protocol' \
  'fault-peer-cleaned serial-protocol' \
  'fault-forged-pass serial-protocol' \
  'fault-reordered serial-protocol' \
  'fault-kernel-relabeled serial-protocol' \
  'fault-global-fail guest-error' \
  'hang timeout' \
  'reset qemu-error' \
  'triple-fault qemu-error'; do
  read -r mode class <<< "$spec"
  set +e; invoke "$mode" >"$tmp/$mode.output" 2>&1; status=$?; set -e
  [[ $status -ne 0 ]] && grep -q "failure_class=$class" "$tmp/$mode.output" || {
    cat "$tmp/$mode.output" >&2; exit 1;
  }
done
echo "Fault-containment QEMU runner success and negative fixture checks passed"
