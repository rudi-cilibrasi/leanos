#!/usr/bin/env bash
# Controlled runner negatives for the direct-port PIC-mask probe (#130).  The
# fake QEMU emits the exact PIC-containment transcript; each mutation must be
# rejected with the precise failure_class.  The two independent-oracle cases
# (pic-write-executed and forged transcripts) fail regardless of the serial
# claim, because either the guest exit status or the mandatory PIC mask
# read-back canary catches the tampering.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$root"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT; touch "$tmp/image.iso"
./scripts/generate-oracle.sh "$tmp/oracle" >/dev/null
invoke() {
  LEANOS_BOOT_SCENARIO=direct-port-pic \
  LEANOS_ORACLE_CORPUS="$tmp/oracle/corpus.tsv" \
  LEANOS_QEMU="$root/tests/qemu-direct-port-pic-fixture.sh" \
  LEANOS_QEMU_FIXTURE_MODE="$1" \
  LEANOS_QEMU_TIMEOUT_SECONDS=1 LEANOS_SERIAL_LOG="$tmp/$1.serial" \
  ./scripts/run-image.sh "$tmp/image.iso"
}
invoke success >/dev/null 2>&1
for spec in \
  'pic-write-executed guest-error' \
  'pic-canary-mutated serial-protocol' \
  'pic-canary-missing serial-protocol' \
  'forged-denial serial-protocol' \
  'forged-pass serial-protocol' \
  'attacker-selected-b serial-protocol' \
  'stale-cr3 serial-protocol' \
  'reordered serial-protocol' \
  'guest-error guest-error' \
  'reset qemu-error' \
  'triple-fault qemu-error' \
  'hang timeout'; do
  read -r mode class <<< "$spec"
  set +e; invoke "$mode" >"$tmp/$mode.output" 2>&1; status=$?; set -e
  [[ $status -ne 0 ]] && grep -q "failure_class=$class" "$tmp/$mode.output" || {
    echo "error: direct-port-pic fixture '$mode' expected failure_class=$class" >&2
    cat "$tmp/$mode.output" >&2; exit 1;
  }
done
echo "Direct-port PIC-mask probe runner success and negative fixture checks passed"
