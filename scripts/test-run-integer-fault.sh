#!/usr/bin/env bash
# Machine-level controlled negatives for the real CPL3 divide-error (#DE) and
# breakpoint (#BP) containment scenarios (#150).  The fake QEMU emits the exact
# integer-fault transcript for each scenario; every mutation must be rejected
# with the precise failure_class.  The transcript-forgery negatives keep a real
# independent oracle: a forged serial PASS with a non-33 guest debug-exit status
# is rejected regardless of the serial text.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$root"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT; touch "$tmp/image.iso"
./scripts/generate-oracle.sh "$tmp/oracle" >/dev/null
invoke() {
  local scenario="$1" mode="$2"
  LEANOS_BOOT_SCENARIO="$scenario" \
  LEANOS_ORACLE_CORPUS="$tmp/oracle/corpus.tsv" \
  LEANOS_QEMU="$root/tests/qemu-integer-fault-fixture.sh" \
  LEANOS_QEMU_FIXTURE_MODE="$mode" \
  LEANOS_QEMU_TIMEOUT_SECONDS=1 LEANOS_SERIAL_LOG="$tmp/$scenario-$mode.serial" \
  ./scripts/run-image.sh "$tmp/image.iso"
}
for scenario in divide-error breakpoint; do
  invoke "$scenario" success >/dev/null 2>&1
  for spec in \
    'wrong-vector serial-protocol' \
    'synthetic-error-word serial-protocol' \
    'wrong-saved-rip serial-protocol' \
    'direct-called-handler serial-protocol' \
    'page-fault-reason-substituted serial-protocol' \
    'rip-rewrite-recovery serial-protocol' \
    'partial-cleanup serial-protocol' \
    'attacker-selected-b serial-protocol' \
    'stale-cr3 serial-protocol' \
    'corrupt-peer-canary serial-protocol' \
    'nested-entry serial-protocol' \
    'forged-pass serial-protocol' \
    'reordered serial-protocol' \
    'forged-pass-guest-error guest-error' \
    'guest-error guest-error' \
    'reset qemu-error' \
    'triple-fault qemu-error' \
    'hang timeout'; do
    read -r mode class <<< "$spec"
    set +e; invoke "$scenario" "$mode" >"$tmp/$scenario-$mode.output" 2>&1; status=$?; set -e
    [[ $status -ne 0 ]] && grep -q "failure_class=$class" "$tmp/$scenario-$mode.output" || {
      echo "error: integer-fault fixture '$scenario/$mode' expected failure_class=$class" >&2
      cat "$tmp/$scenario-$mode.output" >&2; exit 1;
    }
  done
done
echo "Integer-fault (#DE/#BP) runner success and negative fixture checks passed"
