#!/usr/bin/env bash
# Fake QEMU for the real CPL3 divide-error (#DE, vector 0) and breakpoint
# (#BP, vector 3) containment scenarios (#150).  It reuses the shared
# blocking-ipc success transcript (corpus, allocation, paging fixtures, control
# and manifest snapshots) from qemu-fixture.sh, rewrites it into the selected
# integer-fault containment transcript, then applies one controlled mutation so
# the runner's machine-level negatives can be exercised without a real boot.
#
# LEANOS_BOOT_SCENARIO selects divide-error or breakpoint; the two scenarios
# share one implementation and evidence vocabulary, exactly as the booted image
# does.  The transcript-forgery negatives keep a real independent oracle: a
# forged serial PASS is still rejected when the guest debug-exit status is not
# the accepted 33.
set -euo pipefail
serial_protocol="${LEANOS_SERIAL_PROTOCOL:-$(dirname "${LEANOS_ORACLE_CORPUS:-build/boot/corpus.tsv}")/serial-protocol.sh}"
# shellcheck source=/dev/null
source "$serial_protocol"
[[ "${1:-}" == --version ]] && { echo "QEMU integer-fault fixture version 1"; exit 0; }
log=""; for arg in "$@"; do [[ "$arg" == file:* ]] && log="${arg#file:}"; done
[[ -n "$log" ]] || exit 2
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
mode="${LEANOS_QEMU_FIXTURE_MODE:-success}"
scenario="${LEANOS_BOOT_SCENARIO:-divide-error}"
case "$scenario" in
  divide-error) upper=DIVIDE-ERROR; vector=0; rip=faulting-instruction; kind=divide-error ;;
  breakpoint)   upper=BREAKPOINT;   vector=3; rip=post-instruction;     kind=breakpoint ;;
  *) echo "integer-fault fixture: unknown scenario $scenario" >&2; exit 2 ;;
esac

set +e
LEANOS_BOOT_SCENARIO=blocking-ipc LEANOS_QEMU_FIXTURE_MODE=success \
  "$here/qemu-fixture.sh" "$@"
set -e
sed -i \
  -e "s|${LEANOS_SERIAL_10_BOOT} target=x86_64-q35 subjects=2 schedule=blocking-ipc controls=wp,smep,smap|${LEANOS_SERIAL_18_BOOT} target=x86_64-q35 subjects=2 schedule=integer-fault-containment probe=${kind} contract=v1 controls=wp,smep,smap|" \
  -e "/^$(leanos_serial_family_re 9) /d" -e "/^$(leanos_serial_family_re 10) /d" \
  -e "/^$(leanos_serial_re 6 COPY) /d" -e "/^$(leanos_serial_re 11 USER-FAULT) /d" \
  -e "/^$(leanos_serial_re 11 ENTRY-HIGH-WATER) /d" \
  -e "/^$(leanos_serial_re 8 PAGING) root=B selected=1 result=PASS\$/d" \
  -e "/^$(leanos_serial_re 8 PAGING) root=A selected=1 resumed=1 result=PASS\$/d" "$log"
cat >> "$log" <<EOF
${LEANOS_SERIAL_8_PAGING} root=A selected=1 resumed=1 result=PASS
${LEANOS_SERIAL_18_ENTER} subject=1 address-space=1 cpl=3 resources=owned
$(leanos_serial 18 "${upper}-ENTRY") vector=${vector} error=none origin=cpl3 hardware=1 direct-call=0 saved-rip=${rip} subject=1 address-space=1 result=PASS
$(leanos_serial 18 "${upper}-TERMINATE") subject=1 live=0 runnable=0 current=0 queued=0 resumable=0 resources=cap,memory,mapping,endpoint result=PASS
$(leanos_serial 18 "${upper}-DISPATCH") subject=2 address-space=2 source=lean-scheduler context=owned reason=${kind} result=PASS
${LEANOS_SERIAL_8_PAGING} root=B selected=1 result=PASS
$(leanos_serial 18 "${upper}-PEER") subject=2 address-space=2 stack=owned return=validated canaries=preserved resources=unchanged result=PASS
${LEANOS_SERIAL_18_FINAL} status=PASS faulting=terminated survivor=2 vector=${vector} reason=${kind} kernel-origin=fail-stop
EOF

case "$mode" in
  success) exit 33 ;;
  # Wrong delivered vector: the exception did not arrive as vector 0/3.
  wrong-vector) sed -i "s/${upper}-ENTRY vector=${vector}/${upper}-ENTRY vector=13/" "$log"; exit 33 ;;
  # A synthetic hardware error word attached to a no-error-code vector.
  synthetic-error-word) sed -i "s/${upper}-ENTRY vector=${vector} error=none/${upper}-ENTRY vector=${vector} error=5/" "$log"; exit 33 ;;
  # Wrong saved-RIP class (faulting vs post-instruction boundary swapped).
  wrong-saved-rip)
    other=post-instruction; [[ "$rip" == post-instruction ]] && other=faulting-instruction
    sed -i "s/saved-rip=${rip}/saved-rip=${other}/" "$log"; exit 33 ;;
  # The hardware frame was synthesized by a direct handler call.
  direct-called-handler) sed -i 's/direct-call=0/direct-call=1/' "$log"; exit 33 ;;
  # A page-fault reason substituted for the real #DE/#BP reason.
  page-fault-reason-substituted) sed -i "s/reason=${kind}/reason=page-fault/g" "$log"; exit 33 ;;
  # RIP-rewrite recovery: A resumed instead of being retired.
  rip-rewrite-recovery) sed -i "/^$(leanos_serial_re 18 "${upper}-TERMINATE") /d; /^$(leanos_serial_re 18 "${upper}-DISPATCH") /d" "$log"; exit 33 ;;
  # Partial cleanup: a resumable context survived termination.
  partial-cleanup) sed -i 's/resumable=0/resumable=1/' "$log"; exit 33 ;;
  # An attacker-selected survivor rather than the scheduler-selected peer.
  attacker-selected-b) sed -i "s/${upper}-DISPATCH subject=2/${upper}-DISPATCH subject=3/" "$log"; exit 33 ;;
  # Survivor dispatched under a stale address space.
  stale-cr3) sed -i "s/${upper}-DISPATCH subject=2 address-space=2/${upper}-DISPATCH subject=2 address-space=1/" "$log"; exit 33 ;;
  # Corrupted peer register/stack canary.
  corrupt-peer-canary) sed -i 's/canaries=preserved/canaries=corrupt/' "$log"; exit 33 ;;
  # Nested entry: a second normalized entry before the first completed.
  nested-entry) sed -i "/^$(leanos_serial_re 18 "${upper}-ENTRY") /p" "$log"; exit 33 ;;
  # C-only success without the real hardware entry and termination.
  forged-pass) sed -i "/^$(leanos_serial_re 18 "${upper}-ENTRY") /d; /^$(leanos_serial_re 18 "${upper}-TERMINATE") /d" "$log"; exit 33 ;;
  # Reordered termination and dispatch records.
  reordered)
    sed -i -e "s/^$(leanos_serial_re 18 "${upper}-TERMINATE") /$(leanos_serial_family_re 18) __SWAP__ /" \
      -e "s/^$(leanos_serial_re 18 "${upper}-DISPATCH") /$(leanos_serial_re 18 "${upper}-TERMINATE") /" \
      -e "s/^$(leanos_serial_family_re 18) __SWAP__ /$(leanos_serial_re 18 "${upper}-DISPATCH") /" "$log"
    exit 33 ;;
  # Forged serial PASS but the guest actually failed: the independent
  # debug-exit status is the accepted oracle and rejects it regardless.
  forged-pass-guest-error) exit 35 ;;
  guest-error)
    sed -i "s/^$(leanos_serial_re 18 FINAL) .*/$(leanos_serial_re 18 FINAL) status=FAIL reason=kernel-fault/" "$log"
    exit 35 ;;
  reset) exit 0 ;;
  triple-fault) exit 43 ;;
  hang) sleep 10 ;;
  *) exit 2 ;;
esac
