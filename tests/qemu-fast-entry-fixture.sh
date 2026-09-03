#!/usr/bin/env bash
set -euo pipefail
serial_protocol="${LEANOS_SERIAL_PROTOCOL:-$(dirname "${LEANOS_ORACLE_CORPUS:-build/boot/corpus.tsv}")/serial-protocol.sh}"
# shellcheck source=/dev/null
source "$serial_protocol"

[[ "${1:-}" == --version ]] && { echo "QEMU fast-entry fixture version 1"; exit 0; }

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
log=""
for arg in "$@"; do
  [[ "$arg" == file:* ]] && log="${arg#file:}"
done
[[ -n "$log" ]] || exit 2

mode="${LEANOS_QEMU_FIXTURE_MODE:-success}"
mechanism="${LEANOS_BOOT_SCENARIO#fast-entry-}"
[[ "$mechanism" == syscall || "$mechanism" == sysenter ]] || exit 2

case "$mode" in
  hang) sleep 10 ;;
  reset) exit 0 ;;
  triple-fault) exit 1 ;;
esac

set +e
LEANOS_QEMU_FIXTURE_MODE=success \
  "$repo_root/tests/qemu-extended-state-fixture.sh" "$@"
status=$?
set -e
[[ $status -eq 33 ]] || exit "$status"

sed -i \
  -e "s|${LEANOS_SERIAL_13_BOOT} target=x86_64-q35 subjects=2 schedule=extended-state-denial controls=wp,smep,smap,em,mp,ts|${LEANOS_SERIAL_14_BOOT} target=x86_64-q35 subjects=2 schedule=fast-entry-denial controls=wp,smep,smap,em,mp,ts,sce-off|" \
  -e "/^$(leanos_serial_re 13 EXTENDED-STATE) cpuid/i ${LEANOS_SERIAL_14_FAST_ENTRY} cpu.vendor=AuthenticAMD mode=long64 syscall=1 sysenter=1 efer.sce=0 star=0 lstar=0 cstar=0 sfmask=0 sysenter.cs=0 sysenter.esp=0 sysenter.eip=0 writes=complete readback=exact result=PASS" \
  -e "s|${LEANOS_SERIAL_13_EXTENDED_STATE} event=enter subject=1 address-space=1 instruction=x87 expected-vector=7|${LEANOS_SERIAL_14_FAST_ENTRY} event=enter subject=1 address-space=1 instruction=${mechanism} expected-vector=6|" \
  -e "s|${LEANOS_SERIAL_13_EXTENDED_STATE} event=deny subject=1 vector=7 instruction=x87 bank-write=prevented cleanup=complete peer=2|${LEANOS_SERIAL_14_FAST_ENTRY} event=deny subject=1 vector=6 instruction=${mechanism} alternate-target=unreached cleanup=complete peer=2|" \
  -e "s|${LEANOS_SERIAL_13_EXTENDED_STATE} event=peer subject=2 address-space=2 cpl=3 return=validated controls=denied gpr-canaries=preserved|${LEANOS_SERIAL_14_FAST_ENTRY} event=peer subject=2 address-space=2 cpl=3 return=validated controls=denied gpr-canaries=preserved|" \
  -e "s|${LEANOS_SERIAL_13_FINAL} status=PASS denied=1 resumed-a=0 peer-ran=1|${LEANOS_SERIAL_14_FINAL} status=PASS denied=1 resumed-a=0 peer-ran=1 alternate-target=0|" \
  "$log"

case "$mode" in
  success) ;;
  missing-manifest) sed -i "/^$(leanos_serial_re 17 ENTRY-MANIFEST)/d" "$log" ;;
  missing-control) sed -i "/^$(leanos_serial_re 14 FAST-ENTRY) cpu\\./d" "$log" ;;
  wrong-vector) sed -i 's/event=deny subject=1 vector=6/event=deny subject=1 vector=13/' "$log" ;;
  wrong-error-shape) sed -i 's/vector=6 instruction=/vector=6 error=1 instruction=/' "$log" ;;
  stale-binding) sed -i 's/event=enter subject=1 address-space=1/event=enter subject=1 address-space=2/' "$log" ;;
  unexpected-target) sed -i 's/alternate-target=unreached/alternate-target=reached/' "$log" ;;
  policy-relaxation) sed -i 's/return=validated controls=denied/return=validated controls=enabled/' "$log" ;;
  attacker-selected-survivor) sed -i 's/event=peer subject=2 address-space=2/event=peer subject=1 address-space=1/' "$log" ;;
  kernel-contained) sed -i 's/event=enter subject=1/event=enter origin=kernel subject=1/' "$log" ;;
  direct-handler) sed -i 's/event=enter subject=1/event=enter entry=direct subject=1/' "$log" ;;
  partial) sed -i "/^$(leanos_serial_re 14 FINAL)/d" "$log" ;;
  reordered)
    sed -i \
      -e "s/^$(leanos_serial_re 14 FAST-ENTRY) event=enter /__FAST_ENTRY_ENTER__ /" \
      -e "s/^$(leanos_serial_re 14 FAST-ENTRY) event=deny /$(leanos_serial_re 14 FAST-ENTRY) event=enter /" \
      -e "s/^__FAST_ENTRY_ENTER__ /$(leanos_serial_re 14 FAST-ENTRY) event=deny /" \
      "$log"
    ;;
  *) exit 2 ;;
esac

exit 33
