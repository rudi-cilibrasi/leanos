#!/usr/bin/env bash
set -euo pipefail
serial_protocol="${LEANOS_SERIAL_PROTOCOL:-$(dirname "${LEANOS_ORACLE_CORPUS:-build/boot/corpus.tsv}")/serial-protocol.sh}"
# shellcheck source=/dev/null
source "$serial_protocol"

[[ "${1:-}" == --version ]] && { echo "QEMU extended-state fixture version 1"; exit 0; }

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
log=""
for arg in "$@"; do
  [[ "$arg" == file:* ]] && log="${arg#file:}"
done
[[ -n "$log" ]] || exit 2

mode="${LEANOS_QEMU_FIXTURE_MODE:-success}"
case "$mode" in
  hang) sleep 10 ;;
  reset) exit 0 ;;
  triple-fault) exit 1 ;;
esac

set +e
LEANOS_QEMU_FIXTURE_MODE=legacy-success "$repo_root/tests/qemu-fixture.sh" "$@"
status=$?
set -e
[[ $status -eq 33 ]] || exit "$status"
sed -i 's/projection=exact-rich/projection=scalar-checked/' "$log"
sed -i "/^$(leanos_serial_re 8 PAGING) fixture=extra-mapping /a ${LEANOS_SERIAL_8_PAGING} fixture=nmi-guard-mapping root=B level=pt page=6 expected=0 actual=9223372036854800387 result=REJECTED" "$log"
sed -i "/^$(leanos_serial_re 8 PAGING) fixture=wrong-cr3 /a\\
${LEANOS_SERIAL_19_TLB} path=invlpg address-space=2 page=7 pte=cleared order=store,invlpg,publish before=309063438 after=308959202 result=PASS\\
${LEANOS_SERIAL_19_TLB} path=cr3 address-space=2 page=7 pte=cleared order=store,cr3,publish before=309063438 after=308959202 result=PASS\\
${LEANOS_SERIAL_19_TLB} authority=generated-composite effect=page address-space=2 page=7 window=restored result=PASS\\
${LEANOS_SERIAL_19_TLB} mutable-leaf=checked address-space=2 page=7 states=boot,before,unmapped,after immutable-leaves=exact result=PASS" "$log"
sed -i "/^$(leanos_serial_re 8 PAGING) fixture=omitted-mapping /a\\
${LEANOS_SERIAL_8_PAGING} fixture=mmio-wrong-frame root=B level=pt page=342 expected=9223372041130409987 actual=9223372036856176643 result=REJECTED\\
${LEANOS_SERIAL_8_PAGING} fixture=mmio-flip-user root=B level=pt page=342 expected=9223372041130409987 actual=9223372041130409991 result=REJECTED" "$log"
sed -i "/^$(leanos_serial_re 19 TLB) mutable-leaf=checked /a\\
${LEANOS_SERIAL_21_VTD} unit=0 mmio=4275634176 version=16 cap=59110346977575430 ecap=3842 gsts=0 fsts=0 rtaddr=0 stage=pre-activation result=PASS\\
${LEANOS_SERIAL_21_VTD_PLAN} root-frame=400 context-frame=401 root-words=512 context-words=512 present-root-entries=1 present-context-entries=0 translation=disabled deny-all=1 result=PASS\\
${LEANOS_SERIAL_21_VTD_TABLES} root-frame=400 context-frame=401 scrub=verified construct=verified root-words=512 context-words=512 result=PASS\\
${LEANOS_SERIAL_21_VTD_ACTIVATE} order=validate,scrub,construct,publish,invalidate-context,invalidate-iotlb,enable,verify journal=2271560481 gsts=3221225472 fsts=0 rtaddr=1638400 generated-result=0 stage=pre-cpl3 result=PASS" "$log"
sed -i 's/readbacks=5 /readbacks=5 initial-bus-masters=1 initial-bus-master-mask=16 /' "$log"
sed -i 's/readback=exact stage=/readback=exact generated-result=0 stage=/' "$log"
sed -i "/^$(leanos_serial_re 15 DMA) snapshot=/i\\
${LEANOS_SERIAL_15_DMA_FUNCTION} manifest=1 topology=0001000800020002 bdf=0:0.0 present=1 vendor=32902 device=10688 class=393216 command-before=0 command-after=0 assigned=0 bridge=0 multifunction=0 policy=accepted\\
${LEANOS_SERIAL_15_DMA_FUNCTION} manifest=1 topology=0001000800020002 bdf=0:1.0 present=1 vendor=4660 device=4369 class=196608 command-before=3 command-after=0 assigned=0 bridge=0 multifunction=0 policy=accepted\\
${LEANOS_SERIAL_15_DMA_FUNCTION} manifest=1 topology=0001000800020002 bdf=0:3.0 present=0 vendor=0 device=0 class=0 command-before=0 command-after=0 assigned=0 bridge=0 multifunction=0 policy=accepted\\
${LEANOS_SERIAL_15_DMA_FUNCTION} manifest=1 topology=0001000800020002 bdf=0:31.0 present=1 vendor=32902 device=10520 class=393472 command-before=3 command-after=0 assigned=0 bridge=1 multifunction=1 policy=accepted\\
${LEANOS_SERIAL_15_DMA_FUNCTION} manifest=1 topology=0001000800020002 bdf=0:31.2 present=1 vendor=32902 device=10530 class=67073 command-before=7 command-after=0 assigned=0 bridge=0 multifunction=1 policy=accepted\\
${LEANOS_SERIAL_15_DMA_FUNCTION} manifest=1 topology=0001000800020002 bdf=0:31.3 present=1 vendor=32902 device=10544 class=787712 command-before=1 command-after=0 assigned=0 bridge=0 multifunction=1 policy=accepted" "$log"

sed -i \
  -e "s|${LEANOS_SERIAL_6_BOOT} target=x86_64-q35 subjects=2 schedule=one-shot-pit controls=wp,smep,smap|${LEANOS_SERIAL_13_BOOT} target=x86_64-q35 subjects=2 schedule=extended-state-denial controls=wp,smep,smap,em,mp,ts|" \
  -e "/^$(leanos_serial_re 6 CONTROL)/i ${LEANOS_SERIAL_17_ENTRY_MANIFEST} ordinary=8 extended=6,7 contained=0,3 auxiliary=1 terminal=2 extra=0 rsp0=entry-stack ist1=df-stack ist2=nmi-stack result=PASS\\
${LEANOS_SERIAL_16_DIRECT_PORT_CONTROL} tr=40 limit=103 iomap=104 bitmap=absent iopl=0 stage=pre-cpl3 result=PASS\\
${LEANOS_SERIAL_13_EXTENDED_STATE} cpuid.1.x87=1 cpuid.1.mmx=1 cpuid.1.sse=1 cpuid.1.sse2=1 cpuid.1.xsave=1 cpuid.1.osxsave=0 cpuid.1.avx=1 cpu=max result=PASS" \
  -e "/^$(leanos_serial_re 6 COPY)/d" \
  -e "/^$(leanos_serial_family_re 5) /d" \
  -e "/^$(leanos_serial_re 8 PAGING) root=B selected=1 result=PASS\$/d" \
  -e "/^$(leanos_serial_re 6 CLEANUP)/a ${LEANOS_SERIAL_13_EXTENDED_STATE} event=enter subject=1 address-space=1 instruction=x87 expected-vector=7\\
${LEANOS_SERIAL_13_EXTENDED_STATE} event=deny subject=1 vector=7 instruction=x87 bank-write=prevented cleanup=complete peer=2\\
${LEANOS_SERIAL_13_EXTENDED_STATE} event=peer subject=2 address-space=2 cpl=3 return=validated controls=denied gpr-canaries=preserved\\
${LEANOS_SERIAL_13_FINAL} status=PASS denied=1 resumed-a=0 peer-ran=1" \
  "$log"

case "$mode" in
  success) ;;
  missing-cpuid) sed -i '/EXTENDED-STATE cpuid/d' "$log" ;;
  missing-control) sed -i "/^$(leanos_serial_re 6 CONTROL)/d" "$log" ;;
  missing-deny) sed -i '/event=deny/d' "$log" ;;
  missing-peer) sed -i '/event=peer/d' "$log" ;;
  reordered-records)
    sed -i \
      -e "s/^$(leanos_serial_re 13 EXTENDED-STATE) event=enter /__EXTENDED_ENTER__ /" \
      -e "s/^$(leanos_serial_re 13 EXTENDED-STATE) event=deny /$(leanos_serial_re 13 EXTENDED-STATE) event=enter /" \
      -e "s/^__EXTENDED_ENTER__ /$(leanos_serial_re 13 EXTENDED-STATE) event=deny /" \
      "$log"
    ;;
  forged-record) sed -i 's/bank-write=prevented/bank-write=prevented forged=1/' "$log" ;;
  resumed-a) sed -i 's/resumed-a=0/resumed-a=1/' "$log" ;;
  seeded-peer) sed -i 's/bank-write=prevented/bank-write=seeded/' "$log" ;;
  kernel-contained) sed -i 's/event=enter subject=1/event=enter origin=kernel subject=1/' "$log" ;;
  direct-handler) sed -i 's/event=enter subject=1/event=enter entry=direct subject=1/' "$log" ;;
  *) exit 2 ;;
esac

exit 33
