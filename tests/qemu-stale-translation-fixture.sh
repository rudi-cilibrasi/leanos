#!/usr/bin/env bash
# Fake QEMU for the dedicated stale-translation denial scenario (#126).
# It preserves the shared boot/oracle/control evidence, emits the exact CPL3
# prefill -> accepted unmap -> architectural page-fault protocol, and applies
# one controlled mutation for each runner-negative requirement.
set -euo pipefail
serial_protocol="${LEANOS_SERIAL_PROTOCOL:-$(dirname "${LEANOS_ORACLE_CORPUS:-build/boot/corpus.tsv}")/serial-protocol.sh}"
# shellcheck source=/dev/null
source "$serial_protocol"
[[ "${1:-}" == --version ]] && {
  echo "QEMU stale-translation fixture version 1"
  exit 0
}
log=""
for arg in "$@"; do
  [[ "$arg" == file:* ]] && log="${arg#file:}"
done
[[ -n "$log" ]] || exit 2
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
mode="${LEANOS_QEMU_FIXTURE_MODE:-success}"
elf="${LEANOS_FAULT_CONTAINMENT_ELF:?missing stale-translation ELF}"

symbol_value() {
  local symbol="$1" address
  address="$(nm -n "$elf" | awk -v wanted="$symbol" '$3 == wanted { print $1 }')"
  [[ "$address" =~ ^[[:xdigit:]]+$ ]] || exit 2
  printf '%u' "$((16#$address))"
}

set +e
LEANOS_BOOT_SCENARIO=blocking-ipc LEANOS_QEMU_FIXTURE_MODE=success \
  "$here/qemu-fixture.sh" "$@"
set -e
sed -i \
  -e "s|${LEANOS_SERIAL_10_BOOT} target=x86_64-q35 subjects=2 schedule=blocking-ipc controls=wp,smep,smap|${LEANOS_SERIAL_19_BOOT} target=x86_64-q35 subjects=2 schedule=stale-translation-denial probe=cpl3-unmap-read contract=v1 controls=wp,smep,smap,pcid-off|" \
  -e "/^$(leanos_serial_family_re 9) /d" -e "/^$(leanos_serial_family_re 10) /d" \
  -e "/^$(leanos_serial_re 6 COPY) /d" -e "/^$(leanos_serial_re 11 USER-FAULT) /d" \
  -e "/^$(leanos_serial_re 11 ENTRY-HIGH-WATER) /d" \
  -e "/^$(leanos_serial_re 8 PAGING) root=B selected=1 result=PASS\$/d" \
  -e "/^$(leanos_serial_re 8 PAGING) root=A selected=1 resumed=1 result=PASS\$/d" "$log"
cat >>"$log" <<EOF
${LEANOS_SERIAL_8_PAGING} root=B selected=1 result=PASS
${LEANOS_SERIAL_19_ENTER} subject=2 address-space=2 cpl=3 mapping=page7-present-user canary=309063438
${LEANOS_SERIAL_19_TLB_CPL3} event=prefill subject=2 address-space=2 page=7 address=28672 access=read canary=309063438 leaf=present-user result=PASS
${LEANOS_SERIAL_19_TLB_CPL3} event=unmap subject=2 address-space=2 page=7 pte=absent effect=page invalidation=invlpg cr3-reload=0 order=store,invlpg,publish result=PASS
${LEANOS_SERIAL_19_TLB_CPL3} event=reuse frame=same old-owner=2 old-lifetime=1 new-owner=1 new-lifetime=2 old-address-space=2 old-page=7 old-pte=absent new-address-space=1 new-page=7 new-pte=present-user scrub=complete canary=308959202 model=post-reuse-old-page-absent order=unmap,invlpg,publish-unmap,scrub,allocate,write-canary,map-new-owner,publish-reuse result=PASS
${LEANOS_SERIAL_14_PF_WALK} page=7 expected-leaf=0 live-leaf=0 cause=supervisor denial=supervisor result=PASS
${LEANOS_SERIAL_14_PF_SNAPSHOT} codec=1 width=19 words=1,14,4,28672,7,0,0,1,2,2,$(symbol_value page_map_level_4_b),15,$(symbol_value user_b_stale_translation_fault_instruction),35,582,$(symbol_value user_b_stack_top),27,1,0 authorization=1 route=72057594037927937 result=PASS
${LEANOS_SERIAL_19_TLB_CPL3} event=denial vector=14 error=4 origin=cpl3 hardware=1 direct-call=0 subject=2 address-space=2 cr2=28672 page=7 access=read protection=0 pte=absent replacement-owner=1 replacement-lifetime=2 replacement-canary=308959202 replacement-canary-intact=1 route=contain handoff=new-owner cr3-reload-since-unmap=0 result=PASS
${LEANOS_SERIAL_19_TLB_CPL3} event=new-owner-read subject=1 address-space=1 page=7 address=28672 access=read frame=same lifetime=2 canary=308959202 old-address-space=2 old-pte=absent result=PASS
${LEANOS_SERIAL_19_FINAL} status=PASS prefill=1 accepted-unmap=1 exact-invlpg=1 same-frame-reuse=1 scrub=complete new-owner-cpl3-read=1 replacement-canary=intact stale-access=page-fault old-observation=denied containment=1 incidental-cr3-reload=0
EOF

case "$mode" in
  success) exit 33 ;;
  omitted-invalidation)
    sed -i '/TLB-CPL3 event=unmap /d' "$log"; exit 33 ;;
  wrong-page)
    sed -i '/TLB-CPL3 event=unmap /s/page=7/page=8/' "$log"; exit 33 ;;
  wrong-root)
    sed -i '/TLB-CPL3 event=unmap /s/address-space=2/address-space=1/' "$log"; exit 33 ;;
  invalidation-before-store)
    sed -i '/TLB-CPL3 event=unmap /s/order=store,invlpg,publish/order=invlpg,store,publish/' "$log"
    exit 33 ;;
  publication-before-invalidation)
    sed -i '/TLB-CPL3 event=unmap /s/order=store,invlpg,publish/order=store,publish,invlpg/' "$log"
    exit 33 ;;
  omitted-reuse)
    sed -i '/TLB-CPL3 event=reuse /d' "$log"; exit 33 ;;
  reuse-before-unmap)
    sed -i \
      -e "s/^$(leanos_serial_re 19 TLB-CPL3) event=unmap /$(leanos_serial_re 19 TLB-CPL3) event=__SWAP__ /" \
      -e "s/^$(leanos_serial_re 19 TLB-CPL3) event=reuse /$(leanos_serial_re 19 TLB-CPL3) event=unmap /" \
      -e "s/^$(leanos_serial_re 19 TLB-CPL3) event=__SWAP__ /$(leanos_serial_re 19 TLB-CPL3) event=reuse /" \
      "$log"
    exit 33 ;;
  reuse-publication-before-canary)
    sed -i '/TLB-CPL3 event=reuse /s/order=unmap,invlpg,publish-unmap,scrub,allocate,write-canary,map-new-owner,publish-reuse/order=unmap,invlpg,publish-unmap,scrub,allocate,publish-reuse,write-canary,map-new-owner/' "$log"
    exit 33 ;;
  replacement-canary-corrupt)
    sed -i '/TLB-CPL3 event=denial /s/replacement-canary-intact=1/replacement-canary-intact=0/' "$log"
    exit 33 ;;
  omitted-new-owner-read)
    sed -i '/TLB-CPL3 event=new-owner-read /d' "$log"; exit 33 ;;
  new-owner-wrong-address-space)
    sed -i '/TLB-CPL3 event=new-owner-read /s/address-space=1/address-space=2/' "$log"
    exit 33 ;;
  skipped-prefill)
    sed -i '/TLB-CPL3 event=prefill /d' "$log"; exit 33 ;;
  incidental-cr3-reload)
    sed -i 's/cr3-reload-since-unmap=0/cr3-reload-since-unmap=1/' "$log"
    exit 33 ;;
  software-walker-only)
    sed -i '/TLB-CPL3 event=denial /s/hardware=1/hardware=0/' "$log"; exit 33 ;;
  direct-called-page-fault)
    sed -i '/TLB-CPL3 event=denial /s/direct-call=0/direct-call=1/' "$log"; exit 33 ;;
  stale-access-succeeded)
    sed -i 's/stale-access=page-fault/stale-access=read-succeeded/' "$log"; exit 33 ;;
  partial)
    sed -i '/TLB-CPL3 event=denial /d' "$log"; exit 33 ;;
  reordered)
    sed -i \
      -e "s/^$(leanos_serial_re 19 TLB-CPL3) event=prefill /$(leanos_serial_re 19 TLB-CPL3) event=__SWAP__ /" \
      -e "s/^$(leanos_serial_re 19 TLB-CPL3) event=unmap /$(leanos_serial_re 19 TLB-CPL3) event=prefill /" \
      -e "s/^$(leanos_serial_re 19 TLB-CPL3) event=__SWAP__ /$(leanos_serial_re 19 TLB-CPL3) event=unmap /" \
      "$log"
    exit 33 ;;
  guest-error)
    sed -i "s/^$(leanos_serial_re 19 FINAL) .*/$(leanos_serial_re 19 FINAL) status=FAIL reason=stale-access/" "$log"
    exit 35 ;;
  reset) exit 0 ;;
  triple-fault) exit 43 ;;
  hang) sleep 10 ;;
  *) exit 2 ;;
esac
