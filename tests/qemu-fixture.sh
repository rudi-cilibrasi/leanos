#!/usr/bin/env bash
set -euo pipefail
[[ "${1:-}" == --version ]] && { echo "QEMU fixture version 1"; exit 0; }
log=""; for arg in "$@"; do [[ "$arg" == file:* ]] && log="${arg#file:}"; done
[[ -n "$log" ]] || exit 2
memory_mib=128
for ((i=1; i<=$#; ++i)); do
  if [[ "${!i}" == -m ]]; then next=$((i + 1)); memory_mib="${!next%M}"; fi
done
add_nmi_guard_fixture() {
  sed -i '/^LEANOS\/8 PAGING fixture=extra-mapping /a LEANOS/8 PAGING fixture=nmi-guard-mapping root=B level=pt page=6 expected=0 actual=9223372036854800387 result=REJECTED' "$log"
}
add_runtime_relation_fixtures() {
  sed -i '/^LEANOS\/8 PAGING fixture=omitted-mapping /a\
LEANOS/8 PAGING fixture=mutable-wrong-frame root=B level=pt page=7 expected=9223372036854792195 actual=9223372036854796291 result=REJECTED\
LEANOS/8 PAGING fixture=mutable-publish-before-invalidation root=B level=pt page=7 expected=0 actual=9223372036854792195 result=REJECTED\
LEANOS/8 PAGING fixture=mutable-unknown-state root=B level=pt page=7 expected=9223372036854804483 actual=9223372036854804483 result=REJECTED' "$log"
}
add_runtime_invalidation_evidence() {
  sed -i '/^LEANOS\/8 PAGING fixture=wrong-cr3 /a\
LEANOS/19 TLB path=invlpg address-space=2 page=7 pte=cleared order=store,invlpg,publish before=309063438 after=308959202 result=PASS\
LEANOS/19 TLB path=cr3 address-space=2 page=7 pte=cleared order=store,cr3,publish before=309063438 after=308959202 result=PASS\
LEANOS/19 TLB authority=generated-composite effect=page address-space=2 page=7 window=restored result=PASS\
LEANOS/19 TLB mutable-leaf=checked address-space=2 page=7 states=boot,before,unmapped,after immutable-leaves=exact result=PASS' "$log"
}
add_vtd_boot_evidence() {
  sed -i '/^LEANOS\/8 PAGING fixture=omitted-mapping /a\
LEANOS/8 PAGING fixture=mmio-wrong-frame root=B level=pt page=342 expected=9223372041130409987 actual=9223372036856176643 result=REJECTED\
LEANOS/8 PAGING fixture=mmio-flip-user root=B level=pt page=342 expected=9223372041130409987 actual=9223372041130409991 result=REJECTED' "$log"
  sed -i '/^LEANOS\/19 TLB mutable-leaf=checked /a\
LEANOS/21 VTD unit=0 mmio=4275634176 version=16 cap=59110346977575430 ecap=3842 gsts=0 fsts=0 rtaddr=0 stage=pre-activation result=PASS\
LEANOS/21 VTD-PLAN root-frame=400 context-frame=401 root-words=512 context-words=512 present-root-entries=1 present-context-entries=0 translation=disabled deny-all=1 result=PASS' "$log"
}
fault_symbol_value() {
  local symbol="$1" elf="${LEANOS_FAULT_CONTAINMENT_ELF:-build/boot/leanos-fault-containment.elf}"
  local address
  address="$(nm -n "$elf" | awk -v wanted="$symbol" '$3 == wanted { print $1 }')"
  printf '%u' "$((16#$address))"
}
case "${LEANOS_QEMU_FIXTURE_MODE:-success}" in
  dma-missing|dma-forged|dma-prestate-forged|dma-topology-forged|dma-control-forged|dma-readback-forged|dma-generated-result-forged|dma-function-missing|dma-function-duplicate|dma-function-identity-forged|dma-function-class-forged|dma-function-status-forged|dma-function-absent-command-forged|dma-function-command-forged|dma-function-prestate-forged|dma-function-bridge-forged|dma-function-multifunction-forged|dma-function-readback-forged|vtd-missing|vtd-register-forged|vtd-frames-forged)
  mode="${LEANOS_QEMU_FIXTURE_MODE}"
  set +e
  LEANOS_QEMU_FIXTURE_MODE=success "$0" "$@"
  set -e
  if [[ "$mode" == dma-missing ]]; then
    sed -i '/^LEANOS\/15 DMA /d' "$log"
  elif [[ "$mode" == dma-forged ]]; then
    sed -i 's/readbacks=5/readbacks=4/' "$log"
  elif [[ "$mode" == dma-prestate-forged ]]; then
    sed -i 's/initial-bus-masters=1/initial-bus-masters=0/' "$log"
  elif [[ "$mode" == dma-topology-forged ]]; then
    sed -i 's/topology=0001000800020002/topology=0001000800020003/' "$log"
  elif [[ "$mode" == dma-control-forged ]]; then
    sed -i 's/bus-master=disabled/bus-master=enabled/' "$log"
  elif [[ "$mode" == dma-generated-result-forged ]]; then
    sed -i 's/generated-result=0/generated-result=1/' "$log"
  elif [[ "$mode" == dma-function-missing ]]; then
    sed -i '/DMA-FUNCTION .*bdf=0:31.3 /d' "$log"
  elif [[ "$mode" == dma-function-duplicate ]]; then
    sed -i '/DMA-FUNCTION .*bdf=0:31.2 /p' "$log"
  elif [[ "$mode" == dma-function-identity-forged ]]; then
    sed -i '/DMA-FUNCTION .*bdf=0:31.3 /s/vendor=32902/vendor=4660/' "$log"
  elif [[ "$mode" == dma-function-class-forged ]]; then
    sed -i '/DMA-FUNCTION .*bdf=0:31.3 /s/class=787712/class=787713/' "$log"
  elif [[ "$mode" == dma-function-status-forged ]]; then
    sed -i '/DMA-FUNCTION .*bdf=0:3.0 /s/present=0/present=1/' "$log"
  elif [[ "$mode" == dma-function-absent-command-forged ]]; then
    sed -i '/DMA-FUNCTION .*bdf=0:3.0 /s/command-before=0/command-before=4/' "$log"
  elif [[ "$mode" == dma-function-command-forged ]]; then
    sed -i '/DMA-FUNCTION .*bdf=0:31.3 /s/command-before=1/command-before=2049/' "$log"
  elif [[ "$mode" == dma-function-prestate-forged ]]; then
    sed -i '/DMA-FUNCTION .*bdf=0:31.2 /s/command-before=7/command-before=3/' "$log"
  elif [[ "$mode" == dma-function-bridge-forged ]]; then
    sed -i '/DMA-FUNCTION .*bdf=0:31.0 /s/bridge=1/bridge=0/' "$log"
  elif [[ "$mode" == dma-function-multifunction-forged ]]; then
    sed -i '/DMA-FUNCTION .*bdf=0:31.3 /s/multifunction=1/multifunction=0/' "$log"
  elif [[ "$mode" == dma-function-readback-forged ]]; then
    sed -i '/DMA-FUNCTION .*bdf=0:31.2 /s/command-after=0/command-after=4/' "$log"
  elif [[ "$mode" == vtd-missing ]]; then
    sed -i '/^LEANOS\/21 /d' "$log"
  elif [[ "$mode" == vtd-register-forged ]]; then
    sed -i 's/ecap=3842/ecap=3843/' "$log"
  elif [[ "$mode" == vtd-frames-forged ]]; then
    sed -i 's/context-frame=401/context-frame=402/' "$log"
  else
    sed -i 's/readback=exact/readback=changed/' "$log"
  fi
  exit 33
  ;;
esac
case "${LEANOS_QEMU_FIXTURE_MODE:-success}" in
frame-budget-global-counter|frame-budget-cross-charge|frame-budget-owner-forgery|frame-budget-relabel-success|frame-budget-partial-publication|frame-budget-double-credit|frame-budget-double-publication|frame-budget-register-leak|frame-budget-canary|frame-budget-stale-authorized|frame-budget-static-buffer|frame-budget-wrong-frame|frame-budget-non-ring3|frame-budget-missing|frame-budget-reordered|frame-budget-forged)
  mode="${LEANOS_QEMU_FIXTURE_MODE}"
  set +e
  LEANOS_QEMU_FIXTURE_MODE=success "$0" "$@"
  set -e
  case "$mode" in
    frame-budget-global-counter) sed -i 's/peer-a-usage=1/peer-a-usage=0/' "$log" ;;
    frame-budget-cross-charge) sed -i 's/B-ALLOC subject=2/B-ALLOC subject=1/' "$log" ;;
    frame-budget-owner-forgery) sed -i 's/source=generated-current/source=user-word/' "$log" ;;
    frame-budget-relabel-success) sed -i 's/reason=budgetExhausted/reason=accepted/' "$log" ;;
    frame-budget-partial-publication) sed -i 's/object=none/object=11/' "$log" ;;
    frame-budget-double-credit) sed -i 's/repeated-credit=0/repeated-credit=1/' "$log" ;;
    frame-budget-double-publication)
      sed -i \
        -e '/^LEANOS\/20 FRAME /s/physical-frame=513/physical-frame=512/' \
        -e '/^LEANOS\/20 A-ALLOC /s/physical-frame=513/physical-frame=512/' \
        -e '/^LEANOS\/20 SCRUB /s/physical-frame=513/physical-frame=512/' \
        -e '/^LEANOS\/20 B-PUBLISH /s/physical-frame=513/physical-frame=512/' \
        "$log"
      ;;
    frame-budget-register-leak) sed -i 's/canaries=fresh/canaries=leaked/' "$log" ;;
    frame-budget-canary) sed -i 's/first=0/first=165/' "$log" ;;
    frame-budget-stale-authorized) sed -i 's/authorized=0/authorized=1/' "$log" ;;
    frame-budget-static-buffer) sed -i 's/source=generated-mapping/source=static-buffer/' "$log" ;;
    frame-budget-wrong-frame)
      sed -i '/B-PUBLISH /s/physical-frame=513/physical-frame=514/' "$log"
      ;;
    frame-budget-non-ring3) sed -i 's/origin=cpl3/origin=cpl0/' "$log" ;;
    frame-budget-missing) sed -i '/^LEANOS\/20 SCRUB /d' "$log" ;;
    frame-budget-reordered)
      sed -i -e 's/^LEANOS\/20 SCRUB /LEANOS\/20 __SWAP__ /' \
        -e 's/^LEANOS\/20 B-PUBLISH /LEANOS\/20 SCRUB /' \
        -e 's/^LEANOS\/20 __SWAP__ /LEANOS\/20 B-PUBLISH /' "$log"
      ;;
    frame-budget-forged)
      sed -i 's|^LEANOS/20 FINAL .*|LEANOS/20 FINAL status=PASS a-exhausted=0 b-available=1 cleanup=1 scrub=1 fresh=1 stale-denied=1 ring3-reuse=1|' "$log"
      ;;
  esac
  exit 33
  ;;
esac
if [[ "${LEANOS_QEMU_FIXTURE_MODE:-success}" == success &&
      "${LEANOS_BOOT_SCENARIO:-blocking-ipc}" == frame-budget ]]; then
  set +e
  LEANOS_BOOT_SCENARIO=blocking-ipc LEANOS_QEMU_FIXTURE_MODE=success "$0" "$@"
  status=$?
  set -e
  sed -i \
    -e 's|LEANOS/10 BOOT target=x86_64-q35 subjects=2 schedule=blocking-ipc controls=wp,smep,smap|LEANOS/20 BOOT target=x86_64-q35 subjects=2 schedule=frame-budget-v2 budgets=a:1,b:2 controls=wp,smep,smap|' \
    -e '/^LEANOS\/9 /d' -e '/^LEANOS\/10 /d' \
    -e '/^LEANOS\/6 COPY /d' -e '/^LEANOS\/11 USER-FAULT /d' \
    -e '/^LEANOS\/11 ENTRY-HIGH-WATER /d' \
    -e '/^LEANOS\/8 PAGING root=B selected=1 result=PASS$/d' "$log"
  sed -i \
    '/^LEANOS\/7 BOOTALLOC status=PASS$/a LEANOS/20 FRAME physical-frame=513 boot-published-frame=512 prior-publications=0 distinct=1 source=scalar-stream-projection result=PASS' \
    "$log"
  cat >> "$log" <<'EOF'
LEANOS/20 ENTER subject=1 address-space=1 cpl=3 budget=1 usage=0
LEANOS/20 A-ALLOC subject=1 address-space=1 budget=1 usage=1 object=10 handle=65536 physical-frame=513 user-page=4095 source=generated-mapping prior-publications=0 accepted=1
LEANOS/20 A-REJECT subject=1 reason=budgetExhausted budget=1 usage=1 object=none capability=none mapping=none state=unchanged digest=0x4201
LEANOS/20 DISPATCH subject=2 address-space=2 source=generated-current result=PASS
LEANOS/20 B-CONTEXT subject=2 source=kernel-owned-fresh registers=15 canaries=fresh result=PASS
LEANOS/20 B-ALLOC subject=2 address-space=2 budget=2 usage=1 object=20 handle=131072 peer-a-usage=1 accepted=1
LEANOS/20 CLEANUP subject=1 operation=terminate objects=1 mappings=1 capacity-restored=1 repeated-credit=0 effect=flush invalidation=cr3 order=store,cr3,ack,publish checked=1
LEANOS/20 SCRUB physical-frame=513 bytes=4096 complete=1 before-publication=1
LEANOS/20 B-PUBLISH subject=2 object=21 handle=196609 generation=3 physical-frame=513 user-page=4095 source=generated-mapping fresh-lifetime=1
LEANOS/20 STALE handle=65536 old-subject=1 fresh-object=21 authorized=0 reason=stale-generation
LEANOS/20 CANARY subject=2 origin=cpl3 access=direct first=0 last=0 old=165 denied=1 result=PASS
LEANOS/20 FINAL status=PASS a-exhausted=1 b-available=1 cleanup=1 scrub=1 fresh=1 stale-denied=1 ring3-reuse=1
EOF
  exit "$status"
fi
if [[ "${LEANOS_QEMU_FIXTURE_MODE:-success}" == success &&
      ( "${LEANOS_BOOT_SCENARIO:-blocking-ipc}" == fault-containment ||
        "${LEANOS_BOOT_SCENARIO:-blocking-ipc}" == fault-readonly-write ||
        "${LEANOS_BOOT_SCENARIO:-blocking-ipc}" == fault-nx-execute ) ]]; then
  fault_scenario="${LEANOS_BOOT_SCENARIO}"
  set +e
  LEANOS_BOOT_SCENARIO=blocking-ipc LEANOS_QEMU_FIXTURE_MODE=success "$0" "$@"
  status=$?
  set -e
  fault_probe=supervisor-read
  [[ "$fault_scenario" == fault-readonly-write ]] && fault_probe=readonly-write
  [[ "$fault_scenario" == fault-nx-execute ]] && fault_probe=nx-execute
  sed -i \
    -e "s|LEANOS/10 BOOT target=x86_64-q35 subjects=2 schedule=blocking-ipc controls=wp,smep,smap|LEANOS/14 BOOT target=x86_64-q35 subjects=2 schedule=fault-containment probe=${fault_probe} contract=v1 controls=wp,smep,smap|" \
    -e '/^LEANOS\/9 /d' -e '/^LEANOS\/10 /d' \
    -e '/^LEANOS\/6 COPY /d' -e '/^LEANOS\/11 USER-FAULT /d' \
    -e '/^LEANOS\/11 ENTRY-HIGH-WATER /d' \
    -e '/^LEANOS\/8 PAGING root=B selected=1 result=PASS$/d' \
    -e '/^LEANOS\/8 PAGING root=A selected=1 resumed=1 result=PASS$/d' "$log"
  cat >> "$log" <<'EOF'
LEANOS/8 PAGING root=A selected=1 resumed=1 result=PASS
LEANOS/14 ENTER subject=1 address-space=1 cpl=3 resources=owned
EOF
  if [[ "$fault_scenario" == fault-nx-execute ]]; then
    fault_address="$(fault_symbol_value user_a_nx_fault_instruction)"
    fault_page=$((fault_address / 4096))
    printf -v fault_leaf '%u' \
      "$(( (1 << 63) + fault_page * 4096 + 7 ))"
    printf 'LEANOS/14 PF-WALK page=%s expected-leaf=%s live-leaf=%s cause=no-execute denial=no-execute result=PASS\n' \
      "$fault_page" "$fault_leaf" "$fault_leaf" >> "$log"
    printf 'LEANOS/14 PF-SNAPSHOT codec=1 width=19 words=1,14,21,%s,%s,2,1,1,1,1,%s,15,%s,35,534,%s,27,1,0 authorization=1 route=72057598316249602 result=PASS\n' \
      "$fault_address" "$fault_page" \
      "$(fault_symbol_value page_map_level_4_a)" \
      "$fault_address" \
      "$(fault_symbol_value user_a_stack_top)" >> "$log"
    printf 'LEANOS/14 FAULT-ENTRY vector=14 error=21 access=execute protection=1 cr2=%s rip=user-a-nx-fault-instruction origin=cpl3 hardware=1 direct-call=0 subject=1 address-space=1 dispatch=0x00000000ff020202 cleanup=31 survivor=2 payload-canary=armed result=PASS\n' \
      "$fault_address" >> "$log"
  elif [[ "$fault_scenario" == fault-readonly-write ]]; then
    fault_address="$(fault_symbol_value user_a_write_target)"
    fault_page=$((fault_address / 4096))
    fault_leaf=$((fault_page * 4096 + 5))
    printf 'LEANOS/14 PF-WALK page=%s expected-leaf=%s live-leaf=%s cause=not-writable denial=not-writable result=PASS\n' \
      "$fault_page" "$fault_leaf" "$fault_leaf" >> "$log"
    printf 'LEANOS/14 PF-SNAPSHOT codec=1 width=19 words=1,14,7,%s,%s,1,1,1,1,1,%s,15,%s,35,534,%s,27,1,0 authorization=1 route=72057598316249602 result=PASS\n' \
      "$fault_address" "$fault_page" \
      "$(fault_symbol_value page_map_level_4_a)" \
      "$(fault_symbol_value user_a_write_fault_instruction)" \
      "$(fault_symbol_value user_a_stack_top)" >> "$log"
    printf 'LEANOS/14 FAULT-ENTRY vector=14 error=7 access=write protection=1 cr2=%s rip=user-a-write-fault-instruction origin=cpl3 hardware=1 direct-call=0 subject=1 address-space=1 dispatch=0x00000000ff020202 cleanup=31 survivor=2 write-canary=unchanged result=PASS\n' \
      "$fault_address" >> "$log"
  else
    printf '%s\n' \
      'LEANOS/14 PF-WALK page=0 expected-leaf=9223372036854775811 live-leaf=9223372036854775811 cause=supervisor denial=supervisor result=PASS' \
      >> "$log"
    printf 'LEANOS/14 PF-SNAPSHOT codec=1 width=19 words=1,14,5,0,0,0,1,1,1,1,%s,15,%s,35,534,%s,27,1,0 authorization=1 route=72057598316249602 result=PASS\n' \
      "$(fault_symbol_value page_map_level_4_a)" \
      "$(fault_symbol_value user_a_fault_instruction)" \
      "$(fault_symbol_value user_a_stack_top)" >> "$log"
    cat >> "$log" <<'EOF'
LEANOS/14 FAULT-ENTRY vector=14 error=5 access=read protection=1 cr2=0 rip=user-a-fault-instruction origin=cpl3 hardware=1 direct-call=0 subject=1 address-space=1 dispatch=0x00000000ff020202 cleanup=31 survivor=2 result=PASS
EOF
  fi
  cat >> "$log" <<'EOF'
LEANOS/14 TERMINATE subject=1 live=0 runnable=0 current=0 queued=0 resumable=0 resources=cap,memory,mapping,endpoint result=PASS
LEANOS/14 DISPATCH subject=2 address-space=2 source=lean-scheduler context=owned result=PASS
LEANOS/8 PAGING root=B selected=1 result=PASS
LEANOS/14 PEER subject=2 address-space=2 stack=owned return=validated canaries=preserved resources=unchanged result=PASS
LEANOS/14 FINAL status=PASS faulting=terminated survivor=2 kernel-origin=fail-stop
EOF
  exit "$status"
fi
case "${LEANOS_QEMU_FIXTURE_MODE:-success}" in
fault-direct-call|fault-wrong-error|fault-zero-error|fault-wrong-cr2|fault-wrong-rip|fault-wrong-access|fault-wrong-dispatch|fault-mapping-permission-drift|fault-snapshot-missing|fault-snapshot-duplicate|fault-snapshot-version|fault-snapshot-rip|fault-snapshot-authorization|fault-snapshot-route|fault-snapshot-reordered|fault-old-recovery|fault-stale-cr3|fault-cleanup-missing|fault-a-queued|fault-attacker-selection|fault-return-unvalidated|fault-peer-corrupt|fault-peer-cleaned|fault-forged-pass|fault-reordered|fault-kernel-relabeled|fault-global-fail|fault-nx-wrong-error|fault-nx-mapping-permission-drift|fault-nx-payload-forged)
  mode="${LEANOS_QEMU_FIXTURE_MODE}"
  set +e
  LEANOS_QEMU_FIXTURE_MODE=success "$0" "$@"
  set -e
  case "$mode" in
    fault-direct-call) sed -i 's/direct-call=0/direct-call=1/' "$log" ;;
    fault-wrong-error) sed -i 's/error=5/error=7/' "$log" ;;
    fault-zero-error) sed -i 's/error=5/error=0/' "$log" ;;
    fault-wrong-cr2) sed -i 's/cr2=0/cr2=4096/' "$log" ;;
    fault-wrong-rip) sed -i 's/rip=user-a-fault-instruction/rip=user-a-fault-recovered/' "$log" ;;
    fault-wrong-access) sed -i 's/access=read/access=write/' "$log" ;;
    fault-wrong-dispatch) sed -i 's/dispatch=0x00000000ff020202/dispatch=0x00000000ff020203/' "$log" ;;
    fault-mapping-permission-drift)
      sed -i 's/live-leaf=9223372036854775811/live-leaf=9223372036854775815/' "$log"
      ;;
    fault-snapshot-missing) sed -i '/^LEANOS\/14 PF-SNAPSHOT /d' "$log" ;;
    fault-snapshot-duplicate) sed -i '/^LEANOS\/14 PF-SNAPSHOT /p' "$log" ;;
    fault-snapshot-version) sed -i 's/PF-SNAPSHOT codec=1/PF-SNAPSHOT codec=2/' "$log" ;;
    fault-snapshot-rip)
      sed -i -E 's/(PF-SNAPSHOT .*words=([^,]*,){12})[0-9]+/\1999/' "$log"
      ;;
    fault-snapshot-authorization) sed -i 's/ authorization=1 / authorization=0 /' "$log" ;;
    fault-snapshot-route) sed -i 's/ route=72057598316249602 / route=72057598316249603 /' "$log" ;;
    fault-snapshot-reordered)
      snapshot="$(grep '^LEANOS/14 PF-SNAPSHOT ' "$log")"
      sed -i '/^LEANOS\/14 PF-SNAPSHOT /d' "$log"
      sed -i "/^LEANOS\\/14 FAULT-ENTRY /a $snapshot" "$log"
      ;;
    fault-old-recovery) sed -i '/^LEANOS\/14 TERMINATE /d; /^LEANOS\/14 DISPATCH /d' "$log" ;;
    fault-stale-cr3) sed -i 's/subject=2 address-space=2 source/subject=2 address-space=1 source/' "$log" ;;
    fault-cleanup-missing) sed -i 's/resumable=0/resumable=1/' "$log" ;;
    fault-a-queued) sed -i 's/queued=0/queued=1/' "$log" ;;
    fault-attacker-selection) sed -i 's/DISPATCH subject=2/DISPATCH subject=3/' "$log" ;;
    fault-return-unvalidated) sed -i 's/ return=validated//' "$log" ;;
    fault-peer-corrupt) sed -i 's/canaries=preserved/canaries=corrupt/' "$log" ;;
    fault-peer-cleaned) sed -i 's/resources=unchanged/resources=changed/' "$log" ;;
    fault-forged-pass) sed -i '/^LEANOS\/14 FAULT-ENTRY /d; /^LEANOS\/14 TERMINATE /d' "$log" ;;
    fault-reordered)
      sed -i -e 's/^LEANOS\/14 TERMINATE /LEANOS\/14 __SWAP__ /' \
        -e 's/^LEANOS\/14 DISPATCH /LEANOS\/14 TERMINATE /' \
        -e 's/^LEANOS\/14 __SWAP__ /LEANOS\/14 DISPATCH /' "$log"
      ;;
    fault-kernel-relabeled) sed -i 's/origin=cpl3/origin=kernel/' "$log" ;;
    fault-global-fail)
      sed -i 's/^LEANOS\/14 FINAL .*/LEANOS\/14 FINAL status=FAIL reason=kernel-fault/' "$log"
      exit 35
      ;;
    fault-nx-wrong-error) sed -i 's/error=21/error=5/' "$log" ;;
    fault-nx-mapping-permission-drift)
      sed -i -E \
        's/(PF-WALK page=[0-9]+ expected-leaf=[0-9]+) live-leaf=[0-9]+/\1 live-leaf=7/' \
        "$log"
      ;;
    fault-nx-payload-forged)
      sed -i 's/payload-canary=armed/payload-canary=executed/' "$log"
      ;;
  esac
  exit 33
  ;;
esac
if [[ "${LEANOS_QEMU_FIXTURE_MODE:-success}" == success &&
      "${LEANOS_BOOT_SCENARIO:-blocking-ipc}" == preemption ]]; then
  set +e
  LEANOS_QEMU_FIXTURE_MODE=legacy-success "$0" "$@"
  status=$?
  set -e
  sed -i 's/projection=exact-rich/projection=scalar-checked/' "$log"
  add_nmi_guard_fixture
  add_runtime_invalidation_evidence
  add_vtd_boot_evidence
  sed -i 's/readbacks=5 /readbacks=5 initial-bus-masters=1 initial-bus-master-mask=16 /' "$log"
  sed -i 's/readback=exact stage=/readback=exact generated-result=0 stage=/' "$log"
  sed -i '/^LEANOS\/15 DMA snapshot=/i\
LEANOS/15 DMA-FUNCTION manifest=1 topology=0001000800020002 bdf=0:0.0 present=1 vendor=32902 device=10688 class=393216 command-before=0 command-after=0 assigned=0 bridge=0 multifunction=0 policy=accepted\
LEANOS/15 DMA-FUNCTION manifest=1 topology=0001000800020002 bdf=0:1.0 present=1 vendor=4660 device=4369 class=196608 command-before=3 command-after=0 assigned=0 bridge=0 multifunction=0 policy=accepted\
LEANOS/15 DMA-FUNCTION manifest=1 topology=0001000800020002 bdf=0:3.0 present=0 vendor=0 device=0 class=0 command-before=0 command-after=0 assigned=0 bridge=0 multifunction=0 policy=accepted\
LEANOS/15 DMA-FUNCTION manifest=1 topology=0001000800020002 bdf=0:31.0 present=1 vendor=32902 device=10520 class=393472 command-before=3 command-after=0 assigned=0 bridge=1 multifunction=1 policy=accepted\
LEANOS/15 DMA-FUNCTION manifest=1 topology=0001000800020002 bdf=0:31.2 present=1 vendor=32902 device=10530 class=67073 command-before=7 command-after=0 assigned=0 bridge=0 multifunction=1 policy=accepted\
LEANOS/15 DMA-FUNCTION manifest=1 topology=0001000800020002 bdf=0:31.3 present=1 vendor=32902 device=10544 class=787712 command-before=1 command-after=0 assigned=0 bridge=0 multifunction=1 policy=accepted' "$log"
  sed -i '/^LEANOS\/6 CONTROL/i LEANOS/17 ENTRY-MANIFEST ordinary=8 extended=6,7 contained=0,3 auxiliary=1 terminal=2 extra=0 rsp0=entry-stack ist1=df-stack ist2=nmi-stack result=PASS' "$log"
  sed -i '/^LEANOS\/6 CONTROL/i LEANOS/16 DIRECT-PORT-CONTROL tr=40 limit=103 iomap=104 bitmap=absent iopl=0 stage=pre-cpl3 result=PASS' "$log"
  sed -i \
    -e 's/schedule=one-shot-pit/schedule=bounded-two-shot-pit/' \
    -e 's/mode=one-shot origin=cpl3/mode=bounded-one-shot sequence=1 origin=cpl3/' \
    -e 's/stack=restored ticks-masked=1/stack=initial contexts=separate/' \
    -e '/^LEANOS\/6 COPY direction=out/a LEANOS/11 ENTRY-HIGH-WATER path=user-page-fault observed-bytes=496 usable-bytes=16384 margin-bytes=15888 authority=diagnostic result=PASS\nLEANOS/11 USER-FAULT vector=14 error=5 origin=cpl3 address=zero contained=1 result=PASS' \
    -e 's|LEANOS/5 FINAL status=PASS ticks=1|LEANOS/5 TIMER vector=32 source=pit mode=bounded-one-shot sequence=2 origin=cpl3 accepted=1\nLEANOS/5 CONTEXT old-subject=2 old-address-space=2 new-subject=1 new-address-space=1 policy=round-robin\nLEANOS/8 PAGING root=A selected=1 resumed=1 result=PASS\nLEANOS/5 SWITCH subject=1 address-space=1 cr3=switched stack=resumed contexts=separate\nLEANOS/11 ENTRY-HIGH-WATER path=timer-context-switch observed-bytes=512 usable-bytes=16384 margin-bytes=15872 authority=diagnostic result=PASS\nLEANOS/5 RESUME subject=1 caller=1 address-space=1 frame=original canaries=preserved contexts=separate\nLEANOS/5 FINAL status=PASS ticks=2|' \
    "$log"
  exit "$status"
fi
if [[ "${LEANOS_QEMU_FIXTURE_MODE:-success}" == success ]]; then
  set +e
  LEANOS_QEMU_FIXTURE_MODE=legacy-success "$0" "$@"
  status=$?
  set -e
  sed -i 's/projection=exact-rich/projection=scalar-checked/' "$log"
  add_nmi_guard_fixture
  add_runtime_invalidation_evidence
  add_vtd_boot_evidence
  sed -i 's/readbacks=5 /readbacks=5 initial-bus-masters=1 initial-bus-master-mask=16 /' "$log"
  sed -i 's/readback=exact stage=/readback=exact generated-result=0 stage=/' "$log"
  sed -i '/^LEANOS\/15 DMA snapshot=/i\
LEANOS/15 DMA-FUNCTION manifest=1 topology=0001000800020002 bdf=0:0.0 present=1 vendor=32902 device=10688 class=393216 command-before=0 command-after=0 assigned=0 bridge=0 multifunction=0 policy=accepted\
LEANOS/15 DMA-FUNCTION manifest=1 topology=0001000800020002 bdf=0:1.0 present=1 vendor=4660 device=4369 class=196608 command-before=3 command-after=0 assigned=0 bridge=0 multifunction=0 policy=accepted\
LEANOS/15 DMA-FUNCTION manifest=1 topology=0001000800020002 bdf=0:3.0 present=0 vendor=0 device=0 class=0 command-before=0 command-after=0 assigned=0 bridge=0 multifunction=0 policy=accepted\
LEANOS/15 DMA-FUNCTION manifest=1 topology=0001000800020002 bdf=0:31.0 present=1 vendor=32902 device=10520 class=393472 command-before=3 command-after=0 assigned=0 bridge=1 multifunction=1 policy=accepted\
LEANOS/15 DMA-FUNCTION manifest=1 topology=0001000800020002 bdf=0:31.2 present=1 vendor=32902 device=10530 class=67073 command-before=7 command-after=0 assigned=0 bridge=0 multifunction=1 policy=accepted\
LEANOS/15 DMA-FUNCTION manifest=1 topology=0001000800020002 bdf=0:31.3 present=1 vendor=32902 device=10544 class=787712 command-before=1 command-after=0 assigned=0 bridge=0 multifunction=1 policy=accepted' "$log"
  sed -i '/^LEANOS\/6 CONTROL/i LEANOS/17 ENTRY-MANIFEST ordinary=8 extended=6,7 contained=0,3 auxiliary=1 terminal=2 extra=0 rsp0=entry-stack ist1=df-stack ist2=nmi-stack result=PASS' "$log"
  sed -i '/^LEANOS\/6 CONTROL/i LEANOS/16 DIRECT-PORT-CONTROL tr=40 limit=103 iomap=104 bitmap=absent iopl=0 stage=pre-cpl3 result=PASS' "$log"
  sed -i \
    -e 's|LEANOS/6 BOOT target=x86_64-q35 subjects=2 schedule=one-shot-pit|LEANOS/10 BOOT target=x86_64-q35 subjects=2 schedule=blocking-ipc|' \
    -e '/^LEANOS\/5 /d' \
    -e '/^LEANOS\/8 PAGING root=B selected=1 result=PASS$/d' \
    -e '/^LEANOS\/6 COPY direction=in/i LEANOS/8 PAGING root=B selected=1 result=PASS\nLEANOS/10 IPC event=enter subject=2 address-space=2 cpl=3 endpoint=10\nLEANOS/9 CAPREUSE event=initial subject=2 handle=131072 endpoint=10 accepted=1\nLEANOS/9 CAPREUSE event=clear slot=0 old-generation=2 result=PASS\nLEANOS/9 CAPREUSE event=install slot=0 generation=3 endpoint=11 result=PASS\nLEANOS/9 CAPREUSE event=stale-replay subject=2 handle=131072 rejected=1\nLEANOS/9 CAPREUSE event=unchanged endpoint=11 mailbox=empty result=PASS\nLEANOS/9 CAPREUSE event=fresh subject=2 handle=196608 endpoint=11 accepted=1\nLEANOS/9 CAPREUSE status=PASS stale-effects=0 fresh-effects=1\nLEANOS/10 IPC event=block subject=2 endpoint=10 empty=1 runnable=0 result=PASS\nLEANOS/8 PAGING root=A selected=1 resumed=1 result=PASS\nLEANOS/10 IPC event=dispatch subject=1 address-space=1 blocked-subject=2 trusted=1' \
    -e '/^LEANOS\/6 COPY direction=out/a LEANOS/11 ENTRY-HIGH-WATER path=user-page-fault observed-bytes=496 usable-bytes=16384 margin-bytes=15888 authority=diagnostic result=PASS\nLEANOS/11 USER-FAULT vector=14 error=5 origin=cpl3 address=zero contained=1 result=PASS\nLEANOS/10 IPC event=send sender=1 endpoint=10 payload0=1279607118 payload1=20307 accepted=1\nLEANOS/10 IPC event=wake subject=2 ready-insertions=1 reserved=1 result=PASS\nLEANOS/8 PAGING root=B selected=1 result=PASS\nLEANOS/10 IPC event=dispatch subject=2 address-space=2 reservation=owned trusted=1\nLEANOS/10 IPC event=deliver receiver=2 endpoint=10 sender=1 payload0=1279607118 payload1=20307 exact=1 canaries=preserved\nLEANOS/11 ENTRY-HIGH-WATER path=syscall observed-bytes=512 usable-bytes=16384 margin-bytes=15872 authority=diagnostic result=PASS\nLEANOS/10 FINAL status=PASS blocks=1 wakes=1 deliveries=1' \
    "$log"
  if [[ "${LEANOS_BOOT_SCENARIO:-blocking-ipc}" == entry-adversarial ]]; then
    sed -i '/^LEANOS\/6 COPY direction=in/,/^LEANOS\/10 FINAL status=PASS/d' "$log"
    sed -i '/event=dispatch subject=1/a LEANOS/11 ENTRY-ADVERSARIAL attempted-vector=14 delivered=13 privileged-handler=unreached result=PASS\nLEANOS/11 ENTRY-ADVERSARIAL attempted-vector=32 delivered=13 privileged-handler=unreached result=PASS\nLEANOS/16 DIRECT-PORT-DENIAL subject=1 vector=13 error=0 origin=cpl3 port=244 direction=out width=byte purpose=user device-mutation=0 result=PASS\nLEANOS/16 DIRECT-PORT-TERMINATE subject=1 live=0 runnable=0 current=0 queued=0 resumable=0 resources=cap,memory,mapping,endpoint result=PASS\nLEANOS/16 DIRECT-PORT-DISPATCH subject=2 address-space=2 source=lean-scheduler context=owned result=PASS\nLEANOS/8 PAGING root=B selected=1 result=PASS\nLEANOS/16 DIRECT-PORT-PEER subject=2 address-space=2 stack=owned return=validated canaries=preserved resources=unchanged result=PASS\nLEANOS/16 FINAL status=PASS denied=1 resumed-a=0 peer-ran=1 device-mutation=0' "$log"
  fi
  exit "$status"
fi
case "${LEANOS_QEMU_FIXTURE_MODE:-success}" in
entry-high-water-missing|entry-high-water-invalid|entry-high-water-duplicate|entry-high-water-reordered|entry-high-water-wrong-path)
  mode="${LEANOS_QEMU_FIXTURE_MODE}"
  set +e
  LEANOS_QEMU_FIXTURE_MODE=success "$0" "$@"
  set -e
  case "$mode" in
    entry-high-water-missing) sed -i '/^LEANOS\/11 ENTRY-HIGH-WATER /d' "$log" ;;
    entry-high-water-invalid) sed -i 's/margin-bytes=15872/margin-bytes=15871/' "$log" ;;
    entry-high-water-duplicate) sed -i '/^LEANOS\/11 ENTRY-HIGH-WATER /p' "$log" ;;
    entry-high-water-reordered)
      final_high_water_path=syscall
      [[ "${LEANOS_BOOT_SCENARIO:-blocking-ipc}" == preemption ]] &&
        final_high_water_path=timer-context-switch
      sed -i -e 's/path=user-page-fault/path=__ENTRY_HIGH_WATER_SWAP__/' \
        -e "s/path=${final_high_water_path}/path=user-page-fault/" \
        -e "s/path=__ENTRY_HIGH_WATER_SWAP__/path=${final_high_water_path}/" "$log"
      ;;
    entry-high-water-wrong-path)
      sed -i 's/path=user-page-fault/path=kernel-diagnostic/' "$log"
      ;;
  esac
  exit 33
  ;;
esac
case "${LEANOS_QEMU_FIXTURE_MODE:-success}" in
omit-block|old-handoff|wrong-context|missing-wake|duplicate-wake|stolen-delivery|forged-pass)
  mode="${LEANOS_QEMU_FIXTURE_MODE}"
  set +e
  LEANOS_QEMU_FIXTURE_MODE=success "$0" "$@"
  set -e
  case "$mode" in
    omit-block) sed -i '/event=block/d' "$log" ;;
    old-handoff) sed -i '/event=dispatch subject=1/d' "$log" ;;
    wrong-context) sed -i 's/dispatch subject=2 address-space=2/dispatch subject=2 address-space=1/' "$log" ;;
    missing-wake) sed -i '/event=wake/d' "$log" ;;
    duplicate-wake) sed -i '/event=wake/p' "$log" ;;
    stolen-delivery) sed -i 's/event=deliver receiver=2/event=deliver receiver=1/' "$log" ;;
    forged-pass) sed -i '/^LEANOS\/10 IPC/d' "$log" ;;
  esac
  exit 33
  ;;
esac
case "${LEANOS_QEMU_FIXTURE_MODE:-success}" in
reuse-generation-ignored|reuse-truncated-handle|reuse-old-acts-replacement|reuse-forged-pass|reuse-wrong-caller|reuse-fresh-omitted|reuse-reordered)
  mode="${LEANOS_QEMU_FIXTURE_MODE}"
  set +e
  LEANOS_QEMU_FIXTURE_MODE=success "$0" "$@"
  set -e
  case "$mode" in
    reuse-generation-ignored) sed -i 's/handle=131072 rejected=1/handle=131072 accepted=1/' "$log" ;;
    reuse-truncated-handle) sed -i 's/event=stale-replay subject=2 handle=131072/event=stale-replay subject=2 handle=0/' "$log" ;;
    reuse-old-acts-replacement) sed -i 's/mailbox=empty/mailbox=sent/' "$log" ;;
    reuse-forged-pass) sed -i '/^LEANOS\/9 CAPREUSE event=/d' "$log" ;;
    reuse-wrong-caller) sed -i 's/event=initial subject=2/event=initial subject=1/' "$log" ;;
    reuse-fresh-omitted) sed -i '/CAPREUSE event=fresh/d' "$log" ;;
    reuse-reordered) sed -i 's/event=clear/__CLEAR__/; s/event=install/event=clear/; s/__CLEAR__/event=install/' "$log" ;;
  esac
  exit 33
  ;;
esac
case "${LEANOS_QEMU_FIXTURE_MODE:-success}" in
missing-second-tick|fresh-restart|cross-restored|stale-resume-cr3|corrupt-stack|corrupt-flags|corrupt-selectors)
  mode="${LEANOS_QEMU_FIXTURE_MODE}"
  set +e
  LEANOS_QEMU_FIXTURE_MODE=success "$0" "$@"
  set -e
  case "$mode" in
    missing-second-tick) sed -i '/sequence=2/d' "$log" ;;
    fresh-restart) sed -i 's/frame=original/frame=fresh/' "$log" ;;
    cross-restored) sed -i 's/RESUME subject=1 caller=1/RESUME subject=2 caller=2/' "$log" ;;
    stale-resume-cr3) sed -i 's/root=A selected=1 resumed=1/root=B selected=1 resumed=1/' "$log" ;;
    corrupt-stack) sed -i 's/frame=original canaries=preserved/frame=original stack=corrupt/' "$log" ;;
    corrupt-flags) sed -i 's/frame=original canaries=preserved/frame=original flags=corrupt/' "$log" ;;
    corrupt-selectors) sed -i 's/frame=original canaries=preserved/frame=original selectors=corrupt/' "$log" ;;
  esac
  exit 33
  ;;
esac
case "${LEANOS_QEMU_FIXTURE_MODE:-success}" in
legacy-success) printf '%s\n' 'LEANOS/6 BOOT target=x86_64-q35 subjects=2 schedule=one-shot-pit controls=wp,smep,smap' 'LEANOS/15 DMA snapshot=1 topology=0001000800020002 bus=0 scanned=256 present=5 optional-absent=1 writes=5 readbacks=5 bus-master=disabled readback=exact stage=pre-cpl3 result=PASS' > "$log"; printf '%s\n' 'LEANOS/8 PAGING root=A selected=1 leaves=4096 policy=manifest result=PASS' 'LEANOS/8 PAGING root=B selected=0 leaves=4096 policy=manifest result=PASS' 'LEANOS/8 PAGING fixture=flip-present root=B level=pt page=0 expected=1 actual=0 result=REJECTED' 'LEANOS/8 PAGING fixture=flip-user root=B level=pt page=1 expected=1 actual=5 result=REJECTED' 'LEANOS/8 PAGING fixture=flip-writable root=B level=pt page=2 expected=1 actual=3 result=REJECTED' 'LEANOS/8 PAGING fixture=flip-nx root=B level=pt page=3 expected=1 actual=9223372036854775809 result=REJECTED' 'LEANOS/8 PAGING fixture=wrong-frame root=B level=pt page=0 expected=1 actual=4097 result=REJECTED' 'LEANOS/8 PAGING fixture=ancestor-pointer root=B level=pml4 page=0 expected=8199 actual=12295 result=REJECTED' 'LEANOS/8 PAGING fixture=ancestor-flags root=B level=pdpt page=0 expected=12295 actual=12291 result=REJECTED' 'LEANOS/8 PAGING fixture=swapped-user-leaves root=B level=pt page=4 expected=16389 actual=20481 result=REJECTED' 'LEANOS/8 PAGING fixture=extra-mapping root=B level=pt page=5 expected=0 actual=9223372036854796291 result=REJECTED' 'LEANOS/8 PAGING fixture=entry-guard-mapping root=B level=pt page=6 expected=0 actual=9223372036854800387 result=REJECTED' 'LEANOS/8 PAGING fixture=omitted-mapping root=B level=pt page=4 expected=16389 actual=0 result=REJECTED' 'LEANOS/8 PAGING fixture=mutable-wrong-frame root=B level=pt page=7 expected=9223372036854792195 actual=9223372036854796291 result=REJECTED' 'LEANOS/8 PAGING fixture=mutable-publish-before-invalidation root=B level=pt page=7 expected=0 actual=9223372036854792195 result=REJECTED' 'LEANOS/8 PAGING fixture=mutable-unknown-state root=B level=pt page=7 expected=9223372036854804483 actual=9223372036854804483 result=REJECTED' 'LEANOS/8 PAGING fixture=wrong-cr3 root=A level=cr3 page=0 expected=4096 actual=8192 result=REJECTED' 'LEANOS/7 HANDOFF magic=valid info-bytes=1024 mmap-entries=8 result=PASS' "LEANOS/7 MAP boot-pages=4096 reported-top-mib=$((memory_mib - 1)) precedence=reserved result=PASS" 'LEANOS/7 ALLOC frame=512 firmware-usable=1 boot-accessible=1 reserved=0 projection=exact-rich result=PASS' 'LEANOS/7 SCRUB bytes=4096 zero=1 result=PASS' 'LEANOS/7 PUBLISH object=1 owner=1 stale-object=denied result=PASS' 'LEANOS/7 BOOTALLOC status=PASS' >> "$log"; awk -F '\t' '$1 ~ /^[0-9]+$/ { print "LEANOS/3 ORACLE id=" $2 " result=PASS" }' "$LEANOS_ORACLE_CORPUS" >> "$log"; printf '%s\n' 'LEANOS/6 CONTROL cr0.wp=1 cr0.em=1 cr0.mp=1 cr0.ts=1 cr4.osfxsr=0 cr4.osxmmexcpt=0 cr4.osxsave=0 cr4.pke=0 cr4.smep=1 cr4.smap=1 ac=0 stage=exception-path-ready' 'LEANOS/4 PROBE kind=wp vector=14 error=3 origin=kernel address=kernel-text policy=fatal result=PASS' 'LEANOS/4 PROBE kind=smep vector=14 error=17 origin=kernel address=user-a-text policy=fatal result=PASS' 'LEANOS/6 PROBE kind=smap-direct vector=14 origin=kernel ac=0 result=PASS' 'LEANOS/6 POLICY zero=accept max=accept unmapped=reject readonly=reject overflow=reject noncanonical=reject wrong-subject=reject stale=reject atomic=PASS' 'LEANOS/6 CLEANUP omitted=detected wrappers=checked entry=clac result=PASS' 'LEANOS/6 COPY direction=in length=4 cross-page=1 validated=1 user-df=1 kernel-df=cleared ac=cleared result=PASS' 'LEANOS/6 COPY direction=out length=4 cross-page=0 validated=1 user-df=1 kernel-df=cleared destination=verified-by-cpl3 ac=cleared result=PASS' 'LEANOS/5 ENTRY subject=1 address-space=1 cpl=3 yielding=0' 'LEANOS/5 TIMER vector=32 source=pit mode=one-shot origin=cpl3 accepted=1' 'LEANOS/5 CONTEXT old-subject=1 old-address-space=1 new-subject=2 new-address-space=2 policy=round-robin' 'LEANOS/8 PAGING root=B selected=1 result=PASS' 'LEANOS/5 SWITCH subject=2 address-space=2 cr3=switched stack=restored ticks-masked=1' 'LEANOS/5 SYSCALL subject=2 caller=2 address-space=2 authorized=1 canaries=preserved' 'LEANOS/5 FINAL status=PASS ticks=1' >> "$log"; exit 33;;
missing-paging) set +e; LEANOS_QEMU_FIXTURE_MODE=success "$0" "$@"; set -e; sed -i '/LEANOS\/8 PAGING/d' "$log"; exit 33;;
missing-scrub) set +e; LEANOS_QEMU_FIXTURE_MODE=success "$0" "$@"; set -e; sed -i '/LEANOS\/7 SCRUB/d' "$log"; exit 33;;
wrong-memory-map) set +e; LEANOS_QEMU_FIXTURE_MODE=success "$0" "$@"; set -e; sed -i 's/reported-top-mib=[0-9]*/reported-top-mib=32/' "$log"; exit 33;;
reordered-allocation) set +e; LEANOS_QEMU_FIXTURE_MODE=success "$0" "$@"; set -e; sed -i 's|LEANOS/7 SCRUB bytes=4096 zero=1 result=PASS|__SCRUB__|; s|LEANOS/7 PUBLISH object=1 owner=1 stale-object=denied result=PASS|LEANOS/7 SCRUB bytes=4096 zero=1 result=PASS|; s|__SCRUB__|LEANOS/7 PUBLISH object=1 owner=1 stale-object=denied result=PASS|' "$log"; exit 33;;
interrupts-disabled|timer-missing) set +e; LEANOS_QEMU_FIXTURE_MODE=success "$0" "$@"; set -e; sed -i '/LEANOS\/5 TIMER/d' "$log"; exit 33;;
old-resumed) set +e; LEANOS_QEMU_FIXTURE_MODE=success "$0" "$@"; set -e; sed -i 's/SWITCH subject=2/SWITCH subject=1/' "$log"; exit 33;;
wrong-binding) set +e; LEANOS_QEMU_FIXTURE_MODE=success "$0" "$@"; set -e; sed -i 's/caller=2 address-space=2/caller=1 address-space=1/' "$log"; exit 33;;
duplicate-tick) set +e; LEANOS_QEMU_FIXTURE_MODE=success "$0" "$@"; set -e; sed -i '/LEANOS\/5 TIMER/p' "$log"; exit 33;;
corrupt-canary) set +e; LEANOS_QEMU_FIXTURE_MODE=success "$0" "$@"; set -e; sed -i 's/canaries=preserved/canaries=corrupt/' "$log"; exit 33;;
skipped-user) printf '%s\n' 'LEANOS/2 BOOT target=x86_64-q35 entry=int80' 'LEANOS/2 TRANSITION state=0 command=1 result=1' 'LEANOS/2 TRANSITION state=0 command=7 result=0' 'LEANOS/2 SYSCALL kind=authorized result=accepted' 'LEANOS/2 SYSCALL kind=forged result=rejected' 'LEANOS/2 FAULT vector=14 class=user-supervisor-access contained=1' 'LEANOS/2 RESUME kernel=1' 'LEANOS/2 FINAL status=PASS' > "$log"; exit 33;;
forged-result) printf '%s\n' 'LEANOS/2 BOOT target=x86_64-q35 entry=int80' 'LEANOS/2 TRANSITION state=0 command=1 result=1' 'LEANOS/2 TRANSITION state=0 command=7 result=0' 'LEANOS/2 USER cpl=3' 'LEANOS/2 SYSCALL kind=authorized result=accepted' 'LEANOS/2 SYSCALL kind=forged result=accepted' 'LEANOS/2 FAULT vector=14 class=user-supervisor-access contained=1' 'LEANOS/2 RESUME kernel=1' 'LEANOS/2 FINAL status=PASS' > "$log"; exit 33;;
reordered) printf '%s\n' 'LEANOS/2 BOOT target=x86_64-q35 entry=int80' 'LEANOS/2 TRANSITION state=0 command=1 result=1' 'LEANOS/2 TRANSITION state=0 command=7 result=0' 'LEANOS/2 USER cpl=3' 'LEANOS/2 SYSCALL kind=forged result=rejected' 'LEANOS/2 SYSCALL kind=authorized result=accepted' 'LEANOS/2 FAULT vector=14 class=user-supervisor-access contained=1' 'LEANOS/2 RESUME kernel=1' 'LEANOS/2 FINAL status=PASS' > "$log"; exit 33;;
wrong-fault) printf '%s\n' 'LEANOS/2 BOOT target=x86_64-q35 entry=int80' 'LEANOS/2 TRANSITION state=0 command=1 result=1' 'LEANOS/2 TRANSITION state=0 command=7 result=0' 'LEANOS/2 USER cpl=3' 'LEANOS/2 SYSCALL kind=authorized result=accepted' 'LEANOS/2 SYSCALL kind=forged result=rejected' 'LEANOS/2 FAULT vector=13 class=general-protection contained=1' 'LEANOS/2 RESUME kernel=1' 'LEANOS/2 FINAL status=PASS' > "$log"; exit 33;;
missing) : > "$log"; exit 33;;
partial) echo 'LEANOS/2 BOOT target=x86_64-q35 entry=int80' > "$log"; exit 33;;
guest-error) echo 'LEANOS/2 FINAL status=FAIL' > "$log"; exit 35;;
hang) sleep 10;;
*) exit 2;; esac
