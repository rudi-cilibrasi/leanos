#!/usr/bin/env bash
set -euo pipefail
[[ "${1:-}" == --version ]] && { echo "QEMU fixture version 1"; exit 0; }
log=""; for arg in "$@"; do [[ "$arg" == file:* ]] && log="${arg#file:}"; done
[[ -n "$log" ]] || exit 2
memory_mib=128
for ((i=1; i<=$#; ++i)); do
  if [[ "${!i}" == -m ]]; then next=$((i + 1)); memory_mib="${!next%M}"; fi
done
if [[ "${LEANOS_QEMU_FIXTURE_MODE:-success}" == success &&
      "${LEANOS_BOOT_SCENARIO:-blocking-ipc}" == fault-containment ]]; then
  set +e
  LEANOS_BOOT_SCENARIO=blocking-ipc LEANOS_QEMU_FIXTURE_MODE=success "$0" "$@"
  status=$?
  set -e
  sed -i \
    -e 's|LEANOS/10 BOOT target=x86_64-q35 subjects=2 schedule=blocking-ipc controls=wp,smep,smap|LEANOS/14 BOOT target=x86_64-q35 subjects=2 schedule=fault-containment contract=v1 controls=wp,smep,smap|' \
    -e '/^LEANOS\/9 /d' -e '/^LEANOS\/10 /d' \
    -e '/^LEANOS\/6 COPY /d' -e '/^LEANOS\/11 USER-FAULT /d' \
    -e '/^LEANOS\/11 ENTRY-HIGH-WATER /d' \
    -e '/^LEANOS\/8 PAGING root=B selected=1 result=PASS$/d' \
    -e '/^LEANOS\/8 PAGING root=A selected=1 resumed=1 result=PASS$/d' "$log"
  cat >> "$log" <<'EOF'
LEANOS/8 PAGING root=A selected=1 resumed=1 result=PASS
LEANOS/14 ENTER subject=1 address-space=1 cpl=3 resources=owned
LEANOS/14 FAULT-ENTRY vector=14 error=5 origin=cpl3 hardware=1 direct-call=0 subject=1 address-space=1 result=PASS
LEANOS/14 TERMINATE subject=1 live=0 runnable=0 current=0 queued=0 resumable=0 resources=cap,memory,mapping,endpoint result=PASS
LEANOS/14 DISPATCH subject=2 address-space=2 source=lean-scheduler context=owned result=PASS
LEANOS/8 PAGING root=B selected=1 result=PASS
LEANOS/14 PEER subject=2 address-space=2 stack=owned return=validated canaries=preserved resources=unchanged result=PASS
LEANOS/14 FINAL status=PASS faulting=terminated survivor=2 kernel-origin=fail-stop
EOF
  exit "$status"
fi
case "${LEANOS_QEMU_FIXTURE_MODE:-success}" in
fault-direct-call|fault-old-recovery|fault-stale-cr3|fault-cleanup-missing|fault-return-unvalidated|fault-peer-corrupt|fault-forged-pass|fault-kernel-relabeled)
  mode="${LEANOS_QEMU_FIXTURE_MODE}"
  set +e
  LEANOS_QEMU_FIXTURE_MODE=success "$0" "$@"
  set -e
  case "$mode" in
    fault-direct-call) sed -i 's/direct-call=0/direct-call=1/' "$log" ;;
    fault-old-recovery) sed -i '/^LEANOS\/14 TERMINATE /d; /^LEANOS\/14 DISPATCH /d' "$log" ;;
    fault-stale-cr3) sed -i 's/subject=2 address-space=2 source/subject=2 address-space=1 source/' "$log" ;;
    fault-cleanup-missing) sed -i 's/resumable=0/resumable=1/' "$log" ;;
    fault-return-unvalidated) sed -i 's/ return=validated//' "$log" ;;
    fault-peer-corrupt) sed -i 's/canaries=preserved/canaries=corrupt/' "$log" ;;
    fault-forged-pass) sed -i '/^LEANOS\/14 FAULT-ENTRY /d; /^LEANOS\/14 TERMINATE /d' "$log" ;;
    fault-kernel-relabeled) sed -i 's/origin=cpl3/origin=kernel/' "$log" ;;
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
  sed -i '/^LEANOS\/6 CONTROL/i LEANOS/12 ENTRY-MANIFEST ordinary=5 extended=6,7 auxiliary=2 extra=0 rsp0=entry-stack ist1=df-stack result=PASS' "$log"
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
  sed -i '/^LEANOS\/6 CONTROL/i LEANOS/12 ENTRY-MANIFEST ordinary=5 extended=6,7 auxiliary=2 extra=0 rsp0=entry-stack ist1=df-stack result=PASS' "$log"
  sed -i \
    -e 's|LEANOS/6 BOOT target=x86_64-q35 subjects=2 schedule=one-shot-pit|LEANOS/10 BOOT target=x86_64-q35 subjects=2 schedule=blocking-ipc|' \
    -e '/^LEANOS\/5 /d' \
    -e '/^LEANOS\/8 PAGING root=B selected=1 result=PASS$/d' \
    -e '/^LEANOS\/6 COPY direction=in/i LEANOS/8 PAGING root=B selected=1 result=PASS\nLEANOS/10 IPC event=enter subject=2 address-space=2 cpl=3 endpoint=10\nLEANOS/9 CAPREUSE event=initial subject=2 handle=131072 endpoint=10 accepted=1\nLEANOS/9 CAPREUSE event=clear slot=0 old-generation=2 result=PASS\nLEANOS/9 CAPREUSE event=install slot=0 generation=3 endpoint=11 result=PASS\nLEANOS/9 CAPREUSE event=stale-replay subject=2 handle=131072 rejected=1\nLEANOS/9 CAPREUSE event=unchanged endpoint=11 mailbox=empty result=PASS\nLEANOS/9 CAPREUSE event=fresh subject=2 handle=196608 endpoint=11 accepted=1\nLEANOS/9 CAPREUSE status=PASS stale-effects=0 fresh-effects=1\nLEANOS/10 IPC event=block subject=2 endpoint=10 empty=1 runnable=0 result=PASS\nLEANOS/8 PAGING root=A selected=1 resumed=1 result=PASS\nLEANOS/10 IPC event=dispatch subject=1 address-space=1 blocked-subject=2 trusted=1' \
    -e '/^LEANOS\/6 COPY direction=out/a LEANOS/11 ENTRY-HIGH-WATER path=user-page-fault observed-bytes=496 usable-bytes=16384 margin-bytes=15888 authority=diagnostic result=PASS\nLEANOS/11 USER-FAULT vector=14 error=5 origin=cpl3 address=zero contained=1 result=PASS\nLEANOS/10 IPC event=send sender=1 endpoint=10 payload0=1279607118 payload1=20307 accepted=1\nLEANOS/10 IPC event=wake subject=2 ready-insertions=1 reserved=1 result=PASS\nLEANOS/8 PAGING root=B selected=1 result=PASS\nLEANOS/10 IPC event=dispatch subject=2 address-space=2 reservation=owned trusted=1\nLEANOS/10 IPC event=deliver receiver=2 endpoint=10 sender=1 payload0=1279607118 payload1=20307 exact=1 canaries=preserved\nLEANOS/11 ENTRY-HIGH-WATER path=syscall observed-bytes=512 usable-bytes=16384 margin-bytes=15872 authority=diagnostic result=PASS\nLEANOS/10 FINAL status=PASS blocks=1 wakes=1 deliveries=1' \
    "$log"
  if [[ "${LEANOS_BOOT_SCENARIO:-blocking-ipc}" == entry-adversarial ]]; then
    sed -i '/event=dispatch subject=1/a LEANOS/11 ENTRY-ADVERSARIAL attempted-vector=14 delivered=13 privileged-handler=unreached result=PASS\nLEANOS/11 ENTRY-ADVERSARIAL attempted-vector=32 delivered=13 privileged-handler=unreached result=PASS' "$log"
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
legacy-success) echo 'LEANOS/6 BOOT target=x86_64-q35 subjects=2 schedule=one-shot-pit controls=wp,smep,smap' > "$log"; printf '%s\n' 'LEANOS/8 PAGING root=A selected=1 leaves=4096 policy=manifest result=PASS' 'LEANOS/8 PAGING root=B selected=0 leaves=4096 policy=manifest result=PASS' 'LEANOS/8 PAGING fixture=flip-present root=B level=pt page=0 expected=1 actual=0 result=REJECTED' 'LEANOS/8 PAGING fixture=flip-user root=B level=pt page=1 expected=1 actual=5 result=REJECTED' 'LEANOS/8 PAGING fixture=flip-writable root=B level=pt page=2 expected=1 actual=3 result=REJECTED' 'LEANOS/8 PAGING fixture=flip-nx root=B level=pt page=3 expected=1 actual=9223372036854775809 result=REJECTED' 'LEANOS/8 PAGING fixture=wrong-frame root=B level=pt page=0 expected=1 actual=4097 result=REJECTED' 'LEANOS/8 PAGING fixture=ancestor-pointer root=B level=pml4 page=0 expected=8199 actual=12295 result=REJECTED' 'LEANOS/8 PAGING fixture=ancestor-flags root=B level=pdpt page=0 expected=12295 actual=12291 result=REJECTED' 'LEANOS/8 PAGING fixture=swapped-user-leaves root=B level=pt page=4 expected=16389 actual=20481 result=REJECTED' 'LEANOS/8 PAGING fixture=extra-mapping root=B level=pt page=5 expected=0 actual=9223372036854796291 result=REJECTED' 'LEANOS/8 PAGING fixture=entry-guard-mapping root=B level=pt page=6 expected=0 actual=9223372036854800387 result=REJECTED' 'LEANOS/8 PAGING fixture=omitted-mapping root=B level=pt page=4 expected=16389 actual=0 result=REJECTED' 'LEANOS/8 PAGING fixture=wrong-cr3 root=A level=cr3 page=0 expected=4096 actual=8192 result=REJECTED' 'LEANOS/7 HANDOFF magic=valid info-bytes=1024 mmap-entries=8 result=PASS' "LEANOS/7 MAP boot-pages=4096 reported-top-mib=$((memory_mib - 1)) precedence=reserved result=PASS" 'LEANOS/7 ALLOC frame=512 firmware-usable=1 boot-accessible=1 reserved=0 result=PASS' 'LEANOS/7 SCRUB bytes=4096 zero=1 result=PASS' 'LEANOS/7 PUBLISH object=1 owner=1 stale-object=denied result=PASS' 'LEANOS/7 BOOTALLOC status=PASS' >> "$log"; awk -F '\t' '$1 ~ /^[0-9]+$/ { print "LEANOS/3 ORACLE id=" $2 " result=PASS" }' "$LEANOS_ORACLE_CORPUS" >> "$log"; printf '%s\n' 'LEANOS/6 CONTROL cr0.wp=1 cr0.em=1 cr0.mp=1 cr0.ts=1 cr4.osfxsr=0 cr4.osxmmexcpt=0 cr4.osxsave=0 cr4.pke=0 cr4.smep=1 cr4.smap=1 ac=0 stage=exception-path-ready' 'LEANOS/4 PROBE kind=wp vector=14 error=3 origin=kernel address=kernel-text policy=fatal result=PASS' 'LEANOS/4 PROBE kind=smep vector=14 error=17 origin=kernel address=user-a-text policy=fatal result=PASS' 'LEANOS/6 PROBE kind=smap-direct vector=14 origin=kernel ac=0 result=PASS' 'LEANOS/6 POLICY zero=accept max=accept unmapped=reject readonly=reject overflow=reject noncanonical=reject wrong-subject=reject stale=reject atomic=PASS' 'LEANOS/6 CLEANUP omitted=detected wrappers=checked entry=clac result=PASS' 'LEANOS/6 COPY direction=in length=4 cross-page=1 validated=1 user-df=1 kernel-df=cleared ac=cleared result=PASS' 'LEANOS/6 COPY direction=out length=4 cross-page=0 validated=1 user-df=1 kernel-df=cleared destination=verified-by-cpl3 ac=cleared result=PASS' 'LEANOS/5 ENTRY subject=1 address-space=1 cpl=3 yielding=0' 'LEANOS/5 TIMER vector=32 source=pit mode=one-shot origin=cpl3 accepted=1' 'LEANOS/5 CONTEXT old-subject=1 old-address-space=1 new-subject=2 new-address-space=2 policy=round-robin' 'LEANOS/8 PAGING root=B selected=1 result=PASS' 'LEANOS/5 SWITCH subject=2 address-space=2 cr3=switched stack=restored ticks-masked=1' 'LEANOS/5 SYSCALL subject=2 caller=2 address-space=2 authorized=1 canaries=preserved' 'LEANOS/5 FINAL status=PASS ticks=1' >> "$log"; exit 33;;
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
