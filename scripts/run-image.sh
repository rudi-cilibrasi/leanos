#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$repo_root"
source "$repo_root/scripts/q35-platform.sh"
qemu="${LEANOS_QEMU:-qemu-system-x86_64}"
limit="${LEANOS_QEMU_TIMEOUT_SECONDS:-30}"
version="${LEANOS_VERSION:-0.1.0}"
scenario="${LEANOS_BOOT_SCENARIO:-blocking-ipc}"
fault_scenario=0
stale_translation_scenario=0
extended_instruction=x87
extended_vector=7
if [[ "$scenario" == fast-entry-syscall ]]; then
  extended_instruction=syscall
  extended_vector=6
  default_image="build/boot/leanos-${version}-x86_64-fast-entry-syscall.iso"
elif [[ "$scenario" == fast-entry-sysenter ]]; then
  extended_instruction=sysenter
  extended_vector=6
  default_image="build/boot/leanos-${version}-x86_64-fast-entry-sysenter.iso"
elif [[ "$scenario" == extended-state-avx ]]; then
  extended_instruction=avx
  extended_vector=6
  default_image="build/boot/leanos-${version}-x86_64-extended-state-avx.iso"
elif [[ "$scenario" == extended-state-sse2 ]]; then
  extended_instruction=sse2
  extended_vector=6
  default_image="build/boot/leanos-${version}-x86_64-extended-state-sse2.iso"
elif [[ "$scenario" == extended-state-sse ]]; then
  extended_instruction=sse
  extended_vector=6
  default_image="build/boot/leanos-${version}-x86_64-extended-state-sse.iso"
elif [[ "$scenario" == extended-state-mmx ]]; then
  extended_instruction=mmx
  default_image="build/boot/leanos-${version}-x86_64-extended-state-mmx.iso"
elif [[ "$scenario" == extended-state ]]; then
  default_image="build/boot/leanos-${version}-x86_64-extended-state.iso"
elif [[ "$scenario" == preemption ]]; then
  default_image="build/boot/leanos-${version}-x86_64-preemption.iso"
elif [[ "$scenario" == stale-translation-denial ]]; then
  stale_translation_scenario=1
  default_image="build/boot/leanos-${version}-x86_64-fault-stale-translation.iso"
  stale_translation_elf="build/boot/leanos-fault-stale-translation.elf"
elif [[ "$scenario" == frame-budget ]]; then
  default_image="build/boot/leanos-${version}-x86_64-frame-budget.iso"
elif [[ "$scenario" == fault-containment ]]; then
  fault_scenario=1
  fault_probe=supervisor-read
  default_image="build/boot/leanos-${version}-x86_64-fault-containment.iso"
elif [[ "$scenario" == fault-readonly-write ]]; then
  fault_scenario=1
  fault_probe=readonly-write
  default_image="build/boot/leanos-${version}-x86_64-fault-readonly-write.iso"
elif [[ "$scenario" == fault-nx-execute ]]; then
  fault_scenario=1
  fault_probe=nx-execute
  default_image="build/boot/leanos-${version}-x86_64-fault-nx-execute.iso"
elif [[ "$scenario" == entry-adversarial ]]; then
  default_image="build/boot/leanos-${version}-x86_64-entry-adversarial.iso"
elif [[ "$scenario" == direct-port-serial ]]; then
  direct_port_probe_name=serial-out; direct_port_port=1016; direct_port_dir=out
  default_image="build/boot/leanos-${version}-x86_64-direct-port-serial.iso"
elif [[ "$scenario" == direct-port-debug ]]; then
  direct_port_probe_name=debug-exit; direct_port_port=244; direct_port_dir=out
  default_image="build/boot/leanos-${version}-x86_64-direct-port-debug.iso"
elif [[ "$scenario" == direct-port-in ]]; then
  direct_port_probe_name=serial-in; direct_port_port=1021; direct_port_dir=in
  default_image="build/boot/leanos-${version}-x86_64-direct-port-in.iso"
elif [[ "$scenario" == direct-port-pic ]]; then
  direct_port_probe_name=pic-mask; direct_port_port=33; direct_port_dir=out
  default_image="build/boot/leanos-${version}-x86_64-direct-port-pic.iso"
elif [[ "$scenario" == divide-error ]]; then
  integer_fault_kind=divide-error; integer_fault_vector=0
  integer_fault_saved_rip=faulting-instruction; integer_fault_upper=DIVIDE-ERROR
  default_image="build/boot/leanos-${version}-x86_64-divide-error.iso"
elif [[ "$scenario" == breakpoint ]]; then
  integer_fault_kind=breakpoint; integer_fault_vector=3
  integer_fault_saved_rip=post-instruction; integer_fault_upper=BREAKPOINT
  default_image="build/boot/leanos-${version}-x86_64-breakpoint.iso"
else
  default_image="build/boot/leanos-${version}-x86_64.iso"
fi
image="${1:-$default_image}"
log="${LEANOS_SERIAL_LOG:-build/boot/serial.log}"
dma_snapshot="${LEANOS_DMA_SNAPSHOT:-build/boot/dma-quarantine-snapshot-${scenario}.tsv}"
source_revision_file="${LEANOS_SOURCE_REVISION_FILE:-build/boot/SOURCE_REVISION}"
high_water_artifact="${LEANOS_ENTRY_HIGH_WATER_ARTIFACT:-build/boot/entry-stack-high-water-${scenario}.txt}"
fault_snapshot_artifact="${LEANOS_FAULT_SNAPSHOT_ARTIFACT:-build/boot/${scenario}-snapshot.txt}"
fault_elf="${LEANOS_FAULT_CONTAINMENT_ELF:-${stale_translation_elf:-build/boot/leanos-${scenario}.elf}}"
memory_mib="${LEANOS_QEMU_MEMORY_MIB:-128}"
for tool in "$qemu" timeout; do command -v "$tool" >/dev/null 2>&1 || { echo "error: missing required tool '$tool'; install qemu-system-x86=1:8.2.2+ds-0ubuntu1.18 and coreutils=9.4-3ubuntu6.2" >&2; exit 1; }; done
[[ "$limit" =~ ^[1-9][0-9]*$ ]] || { echo "error: timeout must be a positive integer" >&2; exit 1; }
[[ "$memory_mib" =~ ^(64|128)$ ]] || { echo "error: memory must be one of the checked configurations: 64 or 128 MiB" >&2; exit 1; }
reported_top_mib=$((memory_mib - 1))
[[ -f "$image" ]] || { echo "error: image '$image' not found; run ./scripts/build-image.sh first" >&2; exit 1; }
if (( fault_scenario || stale_translation_scenario )); then
  [[ -f "$fault_elf" ]] || {
    echo "error: fault final ELF '$fault_elf' not found; run ./scripts/build-image.sh first" >&2
    exit 1
  }
  symbol_value() {
    local symbol="$1" address
    address="$(nm -n "$fault_elf" | awk -v wanted="$symbol" '$3 == wanted { print $1 }')"
    [[ "$address" =~ ^[[:xdigit:]]+$ ]] || return 1
    printf '%u' "$((16#$address))"
  }
fi
if (( fault_scenario )); then
  fault_cr3="$(symbol_value page_map_level_4_a)" &&
    fault_rsp="$(symbol_value user_a_stack_top)" || {
    echo "error: required fault final-ELF symbol missing" >&2
    exit 1
  }
  if [[ "$fault_probe" == nx-execute ]]; then
    fault_error=21
    fault_access=execute
    fault_access_code=2
    fault_rip_label=user-a-nx-fault-instruction
    fault_rip="$(symbol_value user_a_nx_fault_instruction)"
    fault_address="$fault_rip"
    fault_page=$((fault_address / 4096))
    printf -v fault_leaf '%u' \
      "$(( (1 << 63) + fault_page * 4096 + 7 ))"
    fault_cause=no-execute
    fault_canary=' payload-canary=armed'
  elif [[ "$fault_probe" == readonly-write ]]; then
    fault_error=7
    fault_access=write
    fault_access_code=1
    fault_rip_label=user-a-write-fault-instruction
    fault_rip="$(symbol_value user_a_write_fault_instruction)"
    fault_address="$(symbol_value user_a_write_target)"
    fault_page=$((fault_address / 4096))
    fault_leaf=$((fault_page * 4096 + 5))
    fault_cause=not-writable
    fault_canary=' write-canary=unchanged'
  else
    fault_error=5
    fault_access=read
    fault_access_code=0
    fault_rip_label=user-a-fault-instruction
    fault_rip="$(symbol_value user_a_fault_instruction)"
    fault_address=0
    fault_page=0
    fault_leaf=9223372036854775811
    fault_cause=supervisor
    fault_canary=
  fi
elif (( stale_translation_scenario )); then
  stale_translation_cr3="$(symbol_value page_map_level_4_b)" &&
    stale_translation_rip="$(
      symbol_value user_b_stale_translation_fault_instruction
    )" &&
    stale_translation_rsp="$(symbol_value user_b_stack_top)" || {
    echo "error: required stale-translation final-ELF symbol missing" >&2
    exit 1
  }
fi
mkdir -p "$(dirname "$log")"; : > "$log"
command=()
leanos_q35_command command "$qemu" "$memory_mib" "$log" "$image"
qemu_version="$($qemu --version 2>&1 | head -n 1 || true)"
printf 'QEMU version: %s\nQEMU command:' "${qemu_version:-unknown}" >&2; printf ' %q' "${command[@]}" >&2; printf '\nSerial log: %s\n' "$log" >&2
set +e; timeout --signal=TERM --kill-after=2s "${limit}s" "${command[@]}"; status=$?; set -e
expected="$(mktemp)"; without_allocation="$(mktemp)"
trap 'rm -f "$expected" "$without_allocation"' EXIT
corpus="${LEANOS_ORACLE_CORPUS:-build/boot/corpus.tsv}"
[[ -f "$corpus" ]] || { echo "error: oracle corpus '$corpus' not found" >&2; exit 1; }
if [[ "$scenario" == fast-entry-syscall || "$scenario" == fast-entry-sysenter ]]; then
  echo 'LEANOS/14 BOOT target=x86_64-q35 subjects=2 schedule=fast-entry-denial controls=wp,smep,smap,em,mp,ts,sce-off' > "$expected"
elif [[ "$scenario" == extended-state || "$scenario" == extended-state-mmx ||
      "$scenario" == extended-state-sse || "$scenario" == extended-state-sse2 ||
      "$scenario" == extended-state-avx ]]; then
  echo 'LEANOS/13 BOOT target=x86_64-q35 subjects=2 schedule=extended-state-denial controls=wp,smep,smap,em,mp,ts' > "$expected"
elif [[ "$scenario" == preemption ]]; then
  echo 'LEANOS/6 BOOT target=x86_64-q35 subjects=2 schedule=bounded-two-shot-pit controls=wp,smep,smap' > "$expected"
elif [[ "$scenario" == stale-translation-denial ]]; then
  echo 'LEANOS/19 BOOT target=x86_64-q35 subjects=2 schedule=stale-translation-denial probe=cpl3-unmap-read contract=v1 controls=wp,smep,smap,pcid-off' > "$expected"
elif [[ "$scenario" == frame-budget ]]; then
  echo 'LEANOS/20 BOOT target=x86_64-q35 subjects=2 schedule=frame-budget-v2 budgets=a:1,b:2 controls=wp,smep,smap' > "$expected"
elif (( fault_scenario )); then
  echo "LEANOS/14 BOOT target=x86_64-q35 subjects=2 schedule=fault-containment probe=${fault_probe} contract=v1 controls=wp,smep,smap" > "$expected"
elif [[ "$scenario" == direct-port-serial || "$scenario" == direct-port-debug ||
      "$scenario" == direct-port-in || "$scenario" == direct-port-pic ]]; then
  echo "LEANOS/16 BOOT target=x86_64-q35 subjects=2 schedule=direct-port-containment probe=${direct_port_probe_name} contract=v1 controls=wp,smep,smap" > "$expected"
elif [[ "$scenario" == divide-error || "$scenario" == breakpoint ]]; then
  echo "LEANOS/18 BOOT target=x86_64-q35 subjects=2 schedule=integer-fault-containment probe=${integer_fault_kind} contract=v1 controls=wp,smep,smap" > "$expected"
else
  echo 'LEANOS/10 BOOT target=x86_64-q35 subjects=2 schedule=blocking-ipc controls=wp,smep,smap' > "$expected"
fi
echo 'LEANOS/15 DMA snapshot=1 topology=0001000800020002 bus=0 scanned=256 present=5 optional-absent=1 writes=5 readbacks=5 initial-bus-masters=1 initial-bus-master-mask=16 bus-master=disabled readback=exact generated-result=0 stage=pre-cpl3 result=PASS' >> "$expected"
printf '%s\n' \
  'LEANOS/8 PAGING root=A selected=1 leaves=4096 policy=manifest result=PASS' \
  'LEANOS/8 PAGING root=B selected=0 leaves=4096 policy=manifest result=PASS' \
  'LEANOS/19 TLB path=invlpg address-space=2 page=7 pte=cleared order=store,invlpg,publish before=309063438 after=308959202 result=PASS' \
  'LEANOS/19 TLB path=cr3 address-space=2 page=7 pte=cleared order=store,cr3,publish before=309063438 after=308959202 result=PASS' \
  'LEANOS/19 TLB authority=generated-composite effect=page address-space=2 page=7 window=restored result=PASS' \
  'LEANOS/19 TLB mutable-leaf=checked address-space=2 page=7 states=boot,before,unmapped,after immutable-leaves=exact result=PASS' >> "$expected"
if [[ "$scenario" == frame-budget ]]; then
  frame_budget_boot_physical="$(
    sed -n 's|^LEANOS/7 ALLOC frame=\([0-9][0-9]*\) .*|\1|p' "$log"
  )"
  frame_budget_physical="$(
    sed -n 's|^LEANOS/20 FRAME physical-frame=\([0-9][0-9]*\) .*|\1|p' "$log"
  )"
  [[ "$frame_budget_boot_physical" =~ ^[0-9]+$ &&
     "$frame_budget_physical" =~ ^[0-9]+$ ]] || {
    echo "failure_class=serial-protocol: missing unique boot/scenario physical-frame binding" >&2
    exit 1
  }
  if [[ "$frame_budget_physical" == "$frame_budget_boot_physical" ]]; then
    echo "failure_class=serial-protocol: frame-budget scenario double-published live boot frame" >&2
    exit 1
  fi
  echo "LEANOS/20 FRAME physical-frame=${frame_budget_physical} boot-published-frame=${frame_budget_boot_physical} prior-publications=0 distinct=1 source=scalar-stream-projection result=PASS" >> "$expected"
fi
awk -F '\t' '$1 ~ /^[0-9]+$/ { print "LEANOS/3 ORACLE id=" $2 " result=PASS" }' "$corpus" >> "$expected"
echo 'LEANOS/17 ENTRY-MANIFEST ordinary=8 extended=6,7 contained=0,3 auxiliary=1 terminal=2 extra=0 rsp0=entry-stack ist1=df-stack ist2=nmi-stack result=PASS' >> "$expected"
echo 'LEANOS/16 DIRECT-PORT-CONTROL tr=40 limit=103 iomap=104 bitmap=absent iopl=0 stage=pre-cpl3 result=PASS' >> "$expected"
if [[ "$scenario" == fast-entry-syscall || "$scenario" == fast-entry-sysenter ]]; then
  echo 'LEANOS/14 FAST-ENTRY cpu.vendor=AuthenticAMD mode=long64 syscall=1 sysenter=1 efer.sce=0 star=0 lstar=0 cstar=0 sfmask=0 sysenter.cs=0 sysenter.esp=0 sysenter.eip=0 writes=complete readback=exact result=PASS' >> "$expected"
  echo 'LEANOS/13 EXTENDED-STATE cpuid.1.x87=1 cpuid.1.mmx=1 cpuid.1.sse=1 cpuid.1.sse2=1 cpuid.1.xsave=1 cpuid.1.osxsave=0 cpuid.1.avx=1 cpu=max result=PASS' >> "$expected"
elif [[ "$scenario" == extended-state || "$scenario" == extended-state-mmx ||
      "$scenario" == extended-state-sse || "$scenario" == extended-state-sse2 ||
      "$scenario" == extended-state-avx ]]; then
  echo 'LEANOS/13 EXTENDED-STATE cpuid.1.x87=1 cpuid.1.mmx=1 cpuid.1.sse=1 cpuid.1.sse2=1 cpuid.1.xsave=1 cpuid.1.osxsave=0 cpuid.1.avx=1 cpu=max result=PASS' >> "$expected"
fi
printf '%s\n' \
  'LEANOS/6 CONTROL cr0.wp=1 cr0.em=1 cr0.mp=1 cr0.ts=1 cr4.osfxsr=0 cr4.osxmmexcpt=0 cr4.osxsave=0 cr4.pke=0 cr4.smep=1 cr4.smap=1 ac=0 stage=exception-path-ready' \
  'LEANOS/4 PROBE kind=wp vector=14 error=3 origin=kernel address=kernel-text policy=fatal result=PASS' \
  'LEANOS/4 PROBE kind=smep vector=14 error=17 origin=kernel address=user-a-text policy=fatal result=PASS' \
  'LEANOS/6 PROBE kind=smap-direct vector=14 origin=kernel ac=0 result=PASS' \
  'LEANOS/6 POLICY zero=accept max=accept unmapped=reject readonly=reject overflow=reject noncanonical=reject wrong-subject=reject stale=reject atomic=PASS' \
  'LEANOS/6 CLEANUP omitted=detected wrappers=checked entry=clac result=PASS' >> "$expected"
if [[ "$scenario" == fast-entry-syscall || "$scenario" == fast-entry-sysenter ]]; then
printf '%s\n' \
  "LEANOS/14 FAST-ENTRY event=enter subject=1 address-space=1 instruction=${extended_instruction} expected-vector=6" \
  "LEANOS/14 FAST-ENTRY event=deny subject=1 vector=6 instruction=${extended_instruction} alternate-target=unreached cleanup=complete peer=2" \
  'LEANOS/14 FAST-ENTRY event=peer subject=2 address-space=2 cpl=3 return=validated controls=denied gpr-canaries=preserved' \
  'LEANOS/14 FINAL status=PASS denied=1 resumed-a=0 peer-ran=1 alternate-target=0' >> "$expected"
elif [[ "$scenario" == extended-state || "$scenario" == extended-state-mmx ||
      "$scenario" == extended-state-sse || "$scenario" == extended-state-sse2 ||
      "$scenario" == extended-state-avx ]]; then
printf '%s\n' \
  "LEANOS/13 EXTENDED-STATE event=enter subject=1 address-space=1 instruction=${extended_instruction} expected-vector=${extended_vector}" \
  "LEANOS/13 EXTENDED-STATE event=deny subject=1 vector=${extended_vector} instruction=${extended_instruction} bank-write=prevented cleanup=complete peer=2" \
  'LEANOS/13 EXTENDED-STATE event=peer subject=2 address-space=2 cpl=3 return=validated controls=denied gpr-canaries=preserved' \
  'LEANOS/13 FINAL status=PASS denied=1 resumed-a=0 peer-ran=1' >> "$expected"
elif (( fault_scenario )); then
printf '%s\n' \
  'LEANOS/8 PAGING root=A selected=1 resumed=1 result=PASS' \
  'LEANOS/14 ENTER subject=1 address-space=1 cpl=3 resources=owned' \
  "LEANOS/14 PF-WALK page=${fault_page} expected-leaf=${fault_leaf} live-leaf=${fault_leaf} cause=${fault_cause} denial=${fault_cause} result=PASS" \
  "LEANOS/14 FAULT-ENTRY vector=14 error=${fault_error} access=${fault_access} protection=1 cr2=${fault_address} rip=${fault_rip_label} origin=cpl3 hardware=1 direct-call=0 subject=1 address-space=1 dispatch=0x00000000ff020202 cleanup=31 survivor=2${fault_canary} result=PASS" \
  'LEANOS/14 TERMINATE subject=1 live=0 runnable=0 current=0 queued=0 resumable=0 resources=cap,memory,mapping,endpoint result=PASS' \
  'LEANOS/14 DISPATCH subject=2 address-space=2 source=lean-scheduler context=owned result=PASS' \
  'LEANOS/8 PAGING root=B selected=1 result=PASS' \
  'LEANOS/14 PEER subject=2 address-space=2 stack=owned return=validated canaries=preserved resources=unchanged result=PASS' \
  'LEANOS/14 FINAL status=PASS faulting=terminated survivor=2 kernel-origin=fail-stop' >> "$expected"
elif [[ "$scenario" == direct-port-serial || "$scenario" == direct-port-debug ||
      "$scenario" == direct-port-in || "$scenario" == direct-port-pic ]]; then
printf '%s\n' \
  'LEANOS/8 PAGING root=A selected=1 resumed=1 result=PASS' \
  'LEANOS/16 ENTER subject=1 address-space=1 cpl=3 resources=owned' \
  "LEANOS/16 DIRECT-PORT-DENIAL subject=1 vector=13 error=0 origin=cpl3 port=${direct_port_port} direction=${direct_port_dir} width=byte purpose=user device-mutation=0 result=PASS" \
  'LEANOS/16 DIRECT-PORT-TERMINATE subject=1 live=0 runnable=0 current=0 queued=0 resumable=0 resources=cap,memory,mapping,endpoint result=PASS' \
  'LEANOS/16 DIRECT-PORT-DISPATCH subject=2 address-space=2 source=lean-scheduler context=owned result=PASS' \
  'LEANOS/8 PAGING root=B selected=1 result=PASS' >> "$expected"
if [[ "$scenario" == direct-port-pic ]]; then
  echo 'LEANOS/16 DIRECT-PORT-CANARY register=pic-mask port=33 programmed=255 observed=255 device-mutation=0 result=PASS' >> "$expected"
fi
printf '%s\n' \
  'LEANOS/16 DIRECT-PORT-PEER subject=2 address-space=2 stack=owned return=validated canaries=preserved resources=unchanged result=PASS' \
  'LEANOS/16 FINAL status=PASS denied=1 resumed-a=0 peer-ran=1 device-mutation=0' >> "$expected"
elif [[ "$scenario" == divide-error || "$scenario" == breakpoint ]]; then
printf '%s\n' \
  'LEANOS/8 PAGING root=A selected=1 resumed=1 result=PASS' \
  'LEANOS/18 ENTER subject=1 address-space=1 cpl=3 resources=owned' \
  "LEANOS/18 ${integer_fault_upper}-ENTRY vector=${integer_fault_vector} error=none origin=cpl3 hardware=1 direct-call=0 saved-rip=${integer_fault_saved_rip} subject=1 address-space=1 result=PASS" \
  "LEANOS/18 ${integer_fault_upper}-TERMINATE subject=1 live=0 runnable=0 current=0 queued=0 resumable=0 resources=cap,memory,mapping,endpoint result=PASS" \
  "LEANOS/18 ${integer_fault_upper}-DISPATCH subject=2 address-space=2 source=lean-scheduler context=owned reason=${integer_fault_kind} result=PASS" \
  'LEANOS/8 PAGING root=B selected=1 result=PASS' \
  "LEANOS/18 ${integer_fault_upper}-PEER subject=2 address-space=2 stack=owned return=validated canaries=preserved resources=unchanged result=PASS" \
  "LEANOS/18 FINAL status=PASS faulting=terminated survivor=2 vector=${integer_fault_vector} reason=${integer_fault_kind} kernel-origin=fail-stop" >> "$expected"
elif [[ "$scenario" == frame-budget ]]; then
printf '%s\n' \
  'LEANOS/8 PAGING root=A selected=1 resumed=1 result=PASS' \
  'LEANOS/20 ENTER subject=1 address-space=1 cpl=3 budget=1 usage=0' \
  "LEANOS/20 A-ALLOC subject=1 address-space=1 budget=1 usage=1 object=10 handle=65536 physical-frame=${frame_budget_physical} user-page=4095 source=generated-mapping prior-publications=0 accepted=1" \
  'LEANOS/20 A-REJECT subject=1 reason=budgetExhausted budget=1 usage=1 object=none capability=none mapping=none state=unchanged digest=0x4201' \
  'LEANOS/20 DISPATCH subject=2 address-space=2 source=generated-current result=PASS' \
  'LEANOS/20 B-CONTEXT subject=2 source=kernel-owned-fresh registers=15 canaries=fresh result=PASS' \
  'LEANOS/20 B-ALLOC subject=2 address-space=2 budget=2 usage=1 object=20 handle=131072 peer-a-usage=1 accepted=1' \
  'LEANOS/20 CLEANUP subject=1 operation=terminate objects=1 mappings=1 capacity-restored=1 repeated-credit=0 effect=flush invalidation=cr3 order=store,cr3,ack,publish checked=1' \
  "LEANOS/20 SCRUB physical-frame=${frame_budget_physical} bytes=4096 complete=1 before-publication=1" \
  "LEANOS/20 B-PUBLISH subject=2 object=21 handle=196609 generation=3 physical-frame=${frame_budget_physical} user-page=4095 source=generated-mapping fresh-lifetime=1" \
  'LEANOS/20 STALE handle=65536 old-subject=1 fresh-object=21 authorized=0 reason=stale-generation' \
  'LEANOS/20 CANARY subject=2 origin=cpl3 access=direct first=0 last=0 old=165 denied=1 result=PASS' \
  'LEANOS/20 FINAL status=PASS a-exhausted=1 b-available=1 cleanup=1 scrub=1 fresh=1 stale-denied=1 ring3-reuse=1' >> "$expected"
elif [[ "$scenario" == preemption ]]; then
printf '%s\n' \
  'LEANOS/6 COPY direction=in length=4 cross-page=1 validated=1 user-df=1 kernel-df=cleared ac=cleared result=PASS' \
  'LEANOS/6 COPY direction=out length=4 cross-page=0 validated=1 user-df=1 kernel-df=cleared destination=verified-by-cpl3 ac=cleared result=PASS' \
  'LEANOS/11 USER-FAULT vector=14 error=5 origin=cpl3 address=zero contained=1 result=PASS' \
  'LEANOS/5 ENTRY subject=1 address-space=1 cpl=3 yielding=0' \
  'LEANOS/5 TIMER vector=32 source=pit mode=bounded-one-shot sequence=1 origin=cpl3 accepted=1' \
  'LEANOS/5 CONTEXT old-subject=1 old-address-space=1 new-subject=2 new-address-space=2 policy=round-robin' \
  'LEANOS/8 PAGING root=B selected=1 result=PASS' \
  'LEANOS/5 SWITCH subject=2 address-space=2 cr3=switched stack=initial contexts=separate' \
  'LEANOS/5 SYSCALL subject=2 caller=2 address-space=2 authorized=1 canaries=preserved' \
  'LEANOS/5 TIMER vector=32 source=pit mode=bounded-one-shot sequence=2 origin=cpl3 accepted=1' \
  'LEANOS/5 CONTEXT old-subject=2 old-address-space=2 new-subject=1 new-address-space=1 policy=round-robin' \
  'LEANOS/8 PAGING root=A selected=1 resumed=1 result=PASS' \
  'LEANOS/5 SWITCH subject=1 address-space=1 cr3=switched stack=resumed contexts=separate' \
  'LEANOS/5 RESUME subject=1 caller=1 address-space=1 frame=original canaries=preserved contexts=separate' \
  'LEANOS/5 FINAL status=PASS ticks=2' >> "$expected"
elif [[ "$scenario" == stale-translation-denial ]]; then
printf '%s\n' \
  'LEANOS/8 PAGING root=B selected=1 result=PASS' \
  'LEANOS/19 ENTER subject=2 address-space=2 cpl=3 mapping=page7-present-user canary=309063438' \
  'LEANOS/19 TLB-CPL3 event=prefill subject=2 address-space=2 page=7 address=28672 access=read canary=309063438 leaf=present-user result=PASS' \
  'LEANOS/19 TLB-CPL3 event=unmap subject=2 address-space=2 page=7 pte=absent effect=page invalidation=invlpg cr3-reload=0 order=store,invlpg,publish result=PASS' \
  'LEANOS/19 TLB-CPL3 event=reuse frame=same old-owner=2 old-lifetime=1 new-owner=1 new-lifetime=2 old-address-space=2 old-page=7 old-pte=absent new-address-space=1 new-page=7 new-pte=present-user scrub=complete canary=308959202 model=post-reuse-old-page-absent order=unmap,invlpg,publish-unmap,scrub,allocate,write-canary,map-new-owner,publish-reuse result=PASS' \
  'LEANOS/14 PF-WALK page=7 expected-leaf=0 live-leaf=0 cause=supervisor denial=supervisor result=PASS' \
  "LEANOS/14 PF-SNAPSHOT codec=1 width=19 words=1,14,4,28672,7,0,0,1,2,2,${stale_translation_cr3},15,${stale_translation_rip},35,582,${stale_translation_rsp},27,1,0 authorization=1 route=72057594037927937 result=PASS" \
  'LEANOS/19 TLB-CPL3 event=denial vector=14 error=4 origin=cpl3 hardware=1 direct-call=0 subject=2 address-space=2 cr2=28672 page=7 access=read protection=0 pte=absent replacement-owner=1 replacement-lifetime=2 replacement-canary=308959202 replacement-canary-intact=1 route=contain handoff=new-owner cr3-reload-since-unmap=0 result=PASS' \
  'LEANOS/19 TLB-CPL3 event=new-owner-read subject=1 address-space=1 page=7 address=28672 access=read frame=same lifetime=2 canary=308959202 old-address-space=2 old-pte=absent result=PASS' \
  'LEANOS/19 FINAL status=PASS prefill=1 accepted-unmap=1 exact-invlpg=1 same-frame-reuse=1 scrub=complete new-owner-cpl3-read=1 replacement-canary=intact stale-access=page-fault old-observation=denied containment=1 incidental-cr3-reload=0' >> "$expected"
else
printf '%s\n' \
  'LEANOS/8 PAGING root=B selected=1 result=PASS' \
  'LEANOS/10 IPC event=enter subject=2 address-space=2 cpl=3 endpoint=10' \
  'LEANOS/9 CAPREUSE event=initial subject=2 handle=131072 endpoint=10 accepted=1' \
  'LEANOS/9 CAPREUSE event=clear slot=0 old-generation=2 result=PASS' \
  'LEANOS/9 CAPREUSE event=install slot=0 generation=3 endpoint=11 result=PASS' \
  'LEANOS/9 CAPREUSE event=stale-replay subject=2 handle=131072 rejected=1' \
  'LEANOS/9 CAPREUSE event=unchanged endpoint=11 mailbox=empty result=PASS' \
  'LEANOS/9 CAPREUSE event=fresh subject=2 handle=196608 endpoint=11 accepted=1' \
  'LEANOS/9 CAPREUSE status=PASS stale-effects=0 fresh-effects=1' \
  'LEANOS/10 IPC event=block subject=2 endpoint=10 empty=1 runnable=0 result=PASS' \
  'LEANOS/8 PAGING root=A selected=1 resumed=1 result=PASS' \
  'LEANOS/10 IPC event=dispatch subject=1 address-space=1 blocked-subject=2 trusted=1' \
  >> "$expected"
if [[ "$scenario" == entry-adversarial ]]; then
printf '%s\n' \
  'LEANOS/11 ENTRY-ADVERSARIAL attempted-vector=14 delivered=13 privileged-handler=unreached result=PASS' \
  'LEANOS/11 ENTRY-ADVERSARIAL attempted-vector=32 delivered=13 privileged-handler=unreached result=PASS' \
  'LEANOS/16 DIRECT-PORT-DENIAL subject=1 vector=13 error=0 origin=cpl3 port=244 direction=out width=byte purpose=user device-mutation=0 result=PASS' \
  'LEANOS/16 DIRECT-PORT-TERMINATE subject=1 live=0 runnable=0 current=0 queued=0 resumable=0 resources=cap,memory,mapping,endpoint result=PASS' \
  'LEANOS/16 DIRECT-PORT-DISPATCH subject=2 address-space=2 source=lean-scheduler context=owned result=PASS' \
  'LEANOS/8 PAGING root=B selected=1 result=PASS' \
  'LEANOS/16 DIRECT-PORT-PEER subject=2 address-space=2 stack=owned return=validated canaries=preserved resources=unchanged result=PASS' \
  'LEANOS/16 FINAL status=PASS denied=1 resumed-a=0 peer-ran=1 device-mutation=0' \
  >> "$expected"
else
printf '%s\n' \
  'LEANOS/6 COPY direction=in length=4 cross-page=1 validated=1 user-df=1 kernel-df=cleared ac=cleared result=PASS' \
  'LEANOS/6 COPY direction=out length=4 cross-page=0 validated=1 user-df=1 kernel-df=cleared destination=verified-by-cpl3 ac=cleared result=PASS' \
  'LEANOS/11 USER-FAULT vector=14 error=5 origin=cpl3 address=zero contained=1 result=PASS' \
  'LEANOS/10 IPC event=send sender=1 endpoint=10 payload0=1279607118 payload1=20307 accepted=1' \
  'LEANOS/10 IPC event=wake subject=2 ready-insertions=1 reserved=1 result=PASS' \
  'LEANOS/8 PAGING root=B selected=1 result=PASS' \
  'LEANOS/10 IPC event=dispatch subject=2 address-space=2 reservation=owned trusted=1' \
  'LEANOS/10 IPC event=deliver receiver=2 endpoint=10 sender=1 payload0=1279607118 payload1=20307 exact=1 canaries=preserved' \
  'LEANOS/10 FINAL status=PASS blocks=1 wakes=1 deliveries=1' >> "$expected"
fi
fi
if [[ $status -eq 124 || $status -eq 137 ]]; then echo "failure_class=timeout: QEMU exceeded ${limit}s wall limit" >&2; exit 1; fi
if [[ $status -eq 35 ]]; then echo "failure_class=guest-error: guest emitted failure signal" >&2; exit 1; fi
if [[ $status -ne 33 ]]; then echo "failure_class=qemu-error: QEMU exit status $status (expected 33)" >&2; exit 1; fi
allocation_trace="$(awk '/^LEANOS\/7 /' "$log")"
mapfile -t allocation_lines <<<"$allocation_trace"
if [[ ${#allocation_lines[@]} -ne 6 ]] ||
   [[ ! "${allocation_lines[0]}" =~ ^LEANOS/7\ HANDOFF\ magic=valid\ info-bytes=[1-9][0-9]*\ mmap-entries=[1-9][0-9]*\ result=PASS$ ]] ||
   [[ "${allocation_lines[1]}" != "LEANOS/7 MAP boot-pages=4096 reported-top-mib=${reported_top_mib} precedence=reserved result=PASS" ]] ||
   [[ ! "${allocation_lines[2]}" =~ ^LEANOS/7\ ALLOC\ frame=[0-9]+\ firmware-usable=1\ boot-accessible=1\ reserved=0\ projection=scalar-checked\ result=PASS$ ]] ||
   [[ "${allocation_lines[3]}" != 'LEANOS/7 SCRUB bytes=4096 zero=1 result=PASS' ]] ||
   [[ "${allocation_lines[4]}" != 'LEANOS/7 PUBLISH object=1 owner=1 stale-object=denied result=PASS' ]] ||
   [[ "${allocation_lines[5]}" != 'LEANOS/7 BOOTALLOC status=PASS' ]]; then
  echo "failure_class=boot-allocation-trace: exact ordered allocation protocol not observed" >&2
  exit 1
fi
mapfile -t paging_fixtures < <(grep '^LEANOS/8 PAGING fixture=' "$log")
paging_specs=(
  'flip-present B pt' 'flip-user B pt' 'flip-writable B pt'
  'flip-nx B pt' 'wrong-frame B pt' 'ancestor-pointer B pml4'
  'ancestor-flags B pdpt' 'swapped-user-leaves B pt'
  'extra-mapping B pt' 'nmi-guard-mapping B pt' 'entry-guard-mapping B pt'
  'omitted-mapping B pt' 'mutable-wrong-frame B pt'
  'mutable-publish-before-invalidation B pt' 'mutable-unknown-state B pt'
  'wrong-cr3 A cr3'
)
if [[ ${#paging_fixtures[@]} -ne ${#paging_specs[@]} ]]; then
  echo "failure_class=page-table-fixtures: complete live-mutation matrix not observed" >&2
  exit 1
fi
for ((i = 0; i < ${#paging_specs[@]}; ++i)); do
  read -r name root_name level <<< "${paging_specs[i]}"
  if [[ ! "${paging_fixtures[i]}" =~ ^LEANOS/8\ PAGING\ fixture=${name}\ root=${root_name}\ level=${level}\ page=[0-9]+\ expected=[0-9]+\ actual=[0-9]+\ result=REJECTED$ ]]; then
    echo "failure_class=page-table-fixtures: invalid or reordered fixture '${paging_fixtures[i]}'" >&2
    exit 1
  fi
done
sed -e '/^LEANOS\/7 /d' -e '/^LEANOS\/8 PAGING fixture=/d' \
  -e '/^LEANOS\/15 DMA-FUNCTION /d' "$log" > "$without_allocation"
if (( fault_scenario )); then
  mkdir -p "$(dirname "$fault_snapshot_artifact")"
  grep '^LEANOS/14 PF-SNAPSHOT ' "$log" > "$fault_snapshot_artifact" || {
    echo "failure_class=page-fault-snapshot: canonical snapshot missing" >&2
    exit 1
  }
  mapfile -t fault_snapshot_lines < "$fault_snapshot_artifact"
  if [[ ${#fault_snapshot_lines[@]} -ne 1 ]]; then
    echo "failure_class=page-fault-snapshot: snapshot missing or duplicated" >&2
    exit 1
  fi
  snapshot_line="${fault_snapshot_lines[0]}"
  if [[ ! "$snapshot_line" =~ ^LEANOS/14\ PF-SNAPSHOT\ codec=1\ width=19\ words=([0-9]+(,[0-9]+){18})\ authorization=1\ route=72057598316249602\ result=PASS$ ]]; then
    echo "failure_class=page-fault-snapshot: malformed codec or generated replay result" >&2
    exit 1
  fi
  IFS=, read -r -a snapshot_words <<< "${BASH_REMATCH[1]}"
  expected_snapshot_words=(
    1 14 "$fault_error" "$fault_address" "$fault_page"
    "$fault_access_code"
    1 1 1 1 "$fault_cr3" 15 "$fault_rip"
    35 534 "$fault_rsp" 27 1 0
  )
  for ((i = 0; i < 19; ++i)); do
    if [[ "${snapshot_words[i]}" != "${expected_snapshot_words[i]}" ]]; then
      echo "failure_class=page-fault-snapshot: word $i disagrees with canonical production snapshot" >&2
      exit 1
    fi
  done
  snapshot_line_number="$(grep -n '^LEANOS/14 PF-SNAPSHOT ' "$log" | cut -d: -f1 || true)"
  entry_line_number="$(grep -n '^LEANOS/14 FAULT-ENTRY ' "$log" | cut -d: -f1 || true)"
  if [[ "$entry_line_number" =~ ^[0-9]+$ &&
        "$snapshot_line_number" -ge "$entry_line_number" ]]; then
    echo "failure_class=page-fault-snapshot: snapshot/replay record reordered" >&2
    exit 1
  fi
  sed -i '/^LEANOS\/14 PF-SNAPSHOT /d' "$without_allocation"
fi
if [[ "$scenario" == blocking-ipc || "$scenario" == preemption ]]; then
  final_high_water_path="syscall"
  [[ "$scenario" == preemption ]] && final_high_water_path="timer-context-switch"
  mkdir -p "$(dirname "$high_water_artifact")"
  grep '^LEANOS/11 ENTRY-HIGH-WATER ' "$log" > "$high_water_artifact" || {
    echo "failure_class=entry-stack-high-water: observation missing" >&2; exit 1;
  }
  mapfile -t high_water_lines < "$high_water_artifact"
  if [[ ${#high_water_lines[@]} -ne 2 ]]; then
    echo "failure_class=entry-stack-high-water: missing or duplicate observation" >&2
    exit 1
  fi
  expected_high_water_paths=(user-page-fault "$final_high_water_path")
  for ((i = 0; i < 2; ++i)); do
    if [[ ! "${high_water_lines[i]}" =~ ^LEANOS/11\ ENTRY-HIGH-WATER\ path=${expected_high_water_paths[i]}\ observed-bytes=([0-9]+)\ usable-bytes=16384\ margin-bytes=([0-9]+)\ authority=diagnostic\ result=PASS$ ]]; then
      echo "failure_class=entry-stack-high-water: malformed or reordered observation" >&2
      exit 1
    fi
    observed="${BASH_REMATCH[1]}"; margin="${BASH_REMATCH[2]}"
    if (( observed < 176 || observed + margin != 16384 || margin < 4096 )); then
      echo "failure_class=entry-stack-high-water: invalid observed bound" >&2
      exit 1
    fi
  done
  sed -i '/^LEANOS\/11 ENTRY-HIGH-WATER /d' "$without_allocation"
fi
if ! cmp -s "$expected" "$without_allocation"; then echo "failure_class=serial-protocol: complete expected protocol not observed" >&2; diff -u "$expected" "$without_allocation" >&2 || true; exit 1; fi
if ! ./scripts/write-dma-snapshot.py \
    --serial-log "$log" \
    --source-revision "$source_revision_file" \
    --qemu-version "${qemu_version:-unknown}" \
    --output "$dma_snapshot"; then
  echo "failure_class=dma-snapshot: canonical per-function snapshot rejected" >&2
  exit 1
fi
if [[ "$scenario" == extended-state || "$scenario" == extended-state-mmx ||
      "$scenario" == extended-state-sse || "$scenario" == extended-state-sse2 ||
      "$scenario" == extended-state-avx ]]; then
  default_snapshot="build/boot/extended-state-control-snapshot.txt"
  if [[ "$extended_instruction" == mmx ]]; then
    default_snapshot="build/boot/extended-state-mmx-control-snapshot.txt"
  elif [[ "$extended_instruction" == sse ]]; then
    default_snapshot="build/boot/extended-state-sse-control-snapshot.txt"
  elif [[ "$extended_instruction" == sse2 ]]; then
    default_snapshot="build/boot/extended-state-sse2-control-snapshot.txt"
  elif [[ "$extended_instruction" == avx ]]; then
    default_snapshot="build/boot/extended-state-avx-control-snapshot.txt"
  fi
  snapshot="${LEANOS_EXTENDED_STATE_SNAPSHOT:-$default_snapshot}"
  mkdir -p "$(dirname "$snapshot")"
  grep -E '^LEANOS/(13 EXTENDED-STATE cpuid\.1\.|6 CONTROL )' "$log" > "$snapshot"
  [[ $(wc -l < "$snapshot") -eq 2 ]] || {
    echo "failure_class=extended-state-snapshot: decoded CPUID/control snapshot incomplete" >&2
    exit 1
  }
elif [[ "$scenario" == fast-entry-syscall || "$scenario" == fast-entry-sysenter ]]; then
  snapshot="${LEANOS_FAST_ENTRY_SNAPSHOT:-build/boot/fast-entry-control-snapshot-${extended_instruction}.txt}"
  mkdir -p "$(dirname "$snapshot")"
  grep -E '^LEANOS/(14 FAST-ENTRY cpu\.|13 EXTENDED-STATE cpuid\.1\.|6 CONTROL )' \
    "$log" > "$snapshot"
  [[ $(wc -l < "$snapshot") -eq 3 ]] || {
    echo "failure_class=fast-entry-snapshot: decoded CPUID/MSR/control snapshot incomplete" >&2
    exit 1
  }
fi
echo "LeanOS boot smoke test passed; guest success and complete protocol observed; serial log: $log"
