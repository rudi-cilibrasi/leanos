#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$repo_root"
qemu="${LEANOS_QEMU:-qemu-system-x86_64}"
limit="${LEANOS_QEMU_TIMEOUT_SECONDS:-30}"
version="${LEANOS_VERSION:-0.1.0}"
scenario="${LEANOS_BOOT_SCENARIO:-blocking-ipc}"
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
elif [[ "$scenario" == fault-containment ]]; then
  default_image="build/boot/leanos-${version}-x86_64-fault-containment.iso"
elif [[ "$scenario" == entry-adversarial ]]; then
  default_image="build/boot/leanos-${version}-x86_64-entry-adversarial.iso"
else
  default_image="build/boot/leanos-${version}-x86_64.iso"
fi
image="${1:-$default_image}"
log="${LEANOS_SERIAL_LOG:-build/boot/serial.log}"
high_water_artifact="${LEANOS_ENTRY_HIGH_WATER_ARTIFACT:-build/boot/entry-stack-high-water-${scenario}.txt}"
memory_mib="${LEANOS_QEMU_MEMORY_MIB:-128}"
for tool in "$qemu" timeout; do command -v "$tool" >/dev/null 2>&1 || { echo "error: missing required tool '$tool'; install qemu-system-x86=1:8.2.2+ds-0ubuntu1.17 and coreutils=9.4-3ubuntu6.2" >&2; exit 1; }; done
[[ "$limit" =~ ^[1-9][0-9]*$ ]] || { echo "error: timeout must be a positive integer" >&2; exit 1; }
[[ "$memory_mib" =~ ^(64|128)$ ]] || { echo "error: memory must be one of the checked configurations: 64 or 128 MiB" >&2; exit 1; }
reported_top_mib=$((memory_mib - 1))
[[ -f "$image" ]] || { echo "error: image '$image' not found; run ./scripts/build-image.sh first" >&2; exit 1; }
mkdir -p "$(dirname "$log")"; : > "$log"
command=("$qemu" -machine q35,accel=tcg -cpu max -smp 1 -m "${memory_mib}M" -display none -monitor none -serial "file:$log" -no-reboot -no-shutdown -nic none -device isa-debug-exit,iobase=0xf4,iosize=0x04 -cdrom "$image")
version="$($qemu --version 2>&1 | head -n 1 || true)"
printf 'QEMU version: %s\nQEMU command:' "${version:-unknown}" >&2; printf ' %q' "${command[@]}" >&2; printf '\nSerial log: %s\n' "$log" >&2
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
elif [[ "$scenario" == fault-containment ]]; then
  echo 'LEANOS/14 BOOT target=x86_64-q35 subjects=2 schedule=fault-containment contract=v1 controls=wp,smep,smap' > "$expected"
else
  echo 'LEANOS/10 BOOT target=x86_64-q35 subjects=2 schedule=blocking-ipc controls=wp,smep,smap' > "$expected"
fi
echo 'LEANOS/15 DMA snapshot=1 topology=000800020002 bus=0 scanned=256 present=5 optional-absent=1 writes=5 readbacks=5 initial-bus-masters=1 initial-bus-master-mask=16 bus-master=disabled readback=exact stage=pre-cpl3 result=PASS' >> "$expected"
printf '%s\n' \
  'LEANOS/8 PAGING root=A selected=1 leaves=4096 policy=manifest result=PASS' \
  'LEANOS/8 PAGING root=B selected=0 leaves=4096 policy=manifest result=PASS' >> "$expected"
awk -F '\t' '$1 ~ /^[0-9]+$/ { print "LEANOS/3 ORACLE id=" $2 " result=PASS" }' "$corpus" >> "$expected"
echo 'LEANOS/17 ENTRY-MANIFEST ordinary=6 extended=6,7 auxiliary=1 terminal=2 extra=0 rsp0=entry-stack ist1=df-stack ist2=nmi-stack result=PASS' >> "$expected"
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
elif [[ "$scenario" == fault-containment ]]; then
printf '%s\n' \
  'LEANOS/8 PAGING root=A selected=1 resumed=1 result=PASS' \
  'LEANOS/14 ENTER subject=1 address-space=1 cpl=3 resources=owned' \
  'LEANOS/14 FAULT-ENTRY vector=14 error=5 origin=cpl3 hardware=1 direct-call=0 subject=1 address-space=1 result=PASS' \
  'LEANOS/14 TERMINATE subject=1 live=0 runnable=0 current=0 queued=0 resumable=0 resources=cap,memory,mapping,endpoint result=PASS' \
  'LEANOS/14 DISPATCH subject=2 address-space=2 source=lean-scheduler context=owned result=PASS' \
  'LEANOS/8 PAGING root=B selected=1 result=PASS' \
  'LEANOS/14 PEER subject=2 address-space=2 stack=owned return=validated canaries=preserved resources=unchanged result=PASS' \
  'LEANOS/14 FINAL status=PASS faulting=terminated survivor=2 kernel-origin=fail-stop' >> "$expected"
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
   [[ ! "${allocation_lines[2]}" =~ ^LEANOS/7\ ALLOC\ frame=[0-9]+\ firmware-usable=1\ boot-accessible=1\ reserved=0\ result=PASS$ ]] ||
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
  'extra-mapping B pt' 'entry-guard-mapping B pt'
  'omitted-mapping B pt' 'wrong-cr3 A cr3'
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
sed -e '/^LEANOS\/7 /d' -e '/^LEANOS\/8 PAGING fixture=/d' "$log" > "$without_allocation"
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
