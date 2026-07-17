#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$repo_root"
qemu="${LEANOS_QEMU:-qemu-system-x86_64}"
limit="${LEANOS_QEMU_TIMEOUT_SECONDS:-30}"
version="${LEANOS_VERSION:-0.1.0}"
image="${1:-build/boot/leanos-${version}-x86_64.iso}"
log="${LEANOS_SERIAL_LOG:-build/boot/serial.log}"
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
echo 'LEANOS/6 BOOT target=x86_64-q35 subjects=2 schedule=one-shot-pit controls=wp,smep,smap' > "$expected"
printf '%s\n' \
  'LEANOS/8 PAGING root=A selected=1 leaves=4096 policy=manifest result=PASS' \
  'LEANOS/8 PAGING root=B selected=0 leaves=4096 policy=manifest result=PASS' \
  'LEANOS/8 PAGING fixture=flip-present root=A page=0 result=REJECTED' >> "$expected"
awk -F '\t' '$1 ~ /^[0-9]+$/ { print "LEANOS/3 ORACLE id=" $2 " result=PASS" }' "$corpus" >> "$expected"
printf '%s\n' \
  'LEANOS/6 CONTROL cr0.wp=1 cr4.smep=1 cr4.smap=1 ac=0 stage=exception-path-ready' \
  'LEANOS/4 PROBE kind=wp vector=14 error=3 origin=kernel address=kernel-text policy=fatal result=PASS' \
  'LEANOS/4 PROBE kind=smep vector=14 error=17 origin=kernel address=user-a-text policy=fatal result=PASS' \
  'LEANOS/6 PROBE kind=smap-direct vector=14 origin=kernel ac=0 result=PASS' \
  'LEANOS/6 POLICY zero=accept max=accept unmapped=reject readonly=reject overflow=reject noncanonical=reject wrong-subject=reject stale=reject atomic=PASS' \
  'LEANOS/6 CLEANUP omitted=detected wrappers=checked entry=clac result=PASS' \
  'LEANOS/6 COPY direction=in length=4 cross-page=1 validated=1 user-df=1 kernel-df=cleared ac=cleared result=PASS' \
  'LEANOS/6 COPY direction=out length=4 cross-page=0 validated=1 user-df=1 kernel-df=cleared destination=verified-by-cpl3 ac=cleared result=PASS' \
  'LEANOS/5 ENTRY subject=1 address-space=1 cpl=3 yielding=0' \
  'LEANOS/5 TIMER vector=32 source=pit mode=one-shot origin=cpl3 accepted=1' \
  'LEANOS/5 CONTEXT old-subject=1 old-address-space=1 new-subject=2 new-address-space=2 policy=round-robin' \
  'LEANOS/8 PAGING root=B selected=1 result=PASS' \
  'LEANOS/5 SWITCH subject=2 address-space=2 cr3=switched stack=restored ticks-masked=1' \
  'LEANOS/5 SYSCALL subject=2 caller=2 address-space=2 authorized=1 canaries=preserved' \
  'LEANOS/5 FINAL status=PASS ticks=1' >> "$expected"
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
sed '/^LEANOS\/7 /d' "$log" > "$without_allocation"
if ! cmp -s "$expected" "$without_allocation"; then echo "failure_class=serial-protocol: complete expected protocol not observed" >&2; diff -u "$expected" "$without_allocation" >&2 || true; exit 1; fi
echo "LeanOS boot smoke test passed; guest success and complete protocol observed; serial log: $log"
