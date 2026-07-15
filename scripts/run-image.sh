#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$repo_root"
qemu="${LEANOS_QEMU:-qemu-system-x86_64}"
limit="${LEANOS_QEMU_TIMEOUT_SECONDS:-30}"
version="${LEANOS_VERSION:-0.1.0}"
image="${1:-build/boot/leanos-${version}-x86_64.iso}"
log="${LEANOS_SERIAL_LOG:-build/boot/serial.log}"
for tool in "$qemu" timeout; do command -v "$tool" >/dev/null 2>&1 || { echo "error: missing required tool '$tool'; install qemu-system-x86=1:8.2.2+ds-0ubuntu1.17 and coreutils=9.4-3ubuntu6.2" >&2; exit 1; }; done
[[ "$limit" =~ ^[1-9][0-9]*$ ]] || { echo "error: timeout must be a positive integer" >&2; exit 1; }
[[ -f "$image" ]] || { echo "error: image '$image' not found; run ./scripts/build-image.sh first" >&2; exit 1; }
mkdir -p "$(dirname "$log")"; : > "$log"
command=("$qemu" -machine q35,accel=tcg -cpu max -smp 1 -m 128M -display none -monitor none -serial "file:$log" -no-reboot -no-shutdown -nic none -device isa-debug-exit,iobase=0xf4,iosize=0x04 -cdrom "$image")
version="$($qemu --version 2>&1 | head -n 1 || true)"
printf 'QEMU version: %s\nQEMU command:' "${version:-unknown}" >&2; printf ' %q' "${command[@]}" >&2; printf '\nSerial log: %s\n' "$log" >&2
set +e; timeout --signal=TERM --kill-after=2s "${limit}s" "${command[@]}"; status=$?; set -e
expected="$(mktemp)"; trap 'rm -f "$expected"' EXIT
corpus="${LEANOS_ORACLE_CORPUS:-build/boot/corpus.tsv}"
[[ -f "$corpus" ]] || { echo "error: oracle corpus '$corpus' not found" >&2; exit 1; }
echo 'LEANOS/3 BOOT target=x86_64-q35 subjects=2 schedule=fixed' > "$expected"
awk -F '\t' '$1 ~ /^[0-9]+$/ { print "LEANOS/3 ORACLE id=" $2 " result=PASS" }' "$corpus" >> "$expected"
printf '%s\n' \
  'LEANOS/3 SUBJECT id=1 address-space=1 cpl=3' \
  'LEANOS/3 IPC op=receive subject=1 result=denied reason=missing-receive' \
  'LEANOS/3 IPC op=send subject=1 result=accepted payload=4c45414e:4f53 supplied-sender=99' \
  'LEANOS/3 HANDOFF from=1 to=2 address-space=2 cr3=switched' \
  'LEANOS/3 SUBJECT id=2 address-space=2 cpl=3' \
  'LEANOS/3 IPC op=send subject=2 result=denied reason=missing-send' \
  'LEANOS/3 IPC op=receive subject=2 result=delivered sender=1 payload=4c45414e:4f53' \
  'LEANOS/3 IPC supplied-sender=99 trusted=0 capability-transfer=none' \
  'LEANOS/3 FAULT subject=2 vector=14 class=user-supervisor-access contained=1' \
  'LEANOS/3 RESUME kernel=1' \
  'LEANOS/3 FINAL status=PASS' >> "$expected"
if [[ $status -eq 124 || $status -eq 137 ]]; then echo "failure_class=timeout: QEMU exceeded ${limit}s wall limit" >&2; exit 1; fi
if [[ $status -eq 35 ]]; then echo "failure_class=guest-error: guest emitted failure signal" >&2; exit 1; fi
if [[ $status -ne 33 ]]; then echo "failure_class=qemu-error: QEMU exit status $status (expected 33)" >&2; exit 1; fi
if ! cmp -s "$expected" "$log"; then echo "failure_class=serial-protocol: complete expected protocol not observed" >&2; diff -u "$expected" "$log" >&2 || true; exit 1; fi
echo "LeanOS boot smoke test passed; guest success and complete protocol observed; serial log: $log"
