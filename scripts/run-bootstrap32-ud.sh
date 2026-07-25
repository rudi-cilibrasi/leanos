#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

qemu="${LEANOS_QEMU:-qemu-system-x86_64}"
limit="${LEANOS_QEMU_TIMEOUT_SECONDS:-30}"
version="${LEANOS_VERSION:-0.1.0}"
image="${1:-build/boot/leanos-${version}-x86_64-bootstrap32-ud.iso}"
log="${LEANOS_SERIAL_LOG:-build/boot/bootstrap32-ud.serial.log}"
memory_mib="${LEANOS_QEMU_MEMORY_MIB:-128}"
terminal='LEANOS/18 EARLY-TERMINAL phase=bootstrap32 table=bootstrap32 width=legacy8 vector=6 reason=invalid-opcode error=none frame=eip,cs,eflags stack=boot target=stub32 latch=terminal return=none'

for tool in "$qemu" timeout; do
  command -v "$tool" >/dev/null 2>&1 || {
    echo "error: missing required tool '$tool'" >&2
    exit 1
  }
done
[[ "$limit" =~ ^[1-9][0-9]*$ ]] || {
  echo "error: timeout must be a positive integer" >&2
  exit 1
}
[[ "$memory_mib" =~ ^(64|128)$ ]] || {
  echo "error: memory must be one of the checked configurations: 64 or 128 MiB" >&2
  exit 1
}
[[ -f "$image" ]] || {
  echo "error: image '$image' not found; run ./scripts/build-image.sh first" >&2
  exit 1
}

mkdir -p "$(dirname "$log")"
: > "$log"
command=("$qemu" -machine q35,accel=tcg -cpu max -smp 1
  -m "${memory_mib}M" -display none -monitor none -serial "file:$log"
  -no-reboot -no-shutdown -nic none
  -device isa-debug-exit,iobase=0xf4,iosize=0x04 -cdrom "$image")
qemu_version="$($qemu --version 2>&1 | head -n 1 || true)"
printf 'QEMU version: %s\nQEMU command:' "${qemu_version:-unknown}" >&2
printf ' %q' "${command[@]}" >&2
printf '\nSerial log: %s\n' "$log" >&2

set +e
timeout --signal=TERM --kill-after=2s "${limit}s" "${command[@]}"
status=$?
set -e

if [[ $status -eq 124 || $status -eq 137 ]]; then
  echo "failure_class=timeout: QEMU exceeded ${limit}s wall limit" >&2
  exit 1
fi
if [[ $status -eq 49 ]]; then
  echo "failure_class=guest-evidence: guest rejected the bootstrap32 #UD frame shape" >&2
  exit 1
fi
if [[ $status -ne 45 ]]; then
  echo "failure_class=qemu-error: QEMU exit status $status (expected 45)" >&2
  exit 1
fi
if [[ "$(grep -Fxc "$terminal" "$log")" -ne 1 ]]; then
  echo "failure_class=terminal-record: exactly one bootstrap32 #UD terminal record not observed" >&2
  exit 1
fi
if [[ "$(grep -c . "$log")" -ne 1 ]] || \
   grep -Eq 'status=FAIL|phase=bootstrap64|EARLY64-READY|LEANOS/17 |LEANOS/[0-9]+ (BOOT|FINAL) ' "$log"; then
  echo "failure_class=terminal-record: forged, duplicate, long-mode, or post-terminal output observed" >&2
  exit 1
fi

echo "LeanOS bootstrap32 #UD probe passed; the pre-paging ud2 latched the reviewed early terminal stub"
