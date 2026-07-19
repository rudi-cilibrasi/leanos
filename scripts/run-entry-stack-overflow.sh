#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

qemu="${LEANOS_QEMU:-qemu-system-x86_64}"
limit="${LEANOS_QEMU_TIMEOUT_SECONDS:-30}"
version="${LEANOS_VERSION:-0.1.0}"
image="${1:-build/boot/leanos-${version}-x86_64-entry-stack-overflow.iso}"
log="${LEANOS_SERIAL_LOG:-build/boot/entry-stack-overflow.serial.log}"
memory_mib="${LEANOS_QEMU_MEMORY_MIB:-128}"
terminal='LEANOS/11 ENTRY-STACK-OVERFLOW reason=guard-crossing vector=8 error=0 ist=1 rsp=in-range canaries=intact guard=unmapped adjacent=intact handler=none return=none'

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
if [[ $status -eq 39 ]]; then
  echo "failure_class=guest-evidence: guest rejected overflow evidence" >&2
  exit 1
fi
if [[ $status -ne 37 ]]; then
  echo "failure_class=qemu-error: QEMU exit status $status (expected 37)" >&2
  exit 1
fi
if [[ "$(grep -Fxc "$terminal" "$log")" -ne 1 ]]; then
  echo "failure_class=terminal-record: exactly one typed entry-stack overflow record not observed" >&2
  exit 1
fi
if [[ "$(grep -c '^LEANOS/11 ENTRY-STACK-OVERFLOW ' "$log")" -ne 1 ]] ||
   grep -Eq 'LEANOS/11 ENTRY-STACK-OVERFLOW .*status=(PASS|FAIL)|LEANOS/[0-9]+ FINAL |LEANOS/10 ENTRY-HIGH-WATER ' "$log"; then
  echo "failure_class=terminal-record: duplicate, forged, handler, or post-terminal record observed" >&2
  exit 1
fi

echo "LeanOS entry-stack overflow probe passed; real guard crossing terminated on vector 8 IST1; serial log: $log"
