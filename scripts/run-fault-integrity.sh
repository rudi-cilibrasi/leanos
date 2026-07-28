#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

qemu="${LEANOS_QEMU:-qemu-system-x86_64}"
limit="${LEANOS_QEMU_TIMEOUT_SECONDS:-30}"
version="${LEANOS_VERSION:-0.1.0}"
probe="${LEANOS_FAULT_INTEGRITY_PROBE:-reserved-bit}"
image="${1:-build/boot/leanos-${version}-x86_64-fault-${probe}.iso}"
log="${LEANOS_SERIAL_LOG:-build/boot/fault-${probe}.serial.log}"
elf="${LEANOS_FAULT_INTEGRITY_ELF:-build/boot/leanos-fault-${probe}.elf}"
artifact="${LEANOS_FAULT_TERMINAL_ARTIFACT:-build/boot/fault-${probe}-terminal.txt}"
memory_mib="${LEANOS_QEMU_MEMORY_MIB:-128}"

case "$probe" in
reserved-bit)
  expected_error=12
  expected_access=read
  expected_rip=user-a-reserved-fault-instruction
  expected_authorization=0
  expected_route=144115188075855874
  ;;
walk-mismatch)
  expected_error=5
  expected_access=read
  expected_rip=user-a-fault-instruction
  expected_authorization=1
  expected_route=144115188075855875
  ;;
*)
  echo "error: unknown fault-integrity probe '$probe'" >&2
  exit 1
  ;;
esac

for tool in "$qemu" timeout nm; do
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
[[ -f "$image" && -f "$elf" ]] || {
  echo "error: fault-integrity image or final ELF missing; run ./scripts/build-image.sh first" >&2
  exit 1
}

symbol_value() {
  local symbol="$1" address
  address="$(nm -n "$elf" | awk -v wanted="$symbol" '$3 == wanted { print $1 }')"
  [[ "$address" =~ ^[[:xdigit:]]+$ ]] || return 1
  printf '%u' "$((16#$address))"
}
if [[ "$probe" == reserved-bit ]]; then
  expected_cr2="$(symbol_value user_a_nx_fault_instruction)"
  printf -v expected_leaf '%u' \
    "$(( (1 << 63) | (expected_cr2 / 4096) * 4096 | 7 ))"
  expected_live_leaf="$expected_leaf"
  cpu=max,phys-bits=48
else
  expected_cr2=0
  expected_live_leaf=9223372036854775811
  expected_leaf=9223372036854775809
  cpu=max
fi

mkdir -p "$(dirname "$log")"
: > "$log"
command=("$qemu" -machine q35,accel=tcg -cpu "$cpu" -smp 1
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
if [[ $status -eq 33 ]]; then
  echo "failure_class=normal-success: fatal probe used the normal guest status" >&2
  exit 1
fi
if [[ $status -eq 35 ]]; then
  echo "failure_class=guest-error: guest emitted the generic failure status" >&2
  exit 1
fi
if [[ $status -ne 37 ]]; then
  echo "failure_class=qemu-error: QEMU exit status $status (expected independent fatal status 37)" >&2
  exit 1
fi

terminal_pattern="^LEANOS/14 PF-TERMINAL codec=1 case=${probe} vector=14 error=${expected_error} access=${expected_access} cr2=${expected_cr2} rip=${expected_rip} expected-leaf=${expected_leaf} live-leaf=${expected_live_leaf} authorization=${expected_authorization} route=${expected_route} halt=absorbing containment=0 cleanup=0 dispatch=0 return=none$"
mapfile -t terminal_lines < <(grep '^LEANOS/14 PF-TERMINAL ' "$log" || true)
if [[ ${#terminal_lines[@]} -ne 1 ]] ||
   [[ ! "${terminal_lines[0]}" =~ $terminal_pattern ]]; then
  echo "failure_class=terminal-record: exact generated-policy fatal record not observed" >&2
  exit 1
fi
if grep -Eq '^LEANOS/14 (PF-SNAPSHOT|FAULT-ENTRY|TERMINATE|DISPATCH|PEER|FINAL) |^LEANOS/[0-9]+ FINAL ' "$log"; then
  echo "failure_class=forbidden-record: containment, cleanup, B-dispatch, user-return, or normal success observed" >&2
  exit 1
fi
terminal_line_number="$(grep -n '^LEANOS/14 PF-TERMINAL ' "$log" | cut -d: -f1)"
if tail -n "+$((terminal_line_number + 1))" "$log" | grep -Eq '^LEANOS/'; then
  echo "failure_class=post-terminal: protocol record observed after absorbing fatal result" >&2
  exit 1
fi

mkdir -p "$(dirname "$artifact")"
printf '%s\n' "${terminal_lines[0]}" > "$artifact"
echo "LeanOS fault-integrity probe passed; generated-policy fatal result and independent guest status observed; serial log: $log"
