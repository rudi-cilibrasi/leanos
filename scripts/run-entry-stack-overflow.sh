#!/usr/bin/env bash
set -euo pipefail
serial_protocol="${LEANOS_SERIAL_PROTOCOL:-$(dirname "${LEANOS_ORACLE_CORPUS:-build/boot/corpus.tsv}")/serial-protocol.sh}"
# shellcheck source=/dev/null
source "$serial_protocol"

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
source "$repo_root/scripts/q35-platform.sh"

qemu="${LEANOS_QEMU:-qemu-system-x86_64}"
limit="${LEANOS_QEMU_TIMEOUT_SECONDS:-30}"
version="${LEANOS_VERSION:-0.1.0}"
image="${1:-build/boot/leanos-${version}-x86_64-entry-stack-overflow.iso}"
log="${LEANOS_SERIAL_LOG:-build/boot/entry-stack-overflow.serial.log}"
memory_mib="${LEANOS_QEMU_MEMORY_MIB:-128}"
terminal="${LEANOS_SERIAL_11_ENTRY_STACK_OVERFLOW} reason=guard-crossing vector=8 error=0 ist=1 rsp=in-range canaries=intact guard=unmapped adjacent=intact handler=none return=none"

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
command=()
leanos_q35_command command "$qemu" "$memory_mib" "$log" "$image"
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
if [[ "$(grep -c "^${LEANOS_SERIAL_11_ENTRY_STACK_OVERFLOW} " "$log")" -ne 1 ]] ||
   grep -Eq "${LEANOS_SERIAL_11_ENTRY_STACK_OVERFLOW} .*status=(PASS|FAIL)|LEANOS/[0-9]+ FINAL |${LEANOS_SERIAL_11_ENTRY_HIGH_WATER} " "$log"; then
  echo "failure_class=terminal-record: duplicate, forged, handler, or post-terminal record observed" >&2
  exit 1
fi

echo "LeanOS entry-stack overflow probe passed; real guard crossing terminated on vector 8 IST1; serial log: $log"
