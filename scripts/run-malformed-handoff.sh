#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
source "$repo_root/scripts/q35-platform.sh"

qemu="${LEANOS_QEMU:-qemu-system-x86_64}"
limit="${LEANOS_QEMU_TIMEOUT_SECONDS:-30}"
version="${LEANOS_VERSION:-0.1.0}"
image="${1:-build/boot/leanos-${version}-x86_64-malformed-handoff.iso}"
log="${LEANOS_SERIAL_LOG:-build/boot/malformed-handoff.serial.log}"
memory_mib="${LEANOS_QEMU_MEMORY_MIB:-128}"
reason="${LEANOS_HANDOFF_REJECTION_REASON:-decode-rejected}"
[[ "$reason" =~ ^[a-z0-9]+(-[a-z0-9]+)*$ ]] || {
  echo "error: handoff rejection reason must be a lowercase token" >&2
  exit 1
}
terminal="LEANOS/7 BOOTALLOC status=FAIL reason=$reason"

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
if [[ $status -ne 35 ]]; then
  echo "failure_class=qemu-error: QEMU exit status $status (expected 35)" >&2
  exit 1
fi
mapfile -t allocation_records < <(grep '^LEANOS/7 ' "$log" || true)
if [[ ${#allocation_records[@]} -ne 1 ]] ||
   [[ "${allocation_records[0]:-}" != "$terminal" ]]; then
  echo "failure_class=malformed-handoff: exact decoder rejection not observed" >&2
  exit 1
fi
if grep -Eq '^LEANOS/7 (HANDOFF|MAP|ALLOC|SCRUB|PUBLISH)|^LEANOS/[0-9]+ FINAL .*status=PASS' \
    "$log"; then
  echo "failure_class=authority-leak: rejected handoff exposed boot authority" >&2
  exit 1
fi

echo "LeanOS handoff rejection passed; reason=$reason exposed no authority"
