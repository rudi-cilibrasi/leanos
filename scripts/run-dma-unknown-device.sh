#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
source "$repo_root/scripts/q35-platform.sh"

qemu="${LEANOS_QEMU:-qemu-system-x86_64}"
limit="${LEANOS_QEMU_TIMEOUT_SECONDS:-30}"
version="${LEANOS_VERSION:-0.1.0}"
image="${1:-build/boot/leanos-${version}-x86_64.iso}"
log="${LEANOS_SERIAL_LOG:-build/boot/dma-unknown-device.serial.log}"
memory_mib="${LEANOS_QEMU_MEMORY_MIB:-128}"
terminal='LEANOS/3 FINAL status=FAIL reason=dma-inventory'

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
# Controlled topology violation: the normal production manifest does not admit
# this real DMA-capable function. The shared command is validated before this
# single deliberate mutation so no other platform setting can drift.
command+=(-device edu,bus=pcie.0,addr=0x2)
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
  echo "failure_class=guest-error: guest reported an unrelated evidence failure" >&2
  exit 1
fi
if [[ $status -ne 35 ]]; then
  echo "failure_class=qemu-error: QEMU exit status $status (expected 35)" >&2
  exit 1
fi
if [[ "$(grep -Fxc "$terminal" "$log")" -ne 1 ]] ||
    [[ "$(grep -c '^LEANOS/3 FINAL ' "$log")" -ne 1 ]] ||
    grep -Eq '^LEANOS/15 DMA .*result=PASS|^LEANOS/5 ENTRY|status=PASS' "$log"; then
  echo "failure_class=controlled-negative: exact pre-CPL3 DMA inventory rejection not observed" >&2
  exit 1
fi

echo "LeanOS unknown-device negative passed; guest rejected edu before CPL3; serial log: $log"
