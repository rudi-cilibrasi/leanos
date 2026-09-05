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
memory_mib="${LEANOS_QEMU_MEMORY_MIB:-128}"

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

specs=(
  "missing-mmio-mapping:pt-decode-a"
  "wrong-bar:vtd-assigned-bar"
  "wrong-mmio-identity:vtd-assigned-mmio-identity"
  "forged-fault:vtd-assigned-fault-binding"
  "wrong-fault-victim:vtd-assigned-fault-victim"
  "omit-reuse-invalidation:vtd-reuse-invalidation-omitted"
)
for spec in "${specs[@]}"; do
  IFS=: read -r fixture reason <<<"$spec"
  image="build/boot/leanos-${version}-x86_64-assigned-edu-${fixture}.iso"
  log="build/boot/assigned-edu-${fixture}.serial.log"
  terminal="${LEANOS_SERIAL_3_FINAL} status=FAIL reason=${reason}"
  [[ -f "$image" ]] || {
    echo "error: image '$image' not found; run ./scripts/build-image.sh first" >&2
    exit 1
  }
  : > "$log"
  command=()
  leanos_q35_assigned_edu_command command "$qemu" "$memory_mib" "$log" "$image"
  set +e
  timeout --signal=TERM --kill-after=2s "${limit}s" "${command[@]}"
  status=$?
  set -e
  if [[ $status -eq 124 || $status -eq 137 ]]; then
    echo "failure_class=timeout: $fixture exceeded ${limit}s wall limit" >&2
    exit 1
  fi
  if [[ $status -ne 35 ]] ||
      [[ "$(grep -Fxc "$terminal" "$log")" -ne 1 ]] ||
      [[ "$(grep -c "^${LEANOS_SERIAL_3_FINAL} " "$log")" -ne 1 ]] ||
      grep -Eq "^${LEANOS_SERIAL_21_VTD_ASSIGN} .*result=PASS|^${LEANOS_SERIAL_10_FINAL} status=PASS" "$log"; then
    echo "failure_class=controlled-negative: $fixture did not fail exactly at $reason" >&2
    exit 1
  fi
  echo "LeanOS assigned-EDU negative passed: $fixture -> $reason"
done
