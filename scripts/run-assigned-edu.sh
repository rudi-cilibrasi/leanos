#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
source "$repo_root/scripts/q35-platform.sh"

qemu="${LEANOS_QEMU:-qemu-system-x86_64}"
limit="${LEANOS_QEMU_TIMEOUT_SECONDS:-30}"
version="${LEANOS_VERSION:-0.1.0}"
image="${1:-build/boot/leanos-${version}-x86_64-assigned-edu.iso}"
log="${LEANOS_SERIAL_LOG:-build/boot/assigned-edu.serial.log}"
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
[[ -f "$image" ]] || {
  echo "error: image '$image' not found; run ./scripts/build-image.sh first" >&2
  exit 1
}

mkdir -p "$(dirname "$log")"
: > "$log"
command=()
leanos_q35_assigned_edu_command command "$qemu" "$memory_mib" "$log" "$image"
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
if [[ $status -ne 33 ]]; then
  echo "failure_class=qemu-error: QEMU exit status $status (expected 33)" >&2
  exit 1
fi
edu='LEANOS/15 DMA-FUNCTION manifest=1 topology=0001000800020003 bdf=0:2.0 present=1 vendor=4660 device=4584 class=65280 command-before=259 command-after=0 assigned=1 bridge=0 multifunction=0 policy=accepted'
snapshot='LEANOS/15 DMA snapshot=1 topology=0001000800020003 bus=0 scanned=256 present=6 optional-absent=1 writes=6 readbacks=6 initial-bus-masters=1 initial-bus-master-mask=16 bus-master=disabled readback=exact generated-result=0 stage=pre-cpl3 result=PASS'
assignment='LEANOS/21 VTD-ASSIGN bdf=0:2.0 requester=16 domain=0 tables=generated-readback bar=4271898624 mmio-id=16777453 command=6 memory=enabled bus-master=enabled stage=post-translation result=PASS'
transfer='LEANOS/21 VTD-TRANSFER requester=16 domain=0 generation=1 read-iova=0 write-iova=4096 bytes=16 payload=exact guards=unchanged fsts=0 result=PASS'
read_fault='LEANOS/21 VTD-FAULT requester=16 domain=0 generation=1 direction=read iova=4096 reason=6 sid=16 sentinel=unchanged victim=unchanged state=current result=PASS'
write_fault='LEANOS/21 VTD-FAULT requester=16 domain=0 generation=1 direction=write iova=0 reason=5 sid=16 sentinel=unchanged victim=unchanged state=current result=PASS'
unmapped_fault='LEANOS/21 VTD-FAULT requester=16 domain=0 generation=1 direction=read iova=8192 reason=6 sid=16 protected=subject,kernel,cpu-page-tables,remapping-tables,guards records=complete,unchanged state=current result=PASS'
reuse='LEANOS/21 VTD-REUSE requester=16 domain=0 old-generation=1 old-iova=0 old-access=denied invalidation=complete scrub=complete fresh-lifetime=2 fresh-iova=8192 canary=preserved fresh-transfer=PASS reset=0 result=PASS'
if [[ "$(grep -Fxc "$edu" "$log")" -ne 1 ]] ||
    [[ "$(grep -Fxc "$snapshot" "$log")" -ne 1 ]] ||
    [[ "$(grep -Fxc "$assignment" "$log")" -ne 1 ]] ||
    [[ "$(grep -Fxc "$read_fault" "$log")" -ne 1 ]] ||
    [[ "$(grep -Fxc "$write_fault" "$log")" -ne 1 ]] ||
    [[ "$(grep -Fxc "$unmapped_fault" "$log")" -ne 1 ]] ||
    [[ "$(grep -Fxc "$reuse" "$log")" -ne 1 ]] ||
    [[ "$(grep -Fxc "$transfer" "$log")" -ne 1 ]] ||
    [[ "$(grep -Fxc 'LEANOS/10 FINAL status=PASS blocks=1 wakes=1 deliveries=1' "$log")" -ne 1 ]]; then
  echo "failure_class=evidence: assigned-EDU inventory checkpoint differs" >&2
  exit 1
fi

echo "LeanOS assigned-EDU inventory checkpoint passed; serial log: $log"
