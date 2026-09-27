#!/usr/bin/env bash
# Boot one ISO under both firmware families on the pinned q35 platform and
# require the canonical final PASS from each: SeaBIOS through GRUB i386-pc
# (El Torito BIOS entry) and OVMF through GRUB x86_64-efi (El Torito UEFI
# entry).  Both loaders read the same grub.cfg and enter the same kernel ELF
# through Multiboot2, so this is the end-to-end check that the handoff
# decoder admits either firmware's boot information.
#
# usage: check-firmware-boot.sh [<iso>] [<output-dir>]
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$repo_root"
source "$repo_root/scripts/q35-platform.sh"

image="${1:-build/boot/leanos-0.1.0-x86_64.iso}"
output="${2:-build/boot/firmware-boot}"
qemu="${LEANOS_QEMU:-qemu-system-x86_64}"
limit="${LEANOS_QEMU_TIMEOUT_SECONDS:-120}"
memory_mib="${LEANOS_QEMU_MEMORY_MIB:-128}"
# isa-debug-exit reports (code << 1) | 1; the kernel writes 0x10 on PASS.
readonly pass_exit=33

[[ -f "$image" ]] || { echo "error: image '$image' not found; run ./scripts/build-image.sh first" >&2; exit 1; }
[[ -f "$LEANOS_OVMF_CODE" && -f "$LEANOS_OVMF_VARS" ]] || {
  echo "error: missing OVMF firmware; install Ubuntu package ovmf=2024.02-2ubuntu0.9" >&2
  exit 1
}
mkdir -p "$output"

failed=0
for firmware in seabios ovmf; do
  log="$output/serial-$firmware.log"
  rm -f "$log"
  command=()
  LEANOS_QEMU_FIRMWARE="$firmware" \
    leanos_q35_command command "$qemu" "$memory_mib" "$log" "$image"
  status=0
  timeout "$limit" "${command[@]}" || status=$?
  final="$(grep -a -m1 '^LEANOS/[0-9]* FINAL ' "$log" || true)"
  if [[ $status -eq $pass_exit && "$final" == *' FINAL status=PASS'* ]]; then
    echo "firmware-boot $firmware PASS exit=$status"
  else
    echo "firmware-boot $firmware FAIL exit=$status final='${final:-none}'" >&2
    grep -a 'status=FAIL\|reason=' "$log" | tail -3 >&2 || true
    failed=1
  fi
done
exit "$failed"
