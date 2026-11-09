#!/usr/bin/env bash
# Boot an ISO's kernel over the network (PXE/TFTP) on the pinned q35
# platform, under SeaBIOS and under OVMF.
#
# scripts/build-netboot-tree.sh makes a TFTP tree from the ISO. QEMU's user
# network serves it, and its only boot device is a transitional virtio-net
# function at 00:03.0, the optional network slot of the q35 manifest
# (LeanOS.DMAQuarantine.q35Manifest). SeaBIOS boots it through QEMU's iPXE
# option ROM and GRUB i386-pc's core.0; OVMF through its own PXE client and
# GRUB x86_64-efi's core.efi. Every other pin is the q35 platform's
# (scripts/q35-platform.sh): CPU, IOMMU, VGA, debug exit, firmware images.
#
# The admitted q35 topology (0x0001_0008_0002_0002) has that slot empty, as
# under `-nic none`, so a kernel booted this way must stop at platform
# admission with `FINAL status=FAIL reason=dma-q35-nic-none`: it clears the
# boot NIC's Command word with every other function's and then refuses the
# topology. The check therefore requires, for each firmware, the kernel's
# BOOT record (the ISO's kernel arrived over TFTP and runs) followed by that
# exact refusal, and nothing else. A topology that admits a quarantined boot
# NIC would turn this into a full PASS; it is a separate change to the
# generated q35 snapshot boundary.
#
# usage: check-netboot.sh [<iso>] [<output-dir>]
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$repo_root"
source "$repo_root/scripts/q35-platform.sh"

image="${1:-build/boot/leanos-0.1.0-x86_64.iso}"
output="${2:-build/boot/netboot}"
qemu="${LEANOS_QEMU:-qemu-system-x86_64}"
limit="${LEANOS_QEMU_TIMEOUT_SECONDS:-180}"
memory_mib="${LEANOS_QEMU_MEMORY_MIB:-128}"
# isa-debug-exit reports (code << 1) | 1; the kernel writes 0x11 on FAIL.
readonly fail_exit=35
readonly expected_final='FINAL status=FAIL reason=dma-q35-nic-none'

[[ -f "$image" ]] || { echo "error: image '$image' not found; run ./scripts/build-image.sh first" >&2; exit 1; }
[[ -f "$LEANOS_OVMF_CODE" && -f "$LEANOS_OVMF_VARS" ]] || {
  echo "error: missing OVMF firmware; install Ubuntu package ovmf=2024.02-2ubuntu0.9" >&2
  exit 1
}
mkdir -p "$output"
tree="$output/tree"
./scripts/build-netboot-tree.sh "$image" "$tree"

accelerator="$(leanos_qemu_accelerator)"
cpu="$(leanos_q35_cpu max)"
failed=0
for firmware in seabios ovmf; do
  log="$output/serial-$firmware.log"
  rm -f "$log"
  loader=boot/grub/i386-pc/core.0
  [[ "$firmware" == ovmf ]] && loader=boot/grub/x86_64-efi/core.efi
  command=(
    "$qemu"
    -machine "q35,accel=$accelerator"
    -nodefaults
    -cpu "$cpu"
    -smp 1
    -m "${memory_mib}M"
    -display none
    -monitor none
    -serial "file:$log"
    -no-reboot
    -no-shutdown
    -device intel-iommu,intremap=off,pt=off,caching-mode=off,device-iotlb=off,aw-bits=39,dma-translation=on,snoop-control=off
    -device VGA,bus=pcie.0,addr=0x1
    -device isa-debug-exit,iobase=0xf4,iosize=0x04
    -netdev "user,id=leanos-net,restrict=on,tftp=$tree,bootfile=$loader"
    -device virtio-net-pci,netdev=leanos-net,bus=pcie.0,addr=0x3,disable-legacy=off,bootindex=1
  )
  if [[ "$firmware" == ovmf ]]; then
    vars="$log.ovmf-vars.fd"
    cp "$LEANOS_OVMF_VARS" "$vars"
    command+=(
      -drive "if=pflash,format=raw,readonly=on,file=$LEANOS_OVMF_CODE"
      -drive "if=pflash,format=raw,file=$vars"
    )
  fi
  status=0
  timeout "$limit" "${command[@]}" || status=$?
  # Under OVMF the first record can follow firmware console output on its line.
  boot="$(grep -a -o -m1 'LEANOS/[0-9]* BOOT target=x86_64-q35 .*' "$log" || true)"
  final="$(grep -a -m1 '^LEANOS/[0-9]* FINAL ' "$log" || true)"
  if [[ $status -eq $fail_exit && -n "$boot" && "$final" == *" $expected_final" ]]; then
    echo "netboot $firmware kernel-booted fail-closed exit=$status final='${final#LEANOS/* }'"
  else
    echo "netboot $firmware UNEXPECTED exit=$status boot='${boot:-none}' final='${final:-none}'" >&2
    failed=1
  fi
done
exit "$failed"
