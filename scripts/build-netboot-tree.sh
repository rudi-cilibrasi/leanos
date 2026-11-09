#!/usr/bin/env bash
# Build a network-boot (PXE/TFTP) tree from a LeanOS ISO.
#
# The tree is the ISO's own /boot (the kernel ELF, grub.cfg and the build
# records, byte for byte) plus GRUB's network loaders for both firmware
# families, made with the pinned GRUB:
#
#   boot/grub/i386-pc/core.0        BIOS PXE (SeaBIOS/iPXE, PXE option ROMs)
#   boot/grub/x86_64-efi/core.efi   UEFI PXE (firmware PXE over IPv4)
#
# Both loaders take (tftp)/boot/grub as their prefix, so they read the ISO's
# grub.cfg and load /boot/leanos.elf from the same server: the kernel and its
# configuration are the ISO's, only the delivery differs. Serve the tree's
# root over TFTP and point DHCP at one of the two loaders (docs/boot-image.md,
# "Boot media").
#
# usage: build-netboot-tree.sh <iso> <output-dir>
set -euo pipefail

[[ $# -eq 2 ]] || { echo "usage: $0 <iso> <output-dir>" >&2; exit 2; }
image="$1"
output="$2"
[[ -f "$image" ]] || { echo "error: image '$image' not found" >&2; exit 1; }
for tool in xorriso grub-mknetdir; do
  command -v "$tool" >/dev/null 2>&1 || {
    echo "error: missing '$tool'; install Ubuntu packages xorriso=1:1.5.6-1.1ubuntu3 and grub-common=2.12-1ubuntu7.3" >&2
    exit 1
  }
done
for platform in i386-pc x86_64-efi; do
  [[ -d "/usr/lib/grub/$platform" ]] || {
    echo "error: missing GRUB $platform modules; install grub-pc-bin and grub-efi-amd64-bin (2.12-1ubuntu7.3)" >&2
    exit 1
  }
done

rm -rf "$output"
mkdir -p "$output"
xorriso -osirrox on -indev "$image" -extract /boot "$output/boot" >/dev/null 2>&1 || {
  echo "error: could not extract /boot from '$image'" >&2
  exit 1
}
chmod -R u+w "$output"
[[ -f "$output/boot/leanos.elf" && -f "$output/boot/grub/grub.cfg" ]] || {
  echo "error: '$image' has no /boot/leanos.elf and /boot/grub/grub.cfg" >&2
  exit 1
}
for platform in i386-pc x86_64-efi; do
  grub-mknetdir --net-directory="$output" --subdir=boot/grub \
    -d "/usr/lib/grub/$platform" >/dev/null
done
for loader in boot/grub/i386-pc/core.0 boot/grub/x86_64-efi/core.efi; do
  [[ -f "$output/$loader" ]] || { echo "error: grub-mknetdir did not write $loader" >&2; exit 1; }
done
printf 'netboot tree %s: bios=boot/grub/i386-pc/core.0 uefi=boot/grub/x86_64-efi/core.efi\n' "$output"
