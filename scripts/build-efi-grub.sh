#!/usr/bin/env bash
# Deterministic x86_64 UEFI GRUB for LeanOS boot media.
#
# The BIOS (i386-pc) and UEFI (x86_64-efi) loaders share every grub.cfg and
# hand LeanOS the same Multiboot2 32-bit protected-mode entry, so only the
# loader binary differs between firmware families.  The EFI loader is one
# monolithic image: every module a LeanOS or lab configuration uses is built
# in, so `insmod` lines succeed without a module directory on the medium.
#
# usage: build-efi-grub.sh binary <out.efi> [<embedded.cfg>]
#        build-efi-grub.sh esp-image <out.img> <in.efi>
#
# `binary` writes BOOTX64.EFI with prefix /boot/grub; without an embedded
# configuration GRUB takes the prefix device from the partition it was loaded
# from (a USB stick's FAT).  `esp-image` wraps a binary in a 1440 KiB FAT12
# image at EFI/BOOT/BOOTX64.EFI, as the El Torito UEFI boot entry of an ISO.
# Both outputs are byte-reproducible: grub-mkimage embeds no time, and the
# FAT uses a fixed serial, SOURCE_DATE_EPOCH file times, and a pre-zeroed
# file (mformat -C leaks uninitialised stack bytes into the last sector).
set -euo pipefail

readonly LEANOS_EFI_GRUB_MODULES=(
  normal configfile echo test true sleep reboot halt boot
  search search_fs_file search_fs_uuid probe regexp
  part_gpt part_msdos fat iso9660
  serial terminal loadenv hashsum gcry_sha256
  multiboot2 chain
  setpci iorw memrw datehook
)
readonly LEANOS_EFI_GRUB_MODULE_ROOT=/usr/lib/grub/x86_64-efi
readonly LEANOS_EFI_FAT_SERIAL=4c45414e   # "LEAN"
readonly LEANOS_EFI_SOURCE_DATE_EPOCH=946684800   # 2000-01-01T00:00:00Z

usage() {
  sed -n 's/^# usage: /usage: /p; s/^#        /       /p' "$0" | head -2 >&2
  exit 2
}

[[ -d "$LEANOS_EFI_GRUB_MODULE_ROOT" ]] || {
  echo "error: missing GRUB UEFI modules; install Ubuntu package grub-efi-amd64-bin=2.12-1ubuntu7.3" >&2
  exit 1
}

case "${1:-}" in
  binary)
    [[ $# -eq 2 || $# -eq 3 ]] || usage
    output="$2"
    embedded=()
    if [[ $# -eq 3 ]]; then
      [[ -f "$3" ]] || { echo "error: embedded config '$3' not found" >&2; exit 1; }
      embedded=(-c "$3")
    fi
    grub-mkimage -O x86_64-efi -d "$LEANOS_EFI_GRUB_MODULE_ROOT" \
      -p /boot/grub "${embedded[@]}" -o "$output.tmp" \
      "${LEANOS_EFI_GRUB_MODULES[@]}"
    mv "$output.tmp" "$output"
    ;;
  esp-image)
    [[ $# -eq 3 && -f "$3" ]] || usage
    output="$2"
    export SOURCE_DATE_EPOCH="$LEANOS_EFI_SOURCE_DATE_EPOCH"
    export MTOOLS_SKIP_CHECK=1
    rm -f "$output.tmp"
    truncate -s 1440K "$output.tmp"
    mformat -f 1440 -N "$LEANOS_EFI_FAT_SERIAL" -i "$output.tmp" ::
    mmd -i "$output.tmp" ::/EFI ::/EFI/BOOT
    mcopy -i "$output.tmp" "$3" ::/EFI/BOOT/BOOTX64.EFI
    mv "$output.tmp" "$output"
    ;;
  *) usage ;;
esac
