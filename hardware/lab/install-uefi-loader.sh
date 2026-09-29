#!/usr/bin/env sh
# Add the UEFI GRUB loader to the existing Qotom lab USB stick (run on
# FreeBSD). The stick keeps its i386-pc GRUB in the MBR; UEFI firmware loads
# EFI/BOOT/BOOTX64.EFI from the same FAT partition, and both loaders read
# boot/grub/grub.cfg, whose FreeBSD chain is firmware-aware.
# usage: install-uefi-loader.sh <bootx64-sha256> <grub-cfg-sha256>
# Expects /var/tmp/BOOTX64.EFI (scripts/build-efi-grub.sh binary) and
# /var/tmp/grub-uefi.cfg (a rendered hardware/lab/grub-qotom-ssd.cfg.in).
set -eu
loader=$1
config=$2
test "$(sudo -n geom disk list da0 | awk '/ident:/ {print $2; exit}')" = 11758C40
test "$(sha256 -q /var/tmp/BOOTX64.EFI)" = "$loader"
test "$(sha256 -q /var/tmp/grub-uefi.cfg)" = "$config"
grep -q 'chainloader ($disk,gpt1)/efi/freebsd/loader.efi' /var/tmp/grub-uefi.cfg
sudo -n mkdir -p /mnt/leanos-usb
sudo -n mount -t msdosfs /dev/da0s1 /mnt/leanos-usb
trap 'cd /; sudo -n umount /mnt/leanos-usb' EXIT
grep -a -q '^request=none$' /mnt/leanos-usb/boot/grub/grubenv
# Keep the BIOS-only configuration once, for manual rollback.
if [ ! -f /mnt/leanos-usb/boot/grub/grub.cfg.pre-uefi ]; then
  sudo -n cp /mnt/leanos-usb/boot/grub/grub.cfg /mnt/leanos-usb/boot/grub/grub.cfg.pre-uefi
fi
sudo -n mkdir -p /mnt/leanos-usb/EFI/BOOT
sudo -n cp /var/tmp/BOOTX64.EFI /mnt/leanos-usb/EFI/BOOT/BOOTX64.EFI.new
sudo -n cp /var/tmp/grub-uefi.cfg /mnt/leanos-usb/boot/grub/grub.cfg.new
test "$(sha256 -q /mnt/leanos-usb/EFI/BOOT/BOOTX64.EFI.new)" = "$loader"
test "$(sha256 -q /mnt/leanos-usb/boot/grub/grub.cfg.new)" = "$config"
sudo -n mv /mnt/leanos-usb/EFI/BOOT/BOOTX64.EFI.new /mnt/leanos-usb/EFI/BOOT/BOOTX64.EFI
sudo -n mv /mnt/leanos-usb/boot/grub/grub.cfg.new /mnt/leanos-usb/boot/grub/grub.cfg
sudo -n sync
echo "installed UEFI loader $loader and grub.cfg $config"
