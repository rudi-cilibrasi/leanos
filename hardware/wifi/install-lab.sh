#!/usr/bin/env sh
# Install a LeanOS WiFi lab ELF on the Qotom USB stick (run on FreeBSD).
# usage: install-lab.sh <old-elf-sha256> <new-elf-sha256>
# Expects /var/tmp/leanos-wifi.elf, /var/tmp/grub-wifi.cfg, /var/tmp/leanos-wifi.sha256.
set -eu
old=$1
new=$2
test "$(sudo -n geom disk list da0 | awk '/ident:/ {print $2; exit}')" = 11758C40
test "$(sha256 -q /var/tmp/leanos-wifi.elf)" = "$new"
test "$(grep -c "$new" /var/tmp/grub-wifi.cfg)" -eq 3
sudo -n mkdir -p /mnt/leanos-usb
sudo -n mount -t msdosfs /dev/da0s1 /mnt/leanos-usb
trap 'cd /; sudo -n umount /mnt/leanos-usb' EXIT
test "$(sha256 -q /mnt/leanos-usb/boot/leanos-qotom-lab.elf)" = "$old"
grep -a -q '^request=none$' /mnt/leanos-usb/boot/grub/grubenv
if [ ! -f "/mnt/leanos-usb/boot/leanos-qotom-lab.elf.$old" ]; then
  sudo -n cp /mnt/leanos-usb/boot/leanos-qotom-lab.elf "/mnt/leanos-usb/boot/leanos-qotom-lab.elf.$old"
  sudo -n cp /mnt/leanos-usb/boot/grub/grub.cfg "/mnt/leanos-usb/boot/grub/grub.cfg.$old"
fi
sudo -n cp /var/tmp/leanos-wifi.elf /mnt/leanos-usb/boot/leanos-qotom-lab.elf.new
sudo -n cp /var/tmp/grub-wifi.cfg /mnt/leanos-usb/boot/grub/grub.cfg.new
sudo -n cp /var/tmp/leanos-wifi.sha256 /mnt/leanos-usb/boot/leanos.sha256.new
test "$(sha256 -q /mnt/leanos-usb/boot/leanos-qotom-lab.elf.new)" = "$new"
sudo -n mv /mnt/leanos-usb/boot/leanos-qotom-lab.elf.new /mnt/leanos-usb/boot/leanos-qotom-lab.elf
sudo -n mv /mnt/leanos-usb/boot/grub/grub.cfg.new /mnt/leanos-usb/boot/grub/grub.cfg
sudo -n mv /mnt/leanos-usb/boot/leanos.sha256.new /mnt/leanos-usb/boot/leanos.sha256
sudo -n sync
test "$(sha256 -q /mnt/leanos-usb/boot/leanos-qotom-lab.elf)" = "$new"
test "$(grep -c "$new" /mnt/leanos-usb/boot/grub/grub.cfg)" -eq 3
grep -a -q '^request=none$' /mnt/leanos-usb/boot/grub/grubenv
echo "installed $new"
