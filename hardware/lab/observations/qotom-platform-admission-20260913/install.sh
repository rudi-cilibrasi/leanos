#!/usr/bin/env sh
set -eu
old=49e0e67d52a914904d1615d3f4ee2da8d11d08b83b1ab7ef2bdadf03ea69d18f
new=4eb39eaa138a2b1b71396fa5e64f9811bcc6781ab8bf23de3f6ac72e77e10619
test "$(sudo -n geom disk list da0 | awk '/ident:/ {print $2; exit}')" = 11758C40
test "$(sha256 -q /var/tmp/leanos-qotom-lab.uart.elf)" = "$new"
sudo -n mount -t msdosfs /dev/da0s1 /mnt/leanos-usb
trap 'cd /; sudo -n umount /mnt/leanos-usb' EXIT
test "$(sha256 -q /mnt/leanos-usb/boot/leanos-qotom-lab.elf)" = "$old"
grep -a -q '^request=none$' /mnt/leanos-usb/boot/grub/grubenv
sudo -n cp /var/tmp/leanos-qotom-lab.uart.elf   /mnt/leanos-usb/boot/leanos-qotom-lab.elf.new
sudo -n cp /var/tmp/grub-platform-uart.cfg   /mnt/leanos-usb/boot/grub/grub.cfg.new
sudo -n cp /var/tmp/leanos-platform-uart.sha256   /mnt/leanos-usb/boot/leanos.sha256.new
test "$(sha256 -q /mnt/leanos-usb/boot/leanos-qotom-lab.elf.new)" = "$new"
sudo -n mv /mnt/leanos-usb/boot/leanos-qotom-lab.elf.new   /mnt/leanos-usb/boot/leanos-qotom-lab.elf
sudo -n mv /mnt/leanos-usb/boot/grub/grub.cfg.new   /mnt/leanos-usb/boot/grub/grub.cfg
sudo -n mv /mnt/leanos-usb/boot/leanos.sha256.new   /mnt/leanos-usb/boot/leanos.sha256
sudo -n sync
test "$(sha256 -q /mnt/leanos-usb/boot/leanos-qotom-lab.elf)" = "$new"
test "$(grep -c "$new" /mnt/leanos-usb/boot/grub/grub.cfg)" -eq 3
grep -a -q '^request=none$' /mnt/leanos-usb/boot/grub/grubenv
