#!/usr/bin/env sh
set -eu
old=4eb39eaa138a2b1b71396fa5e64f9811bcc6781ab8bf23de3f6ac72e77e10619
new=747e1a96d123ec7e429a33cf8fa3f9daa1e9aedb0f653d7c21fe627ed78c41d8
test "$(sudo -n geom disk list da0 | awk '/ident:/ {print $2; exit}')" = 11758C40
test "$(sha256 -q /var/tmp/leanos-qotom-screen.elf)" = "$new"
sudo -n mount -t msdosfs /dev/da0s1 /mnt/leanos-usb
trap 'cd /; sudo -n umount /mnt/leanos-usb' EXIT
test "$(sha256 -q /mnt/leanos-usb/boot/leanos-qotom-lab.elf)" = "$old"
grep -a -q '^request=none$' /mnt/leanos-usb/boot/grub/grubenv
sudo -n cp /var/tmp/leanos-qotom-screen.elf /mnt/leanos-usb/boot/leanos-qotom-lab.elf.new
sudo -n cp /var/tmp/grub-screen.cfg /mnt/leanos-usb/boot/grub/grub.cfg.new
sudo -n cp /var/tmp/leanos-screen.sha256 /mnt/leanos-usb/boot/leanos.sha256.new
test "$(sha256 -q /mnt/leanos-usb/boot/leanos-qotom-lab.elf.new)" = "$new"
sudo -n mv /mnt/leanos-usb/boot/leanos-qotom-lab.elf.new /mnt/leanos-usb/boot/leanos-qotom-lab.elf
sudo -n mv /mnt/leanos-usb/boot/grub/grub.cfg.new /mnt/leanos-usb/boot/grub/grub.cfg
sudo -n mv /mnt/leanos-usb/boot/leanos.sha256.new /mnt/leanos-usb/boot/leanos.sha256
sudo -n sync
test "$(sha256 -q /mnt/leanos-usb/boot/leanos-qotom-lab.elf)" = "$new"
test "$(grep -c "$new" /mnt/leanos-usb/boot/grub/grub.cfg)" -eq 3
grep -a -q '^request=none$' /mnt/leanos-usb/boot/grub/grubenv
