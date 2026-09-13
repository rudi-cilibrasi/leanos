#!/usr/bin/env sh
set -eu
old=2ca33caa063698c1648fbc630c27d8c9ccc46031553ef479de881b792b51e9e5
new=49e0e67d52a914904d1615d3f4ee2da8d11d08b83b1ab7ef2bdadf03ea69d18f
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
test "$(sha256 -q /var/tmp/leanos-qotom-lab.live.elf)" = "$new"
sudo -n mount -t msdosfs /dev/da0s1 /mnt/leanos-lab
trap 'cd /; sudo -n umount /mnt/leanos-lab' EXIT
test "$(sha256 -q /mnt/leanos-lab/boot/leanos-qotom-lab.elf)" = "$old"
sudo -n cp /var/tmp/leanos-qotom-lab.live.elf \
  /mnt/leanos-lab/boot/leanos-qotom-lab.elf.platform-staged
test "$(sha256 -q /mnt/leanos-lab/boot/leanos-qotom-lab.elf.platform-staged)" = "$new"
sudo -n mv /mnt/leanos-lab/boot/leanos-qotom-lab.elf.platform-staged \
  /mnt/leanos-lab/boot/leanos-qotom-lab.elf
sudo -n cp /var/tmp/grub-platform-live.cfg /mnt/leanos-lab/boot/grub/grub.cfg
sudo -n cp /var/tmp/leanos-platform-live.sha256 /mnt/leanos-lab/boot/leanos.sha256
sudo -n sync
test "$(sha256 -q /mnt/leanos-lab/boot/leanos-qotom-lab.elf)" = "$new"
grep -a -q '^request=none$' /mnt/leanos-lab/boot/grub/grubenv
