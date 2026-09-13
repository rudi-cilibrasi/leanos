#!/usr/bin/env sh
set -eu
old=9ee190af8aa4ba2485187e7118025aa584f25e5a14b2682044a3faf245734a94
new=2ca33caa063698c1648fbc630c27d8c9ccc46031553ef479de881b792b51e9e5
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
test "$(sha256 -q /var/tmp/leanos-qotom-lab.elf)" = "$new"
sudo -n mount -t msdosfs /dev/da0s1 /mnt/leanos-lab
trap 'cd /; sudo -n umount /mnt/leanos-lab' EXIT
test "$(sha256 -q /mnt/leanos-lab/boot/leanos-qotom-lab.elf)" = "$old"
# The FAT volume was full. Remove only named obsolete experiment backups while
# retaining leanos-qotom-lab.elf.backup-blocking-pass as the recovery image.
sudo -n rm -f \
  /mnt/leanos-lab/boot/leanos-qotom-lab.elf.backup-9ee190af \
  /mnt/leanos-lab/boot/leanos-qotom-lab.elf.backup-4863c3de \
  /mnt/leanos-lab/boot/leanos-qotom-lab.elf.backup-6092c00a \
  /mnt/leanos-lab/boot/leanos-qotom-lab.elf.backup-7e3c9c0c
sudo -n cp /var/tmp/leanos-qotom-lab.elf \
  /mnt/leanos-lab/boot/leanos-qotom-lab.elf.platform-staged
test "$(sha256 -q /mnt/leanos-lab/boot/leanos-qotom-lab.elf.platform-staged)" = "$new"
sudo -n mv /mnt/leanos-lab/boot/leanos-qotom-lab.elf.platform-staged \
  /mnt/leanos-lab/boot/leanos-qotom-lab.elf
sudo -n cp /var/tmp/grub.cfg /mnt/leanos-lab/boot/grub/grub.cfg
sudo -n cp /var/tmp/leanos.sha256 /mnt/leanos-lab/boot/leanos.sha256
sudo -n sync
test "$(sha256 -q /mnt/leanos-lab/boot/leanos-qotom-lab.elf)" = "$new"
grep -a -q '^request=none$' /mnt/leanos-lab/boot/grub/grubenv
