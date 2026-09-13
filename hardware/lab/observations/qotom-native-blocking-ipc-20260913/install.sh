#!/usr/bin/env sh
set -eu
old=7e3c9c0ccffb0fb94888d5c189d902dbec93094e98ede80468a4370dae52e4fa
new=61e5a57715f48fe2e80888381a2178ad49d2ea088d3effa1ce0202bd7c0b6638
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
test "$(sha256 -q /var/tmp/leanos-qotom-lab.elf)" = "$new"
sudo -n mount -t msdosfs /dev/da0s1 /mnt/leanos-lab
trap 'sudo -n umount /mnt/leanos-lab' EXIT
test "$(sha256 -q /mnt/leanos-lab/boot/leanos-qotom-lab.elf)" = "$old"
sudo -n cp /mnt/leanos-lab/boot/leanos-qotom-lab.elf \
  /mnt/leanos-lab/boot/leanos-qotom-lab.elf.backup-7e3c9c0c
sudo -n cp /mnt/leanos-lab/boot/grub/grub.cfg \
  /mnt/leanos-lab/boot/grub/grub.cfg.backup-7e3c9c0c
sudo -n cp /mnt/leanos-lab/boot/leanos.sha256 \
  /mnt/leanos-lab/boot/leanos.sha256.backup-7e3c9c0c
sudo -n cp /var/tmp/leanos-qotom-lab.elf \
  /mnt/leanos-lab/boot/leanos-qotom-lab.elf
sudo -n cp /var/tmp/grub.cfg /mnt/leanos-lab/boot/grub/grub.cfg
sudo -n cp /var/tmp/leanos.sha256 /mnt/leanos-lab/boot/leanos.sha256
sudo -n sync
test "$(sha256 -q /mnt/leanos-lab/boot/leanos-qotom-lab.elf)" = "$new"
grep -a -q '^request=none$' /mnt/leanos-lab/boot/grub/grubenv
