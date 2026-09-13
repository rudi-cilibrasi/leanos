#!/usr/bin/env sh
set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
mnt=/mnt/leanos-install
backup=/var/tmp/leanos-before-nosmap-control-309586b.tar.gz
test "$(sha256 -q /var/tmp/leanos-qotom-lab.elf)" = 68cb36fd3e4201c552e1a8debd24f52be51a96eaf182e6814f2eb8c1ec2c0d6d
test "$(sha256 -q /var/tmp/qotom-grub-nosmap.cfg)" = 3de619d44b03ffdfba73e8bffe0c297101413553e385f6b8452d42519af721ed
test "$(sha256 -q /var/tmp/leanos-nosmap.sha256)" = c473cd46ddf7cbc229104c034e4a628614716e2ecad5f3a52e8b13392d74632c
test ! -e "$backup"
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
grep -a -q '^request=none$' "$mnt/boot/grub/grubenv"
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 97e9c6e6be402c4c6eebab63664f7f93074abdbb01f8345f8bc2abe01600bcd9
sudo -n tar -czf "$backup" -C "$mnt" boot
sudo -n cp /var/tmp/leanos-qotom-lab.elf "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp /var/tmp/qotom-grub-nosmap.cfg "$mnt/boot/grub/grub.cfg"
sudo -n cp /var/tmp/leanos-nosmap.sha256 "$mnt/boot/leanos.sha256"
sync
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 68cb36fd3e4201c552e1a8debd24f52be51a96eaf182e6814f2eb8c1ec2c0d6d
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 3de619d44b03ffdfba73e8bffe0c297101413553e385f6b8452d42519af721ed
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = c473cd46ddf7cbc229104c034e4a628614716e2ecad5f3a52e8b13392d74632c
grep -a -q '^request=none$' "$mnt/boot/grub/grubenv"
