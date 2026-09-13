#!/usr/bin/env sh
set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
mnt=/mnt/leanos-install
backup=/var/tmp/leanos-before-copy-root-75d666b.tar.gz
test "$(sha256 -q /var/tmp/leanos-copy-root-lab.elf)" = 16ccf8f1e0e62c88b02a2c8b1a8cca75c31a7341fa9bdcbe6aba733d6293e74c
test "$(sha256 -q /var/tmp/qotom-grub-copy-root.cfg)" = 245db2f08ed3d6f5af5f04ebc3b57d9ad5625b2e772a2b2b874a996b09f45756
test "$(sha256 -q /var/tmp/leanos-copy-root.sha256)" = 900bca428dbc5233470a4ec3ba213b14b65871029a9b1fe8e28f74bb40fed1e4
test ! -e "$backup"
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
grep -a -q '^request=none$' "$mnt/boot/grub/grubenv"
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 68cb36fd3e4201c552e1a8debd24f52be51a96eaf182e6814f2eb8c1ec2c0d6d
sudo -n tar -czf "$backup" -C "$mnt" boot
sudo -n cp /var/tmp/leanos-copy-root-lab.elf "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp /var/tmp/qotom-grub-copy-root.cfg "$mnt/boot/grub/grub.cfg"
sudo -n cp /var/tmp/leanos-copy-root.sha256 "$mnt/boot/leanos.sha256"
sync
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 16ccf8f1e0e62c88b02a2c8b1a8cca75c31a7341fa9bdcbe6aba733d6293e74c
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 245db2f08ed3d6f5af5f04ebc3b57d9ad5625b2e772a2b2b874a996b09f45756
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = 900bca428dbc5233470a4ec3ba213b14b65871029a9b1fe8e28f74bb40fed1e4
grep -a -q '^request=none$' "$mnt/boot/grub/grubenv"
