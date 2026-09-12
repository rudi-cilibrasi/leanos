set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp/leanos-txe-status-stage-9f8f0b0
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = 2b2953d3aa0395f7b7691d65ee47ec227a5efd6cee13f1e64c9ffa0f4f7d19e3
test "$(sha256 -q "$stage/leanos.sha256")" = dc7fd76bc361c70fc372ba648b414a7cc452f81000380b97b3b53eed1cd161eb
test "$(sha256 -q "$stage/grub.cfg")" = 6e9816341db1a5b85be42ea1ae0df5077c5d278171025b93c6859fa395b00855
test ! -e /var/tmp/leanos-before-txe-status-9f8f0b0.tar.gz
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 28b53a1769147eea00f7b6cdd1e826d5207b1080df12b5495b2d8b063e7804db
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = dcee6e8eca2fd6b20110352abd10f3df7b8b52e0e0633859a5fc54e09b54fd22
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sudo -n tar -czf /var/tmp/leanos-before-txe-status-9f8f0b0.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sudo -n cp "$stage/grub.cfg" "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 2b2953d3aa0395f7b7691d65ee47ec227a5efd6cee13f1e64c9ffa0f4f7d19e3
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 6e9816341db1a5b85be42ea1ae0df5077c5d278171025b93c6859fa395b00855
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = dc7fd76bc361c70fc372ba648b414a7cc452f81000380b97b3b53eed1cd161eb
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv" "$mnt/boot/grub/watchdog-window.cfg" "$mnt/boot/grub/watchdog.cfg"
sysctl kern.boottime
