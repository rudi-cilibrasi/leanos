set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp/leanos-xhci-bme-stage-9bd2f52
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = 42e3c9588f03cc9627f460d62e004a4a4251359607c17d2088d74285c52b4967
test "$(sha256 -q "$stage/leanos.sha256")" = b60aa7c2e2d2c29cfae92e4869d6996c391c4d65aad3dc740976fbee76d6bed4
test "$(sha256 -q "$stage/grub.cfg")" = 8bb43e5638fa7054cdfe72ad9dc18748f38e5e80baab99f35776d0191dc1febf
test ! -e /var/tmp/leanos-before-xhci-bme-9bd2f52.tar.gz
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = e04546479e316e4086a3005fdc55e95740b195309889d0286e956b064fc20721
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = cc4bc5e1604d912e77b454d603e4e47690566d72928dbbf0d31dfee3fe4194b2
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sudo -n tar -czf /var/tmp/leanos-before-xhci-bme-9bd2f52.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sudo -n cp "$stage/grub.cfg" "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 42e3c9588f03cc9627f460d62e004a4a4251359607c17d2088d74285c52b4967
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 8bb43e5638fa7054cdfe72ad9dc18748f38e5e80baab99f35776d0191dc1febf
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = b60aa7c2e2d2c29cfae92e4869d6996c391c4d65aad3dc740976fbee76d6bed4
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv" "$mnt/boot/grub/watchdog-window.cfg" "$mnt/boot/grub/watchdog.cfg"
sysctl kern.boottime
