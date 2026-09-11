set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp/leanos-xhci-operational-stage-2d2a350
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = e04546479e316e4086a3005fdc55e95740b195309889d0286e956b064fc20721
test "$(sha256 -q "$stage/leanos.sha256")" = 09b8d3806c0e06fd9af278bb18355b08cd1d198c73ef8693b9f1df8df2139b8f
test "$(sha256 -q "$stage/grub.cfg")" = cc4bc5e1604d912e77b454d603e4e47690566d72928dbbf0d31dfee3fe4194b2
test ! -e /var/tmp/leanos-before-xhci-operational-2d2a350.tar.gz
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 310520a9aec783f084fdd48253f8ba293b3a06968d443375806b10387ad70f94
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 2c8f4c72633fca13ba565397ef766c8dea67b585292b02340dc086ff7f5208ba
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sudo -n tar -czf /var/tmp/leanos-before-xhci-operational-2d2a350.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sudo -n cp "$stage/grub.cfg" "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = e04546479e316e4086a3005fdc55e95740b195309889d0286e956b064fc20721
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = cc4bc5e1604d912e77b454d603e4e47690566d72928dbbf0d31dfee3fe4194b2
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = 09b8d3806c0e06fd9af278bb18355b08cd1d198c73ef8693b9f1df8df2139b8f
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv" "$mnt/boot/grub/watchdog-window.cfg" "$mnt/boot/grub/watchdog.cfg"
sysctl kern.boottime
