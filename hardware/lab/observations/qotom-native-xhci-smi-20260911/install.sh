set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp/leanos-xhci-smi-stage-0d3cca0
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = 310520a9aec783f084fdd48253f8ba293b3a06968d443375806b10387ad70f94
test "$(sha256 -q "$stage/leanos.sha256")" = f7002c2ca64c3b4f53f31a894e9be117d68693b5a7a5693919db1dfb448b80bc
test "$(sha256 -q "$stage/grub.cfg")" = 2c8f4c72633fca13ba565397ef766c8dea67b585292b02340dc086ff7f5208ba
test ! -e /var/tmp/leanos-before-xhci-smi-0d3cca0.tar.gz
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 823ae01d773058aec8ea12af0029e3632470be96051e98cdf462097005e0bdb3
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = c98b08c33d820f0201ff353c0712d675f6ee5627a9559d68bd80dc5a4eba7387
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sudo -n tar -czf /var/tmp/leanos-before-xhci-smi-0d3cca0.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sudo -n cp "$stage/grub.cfg" "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 310520a9aec783f084fdd48253f8ba293b3a06968d443375806b10387ad70f94
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 2c8f4c72633fca13ba565397ef766c8dea67b585292b02340dc086ff7f5208ba
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = f7002c2ca64c3b4f53f31a894e9be117d68693b5a7a5693919db1dfb448b80bc
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv" "$mnt/boot/grub/watchdog-window.cfg" "$mnt/boot/grub/watchdog.cfg"
sysctl kern.boottime
