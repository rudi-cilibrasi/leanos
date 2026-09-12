set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp/leanos-pcie-device-stage-387f2fb
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = f26096ec00ab2a04b6d8fc5f204c15d78bc06ef52eed8bbfd4816dcdfb4f7c92
test "$(sha256 -q "$stage/leanos.sha256")" = 4c8f5e884d5b665f5f14e88758523433376b0b701b2455120e860694ac8df3a4
test "$(sha256 -q "$stage/grub.cfg")" = f3fe72b79a8c094bad0e9b3edf0c290160c6fb52a03081e9e20ecda5f2de4711
test ! -e /var/tmp/leanos-before-pcie-device-387f2fb.tar.gz
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 42e3c9588f03cc9627f460d62e004a4a4251359607c17d2088d74285c52b4967
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 8bb43e5638fa7054cdfe72ad9dc18748f38e5e80baab99f35776d0191dc1febf
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sudo -n tar -czf /var/tmp/leanos-before-pcie-device-387f2fb.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sudo -n cp "$stage/grub.cfg" "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = f26096ec00ab2a04b6d8fc5f204c15d78bc06ef52eed8bbfd4816dcdfb4f7c92
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = f3fe72b79a8c094bad0e9b3edf0c290160c6fb52a03081e9e20ecda5f2de4711
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = 4c8f5e884d5b665f5f14e88758523433376b0b701b2455120e860694ac8df3a4
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv" "$mnt/boot/grub/watchdog-window.cfg" "$mnt/boot/grub/watchdog.cfg"
sysctl kern.boottime
