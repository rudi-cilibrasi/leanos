set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp/leanos-ahci-port-stage-1543c35
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = f15d68953a4179897c7b9a075135c722a538e84c77d25bd4561eeba65e810a67
test "$(sha256 -q "$stage/leanos.sha256")" = 968ecd5c6d3e0efdc2d77b518c416b66f0be64b6b929df2c90797c79416e2d02
test "$(sha256 -q "$stage/grub.cfg")" = 8771cd41627553cda668c88e72a5d7d7f5278439951e2ae76ac0b040fb9ecb56
test ! -e /var/tmp/leanos-before-ahci-port-1543c35.tar.gz
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = ed5959168554891957b49d7aae7a0618f39874ba40eb5810a98ddfd8ab3dbc90
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = a45c7340ef76dc9db888d8bbe58b61144483231d12fcae29a25a9ac58f229972
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sudo -n tar -czf /var/tmp/leanos-before-ahci-port-1543c35.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sudo -n cp "$stage/grub.cfg" "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = f15d68953a4179897c7b9a075135c722a538e84c77d25bd4561eeba65e810a67
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 8771cd41627553cda668c88e72a5d7d7f5278439951e2ae76ac0b040fb9ecb56
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = 968ecd5c6d3e0efdc2d77b518c416b66f0be64b6b929df2c90797c79416e2d02
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv" "$mnt/boot/grub/watchdog-window.cfg" "$mnt/boot/grub/watchdog.cfg"
sysctl kern.boottime
