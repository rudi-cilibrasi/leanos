set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp/leanos-handoff-stage-48198c8
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = 0ff805e5f956ddbf6f82cd8b6c81128ce0097ec0fd3c809cc24907b8b3bf2897
test "$(sha256 -q "$stage/leanos.sha256")" = 2a5788dda34d0ab1fe346dbdfb88430c26d1107d19729b9898731eb8c31312c6
test "$(sha256 -q "$stage/grub.cfg")" = f89b65fa7a9b5f756a64da095ed5883000131cf6302385f37b8642b8707dfb87
test ! -e /var/tmp/leanos-before-handoff-48198c8.tar.gz
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 64a5e46f2f99c3d273569be2abea03e9633e11817cc8123657532e0510810723
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = b015f099870dd252b0ee91f636269297dc24a18e793c25c35a4a98235fa3c6b6
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sudo -n tar -czf /var/tmp/leanos-before-handoff-48198c8.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sudo -n cp "$stage/grub.cfg" "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 0ff805e5f956ddbf6f82cd8b6c81128ce0097ec0fd3c809cc24907b8b3bf2897
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = f89b65fa7a9b5f756a64da095ed5883000131cf6302385f37b8642b8707dfb87
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = 2a5788dda34d0ab1fe346dbdfb88430c26d1107d19729b9898731eb8c31312c6
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv" "$mnt/boot/grub/watchdog-window.cfg" "$mnt/boot/grub/watchdog.cfg"
sysctl kern.boottime
