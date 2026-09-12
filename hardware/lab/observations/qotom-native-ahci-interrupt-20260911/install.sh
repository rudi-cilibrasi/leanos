set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp/leanos-ahci-interrupt-stage-50009b7
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = 917f6c3b53ffa8404a545db651a4c44c1c66add6310a789f08629797c0f73fc8
test "$(sha256 -q "$stage/leanos.sha256")" = 2474ac58d6e821adfe275391eba305ce9ed9337b11cf8e8ab9c9338440cd069f
test "$(sha256 -q "$stage/grub.cfg")" = c3ebd34420bf28836720a8daaf3dd611a414ff88153e9eb807a26c0255b98f0d
test ! -e /var/tmp/leanos-before-ahci-interrupt-50009b7.tar.gz
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = f15d68953a4179897c7b9a075135c722a538e84c77d25bd4561eeba65e810a67
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 8771cd41627553cda668c88e72a5d7d7f5278439951e2ae76ac0b040fb9ecb56
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sudo -n tar -czf /var/tmp/leanos-before-ahci-interrupt-50009b7.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sudo -n cp "$stage/grub.cfg" "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 917f6c3b53ffa8404a545db651a4c44c1c66add6310a789f08629797c0f73fc8
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = c3ebd34420bf28836720a8daaf3dd611a414ff88153e9eb807a26c0255b98f0d
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = 2474ac58d6e821adfe275391eba305ce9ed9337b11cf8e8ab9c9338440cd069f
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv" "$mnt/boot/grub/watchdog-window.cfg" "$mnt/boot/grub/watchdog.cfg"
sysctl kern.boottime
