set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp/leanos-ahci-bme-stage-0ce3766
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = 2a005a751847f83a735c5ba2fae8a92463a09a7a0704f318ba0cdd6df993c0a1
test "$(sha256 -q "$stage/leanos.sha256")" = 12981aeee90601bc2f55c72dd3ae2e5d65e8f273868a592ae7f401d6dbc1e3ff
test "$(sha256 -q "$stage/grub.cfg")" = 039c9217812c86da182bac121a06223667faa1f72034f89dda7b4246e5f9e032
test ! -e /var/tmp/leanos-before-ahci-bme-0ce3766.tar.gz
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 917f6c3b53ffa8404a545db651a4c44c1c66add6310a789f08629797c0f73fc8
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = c3ebd34420bf28836720a8daaf3dd611a414ff88153e9eb807a26c0255b98f0d
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sudo -n tar -czf /var/tmp/leanos-before-ahci-bme-0ce3766.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sudo -n cp "$stage/grub.cfg" "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 2a005a751847f83a735c5ba2fae8a92463a09a7a0704f318ba0cdd6df993c0a1
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 039c9217812c86da182bac121a06223667faa1f72034f89dda7b4246e5f9e032
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = 12981aeee90601bc2f55c72dd3ae2e5d65e8f273868a592ae7f401d6dbc1e3ff
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv" "$mnt/boot/grub/watchdog-window.cfg" "$mnt/boot/grub/watchdog.cfg"
sysctl kern.boottime
