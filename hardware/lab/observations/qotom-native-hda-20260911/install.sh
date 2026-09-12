set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp/leanos-hda-stage-eac5ee6
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = 10eefd4102584d38a0d8e6f4d9babf57b3f9539527cafa366f1e691acd1ba13c
test "$(sha256 -q "$stage/leanos.sha256")" = 941197ece8c9a307a855717a4c3be10718ed30f09c9c94bb11dfad0f95a0c139
test "$(sha256 -q "$stage/grub.cfg")" = 5244073aabbe1a3f4e6d594b4c5159ffd5eab8e4825cde2e05e9cc1e1d84d1e6
test ! -e /var/tmp/leanos-before-hda-eac5ee6.tar.gz
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 2a005a751847f83a735c5ba2fae8a92463a09a7a0704f318ba0cdd6df993c0a1
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 039c9217812c86da182bac121a06223667faa1f72034f89dda7b4246e5f9e032
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sudo -n tar -czf /var/tmp/leanos-before-hda-eac5ee6.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sudo -n cp "$stage/grub.cfg" "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 10eefd4102584d38a0d8e6f4d9babf57b3f9539527cafa366f1e691acd1ba13c
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 5244073aabbe1a3f4e6d594b4c5159ffd5eab8e4825cde2e05e9cc1e1d84d1e6
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = 941197ece8c9a307a855717a4c3be10718ed30f09c9c94bb11dfad0f95a0c139
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv" "$mnt/boot/grub/watchdog-window.cfg" "$mnt/boot/grub/watchdog.cfg"
sysctl kern.boottime
