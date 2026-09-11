set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp/leanos-legacy-stage-5e95558
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = 64a5e46f2f99c3d273569be2abea03e9633e11817cc8123657532e0510810723
test "$(sha256 -q "$stage/leanos.sha256")" = 2f3749a622ed9167babbbe59fa7600144b3161dd0635bc125e3c4343ee319f0a
test "$(sha256 -q "$stage/grub.cfg")" = b015f099870dd252b0ee91f636269297dc24a18e793c25c35a4a98235fa3c6b6
test ! -e /var/tmp/leanos-before-legacy-5e95558.tar.gz
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 98ca8356b613e4f0ff7bfd6f80a6f5e461c56ba37b5a5f59d66ac404a3bd7982
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 32acba68774d438370c9282d073ae61205a9456e322ac232e59d689d4450408b
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sudo -n tar -czf /var/tmp/leanos-before-legacy-5e95558.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sudo -n cp "$stage/grub.cfg" "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 64a5e46f2f99c3d273569be2abea03e9633e11817cc8123657532e0510810723
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = b015f099870dd252b0ee91f636269297dc24a18e793c25c35a4a98235fa3c6b6
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = 2f3749a622ed9167babbbe59fa7600144b3161dd0635bc125e3c4343ee319f0a
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv" "$mnt/boot/grub/watchdog-window.cfg" "$mnt/boot/grub/watchdog.cfg"
sysctl kern.boottime
