set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp/leanos-capabilities-stage-69ee9cb
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = 27773506501f290f107cf80b860e8f9a92034496d05b86787240d543b4b3ec37
test "$(sha256 -q "$stage/leanos.sha256")" = d251b97fc4ac368df12b9f22fc02592049126eba816a941585d9af54cd157647
test "$(sha256 -q "$stage/grub.cfg")" = d21dfa818f80b9779604ce9de9ef4b4956d3072c024dc21bff75ce6b05809c13
test ! -e /var/tmp/leanos-before-capabilities-69ee9cb.tar.gz
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = d5e95500e224cc6e85665de6060f5912c21413ebb6693637c936213220521cce
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 5db8b48536a7e52e54542f411f454de0103e57cad8bb8047cdd60235c08f07fb
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sudo -n tar -czf /var/tmp/leanos-before-capabilities-69ee9cb.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sudo -n cp "$stage/grub.cfg" "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 27773506501f290f107cf80b860e8f9a92034496d05b86787240d543b4b3ec37
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = d21dfa818f80b9779604ce9de9ef4b4956d3072c024dc21bff75ce6b05809c13
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = d251b97fc4ac368df12b9f22fc02592049126eba816a941585d9af54cd157647
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv" "$mnt/boot/grub/watchdog-window.cfg" "$mnt/boot/grub/watchdog.cfg"
sysctl kern.boottime
