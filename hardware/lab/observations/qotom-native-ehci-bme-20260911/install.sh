set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp/leanos-bme-stage-296229d
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = 60c016683940c3b252a7243c384fc97d2e482ed2d2fe74b31b5d2dffd107fe83
test "$(sha256 -q "$stage/leanos.sha256")" = 22ca09bbc55dc645173857734664e337eee5d0187bfc0b3a0bc6c8ff198ca858
test "$(sha256 -q "$stage/grub.cfg")" = 1a1198b957b489629654983ab6bfcee3b29a1d02e2a89506995541c96cf99b62
test ! -e /var/tmp/leanos-before-bme-296229d.tar.gz
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = c9b39bc70e68ee78ec6a7831b1315fe66230a0dd9e7810ded91e28b1a54bd814
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 251aa5c03419f298d10d489563fe5006564fb0bdddbb926dc7df61d03d43c341
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sudo -n tar -czf /var/tmp/leanos-before-bme-296229d.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sudo -n cp "$stage/grub.cfg" "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 60c016683940c3b252a7243c384fc97d2e482ed2d2fe74b31b5d2dffd107fe83
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 1a1198b957b489629654983ab6bfcee3b29a1d02e2a89506995541c96cf99b62
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = 22ca09bbc55dc645173857734664e337eee5d0187bfc0b3a0bc6c8ff198ca858
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv" "$mnt/boot/grub/watchdog-window.cfg" "$mnt/boot/grub/watchdog.cfg"
sysctl kern.boottime
