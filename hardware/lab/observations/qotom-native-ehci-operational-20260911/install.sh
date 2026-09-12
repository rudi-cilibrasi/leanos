set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp/leanos-operational-stage-e42b6ea
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = c9b39bc70e68ee78ec6a7831b1315fe66230a0dd9e7810ded91e28b1a54bd814
test "$(sha256 -q "$stage/leanos.sha256")" = 08f52d909ad03d4980f6979219e8f6082f847da40d0117d0477f4ec444bef003
test "$(sha256 -q "$stage/grub.cfg")" = 251aa5c03419f298d10d489563fe5006564fb0bdddbb926dc7df61d03d43c341
test ! -e /var/tmp/leanos-before-operational-e42b6ea.tar.gz
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 809788ba245bfb3fd332d95a4d21b95c10e933b161f2bd7f2fbeef0c3834d3b2
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 06c4a9db0922db1521ad77679971f87791a6fae39359d47b85a3c9adbbb5d71c
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sudo -n tar -czf /var/tmp/leanos-before-operational-e42b6ea.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sudo -n cp "$stage/grub.cfg" "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = c9b39bc70e68ee78ec6a7831b1315fe66230a0dd9e7810ded91e28b1a54bd814
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 251aa5c03419f298d10d489563fe5006564fb0bdddbb926dc7df61d03d43c341
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = 08f52d909ad03d4980f6979219e8f6082f847da40d0117d0477f4ec444bef003
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv" "$mnt/boot/grub/watchdog-window.cfg" "$mnt/boot/grub/watchdog.cfg"
sysctl kern.boottime
