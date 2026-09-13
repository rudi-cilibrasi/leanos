set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp/leanos-broadcom-d3-stage-255546ca
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = 255546caf21a680b1114817f1874e3d08c5d3e8e524155ddfae38b64bab94110
test "$(sha256 -q "$stage/leanos.sha256")" = 4f039142623cc5b1ab88e92681923e03a3124f4413a93f763a0318ec44b59d75
test "$(sha256 -q "$stage/grub.cfg")" = 95b585839f63f75963f76bbfe71bac49871feb9292bdc0766b4773b1eb5d0980
test ! -e /var/tmp/leanos-before-broadcom-d3-255546ca.tar.gz
sudo -n mkdir -p "$mnt"
if mount | grep -q "on $mnt "; then exit 17; fi
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = a8aa4fdd94279d3a4cc312361d8acbb7c49b081552b8943e745ac4d0ca836480
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = 0e65231d644f5c8d5fb6a7b38f2e69607bf6f4188063f0c31cb28ae48d59f2d9
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 2829a06d84be8f5b57b5016358dce6cf0143687a1b03cf4a171be3c4ddad4827
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sudo -n tar -czf /var/tmp/leanos-before-broadcom-d3-255546ca.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sudo -n cp "$stage/grub.cfg" "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 255546caf21a680b1114817f1874e3d08c5d3e8e524155ddfae38b64bab94110
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = 4f039142623cc5b1ab88e92681923e03a3124f4413a93f763a0318ec44b59d75
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 95b585839f63f75963f76bbfe71bac49871feb9292bdc0766b4773b1eb5d0980
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv" "$mnt/boot/grub/watchdog-window.cfg" "$mnt/boot/grub/watchdog.cfg"
sudo -n umount "$mnt"
trap - EXIT
sysctl kern.boottime
