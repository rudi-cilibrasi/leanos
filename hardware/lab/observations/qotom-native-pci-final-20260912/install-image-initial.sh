set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
mnt=/mnt/leanos-verify
backup=/var/tmp/leanos-before-pci-final-d7ae6577.tar.gz
test "$(sha256 -q /var/tmp/leanos-qotom-lab.elf)" = d7ae6577052a6558040064161d7fafd2388e03a9697df1e31dde99640287a0dc
test "$(sha256 -q /var/tmp/leanos.sha256)" = bb0e0a6b7a5ba4b429aacae5b72bdc6f1df0daec33741e678678d450f7d7d082
test "$(sha256 -q /var/tmp/grub.cfg)" = 69c217ee92cd1ed02a2535464f241688197237efed256cbc6aec5ff9394d49d5
test ! -e "$backup"
if mount | grep -q "on $mnt "; then exit 17; fi
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = c2cbec01015efb0057c2c844e354e5ba40531c0642bdbe09ffe5b15a0b6f7931
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = ca3627483a6dd200b5c932bbb967b29be70e63576bd29f1cbf9a924ff4c910b8
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = e35b6ee3bd07484ace4422eace29c37c8f1220f5848beb32d2882870ef623c8c
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx request=none "$mnt/boot/grub/grubenv"
sudo -n tar -czf "$backup" -C "$mnt" boot
sudo -n cp /var/tmp/leanos-qotom-lab.elf "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp /var/tmp/leanos.sha256 "$mnt/boot/leanos.sha256"
sudo -n cp /var/tmp/grub.cfg "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = d7ae6577052a6558040064161d7fafd2388e03a9697df1e31dde99640287a0dc
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = bb0e0a6b7a5ba4b429aacae5b72bdc6f1df0daec33741e678678d450f7d7d082
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 69c217ee92cd1ed02a2535464f241688197237efed256cbc6aec5ff9394d49d5
grep -qx request=none "$mnt/boot/grub/grubenv"
test "$(grep -c d7ae6577052a6558040064161d7fafd2388e03a9697df1e31dde99640287a0dc "$mnt/boot/grub/grub.cfg")" = 3
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv"
sudo -n umount "$mnt"
trap - EXIT
