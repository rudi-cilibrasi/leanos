set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = c2cbec01015efb0057c2c844e354e5ba40531c0642bdbe09ffe5b15a0b6f7931
test "$(sha256 -q "$stage/leanos.sha256")" = ca3627483a6dd200b5c932bbb967b29be70e63576bd29f1cbf9a924ff4c910b8
test ! -e /var/tmp/leanos-before-txe-bme-c2cbec01.tar.gz
sudo -n mkdir -p "$mnt"
if mount | grep -q "on $mnt "; then exit 17; fi
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 7a5adf357d7bfd9d52839f84889e240680d2d1db7fdc43c0c4fcfdc5cbf638ca
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = edd52bb2feaed6d6eb29440ef0f126e25ad48fa8226c5d408e8ea73a9843ae41
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 978a05c733085a85a58afa0a6d78ef0d547c116389f9b749bc162a788c3f75b8
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
test -s "$mnt/boot/grub/i386-pc/normal.mod"
test -s "$mnt/boot/grub/i386-pc/multiboot2.mod"
sudo -n tar -czf /var/tmp/leanos-before-txe-bme-c2cbec01.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = c2cbec01015efb0057c2c844e354e5ba40531c0642bdbe09ffe5b15a0b6f7931
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = ca3627483a6dd200b5c932bbb967b29be70e63576bd29f1cbf9a924ff4c910b8
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 978a05c733085a85a58afa0a6d78ef0d547c116389f9b749bc162a788c3f75b8
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv"
sudo -n umount "$mnt"
trap - EXIT
sysctl kern.boottime
