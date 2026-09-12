set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
test "$(sha256 -q /var/tmp/grub-txe-bme.cfg)" = e35b6ee3bd07484ace4422eace29c37c8f1220f5848beb32d2882870ef623c8c
mnt=/mnt/leanos-verify
sudo -n mkdir -p "$mnt"
if mount | grep -q "on $mnt "; then exit 17; fi
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = c2cbec01015efb0057c2c844e354e5ba40531c0642bdbe09ffe5b15a0b6f7931
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = ca3627483a6dd200b5c932bbb967b29be70e63576bd29f1cbf9a924ff4c910b8
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 978a05c733085a85a58afa0a6d78ef0d547c116389f9b749bc162a788c3f75b8
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx request=none "$mnt/boot/grub/grubenv"
sudo -n cp /var/tmp/grub-txe-bme.cfg "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = e35b6ee3bd07484ace4422eace29c37c8f1220f5848beb32d2882870ef623c8c
grep -qx request=none "$mnt/boot/grub/grubenv"
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv"
sudo -n umount "$mnt"
trap - EXIT
