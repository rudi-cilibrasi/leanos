set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp/leanos-graphics-bme-stage-7a5adf35
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = 7a5adf357d7bfd9d52839f84889e240680d2d1db7fdc43c0c4fcfdc5cbf638ca
test "$(sha256 -q "$stage/leanos.sha256")" = edd52bb2feaed6d6eb29440ef0f126e25ad48fa8226c5d408e8ea73a9843ae41
test "$(sha256 -q "$stage/grub.cfg")" = 978a05c733085a85a58afa0a6d78ef0d547c116389f9b749bc162a788c3f75b8
test ! -e /var/tmp/leanos-before-broadcom-status-fix-7a5adf35.tar.gz
sudo -n mkdir -p "$mnt"
if mount | grep -q "on $mnt "; then exit 17; fi
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = b2d11cb9b3e69f79557ed430812dbc932315a6ee7cbd34050dc09f89c407431b
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = 62fb3182b497c012f4df16a7ed964f03d71727dfc374d0193ddae7927ddafc2c
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 98aa86429e34a5cf279e656055e797f652401686a0ca38ef65ea83657e6fbccd
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
test -s "$mnt/boot/grub/i386-pc/normal.mod"
test -s "$mnt/boot/grub/i386-pc/multiboot2.mod"
sudo -n tar -czf /var/tmp/leanos-before-broadcom-status-fix-7a5adf35.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sudo -n cp "$stage/grub.cfg" "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 7a5adf357d7bfd9d52839f84889e240680d2d1db7fdc43c0c4fcfdc5cbf638ca
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = edd52bb2feaed6d6eb29440ef0f126e25ad48fa8226c5d408e8ea73a9843ae41
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 978a05c733085a85a58afa0a6d78ef0d547c116389f9b749bc162a788c3f75b8
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
test -s "$mnt/boot/grub/i386-pc/normal.mod"
test -s "$mnt/boot/grub/i386-pc/multiboot2.mod"
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv" "$mnt/boot/grub/watchdog-window.cfg" "$mnt/boot/grub/watchdog.cfg"
sudo -n umount "$mnt"
trap - EXIT
sysctl kern.boottime
