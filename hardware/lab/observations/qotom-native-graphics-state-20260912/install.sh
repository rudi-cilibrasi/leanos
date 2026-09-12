set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp/leanos-graphics-state-stage-50826885
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = 50826885480d163d5eadb7f9614d95fe969859fb5e848c22659de4cbb7845827
test "$(sha256 -q "$stage/leanos.sha256")" = 6d6fa508d280ee083ce2ceb00d4408f8e82dbb6e4b3c0a2ed684642fd0054979
test "$(sha256 -q "$stage/grub.cfg")" = 15afa092b996afce912b9eb3a715ed1f5ebf63433339570f73a69d6d62b6bf5d
test ! -e /var/tmp/leanos-before-graphics-command-fix-50826885.tar.gz
sudo -n mkdir -p "$mnt"
if mount | grep -q "on $mnt "; then exit 17; fi
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = e747bc72ecfacdc757ea1dfdab741f25057b5b241ca7fcf0494bc43ef60d0108
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 4d4c53f0ea3d1348d6d2427bb39a031c03fe0d65bb003dba79ea5df44008814e
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
test -s "$mnt/boot/grub/i386-pc/normal.mod"
test -s "$mnt/boot/grub/i386-pc/multiboot2.mod"
sudo -n tar -czf /var/tmp/leanos-before-graphics-command-fix-50826885.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sudo -n cp "$stage/grub.cfg" "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 50826885480d163d5eadb7f9614d95fe969859fb5e848c22659de4cbb7845827
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = 6d6fa508d280ee083ce2ceb00d4408f8e82dbb6e4b3c0a2ed684642fd0054979
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 15afa092b996afce912b9eb3a715ed1f5ebf63433339570f73a69d6d62b6bf5d
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
test -s "$mnt/boot/grub/i386-pc/normal.mod"
test -s "$mnt/boot/grub/i386-pc/multiboot2.mod"
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv" "$mnt/boot/grub/watchdog-window.cfg" "$mnt/boot/grub/watchdog.cfg"
sudo -n umount "$mnt"
trap - EXIT
sysctl kern.boottime
