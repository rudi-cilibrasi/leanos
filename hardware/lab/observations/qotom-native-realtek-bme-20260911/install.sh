set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp/leanos-realtek-bme-stage-01b11b5
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = 38b9a678db2023a37e0b9fb72920aef2770f8e7eac115563566e663a6e217e86
test "$(sha256 -q "$stage/leanos.sha256")" = b6406cb95959fa6e1a4eb21d6f3da209923956a291b6ff72f3e5bae3bc553533
test "$(sha256 -q "$stage/grub.cfg")" = 116bbadb8d460c868e504dc0c1f670e4c596694522ce023d8a6a282241402b8f
test ! -e /var/tmp/leanos-before-realtek-bme-01b11b5.tar.gz
if mount | grep -q "on $mnt "; then exit 17; fi
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 0af703abc4160289e05c92020adc4271980955d3198e391751564dff3e1ef382
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = ce6ad15f9495f118f0173749758ed9559ba238b9689f568d41c4b9bf0f471c4c
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = 73a6c69bead6a48ee8bd601829d2e56670ddd8e6e1e89620e3f854d5b01a7ad9
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sudo -n tar -czf /var/tmp/leanos-before-realtek-bme-01b11b5.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sudo -n cp "$stage/grub.cfg" "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 38b9a678db2023a37e0b9fb72920aef2770f8e7eac115563566e663a6e217e86
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 116bbadb8d460c868e504dc0c1f670e4c596694522ce023d8a6a282241402b8f
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = b6406cb95959fa6e1a4eb21d6f3da209923956a291b6ff72f3e5bae3bc553533
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv" "$mnt/boot/grub/watchdog-window.cfg" "$mnt/boot/grub/watchdog.cfg"
sudo -n umount "$mnt"
trap - EXIT
sysctl kern.boottime
