set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp/leanos-realtek-stage-0374587
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = 0af703abc4160289e05c92020adc4271980955d3198e391751564dff3e1ef382
test "$(sha256 -q "$stage/leanos.sha256")" = 73a6c69bead6a48ee8bd601829d2e56670ddd8e6e1e89620e3f854d5b01a7ad9
test "$(sha256 -q "$stage/grub.cfg")" = ce6ad15f9495f118f0173749758ed9559ba238b9689f568d41c4b9bf0f471c4c
test ! -e /var/tmp/leanos-before-realtek-0374587.tar.gz
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = da6dff89a00f5e0d448761d1e0f9ac843b2ee66fab8d6ac28dd87d6d3d4b017a
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 31c32a61aacd4cf83460274e27e8042f9cc4e42fec9e21ce8abd0a7ca5feb5a0
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = be40485e8f373c87f33ad798b0cc0ed1848d7fb781711ae1f114f6fe32f9c3f5
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sudo -n tar -czf /var/tmp/leanos-before-realtek-0374587.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sudo -n cp "$stage/grub.cfg" "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 0af703abc4160289e05c92020adc4271980955d3198e391751564dff3e1ef382
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = ce6ad15f9495f118f0173749758ed9559ba238b9689f568d41c4b9bf0f471c4c
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = 73a6c69bead6a48ee8bd601829d2e56670ddd8e6e1e89620e3f854d5b01a7ad9
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv" "$mnt/boot/grub/watchdog-window.cfg" "$mnt/boot/grub/watchdog.cfg"
sysctl kern.boottime
