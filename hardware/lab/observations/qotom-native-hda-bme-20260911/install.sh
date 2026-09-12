set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp/leanos-hda-bme-stage-7ff1f02
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = 28b53a1769147eea00f7b6cdd1e826d5207b1080df12b5495b2d8b063e7804db
test "$(sha256 -q "$stage/leanos.sha256")" = b1dbc0c64cfffeb4f0376dbc58ee4ca56b79e5b5ae72b773561b6a346c271acc
test "$(sha256 -q "$stage/grub.cfg")" = dcee6e8eca2fd6b20110352abd10f3df7b8b52e0e0633859a5fc54e09b54fd22
test ! -e /var/tmp/leanos-before-hda-bme-7ff1f02.tar.gz
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 85c208b2b448a5809e9555e5b5b9fc2ce36253fce5755b4e45e10ce6a381c226
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 3034efb8f9d7e41fdde9f74487617ff222e7c40f628da316742ae45b9ad44e8d
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sudo -n tar -czf /var/tmp/leanos-before-hda-bme-7ff1f02.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sudo -n cp "$stage/grub.cfg" "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 28b53a1769147eea00f7b6cdd1e826d5207b1080df12b5495b2d8b063e7804db
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = dcee6e8eca2fd6b20110352abd10f3df7b8b52e0e0633859a5fc54e09b54fd22
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = b1dbc0c64cfffeb4f0376dbc58ee4ca56b79e5b5ae72b773561b6a346c271acc
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv" "$mnt/boot/grub/watchdog-window.cfg" "$mnt/boot/grub/watchdog.cfg"
sysctl kern.boottime
