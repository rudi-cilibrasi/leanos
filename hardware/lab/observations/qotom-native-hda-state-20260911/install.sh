set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp/leanos-hda-state-stage-1df1986
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = 85c208b2b448a5809e9555e5b5b9fc2ce36253fce5755b4e45e10ce6a381c226
test "$(sha256 -q "$stage/leanos.sha256")" = e5d2941e7cadd9e903380ca723f98935110c02870674bb567ede44c80618f790
test "$(sha256 -q "$stage/grub.cfg")" = 3034efb8f9d7e41fdde9f74487617ff222e7c40f628da316742ae45b9ad44e8d
test ! -e /var/tmp/leanos-before-hda-state-1df1986.tar.gz
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 10eefd4102584d38a0d8e6f4d9babf57b3f9539527cafa366f1e691acd1ba13c
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 5244073aabbe1a3f4e6d594b4c5159ffd5eab8e4825cde2e05e9cc1e1d84d1e6
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sudo -n tar -czf /var/tmp/leanos-before-hda-state-1df1986.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sudo -n cp "$stage/grub.cfg" "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 85c208b2b448a5809e9555e5b5b9fc2ce36253fce5755b4e45e10ce6a381c226
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 3034efb8f9d7e41fdde9f74487617ff222e7c40f628da316742ae45b9ad44e8d
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = e5d2941e7cadd9e903380ca723f98935110c02870674bb567ede44c80618f790
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv" "$mnt/boot/grub/watchdog-window.cfg" "$mnt/boot/grub/watchdog.cfg"
sysctl kern.boottime
