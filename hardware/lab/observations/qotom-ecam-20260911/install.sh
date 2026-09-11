set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp/leanos-ecam-stage-05ce325
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = 1c2f901a22280ae8b4a63471f94c63ae7e8afbc98109aae01930a656d85f70ac
test "$(sha256 -q "$stage/leanos.sha256")" = dad1181287f80fce61da593d394a8b400d1068d092900e1dc72e3f99d1ee601b
test "$(sha256 -q "$stage/grub.cfg")" = 493b45ddb3115ebf376a8ebc2b52cc41fdaa0e556f6dffcae174b6db4257dd44
test ! -e /var/tmp/leanos-before-ecam-05ce325.tar.gz
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = d02ea7892b4f31b96372beab8daadbd0b1ca215943d623419a1c58dd501eeadb
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 6034a1c2d0a85da286326c4a9feb2841dc45aea1020b1961e85582aff7442a38
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sudo -n tar -czf /var/tmp/leanos-before-ecam-05ce325.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sudo -n cp "$stage/grub.cfg" "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 1c2f901a22280ae8b4a63471f94c63ae7e8afbc98109aae01930a656d85f70ac
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 493b45ddb3115ebf376a8ebc2b52cc41fdaa0e556f6dffcae174b6db4257dd44
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = dad1181287f80fce61da593d394a8b400d1068d092900e1dc72e3f99d1ee601b
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv" "$mnt/boot/grub/watchdog-window.cfg" "$mnt/boot/grub/watchdog.cfg"
sysctl kern.boottime
