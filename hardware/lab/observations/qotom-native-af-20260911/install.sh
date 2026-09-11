set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp/leanos-af-stage-7d6348d
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = e369f33024ec667d125b9a92d9e5bedf7936b53f4f3e6018d3e3a733f13b10a2
test "$(sha256 -q "$stage/leanos.sha256")" = 01c26c2921077c6312431968a50bb35a80e0c08737571cb30ff0087579a98b37
test "$(sha256 -q "$stage/grub.cfg")" = 284d8b4693b36b84889282530bd2e3d3f2be93de5551e4569e004aca3034f9b5
test ! -e /var/tmp/leanos-before-af-7d6348d.tar.gz
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 27773506501f290f107cf80b860e8f9a92034496d05b86787240d543b4b3ec37
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = d21dfa818f80b9779604ce9de9ef4b4956d3072c024dc21bff75ce6b05809c13
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sudo -n tar -czf /var/tmp/leanos-before-af-7d6348d.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sudo -n cp "$stage/grub.cfg" "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = e369f33024ec667d125b9a92d9e5bedf7936b53f4f3e6018d3e3a733f13b10a2
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 284d8b4693b36b84889282530bd2e3d3f2be93de5551e4569e004aca3034f9b5
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = 01c26c2921077c6312431968a50bb35a80e0c08737571cb30ff0087579a98b37
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv" "$mnt/boot/grub/watchdog-window.cfg" "$mnt/boot/grub/watchdog.cfg"
sysctl kern.boottime
