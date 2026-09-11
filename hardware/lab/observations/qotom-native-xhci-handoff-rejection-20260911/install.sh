set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp/leanos-xhci-handoff-stage-cf0829c
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = 2d26ea6a71c542b2891bd01665ff73156c6d2c96b5ecc00fcd11ac1dec9391bf
test "$(sha256 -q "$stage/leanos.sha256")" = 738c990c014d38a8d2437d6933bc7d583914854d41d894857d1be9635a932bfb
test "$(sha256 -q "$stage/grub.cfg")" = 92dadf6a6731cc77dc6402ffc0ebfe18fe96e01ea075f8e543915424b2c4c658
test ! -e /var/tmp/leanos-before-xhci-handoff-cf0829c.tar.gz
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 1733a83f4df5c538e568f8398884efe7df3c196b44f3f0bedcc6abef5aab6445
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = f8f58710ed2b80ac78cf8fcf80464b6f666b0aa408b8550e884695bd5ddb5949
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sudo -n tar -czf /var/tmp/leanos-before-xhci-handoff-cf0829c.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sudo -n cp "$stage/grub.cfg" "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 2d26ea6a71c542b2891bd01665ff73156c6d2c96b5ecc00fcd11ac1dec9391bf
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 92dadf6a6731cc77dc6402ffc0ebfe18fe96e01ea075f8e543915424b2c4c658
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = 738c990c014d38a8d2437d6933bc7d583914854d41d894857d1be9635a932bfb
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv" "$mnt/boot/grub/watchdog-window.cfg" "$mnt/boot/grub/watchdog.cfg"
sysctl kern.boottime
