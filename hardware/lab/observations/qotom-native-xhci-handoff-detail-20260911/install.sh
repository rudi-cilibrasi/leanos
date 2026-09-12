set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp/leanos-xhci-handoff-v2-stage-9add482
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = b5f4f7be7726a3ed92656cde891c537786fa758f71436c62c8f1a910e16803aa
test "$(sha256 -q "$stage/leanos.sha256")" = 30bf7b8cc21a693c42127bbd4d8c7741eaa7189347b39d8faec234fcae8e1d7d
test "$(sha256 -q "$stage/grub.cfg")" = eb3db131acd1487601dee712439250b0dd3c6db2a5fa5bd7c5a7280170efe694
test ! -e /var/tmp/leanos-before-xhci-handoff-v2-9add482.tar.gz
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 2d26ea6a71c542b2891bd01665ff73156c6d2c96b5ecc00fcd11ac1dec9391bf
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 92dadf6a6731cc77dc6402ffc0ebfe18fe96e01ea075f8e543915424b2c4c658
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sudo -n tar -czf /var/tmp/leanos-before-xhci-handoff-v2-9add482.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sudo -n cp "$stage/grub.cfg" "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = b5f4f7be7726a3ed92656cde891c537786fa758f71436c62c8f1a910e16803aa
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = eb3db131acd1487601dee712439250b0dd3c6db2a5fa5bd7c5a7280170efe694
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = 30bf7b8cc21a693c42127bbd4d8c7741eaa7189347b39d8faec234fcae8e1d7d
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv" "$mnt/boot/grub/watchdog-window.cfg" "$mnt/boot/grub/watchdog.cfg"
sysctl kern.boottime
