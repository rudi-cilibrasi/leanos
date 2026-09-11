set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp/leanos-xhci-live-status-stage-dbeb9fc
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = 823ae01d773058aec8ea12af0029e3632470be96051e98cdf462097005e0bdb3
test "$(sha256 -q "$stage/leanos.sha256")" = dd3e09645ef8efd2fea14f28139b0915355baa94aa327bf1745e489461845654
test "$(sha256 -q "$stage/grub.cfg")" = c98b08c33d820f0201ff353c0712d675f6ee5627a9559d68bd80dc5a4eba7387
test ! -e /var/tmp/leanos-before-xhci-live-status-dbeb9fc.tar.gz
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = b5f4f7be7726a3ed92656cde891c537786fa758f71436c62c8f1a910e16803aa
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = eb3db131acd1487601dee712439250b0dd3c6db2a5fa5bd7c5a7280170efe694
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sudo -n tar -czf /var/tmp/leanos-before-xhci-live-status-dbeb9fc.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sudo -n cp "$stage/grub.cfg" "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 823ae01d773058aec8ea12af0029e3632470be96051e98cdf462097005e0bdb3
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = c98b08c33d820f0201ff353c0712d675f6ee5627a9559d68bd80dc5a4eba7387
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = dd3e09645ef8efd2fea14f28139b0915355baa94aa327bf1745e489461845654
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv" "$mnt/boot/grub/watchdog-window.cfg" "$mnt/boot/grub/watchdog.cfg"
sysctl kern.boottime
