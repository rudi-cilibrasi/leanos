#!/usr/bin/env sh
set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
mnt=/mnt/leanos-install
backup=/var/tmp/leanos-before-pci-trust-83f6686.tar.gz
test "$(sha256 -q /var/tmp/leanos-qotom-trust-83f6686.elf)" = 97e9c6e6be402c4c6eebab63664f7f93074abdbb01f8345f8bc2abe01600bcd9
test "$(sha256 -q /var/tmp/grub-qotom-trust-83f6686.cfg)" = 0d153f8338ae9da0c891f50f68011a4845a47ccf84cbbfed8fff0d24f8445b1f
test "$(sha256 -q /var/tmp/leanos-trust-83f6686.sha256)" = 0287c8269d089df88683dc29403a23b8f33cec8213acf851be91e8e73fa993ea
test ! -e "$backup"
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
grep -a -q '^request=none$' "$mnt/boot/grub/grubenv"
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = d7ae6577052a6558040064161d7fafd2388e03a9697df1e31dde99640287a0dc
sudo -n tar -czf "$backup" -C "$mnt" boot
sudo -n cp /var/tmp/leanos-qotom-trust-83f6686.elf "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp /var/tmp/grub-qotom-trust-83f6686.cfg "$mnt/boot/grub/grub.cfg"
sudo -n cp /var/tmp/leanos-trust-83f6686.sha256 "$mnt/boot/leanos.sha256"
sync
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 97e9c6e6be402c4c6eebab63664f7f93074abdbb01f8345f8bc2abe01600bcd9
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 0d153f8338ae9da0c891f50f68011a4845a47ccf84cbbfed8fff0d24f8445b1f
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = 0287c8269d089df88683dc29403a23b8f33cec8213acf851be91e8e73fa993ea
grep -a -q '^request=none$' "$mnt/boot/grub/grubenv"
