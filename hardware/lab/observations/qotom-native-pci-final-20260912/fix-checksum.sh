#!/usr/bin/env sh
set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
test "$(sha256 -q /var/tmp/leanos-pci-final.sha256)" = df5406eff92f4b15ed7162fce8c51b484d9eb22cf6fb232e6dcd555f27e71aa1
mnt=/mnt/leanos-verify
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = d7ae6577052a6558040064161d7fafd2388e03a9697df1e31dde99640287a0dc
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = bb0e0a6b7a5ba4b429aacae5b72bdc6f1df0daec33741e678678d450f7d7d082
grep -qx request=none "$mnt/boot/grub/grubenv"
sudo -n cp /var/tmp/leanos-pci-final.sha256 "$mnt/boot/leanos.sha256"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = df5406eff92f4b15ed7162fce8c51b484d9eb22cf6fb232e6dcd555f27e71aa1
grep -qx request=none "$mnt/boot/grub/grubenv"
sudo -n umount "$mnt"
trap - EXIT
