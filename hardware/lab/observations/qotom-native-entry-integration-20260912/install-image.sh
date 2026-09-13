#!/usr/bin/env sh
set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
mnt=/mnt/leanos-install
backup=/var/tmp/leanos-before-entry-flags-d0d9e4b.tar.gz
test "$(sha256 -q /var/tmp/leanos-flags-d0d9e4b/leanos-qotom-lab.elf)" = 53b64275e9d690052cf413c2c1c1431d541d8c9e342a42ee84342503944028b8
test "$(sha256 -q /var/tmp/leanos-flags-d0d9e4b/grub.cfg)" = 80ccd8cc52a5897d177d35d4f1737222e08f15a9c9e392c6e0bc2db1c04ef8a3
test "$(sha256 -q /var/tmp/leanos-flags-d0d9e4b/leanos.sha256)" = 931c61b556ce0a90a34338e8179389b1e9f8c978e16b4223cea1441e2d282595
test ! -e "$backup"
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
grep -a -q '^request=none$' "$mnt/boot/grub/grubenv"
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = ea731c5667b784f660d851c6240fa5407d7ee13f8f5c8eb11c20ffdf32a3dac9
sudo -n tar -czf "$backup" -C "$mnt" boot
sudo -n cp /var/tmp/leanos-flags-d0d9e4b/leanos-qotom-lab.elf "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp /var/tmp/leanos-flags-d0d9e4b/grub.cfg "$mnt/boot/grub/grub.cfg"
sudo -n cp /var/tmp/leanos-flags-d0d9e4b/leanos.sha256 "$mnt/boot/leanos.sha256"
sync
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 53b64275e9d690052cf413c2c1c1431d541d8c9e342a42ee84342503944028b8
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 80ccd8cc52a5897d177d35d4f1737222e08f15a9c9e392c6e0bc2db1c04ef8a3
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = 931c61b556ce0a90a34338e8179389b1e9f8c978e16b4223cea1441e2d282595
grep -a -q '^request=none$' "$mnt/boot/grub/grubenv"
