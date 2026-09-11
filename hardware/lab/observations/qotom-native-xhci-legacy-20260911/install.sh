set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp/leanos-xhci-legacy-stage-ba753d8
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = 1733a83f4df5c538e568f8398884efe7df3c196b44f3f0bedcc6abef5aab6445
test "$(sha256 -q "$stage/leanos.sha256")" = ce7918a04f38a89fa4733c30b8043d05692d4d460e726aeef9389ca9aa8720fe
test "$(sha256 -q "$stage/grub.cfg")" = f8f58710ed2b80ac78cf8fcf80464b6f666b0aa408b8550e884695bd5ddb5949
test ! -e /var/tmp/leanos-before-xhci-legacy-ba753d8.tar.gz
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = aeab1521c05f702627c0aff177d707e3e2cad94891e17a731fcf392f7a25c911
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 54d98dc446ac617210df24f862d63144d0bb4e809492b4902b1ce5502aa65b40
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sudo -n tar -czf /var/tmp/leanos-before-xhci-legacy-ba753d8.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sudo -n cp "$stage/grub.cfg" "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 1733a83f4df5c538e568f8398884efe7df3c196b44f3f0bedcc6abef5aab6445
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = f8f58710ed2b80ac78cf8fcf80464b6f666b0aa408b8550e884695bd5ddb5949
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = ce7918a04f38a89fa4733c30b8043d05692d4d460e726aeef9389ca9aa8720fe
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv" "$mnt/boot/grub/watchdog-window.cfg" "$mnt/boot/grub/watchdog.cfg"
sysctl kern.boottime
