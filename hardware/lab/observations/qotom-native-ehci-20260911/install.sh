set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp/leanos-ehci-stage-1be485c
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = 98ca8356b613e4f0ff7bfd6f80a6f5e461c56ba37b5a5f59d66ac404a3bd7982
test "$(sha256 -q "$stage/leanos.sha256")" = dbe687e4d973dc72764be1d221752b4f1d8091acfd25e1f96df88420773328c6
test "$(sha256 -q "$stage/grub.cfg")" = 32acba68774d438370c9282d073ae61205a9456e322ac232e59d689d4450408b
test ! -e /var/tmp/leanos-before-ehci-1be485c.tar.gz
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = e369f33024ec667d125b9a92d9e5bedf7936b53f4f3e6018d3e3a733f13b10a2
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 284d8b4693b36b84889282530bd2e3d3f2be93de5551e4569e004aca3034f9b5
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sudo -n tar -czf /var/tmp/leanos-before-ehci-1be485c.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sudo -n cp "$stage/grub.cfg" "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 98ca8356b613e4f0ff7bfd6f80a6f5e461c56ba37b5a5f59d66ac404a3bd7982
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 32acba68774d438370c9282d073ae61205a9456e322ac232e59d689d4450408b
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = dbe687e4d973dc72764be1d221752b4f1d8091acfd25e1f96df88420773328c6
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv" "$mnt/boot/grub/watchdog-window.cfg" "$mnt/boot/grub/watchdog.cfg"
sysctl kern.boottime
