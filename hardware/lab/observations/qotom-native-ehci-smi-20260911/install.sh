set -eu
test "$(sudo -n camcontrol inquiry da0 -S)" = 11758C40
stage=/var/tmp/leanos-smi-stage-647e983
mnt=/mnt/leanos-verify
test "$(sha256 -q "$stage/leanos-qotom-lab.elf")" = 809788ba245bfb3fd332d95a4d21b95c10e933b161f2bd7f2fbeef0c3834d3b2
test "$(sha256 -q "$stage/leanos.sha256")" = 567280980d70c88897c63dce15ede7472f7dee53928a5b98ed67bc2016f8bb30
test "$(sha256 -q "$stage/grub.cfg")" = 06c4a9db0922db1521ad77679971f87791a6fae39359d47b85a3c9adbbb5d71c
test ! -e /var/tmp/leanos-before-smi-647e983.tar.gz
sudo -n mount -t msdosfs /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 0ff805e5f956ddbf6f82cd8b6c81128ce0097ec0fd3c809cc24907b8b3bf2897
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = f89b65fa7a9b5f756a64da095ed5883000131cf6302385f37b8642b8707dfb87
test "$(sha256 -q "$mnt/boot/grub/grubenv")" = 14966b4aadefce8a97d5c6e4303bc04ffda6c4e738f4c1741b6edaf9da92ec66
grep -qx 'request=none' "$mnt/boot/grub/grubenv"
sudo -n tar -czf /var/tmp/leanos-before-smi-647e983.tar.gz -C "$mnt" boot
sudo -n cp "$stage/leanos-qotom-lab.elf" "$mnt/boot/leanos-qotom-lab.elf"
sudo -n cp "$stage/leanos.sha256" "$mnt/boot/leanos.sha256"
sudo -n cp "$stage/grub.cfg" "$mnt/boot/grub/grub.cfg"
sync
sudo -n umount "$mnt"
trap - EXIT
sudo -n fsck_msdosfs -n /dev/da0s1
sudo -n mount -t msdosfs -o ro /dev/da0s1 "$mnt"
trap 'sudo -n umount "$mnt"' EXIT
test "$(sha256 -q "$mnt/boot/leanos-qotom-lab.elf")" = 809788ba245bfb3fd332d95a4d21b95c10e933b161f2bd7f2fbeef0c3834d3b2
test "$(sha256 -q "$mnt/boot/grub/grub.cfg")" = 06c4a9db0922db1521ad77679971f87791a6fae39359d47b85a3c9adbbb5d71c
test "$(sha256 -q "$mnt/boot/leanos.sha256")" = 567280980d70c88897c63dce15ede7472f7dee53928a5b98ed67bc2016f8bb30
sha256 "$mnt/boot/leanos-qotom-lab.elf" "$mnt/boot/leanos.sha256" "$mnt/boot/grub/grub.cfg" "$mnt/boot/grub/grubenv" "$mnt/boot/grub/watchdog-window.cfg" "$mnt/boot/grub/watchdog.cfg"
sysctl kern.boottime
