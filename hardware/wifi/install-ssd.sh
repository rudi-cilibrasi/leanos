#!/usr/bin/env sh
# Install a LeanOS lab ELF on the FreeBSD disk's EFI system partition for the
# SSD-image GRUB configuration (hardware/lab/grub-qotom-ssd.cfg.in). Run on
# FreeBSD. The previous image is kept as /leanos/previous/.
# usage: install-ssd.sh <elf-sha256>   (expects /var/tmp/leanos-wifi.elf)
set -eu
new=$1
dir=/boot/efi/leanos
mount | grep -q ' on /boot/efi (msdosfs' || { echo "EFI partition not mounted"; exit 1; }
test "$(sha256 -q /var/tmp/leanos-wifi.elf)" = "$new"
sudo -n mkdir -p "$dir/previous"
if [ -f "$dir/leanos-qotom-lab.elf" ]; then
  sudo -n cp "$dir/leanos-qotom-lab.elf" "$dir/leanos.sha256" "$dir/leanos-digest.cfg" "$dir/previous/"
fi
# Stage, verify, then switch the digest last: GRUB boots only a digest whose
# ELF and list are already in place.
sudo -n rm -f "$dir/leanos-digest.cfg"
sudo -n cp /var/tmp/leanos-wifi.elf "$dir/leanos-qotom-lab.elf"
printf '%s  leanos-qotom-lab.elf\n' "$new" | sudo -n tee "$dir/leanos.sha256" >/dev/null
test "$(sha256 -q "$dir/leanos-qotom-lab.elf")" = "$new"
printf 'set leanos_digest=%s\n' "$new" | sudo -n tee "$dir/leanos-digest.cfg" >/dev/null
sudo -n sync
echo "installed $new in $dir"
