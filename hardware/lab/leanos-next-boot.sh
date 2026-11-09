#!/bin/sh
# Ask the Qotom's internal-disk GRUB (issue #620) to boot the installed LeanOS
# image once, on the next boot; or clear that request. Run on FreeBSD as a user
# with `sudo -n`. The request names the image's digest, so GRUB boots only the
# image it was made for; GRUB consumes it before loading anything.
# usage: leanos-next-boot.sh [clear]
set -eu
esp=/boot/efi
env=$esp/leanos/grub/grubenv
die() { echo "leanos-next-boot: $*" >&2; exit 1; }
[ -f "$env" ] || die "$env is missing: is the internal GRUB installed (hardware/lab/install-internal-grub.sh)?"
if [ "${1:-}" = clear ]; then
    request=none
else
    [ $# -eq 0 ] || die 'usage: leanos-next-boot.sh [clear]'
    digest=$(sed -n 's/^set leanos_digest=\([0-9a-f]\{64\}\)$/\1/p' "$esp/leanos/leanos-digest.cfg")
    [ -n "$digest" ] || die "no digest in $esp/leanos/leanos-digest.cfg"
    (cd "$esp/leanos" && sha256 -c "$digest" leanos-qotom-lab.elf >/dev/null) ||
        die 'leanos-qotom-lab.elf does not match its digest'
    request=leanos-$digest
fi
tmp=$(mktemp)
# A GRUB environment block: exactly 1024 bytes, padded with '#'.
awk -v r="$request" 'BEGIN { s = "# GRUB Environment Block\nrequest=" r "\n"; while (length(s) < 1024) s = s "#"; printf "%s", s }' >"$tmp"
[ "$(stat -f %z "$tmp")" -eq 1024 ] || die 'environment block is not 1024 bytes'
sudo -n cp "$tmp" "$env"
rm -f "$tmp"
sudo -n sync
echo "next boot: request=$request"
