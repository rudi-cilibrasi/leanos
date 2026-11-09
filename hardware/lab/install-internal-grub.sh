#!/bin/sh
# Install GRUB on the Qotom's internal disk, beside FreeBSD (issue #620), or
# take it out again. Run on FreeBSD as a user with `sudo -n`.
#
#   install-internal-grub.sh check BUNDLE     install's checks only; writes nothing
#   install-internal-grub.sh install BUNDLE   BUNDLE: the output directory of
#       scripts/build-qotom-internal-grub.py --current-mbr <this disk's sector 0>
#   install-internal-grub.sh rollback BACKUP  BACKUP: the directory install printed
#   install-internal-grub.sh status
#
# install checks the bundle's SHA256SUMS, the partition layout and that
# sector 0 is the pmbr the bundle was built from (or the bundle's GRUB, for a
# reinstall), and keeps sector 0 and `gpart backup` in /var/backups. Then it
# writes, verifying each by reading it back:
#   1. grub.cfg, freebsd-mbr.bin and grubenv to /boot/efi/leanos/grub;
#   2. a bios-boot partition, ada0p4, in the gap at 533544 (984 sectors), and
#      core.img into it;
#   3. sector 0 last: GRUB's boot sector (gpart bootcode -b keeps the
#      protective partition table).
# Nothing reads 1 or 2 until 3 is done, and 3 is one sector.
# rollback writes the saved pmbr back to sector 0 and deletes ada0p4.
set -eu
disk=ada0
core_lba=533544
core_sectors=984
esp=/boot/efi
dir=$esp/leanos/grub
expected='ada0p1 40 532480 efi
ada0p2 532520 1024 freebsd-boot
ada0p3 534528 249534464 freebsd-zfs'

die() { echo "install-internal-grub: $*" >&2; exit 1; }
sector0() { sudo -n dd if=/dev/$disk bs=512 count=1 2>/dev/null | sha256 -q; }
# name start size type, for each partition of $disk
layout() { gpart show -p $disk | awk -v d="$disk" '$3 ~ "^" d "p[0-9]+$" {print $3, $1, $2, $4}'; }
p4() { layout | grep "^${disk}p4 " || true; }

show_status() {
    s=$(sector0)
    echo "sector 0 sha256 $s"
    if [ -f "$dir/freebsd-mbr.bin" ] && [ "$s" = "$(sha256 -q "$dir/freebsd-mbr.bin")" ]; then
        echo 'sector 0 is the saved FreeBSD pmbr: internal GRUB not active'
    fi
    echo "ada0p4: $(p4)"
    if [ -f "$dir/grubenv" ]; then
        echo "one-shot $(grep -a '^request=' "$dir/grubenv")"
    fi
}

# Every precondition of install; writes nothing.
do_check() {
    bundle=$1
    cd "$bundle"
    for f in mbr.bin core.img freebsd-mbr.bin grub.cfg grubenv; do
        want=$(awk -v f="$f" '$2 == f {print $1}' SHA256SUMS)
        [ -n "$want" ] && [ "$(sha256 -q "$f")" = "$want" ] || die "$f does not match SHA256SUMS"
    done
    mount | grep -q " on $esp (msdosfs" || die "$esp is not mounted"
    [ "$(layout | grep -v "^${disk}p4 ")" = "$expected" ] || die "unexpected partition layout: $(layout)"
    part=$(p4)
    [ -z "$part" ] || [ "$part" = "${disk}p4 $core_lba $core_sectors bios-boot" ] ||
        die "${disk}p4 exists and is not the bios-boot partition at $core_lba: $part"
    if [ -z "$part" ]; then
        gpart show $disk | grep -Eq "^ +$core_lba +$core_sectors +- free -" ||
            die "no free gap of $core_sectors sectors at $core_lba"
    fi
    now=$(sector0)
    if [ "$now" != "$(sha256 -q freebsd-mbr.bin)" ] && [ "$now" != "$(sha256 -q mbr.bin)" ]; then
        die 'sector 0 is neither the pmbr this bundle was built from nor its GRUB'
    fi
    echo "check: bundle, layout and sector 0 as expected (ada0p4: ${part:-to be added})"
}

do_install() {
    do_check "$1"
    backup=/var/backups/leanos-internal-grub-$(date -u +%Y%m%dT%H%M%SZ)
    sudo -n mkdir -p "$backup"
    sudo -n dd if=/dev/$disk of="$backup/sector0.bin" bs=512 count=1 2>/dev/null
    sudo -n cp freebsd-mbr.bin "$backup/freebsd-mbr.bin"
    gpart backup $disk | sudo -n tee "$backup/gpart.txt" >/dev/null
    echo "backup: $backup"

    sudo -n mkdir -p "$dir"
    for f in grub.cfg freebsd-mbr.bin grubenv; do
        sudo -n cp "$f" "$dir/$f"
        [ "$(sha256 -q "$dir/$f")" = "$(sha256 -q "$f")" ] || die "$dir/$f did not verify"
    done
    sudo -n sync
    echo "1/3 $dir: grub.cfg, freebsd-mbr.bin, grubenv"

    if [ -z "$part" ]; then
        sudo -n gpart add -t bios-boot -b $core_lba -s $core_sectors -i 4 -l grubboot0 $disk >/dev/null
    fi
    [ "$(p4)" = "${disk}p4 $core_lba $core_sectors bios-boot" ] || die "bios-boot partition not as expected: $(p4)"
    sudo -n gpart bootcode -p core.img -i 4 $disk >/dev/null
    n=$(( $(stat -f %z core.img) / 512 ))
    [ "$(sudo -n dd if=/dev/${disk}p4 bs=512 count=$n 2>/dev/null | sha256 -q)" = "$(sha256 -q core.img)" ] ||
        die "core.img did not verify in ${disk}p4"
    echo "2/3 ${disk}p4: core.img, $n sectors"

    sudo -n gpart bootcode -b mbr.bin $disk >/dev/null
    [ "$(sector0)" = "$(sha256 -q mbr.bin)" ] ||
        die "sector 0 did not verify; restore it with: $0 rollback $backup"
    echo "3/3 sector 0: GRUB's boot sector"
    echo "installed. FreeBSD stays the default; undo with: $0 rollback $backup"
}

do_rollback() {
    backup=$1
    [ -f "$backup/freebsd-mbr.bin" ] || die "$backup has no freebsd-mbr.bin"
    sudo -n gpart bootcode -b "$backup/freebsd-mbr.bin" $disk >/dev/null
    [ "$(sector0)" = "$(sha256 -q "$backup/freebsd-mbr.bin")" ] || die 'sector 0 did not verify'
    echo "sector 0: FreeBSD's pmbr"
    if [ "$(p4)" = "${disk}p4 $core_lba $core_sectors bios-boot" ]; then
        sudo -n gpart delete -i 4 $disk >/dev/null
        echo "${disk}p4 deleted"
    fi
    sudo -n rm -rf "$dir"
    echo "rolled back; $esp/leanos (the LeanOS image) is kept"
}

case "${1:-}" in
    check) [ $# -eq 2 ] || die "usage: check BUNDLE"; do_check "$2" ;;
    install) [ $# -eq 2 ] || die "usage: install BUNDLE"; do_install "$2" ;;
    rollback) [ $# -eq 2 ] || die "usage: rollback BACKUP"; do_rollback "$2" ;;
    status) show_status ;;
    *) die 'usage: install-internal-grub.sh check BUNDLE | install BUNDLE | rollback BACKUP | status' ;;
esac
