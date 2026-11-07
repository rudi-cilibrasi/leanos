# LeanOS boots from the Qotom's internal disk, without the stick (2026-11-06)

Issue #620, [docs/qotom-internal-boot.md](../../../../docs/qotom-internal-boot.md).

The board boots legacy BIOS (`machdep.bootmethod=BIOS`). FreeBSD saw a single
disk, `ada0` (Hoodisk SSD): no USB stick was plugged in.

## Install

`install-internal-grub.sh check`, then `install`. The bundle was built from
`ada0`'s own sector 0, which was FreeBSD's `pmbr`: its first 446 bytes equal
`/boot/pmbr`, and the sector's SHA-256 is `4ac42b01...91ca`.

```text
check: bundle, layout and sector 0 as expected (ada0p4: to be added)
backup: /var/backups/leanos-internal-grub-20261107T024607Z
1/3 /boot/efi/leanos/grub: grub.cfg, freebsd-mbr.bin, grubenv
2/3 ada0p4: core.img, 394 sectors
3/3 sector 0: GRUB's boot sector
```

`gpart show ada0` afterwards:

```text
=>       40  250069600  ada0  GPT  (119G)
         40     532480     1  efi  (260M)
     532520       1024     2  freebsd-boot  (512K)
     533544        984     4  bios-boot  (492K)
     534528  249534464     3  freebsd-zfs  (119G)
  250068992        648        - free -  (324K)
```

Sector 0 then had SHA-256 `34b09920...b9`, that of the bundle's `mbr.bin`.

## Default boot: FreeBSD

`shutdown -r now`, serial capture [`default-boot.raw`](default-boot.raw)
(COM1, 38400 8N1):

```text
LEANOS-DISK/1 CORE root=hd0,gpt1 prefix=(hd0,gpt1)/leanos/grub
LEANOS-DISK/1 MENU disk=hd0 default=freebsd timeout=5
LEANOS-DISK/1 CHAIN freebsd disk=hd0
FreeBSD/amd64 (qotom) (ttyu0)
```

FreeBSD came back with `zroot` ONLINE.

## One-shot LeanOS boot

The image was a plain completion-mode lab kernel, with no device programs:
`scripts/build-qotom-recovery-lab.py --prepared-repo .` at 6287d5ae, SHA-256
`de279092d637ce5b794f4230b25fcb45d8cdab62b7d517e7b0ee975c4c29efe2`. It was
installed with `hardware/wifi/install-ssd.sh`, then requested with
`leanos-next-boot.sh` before `shutdown -r now`. Serial capture
[`leanos-boot.raw`](leanos-boot.raw):

```text
LEANOS-DISK/1 CORE root=hd0,gpt1 prefix=(hd0,gpt1)/leanos/grub
LEANOS-DISK/1 REQUEST consumed=1
LEANOS-DISK/1 MENU disk=hd0 default=leanos timeout=0
LEANOS-DISK/1 LEANOS load=1
leanos-qotom-lab.elf: OK
LEANOS-LAB/1 MODE qotom-reset-after-final seconds=30
LEANOS/24 BOOT target=qotom-j1900-candidate phase=cpu-diagnostic platform-admitted=0 cpl3=0
LEANOS/3 FINAL status=FAIL reason=qotom-platform-pending
LEANOS-DISK/1 CORE root=hd0,gpt1 prefix=(hd0,gpt1)/leanos/grub
LEANOS-DISK/1 MENU disk=hd0 default=freebsd timeout=5
LEANOS-DISK/1 CHAIN freebsd disk=hd0
FreeBSD/amd64 (qotom) (ttyu0)
```

- **The boot.** GRUB consumed the request before loading, checked the
  image's hash and booted it.
- **The terminal record.** `qotom-platform-pending` is the lab kernel's
  terminal on this board: the platform is not admitted.
- **The way back.** 30 seconds after `FINAL`, the image reset the board
  through 0xCF9. GRUB's default then booted FreeBSD, with `request=none` left
  in `grubenv`, and no one touched the board.

The previous image, the `rtl8168-arp` lab image `9cd40e56...`, is in
`/leanos/previous/`.

Capture SHA-256: `default-boot.raw`
`2ff9b120159b4e2da7c887ed1062268abc58e8003bf69b458fa8adaf22bb6c67`,
`leanos-boot.raw`
`a5a91820e3a0c48241cf0e7ef7d5ba18481958454e76ec751cc7da1068bcc37c`.
