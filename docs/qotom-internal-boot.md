# Booting LeanOS from the Qotom's internal disk (issue #620)

The Qotom boots LeanOS from its internal disk, beside FreeBSD, with no USB
stick. FreeBSD stays the default and boots exactly as before. LeanOS is the
second entry of a GRUB menu on the same disk, and a one-shot request selects
it remotely.

## The disk

`ada0` is the FreeBSD install's GPT disk. The disk's 492 KiB gap between
`freebsd-boot` and `freebsd-zfs` now holds a `bios-boot` partition, `ada0p4`:

| Partition | Start | Size | Holds |
| --- | --- | --- | --- |
| sector 0 | 0 | 1 | GRUB's boot sector, which replaces FreeBSD's `pmbr` there, with the protective partition table unchanged |
| `ada0p1` (`efi`) | 40 | 260 MiB | `/leanos`: the LeanOS image (`hardware/wifi/install-ssd.sh`) and `/leanos/grub` |
| `ada0p2` (`freebsd-boot`) | 532520 | 512 KiB | `gptzfsboot`, unchanged |
| `ada0p4` (`bios-boot`, new) | 533544 | 492 KiB | GRUB's `core.img` (394 sectors) |
| `ada0p3` (`freebsd-zfs`) | 534528 | 119 GiB | `zroot`, unchanged |

The BIOS loads sector 0, which loads `core.img` from `ada0p4`.

- **`core.img`.** All its modules are built in. It opens the serial console
  (COM1, 38400 8N1) on its first line, so a broken menu still leaves a GRUB
  prompt on serial.
- **The menu.** It reads `/leanos/grub/grub.cfg` on the ESP
  ([`hardware/lab/grub-qotom-internal.cfg.in`](../hardware/lab/grub-qotom-internal.cfg.in)),
  which offers two entries, each after a 5-second menu:
  - **FreeBSD**, the default, chainloads `/leanos/grub/freebsd-mbr.bin`. That
    file is the disk's original sector 0, FreeBSD's `pmbr`. So FreeBSD boots
    through its own `pmbr`, `gptzfsboot` and loader, as it did before GRUB was
    installed.
  - **LeanOS** boots `/leanos/leanos-qotom-lab.elf` with `multiboot2`, only if
    `/leanos/leanos.sha256` checks. If it does not, the entry falls back to
    FreeBSD.
- **The one-shot request.** `hardware/lab/leanos-next-boot.sh`, run on
  FreeBSD, writes `request=leanos-<digest>` to `/leanos/grub/grubenv`. GRUB
  consumes the request before it loads anything, and boots LeanOS only if the
  digest is that of the installed image. So the next boot is FreeBSD again,
  however the LeanOS run ends.

If the lab stick is plugged in and boots first, its GRUB chainloads this disk's
sector 0 for its FreeBSD default (`hardware/lab/grub-qotom-ssd.cfg.in`). It
thereby reaches this menu, which then sees the disk as `hd1`.

Records on serial start with `LEANOS-DISK/1`: `CORE`, `MENU`, `REQUEST`,
`CHAIN freebsd`, `LEANOS load=1`, `LOAD-FAILED` and `CHAIN-FAILED`.

## Build, install, use, undo

1. **Build** the bundle from the disk's own sector 0:

   ```sh
   ssh freebsd@192.168.6.21 'sudo -n dd if=/dev/ada0 bs=512 count=1' > sector0.bin
   scripts/build-qotom-internal-grub.py --current-mbr sector0.bin --out build/qotom-internal-grub
   ```

   `core.img` and the boot sector are made with `grub-mkimage` and the setup
   step that `grub-bios-setup` does: the core's sector in the boot sector, and
   the core's own blocklist. The setup is done in the script so that the exact
   bytes are tested before they are written.
2. **Install** on FreeBSD. Copy the bundle and `hardware/lab/*.sh` to the
   Qotom, then:

   ```sh
   sh install-internal-grub.sh check BUNDLE     # every precondition; writes nothing
   sh install-internal-grub.sh install BUNDLE
   ```

   - **Checks.** `install` checks the bundle's `SHA256SUMS` and the partition
     layout. It also checks that sector 0 is the `pmbr` the bundle was built
     from, or the bundle's own GRUB, for a reinstall.
   - **Backup.** It saves sector 0 and `gpart backup` in
     `/var/backups/leanos-internal-grub-<time>`.
   - **Writes.** It writes the ESP files, then `ada0p4` and `core.img`
     (`gpart add`, `gpart bootcode -p`), then sector 0 last
     (`gpart bootcode -b`, which keeps the partition table). It reads each
     write back before the next. Nothing reads the first two until sector 0
     changes.
3. **Boot LeanOS once** with `sh leanos-next-boot.sh` and a reboot. Or pick
   "LeanOS" in the menu on the console or on serial.
4. **Undo** with `sh install-internal-grub.sh rollback <backup directory>`. It
   writes the saved `pmbr` back to sector 0, deletes `ada0p4` and removes
   `/leanos/grub`.

## Tests

`scripts/test-qotom-internal-grub.py` runs in `scripts/check.sh` (images). It
boots the bundle in QEMU from a sparse disk with the Qotom's GPT, the same
offsets and the same size. A sentinel in place of `pmbr`
(`hardware/lab/pmbr-sentinel.S`) prints the BIOS drive it is given, and the q35
kernel `build/boot/leanos.elf` stands in for the lab image. The cases:

| Case | Required |
| --- | --- |
| default | the menu times out to FreeBSD, whose `pmbr` gets DL 0x80 |
| leanos | the request is consumed, the image's hash checks, and the kernel reaches `FINAL status=PASS` |
| stale | a request for another digest is consumed, and FreeBSD boots |
| hash-mismatch | `LOAD-FAILED fallback=freebsd`, and FreeBSD boots |
| stick-chain | a first disk chainloads this one as the stick does; the menu sees `hd1`, and `pmbr` gets DL 0x81 |

Every case also requires `request=none` in `grubenv` afterwards.

Before the install, the exact bundle for the Qotom was also booted once by
hand on a disk with the Qotom's real `pmbr` and `gptzfsboot` (read from
`ada0`). Its `zroot` partition held the `zroot` pool of the FreeBSD
15.0-RELEASE ZFS VM image. GRUB's FreeBSD entry chainloaded that `pmbr`,
which loaded `gptzfsboot`, the loader and the kernel, up to
`Trying to mount root from zfs:zroot/ROOT/default`. The boot then stopped in
single-user mode, because the VM image's `fstab` names labels the test disk
lacks.

## On the Qotom

Installed on 2026-11-06, with no USB stick plugged in
([observation](../hardware/lab/observations/qotom-internal-grub-20261106/README.md)).
The BIOS booted the internal disk, and GRUB ran from it as `hd0`:

- **Default.** The menu timed out to FreeBSD, which booted through its own
  `pmbr` and came back with `zroot` ONLINE.
- **One-shot.** A plain completion-mode lab kernel booted from `/leanos`:
  `REQUEST consumed=1`, then `leanos-qotom-lab.elf: OK`, then the kernel's
  records up to `LEANOS/3 FINAL status=FAIL reason=qotom-platform-pending`,
  the lab kernel's usual terminal on this board.
- **The way back.** 30 seconds after `FINAL`, the image reset the board.
  GRUB's default booted FreeBSD, with no one at the board.

## Not covered

- **UEFI.** The board boots legacy BIOS (`machdep.bootmethod=BIOS`). Under
  UEFI, the firmware runs the ESP's `EFI/BOOT/BOOTX64.EFI`, FreeBSD's loader,
  and this menu is not used. A UEFI GRUB beside it would need a firmware boot
  entry.
- **A watchdog.** As with the stick's plain one-shot request, a LeanOS image
  that hangs before it resets the board needs a power cycle. The request is
  already consumed, so that power cycle boots FreeBSD.
- **FreeBSD updates.** `gpart bootcode -b /boot/pmbr ada0`, which some FreeBSD
  upgrade instructions give, replaces GRUB's boot sector. That only restores
  the FreeBSD-only boot, and `install` puts GRUB back. Updates of
  `gptzfsboot` in `ada0p2` need nothing, since GRUB chains through `pmbr`.
