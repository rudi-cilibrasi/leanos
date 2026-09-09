# Qotom boot recovery experiment

This is an opt-in lab prototype for issue #333, separate from the canonical
halt-until-reset observation in #327. It is not yet a demonstrated unattended
hardware loop and does not change physical platform admission.

## Arrangement

The firmware must boot the legacy USB disk first. Its writable FAT32 partition
contains GRUB, an environment block, the lab ELF and a SHA-256 check file.
FreeBSD on the existing internal disk is GRUB's persistent default. GRUB
identifies that disk by the UUID of its second GPT partition before chainloading
its existing MBR. The internal disk's bootloader and partition table are not
modified.

An operator arms exactly one request in `boot/grub/grubenv`:

- `none`: chainload FreeBSD.
- `reboot-test`: consume the request, wait three seconds, reboot; the next boot
  defaults to FreeBSD.
- `leanos-<ELF SHA-256>`: consume the request, verify the ELF against the check
  file, and launch LeanOS. The configuration binds the permitted ELF digest.

GRUB writes `request=none` before launching either one-shot action. A failed
state write or image check falls back to FreeBSD. This is accidental-corruption
and operator-error detection, not protection against someone who can rewrite
both the USB configuration and image. The saved environment needs plain-disk
BIOS access to a supported writable filesystem; it cannot live in the existing
read-only ISO or the internal ZFS filesystem. See the
[GRUB environment documentation](https://www.gnu.org/software/grub/manual/grub/html_node/Environment-block.html).

The lab kernel prints an explicit `LEANOS-LAB/1 MODE` record and retains the
normal admission checks. Its terminal function polls the Qotom FADT's 24-bit
ACPI PM timer at port `0x408` for 30 seconds, drains COM1, and writes reset value
6 to port `0xcf9`. The captured firmware declares these addresses. The hook
refuses that board-specific path unless PCI host identity is `8086:0f00`.
That identity is a narrow lab guard, not the complete admission profile in #291.

The normal kernel source is not edited: the builder creates a separate overlay
and ELF. Lab captures must never be classified as canonical absorbing-halt
captures. Recovery and LeanOS scenario results must be reported separately.
The current image is expected to reject `dma-identity`, not succeed at CPL3.

## Build and local tests

First prepare a normal build in a separate checkout of the same kernel source.
The prototype reuses that checkout's generated build inputs and records an
overlay hash. It requires Linux, GCC, binutils, GRUB BIOS tools, sfdisk, dosfstools,
mtools, and sudo for loop-device mounting.

```sh
python3 scripts/build-qotom-recovery-lab.py --prepared-repo ../leanos
python3 scripts/create-qotom-lab-usb.py --freebsd-boot-uuid UUID_OF_ADA0P2
python3 scripts/test-qotom-lab-usb.py \
  --image build/qotom-lab/usb.img --freebsd-boot-uuid UUID_OF_ADA0P2
```

The image builder creates a 96 MiB regular file and only attaches that file to
a loop device. It never writes a physical disk. The test uses a fake GPT disk
with a small serial-output MBR, not an emulated FreeBSD installation. It verifies
default fallback, one-shot consumption across a real emulator reset, unknown
requests, image hash mismatch, and launch of the lab rejection kernel. It reads
the environment back after every case to verify that the request was consumed.
The simulated PC is not the Qotom, so the board-specific terminal reset is not
exercised by that test.

## Physical preparation and current result

Before the first write, identify the USB by serial, capacity, and current mount
state. Back up every byte that will be overwritten. For this session the first
96 MiB was backed up both on mgnuc and FreeBSD; SHA-256:
`4f0628a5e219433959703eea6b085fe1bdb6709eb926968e2e7be448d3538cc4`.
The canonical rejection ISO and its earlier original-media backup are retained.

Write only the identified USB device, flush it, and read back the same byte
count. Mount its FAT partition to edit the environment, then unmount before
reboot. Do not use an internal-disk path for this operation. On this board the
USB is `/dev/da0`, its FAT partition is `/dev/da0s1`, and the internal disk is
`/dev/ada0`. These names require re-verification after hardware changes.

Create requests with `grub-editenv` on the observing host, copy the resulting
1024-byte environment file to the mounted USB's `boot/grub/grubenv`, sync and
unmount. The command for the non-kernel test is:

```sh
grub-editenv /tmp/lab-grubenv create
grub-editenv /tmp/lab-grubenv set request=reboot-test
```

At 2026-09-09 16:56:20 UTC the first physical default test rebooted FreeBSD.
FreeBSD's next boot time was 16:56:47 UTC. Serial capture contained firmware
prefix bytes but no lab GRUB marker. Therefore this is **not** evidence of
successful USB-to-FreeBSD chainloading; the firmware appears to have bypassed
the USB. A `reboot-test` request is now armed pending legacy USB-first selection.
The media ELF was read back as
`9226ca1e9ea33607ba73e1acbfe3df5063665df9f5b13fbbd001cc7fb89bbdb2`.

The expected physical sequence is `SELECT reboot-test consumed=1`, a firmware
reset, `CHAIN freebsd`, then a new FreeBSD boot and working SSH. Only after that
passes should the lab kernel request be armed and tested for three consecutive
capture/reset/FreeBSD cycles. COM1 capture remains 38400 baud, 8N1, no flow
control, FTDI adapter and null-modem cable.

## Hang recovery and rollback

The lab completion hook only runs when the kernel reaches its terminal function.
A loader hang, earlier kernel hang, stalled PM timer, or ineffective reset still
requires another mechanism. FreeBSD successfully attached `ichwd0` as an Intel
Bay Trail watchdog during inspection, but watchdog arming across this boot path
has not been implemented or tested. Loading the driver alone is not hang-recovery
evidence. Its implementation is documented in the
[FreeBSD watchdog driver](https://github.com/freebsd/freebsd-src/blob/releng/15.0/sys/dev/ichwd/ichwd.c).
No persistent watchdog service was enabled.

To disarm, install an environment block with `request=none` while in FreeBSD.
To bypass the lab entirely, select the internal FreeBSD disk in firmware or
remove the USB. To restore the pre-experiment USB prefix, verify the recorded
backup hash and USB identity, then restore exactly the backed-up 96 MiB and
verify its readback. The remaining USB bytes were not changed.
