# Qotom boot recovery experiment

This is an opt-in lab prototype for issue #333, separate from the canonical
halt-until-reset observation in #327. Completed-run recovery and watchdog
recovery from deliberate loader and early-kernel stalls have been observed on
the physical board. It does not broaden physical platform admission.

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
- `watchdog-leanos-<digest>-<UTC minute fields>`: consume the request, validate
  its current-minute window, arm the board watchdog, verify and launch the lab
  ELF. This is the runner default. The digest must match the configured image.
- `leanos-<ELF SHA-256>`: the historical unprotected launch for explicit
  comparisons; it still consumes the request and verifies the image.
- `watchdog-test-<UTC minute fields>` and `watchdog-kernel-<digest>-<UTC minute fields>`:
  deliberate loader/early-kernel stall experiments described in the watchdog notes.
- `rtc-probe`: an unarmed 65-second clock/expiry preflight. The old unbounded
  `watchdog-test` request is disabled.

GRUB writes `request=none` before executing a one-shot action. A failed
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
requests, invalid environment state, image hash mismatch, and launch of the lab rejection kernel. It reads
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
the USB. After the operator selected legacy USB first, the capture at 17:02 UTC showed
`SELECT reboot-test consumed=1`, a reset, then `CHAIN freebsd disk=hd1`. FreeBSD
returned with boot time 17:02:57 UTC and the saved request was `none`.
The media ELF was read back as
`9226ca1e9ea33607ba73e1acbfe3df5063665df9f5b13fbbd001cc7fb89bbdb2`.

The first actual LeanOS lab run emitted its expected `dma-identity` FINAL at
17:04:52 UTC. Subsequent firmware bytes appeared about 34 seconds later, followed
by `CHAIN freebsd disk=hd1` at 17:05:27. FreeBSD returned with boot time 17:05:42
and working SSH. The BIOS remained configured to select USB. Three additional
automated cycles then passed consecutively, with post-terminal quiet intervals
of 34.27, 34.28 and 36.69 seconds. Every cycle verified a new FreeBSD boot, working
SSH, and `request=none`. The retained lab observations are in
`hardware/lab/observations/qotom-20260909/`. This includes the exact producer
script used; the current classifier additionally rejects nonmonotonic timestamps
and unexpected earlier kernel records. COM1 capture remains 38400 baud, 8N1, no flow
control, FTDI adapter and null-modem cable.

## Automated completed-run captures

After USB-first selection and a successful physical fallback test, run the local
orchestrator with access to the serial device and authenticated SSH:

```sh
python3 scripts/run-qotom-recovery-lab.py \
  --host freebsd@HOST --host-key-alias freebsd.lan \
  --usb-serial USB_SERIAL --serial-device /dev/serial/by-id/ADAPTER \
  --elf build/qotom-lab/leanos-qotom-lab.elf \
  --output /path/to/new/capture-directory --cycles 3
```

The default `watchdog-leanos` scenario validates the USB serial and remote ELF
digest and generates a dated, digest-bound request from the verified board UTC
clock. GRUB consumes it and arms 120 watchdog ticks before loading LeanOS. The
runner starts serial collection before reboot and bounds each protected cycle
at 420 seconds. It requires one arm, the exact load digest and lab rejection
trace, 30–90 seconds of post-terminal quiet, a subsequent consumed-request
default and chain marker, a changed FreeBSD boot time, authenticated SSH, and
the saved request cleared to `none`. Explicit `--scenario leanos` retains the
older unprotected 180-second completed-run path for comparisons. It stops on failure instead of retrying
boots indefinitely. Raw bytes, chunk timestamps, SSH reboot output and result
metadata are retained per cycle. The runner currently targets this rejection
image, not an arbitrary future CPL3 success protocol.

`--ssh-prefix` accepts an argument list such as `sshpass -e ssh` if password
credentials are supplied externally in `SSHPASS`; credentials are not written
into the evidence. Normal SSH agent/key authentication is preferable for repeat
use. The tool does not install an SSH key or modify the internal bootloader.
If a request was armed but a later step failed, disarm it before an unrelated
reboot. The same fixed mount point must not be used concurrently by other tools.

`test-qotom-recovery-capture.py` rejects changed/truncated traces, false success,
duplicate terminals, insufficient quiet, unexpected kernel output and a repeated
LeanOS selection. `test-qotom-lab-usb.py` exercises the actual GRUB boot code in
QEMU with a fake fallback disk. The emulator tests use an explicitly marked mock timer for guarded image loads;
physical loader and early-kernel hang recovery are established by the separate
[watchdog observations](qotom-watchdog-lab.md), not by the emulator mocks.

## Hang recovery and rollback

The completion hook alone only runs when the kernel reaches its terminal
function. The default route now arms the Bay Trail TCO watchdog in GRUB before
loading the image. Deliberate loader and early-kernel stalls have both recovered
to authenticated FreeBSD SSH; see the exact captures and limits in the
[watchdog notes](qotom-watchdog-lab.md). Recovery does not convert a missing or
incorrect LeanOS terminal trace into a successful scenario. The hardware tests
cover the current rejection image and explicit early stalls, not arbitrary
future platform changes. No persistent FreeBSD watchdog service is enabled.

To disarm, install an environment block with `request=none` while in FreeBSD.
To bypass the lab entirely, select the internal FreeBSD disk in firmware or
remove the USB. To restore the pre-experiment USB prefix, verify the recorded
backup hash and USB identity, then restore exactly the backed-up 96 MiB and
verify its readback. The remaining USB bytes were not changed.

## PCI diagnostic capture

The optional PCI mode uses protocol family 25 and the generated CPU, MSR, and
PCI inventory replay boundaries. Build it in a separate lab checkout from
prepared inputs with identical kernel source:

```sh
python3 scripts/build-qotom-recovery-lab.py \
  --prepared-repo ../leanos --pci-diagnostic
python3 scripts/test-qotom-pci-diagnostic-image.py \
  --elf build/qotom-pci-lab/leanos-qotom-lab.elf \
  --lab-completion --output build/qotom-pci-lab/qemu
```

The builder retains the completion-reset overlay and links the diagnostic's
native PCI reader. Its output directory is `build/qotom-pci-lab`; the default
lab image stays in `build/qotom-lab`. `create-qotom-lab-usb.py --pci-diagnostic`
selects the new directory when creating a local USB disk image. This packaging
option does not write or install anything on the physical Qotom. Exercise the
resulting disk image with the matching test mode:

```sh
python3 scripts/create-qotom-lab-usb.py \
  --pci-diagnostic --freebsd-boot-uuid UUID_OF_ADA0P2
python3 scripts/test-qotom-lab-usb.py \
  --pci-diagnostic --image build/qotom-pci-lab/usb.img \
  --freebsd-boot-uuid UUID_OF_ADA0P2
```

This uses a fake fallback disk and retains serial logs and replay results under
`build/qotom-pci-lab/usb-tests`. Kernel-launch cases use an emulated J1900 CPU
profile so they reach the PCI diagnostic. The watchdog recipe is mocked in the
loader tests; request consumption, bad hashes, and fallback remain checked.

After provisioning the corresponding protected lab image, pass
`--pci-diagnostic` to `run-qotom-recovery-lab.py` with the usual host, USB serial,
serial-device, ELF, and output arguments. It requires `watchdog-leanos` mode
and is mutually exclusive with `--cpu-diagnostic`. `--diagnostic-replay` selects
the CPU/MSR executable; `--pci-replay` selects the PCI inventory executable.
Before any SSH or boot arming, both executable self-tests must pass and the
PCI executable must reject an empty inventory through its bounded CLI.
The tool retains the protocol and hashes of both executables, rejects changed
replay inputs during capture, and saves the extracted diagnostic bytes.

The existing image digest, watchdog launch, quiet interval, FreeBSD chain,
SSH restoration, and consumed-request checks remain required. A scan failure
can be captured and replayed without becoming a successful inventory result.
Neither recovery nor an inventory match authorizes platform admission or CPL3.
QEMU checks the completion-mode prefix and PCI observations on an unrelated
host bridge; it does not verify the physical board-specific reset timer.

## Raw GRUB handoff observation

For a diagnostic capture of the actual bootloader bytes, add
`--handoff-capture` alongside `--pci-diagnostic` to both the lab builder and
the physical recovery runner. The builder's `boot/kernel.c` input remains
unchanged; only the opt-in overlay emits the additional lab records. It
checks the Multiboot2 magic, pointer alignment, initial 16 MiB mapping bound,
and a 16–65,536 byte aligned extent before reading the payload. Rejected
extents emit status 1 and no payload. Valid extents are emitted in ordered
64-byte hex chunks before the ordinary CPU/PCI diagnostic records.

The observer retains `multiboot2.bin` byte-for-byte and a `handoff.json`
metadata report, including the executing initial APIC ID, raw hash, tag-chain
shape, memory-map entry format, and advertised framebuffer geometry when
present. The handoff decoder hash is bound before and after recording.
Malformed or unknown tag content is retained; a structurally valid chain
alone does not grant memory, topology, or display authority. Referenced ACPI
tables outside the Multiboot2 block are not copied by this mode and remain a
separate capture requirement. The byte stream is an observation, not proof
that firmware or other processors could not modify memory during the read.

Run the transport and native read-bound checks, then the actual overlay in
QEMU (including CPU rejection and PCI overflow cases):

```sh
python3 scripts/test-qotom-handoff-capture.py
python3 scripts/test-qotom-pci-diagnostic-image.py \
  --elf build/qotom-pci-lab/leanos-qotom-lab.elf \
  --output build/qotom-handoff-qemu --lab-completion --handoff-capture
```

The handoff records use the `LEANOS-LAB/1` namespace. The existing generated
CPU/PCI stream and its terminal result are unchanged. The runner requires an
explicit handoff flag so an unexpected prelude cannot silently pass as an
ordinary diagnostic capture. Physical display acceptance still requires an
operator observation; framebuffer metadata does not establish visible output.
