# AHCI identify program

`LeanOS/Storage/Ahci.lean` is a Lean device program for the Qotom's Intel Bay
Trail SATA controller (PCI `8086:0f23` at 00:13.0). It is the first program
that selects a BAR other than BAR0: its target names the ABAR at
configuration offset 0x24 and a 2 KiB window.

It is read-only towards the disk. It checks the controller identity and that
port 1 (the only implemented port) has a device with the PHY up, stops the
port's command and FIS-receive engines if firmware left them running, points
PxCLB and PxFB at executor scratch, and issues one IDENTIFY DEVICE through
command slot 0 with a single 512-byte PRD. It polls for completion (a
task-file error fails the program), prints the identify words for serial
number, firmware, model and LBA48 capacity, stops the engines again and
clears Bus Master.

## Confinement

The program is admitted under `qotomAhciPolicy`
([device-program confinement](device-program-confinement.md)): the ABAR
window, configuration reads of identity and command only, no configuration
writes, Memory Space and Bus Master (and clearing Bus Master), DMA into
scratch, and PxCLB/PxFB as address sinks, so both can only ever point into
scratch. The command-table and PRD pointers live in scratch and fall under
the J1900 DMA assumption of
[ADR 0021](adr/0021-j1900-device-dma-destinations.md).

## Trying it

```sh
lake exe leanos-wifi-gen ahci-identify build/wifi/ahci.bin
python3 scripts/build-qotom-recovery-lab.py --prepared-repo . --lab-program build/wifi/ahci.bin
```

then install and boot the image as in `docs/wifi-driver.md`. Print tags
`0x31xx` report controller registers; `0x32ww` carries identify words `ww`
and `ww + 1`.

Hardware: `hardware/lab/observations/qotom-ahci-identify-20260929` — the
decoded model, firmware, serial and capacity match FreeBSD's
`camcontrol identify` for the same disk.

## One-sector read service on q35 (issue #496)

`LeanOS/Storage/AhciRead.lean` is the second device program hosted by the
canonical kernel, as a copy of the keyboard's device-service pattern
([ADR 0022](adr/0022-device-programs-as-kernel-services.md)). It drives
q35's built-in ICH9 AHCI (`8086:2922` at 00:1f.2, requester 250, ABAR at
0x24) in the `ahci-service` image, and it never writes the disk.

The program checks the controller identity and that ports 0 and 1 are
implemented, stops the command and FIS-receive engines of both ports
(firmware leaves them running on its own memory), checks that port 1 has a
device with the PHY up, and only then sets Bus Master. It points port 1's
command list and received-FIS area at scratch, issues one READ DMA EXT of one
sector at the fixed LBA `readLba` (7) through slot 0 with one 512-byte PRD,
and polls for completion. It then stops port 1's engines, clears Bus Master,
reports the LBA, and yields the sector's 128 dwords one at a time. Every
structure the controller touches lies in the first scratch page.

It is admitted under `q35AhciPolicy`: a 512-byte window (host control
registers and ports 0 and 1 only), identity and command reads, no
configuration writes, Memory Space and Bus Master (and clearing Bus Master),
DMA, PxCLB/PxFB of ports 0 and 1 as address sinks, and a **descriptor map**
(`AhciRead.descriptorMap`): the CTBA of all 32 command headers and the data
base of the 40 PRDs that fit before the data buffer. So, unlike the Qotom
identify program above, its command-table and PRD pointers are covered by
`run_admissible_descriptors`; the negative fixtures reject forged CTBA and
PRD pointers. That the map lists every pointer the controller follows for
these commands (AHCI 1.3.1 §4.2.2–4.2.3, PRDTL 1) is a named assumption
(ADR 0021).

The disk is not a committed binary: `scripts/generate-ahci-service-disk.py`
writes a fixed 16-sector image (each sector labelled with its LBA, every 16th
dword zero) that `scripts/run-image.sh` regenerates for each run and QEMU
attaches behind port 1 with `snapshot=on`. `--check-transcript` verifies that
the committed transcript carries exactly the generated sector at the
program's LBA and its FNV-1a digest.

```sh
lake exe leanos-wifi-gen ahci-q35-service build/wifi/ahci-q35.bin
LEANOS_BOOT_SCENARIO=ahci-service LEANOS_QEMU_TIMEOUT_SECONDS=120 ./scripts/run-image.sh
```
