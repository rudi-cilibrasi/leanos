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
