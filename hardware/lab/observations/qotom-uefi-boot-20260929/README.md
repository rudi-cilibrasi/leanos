# LeanOS booted through UEFI on the Qotom — 2026-09-29

The Qotom firmware was switched from Win7 Legacy to **UEFI (Win7 UEFI)**
mode, Secure Boot off. The lab stick keeps its i386-pc GRUB in the MBR and
now also carries `EFI/BOOT/BOOTX64.EFI` from `scripts/build-efi-grub.sh`
(SHA256 `6c7f3baa0b174ef976a60d07c1e3202e3b2f070535110f0ca8ed27f2ea3d1a16`).
Both loaders read the same `boot/grub/grub.cfg`, rendered from
`hardware/lab/grub-qotom-ssd.cfg.in` (SHA256
`9e56eb78a05cabbfdc23de87d6a124c1d028dbdd2422505bffa482e4f32f0bac`).

A watchdog-protected one-shot request booted the LeanOS lab ELF from the
SSD's EFI system partition through UEFI GRUB, and the next boot chained back
to FreeBSD, which reported `machdep.bootmethod=UEFI`:

```text
LEANOS-LAB/1 WATCHDOG-LEANOS-LOAD
LEANOS-LAB/1 WIFI-BEGIN id=0x435314e4 bar0=0xd0700004
WIFI 0104 0x00100000
LEANOS-LAB/1 WIFI-DHCP address=192.168.6.30
LEANOS-LAB/1 WIFI-PING listening address=192.168.6.30
LEANOS-LAB/1 WIFI-PING echo-replies=20
LEANOS-LAB/1 WIFI-END status=0 code=0x00000000
LEANOS/3 FINAL status=FAIL reason=qotom-platform-pending
LEANOS-LAB/1 DEFAULT request=none
LEANOS-LAB/1 CHAIN freebsd disk=hd1
```

The kernel admitted the UEFI GRUB Multiboot2 handoff (EFI memory map tag
after the ACPI tags; distinct ACPI 1.0/2.0 RSDTs) and reached the lab's
ordinary final record, `qotom-platform-pending`, as under Legacy mode. From
the wired workstation, 20/20 pings were answered, RTT 6.5–10.5 ms (average
8.0 ms).

Two UEFI-only differences were found on this hardware and fixed:

- The firmware leaves the BCM43224's PCI command register at 0 (`WIFI 0104`
  above; Legacy BIOS had enabled memory decoding). The first UEFI run failed
  `wrongChip` (0x11) reading `0xffffffff` through BAR0. The driver now sets
  Memory Space and Bus Master itself, as `pci_enable_device` and
  `pci_set_master` do.
- Chainloaded from GRUB, FreeBSD's `loader.efi` searched the firmware's
  current boot entry (the stick) and failed with "Failed to find boot
  partition". The lab configuration now passes
  `rootdev=zfs:zroot/ROOT/default:`, and under UEFI exits to the firmware
  boot manager if the chain still fails.

The Qotom's WiFi antennas were first attached on 2026-09-28; earlier
unreliable joins (`noAuth`, and AP disassociation reason 34) were from
running without antennas.

ELF SHA256 `302d2ec0cf126f5700114dddbec409a50136f86fec3084918804f94f3bf085e6`
(embeds the network PMK; not retained). Capture SHA256
`4f1001fde4eb61e0d1b9f08d7daf8d9929b7430d2011926a47778b83054b13e6`.

Not established: pure-UEFI (Win8 / CSM off) mode, where there is no legacy
text display; serial evidence is unaffected, but that mode was not run.
