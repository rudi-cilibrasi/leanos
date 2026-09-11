# Qotom PAT and control-register observation

Source d21d55bd0ea320f43bc5880fa7e3f93463935068, clean lab build.
ELF SHA256: `9bad6db87275f06417f1b85de1d3cd520ae19fcc14fc67864bac2fd74aef241a`.
Win7 legacy USB boot, FTDI/null modem to COM1, 38400 baud, 8N1, no flow control.
The sampler follows successful CPU/control checks and the executing BSP record.

Physical observations: CPUID EDX 3219913727; PAT available;
IA32_PAT 0x0007040600070406 (slots 6,4,7,0,6,4,7,0);
CR0 0x8001001f, CR3 0x150000, CR4 0x68. The executing APIC sample is
0xfee00900, BSP APIC ID 0. These are observations, not MMIO mapping admission.
No PAT/control writes or ECAM MMIO read is introduced by this sampler.

The unchanged mechanism-1 diagnostic encountered selector interference:
3196 reads, one mismatch, then capacity status 2 at 0b:11.3 offset 0,
no published inventory, FINAL FAIL reason qotom-pci-enumeration.
This image predates PR #386's return-failure correction; do not interpret this
capacity status or suspect value as an authoritative seventeenth device.
No PCI quarantine, DMA containment, or CPL3 success is claimed.

Protected recovery passed: 34.31315643299604 seconds of terminal quiet,
FreeBSD SSH restored with changed boot time, request=none verified.
This is lab completion/reset evidence, not canonical terminal-halt evidence.

All eight QEMU image cases passed. The initial USB suite passed nineteen cases
but timed out after 15 seconds in normal-guard-boot, before kernel output.
A retained local debug run with added GRUB markers passed checksum, Multiboot
load and kernel boot. An unmodified retest of all four normal-guard cases
then passed. The timeout cause is unproven; preserve usb-initial.log rather
than describing the first full suite as successful. usb-guard-retest.json
covers only those four retested cases. No loader code was changed for the retest.

The installed USB files were backed up, updated in place, synced, checked with
fsck_msdosfs -n and verified by read-only hashes. Recovery recipes are unchanged.
The build manifest pins the source overlay and final ELF; the ELF is not stored
in this observation directory. Replay uses the recorded unchanged CPU/PCI tools.
