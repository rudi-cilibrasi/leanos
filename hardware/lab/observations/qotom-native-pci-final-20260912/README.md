# Native Qotom final PCI checkpoint capture — 2026-09-12

A protected Win7 Legacy boot completed every bounded device transition and a
fresh final ECAM enumeration of all sixteen Qotom functions. The generated Lean
identity/header and Command checks accepted this exact final Command vector:

```text
0007,0003,0003,0002,0102,0002,0003,0003,
0003,0003,0402,0007,0003,0003,0000,0003
```

The final record reported status 6, index 16, count 16,
`commands-accepted=1`, assumption mask 3, and `admitted=0`. The first two mask
bits state the reviewed fixed-infrastructure and LPC assumptions. Posted-write
drain, TXE-private DMA quiescence, and continuing firmware/SMM noninterference
remain false. LeanOS therefore reached the intended typed terminal
`qotom-pci-assumptions`; it did not authorize CPL3 or claim platform DMA
quarantine. VT-d is explicitly not applicable to this initial J1900 profile,
and no q35 VT-d MMIO was accessed.

The successful raw capture SHA256 is
`c43e97fe13aee87137f81a60836ff8df7557032272535ef516af8d2da67ecd1c`.
The protected ELF SHA256 is
`d7ae6577052a6558040064161d7fafd2388e03a9697df1e31dde99640287a0dc`.
The build manifest records a clean source revision
`7bb1fb1c964c18080759601067843964b037c2f8` and 161 hashed build inputs.

The watchdog recovered FreeBSD after 34.3113842579769 seconds of serial quiet.
The FreeBSD boot time changed from 1789252838 to 1789253021 and the one-shot
request was consumed. Independent SSH inspection confirmed USB serial
`11758C40`, all installed hashes, a disarmed GRUB environment, no lingering
mount, and the recovered Intel TXE function. Serial was FTDI/null-modem COM1 at
38400 baud, 8N1, with no flow control.

The first attempt in `load-rejection` never loaded LeanOS. Its generated
checksum line used `leanos-qotom-lab.elf`, while this GRUB setup resolves the
manifest from the filesystem root and requires `/boot/leanos-qotom-lab.elf`.
GRUB reported an invalid filename, consumed the request, and immediately
chained to FreeBSD. `fix-checksum.sh` records the bounded correction; the
successful retry used the same ELF and GRUB configuration.

This evidence establishes the complete final identity and PCI Command
observation. The three false assumptions are the next exact work for GitHub
issue #330, followed by whole-profile production dispatch before any q35-only
path.
