# Native xHCI bus-master disable — 2026-09-11

The protected Win7 Legacy boot completed xHCI ownership handoff and SMI disable,
then observed USBSTS=1, USBCMD=0, USBSTS=1. The BME helper refreshed the stopped
state, wrote one 16-bit PCI Command value at 00:14.0 offset 4, and verified
Command `0x0006` to `0x0002`, with status 0. Immediate and final readback and
complete final resource/list/ownership/stopped-state checks passed. MMIO decode
remains enabled; the word write preserves the adjacent PCI Status register.
No operational write, reset or rollback was performed.

This records the bounded bus-master clear. It does not establish outstanding
transaction drain, continuing firmware/AP exclusion or system-wide DMA
quarantine. Other device contracts and whole-profile integration remain open.
The diagnostic terminal remains `qotom-platform-pending`.

FreeBSD recovered after 34.309655685996404 seconds of serial quiet, boot time
1789165000 to 1789167041, with the request consumed. Independent SSH verified
the installed image/configuration and request=none, then removed the read-only
mount. Serial was FTDI/null modem COM1 at 38400 baud, 8N1.

ELF SHA256:
`42e3c9588f03cc9627f460d62e004a4a4251359607c17d2088d74285c52b4967`.
Build and runner revision: 9bd2f52ef84b2b70a574d93bfb111cb81628ae4d; sources were
clean. All 93 manifest hashes, the unchanged eight-site MSR-write audit and QEMU
foreign-firmware rejection passed. Guarded USB serial 11758C40, backup, old/new
hashes and filesystem checks passed before the protected boot.
