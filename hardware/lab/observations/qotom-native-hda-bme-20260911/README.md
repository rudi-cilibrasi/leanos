# Native HDA bus-master disable — 2026-09-11

The protected Win7 Legacy capture reports status 0, attempted 1, Command
`0006` before and `0002` after (hexadecimal). The helper refreshed the stopped
ring/stream state, attempted one 16-bit write at 00:1b.0 offset 4, checked
immediate readback, refreshed all state/resource observations and checked final
Command. MMIO decoding and adjacent PCI Status were preserved.

The [design](../../../../docs/qotom-hda-bme.md) specifies 97 reads and one write.
No ring, stream or position register write, stop request, reset or polling
occurred. These sequential samples and Command readback do not establish
transaction drain, continuing firmware/AP exclusion or system-wide DMA
containment. The terminal remains `qotom-platform-pending`.

FreeBSD recovered after 34.31826545501826 seconds of serial quiet,
boot time 1789182519 to 1789182881, with the request consumed.
Independent SSH verified BIOS boot, installed image/configuration hashes and
request=none, then removed the read-only USB mount. Serial: FTDI/null modem
COM1, 38400 baud, 8N1, no flow control.

ELF SHA256:
`28b53a1769147eea00f7b6cdd1e826d5207b1080df12b5495b2d8b063e7804db`.
Build and runner revision: 7ff1f023f8150fc5af1f80576ec5667d4d3ab2d3; clean sources.
All 123 build hashes, the eight-site MSR-write audit, single-word store
disassembly and QEMU foreign-firmware rejection passed. All 55 protected
capture groups passed before building. Guarded USB serial 11758C40, backup,
old/new hashes and filesystem checks passed before reboot.
