# Native Realtek state capture — 2026-09-11

The protected Win7 Legacy boot reports two successful `REALTEK-STATE` records,
indices 13 and 15. Both endpoints returned stable TXCFG `2f900d00`, Command
`00`, interrupt mask `0000`, receive configuration `0002ff0e`, Command `00`
and TXCFG `2f900d00` (hexadecimal). TXCFG's hardware-revision field satisfies
mask `7cc00000 = 2c800000`, identifying the reviewed RTL8168E-VL candidate.

The [design](../../../../docs/qotom-realtek-state.md) brackets each endpoint's
six typed MMIO reads with complete checks of its upstream bridge routing and
PCIe state after that root port's BME transition. It writes no endpoint
register. These sequential samples do not prove device shutdown, transaction
drain, continuing firmware exclusion, DMA containment or platform admission.
The terminal remains `qotom-platform-pending`.

FreeBSD recovered automatically after 34.31011284497799 seconds of serial
quiet, boot time 1789187141 to 1789189659, with the request consumed.
Independent SSH verified BIOS boot and installed hashes, then removed the
read-only mount. Serial: FTDI/null modem COM1, 38400 baud, 8N1, no flow control.

ELF SHA256:
`0af703abc4160289e05c92020adc4271980955d3198e391751564dff3e1ef382`.
Build and runner revision: `0374587f0018907310ed0a87008d636b363a42dc`.
All 134 build hashes, eight MSR sites, typed load disassembly and QEMU
foreign-firmware rejection passed. The full protected suite passed 61 groups.
Guarded USB serial 11758C40, unique backup, prior/new hashes and filesystem
checks passed before reboot. The capture runner exited successfully.
