# Native Realtek BME capture — 2026-09-11

The protected Win7 Legacy boot reports two successful `REALTEK-BME` records,
indices 13 and 15. Each endpoint Command changed from `0007` to `0003` through
one 16-bit store after its complete routed stopped-state refresh. Both retained
and final engine samples remained TXCFG `2f900d00`, Command `00`, interrupt
mask `0000`, receive configuration `0002ff0e`, Command `00`, and TXCFG
`2f900d00` (hexadecimal).

The [design](../../../../docs/qotom-realtek-bme.md) binds each write to its exact
endpoint, bridge route, successful upstream root-port transition, prior stopped
state, copied firmware and active root/control state. It retains memory and I/O
decoding and adjacent PCI Status. The sequential queue-empty and Transactions
Pending samples do not establish transaction drain, continuing firmware/AP
exclusion, system-wide DMA containment or platform admission. The terminal
remains `qotom-platform-pending`.

FreeBSD recovered automatically after 34.308428978023585 seconds of serial
quiet, boot time 1789191219 to 1789193019, with the request consumed. Independent
SSH verified the installed hashes and unique backup, then removed the read-only
mount. Serial: FTDI/null modem COM1, 38400 baud, 8N1, no flow control.

ELF SHA256:
`38b9a678db2023a37e0b9fb72920aef2770f8e7eac115563566e663a6e217e86`.
Build and runner revision: `01b11b58e5270bf5cf547aa14c7453c293397ba3`.
All 138 build hashes, eight MSR sites, exact word-store disassembly and QEMU
foreign-firmware rejection passed. The pinned capability suite and all 63
protected capture groups passed. Guarded USB serial 11758C40, unique backup,
prior/new hashes and filesystem checks passed before reboot. The capture runner
and independent recovery inspection completed successfully.
