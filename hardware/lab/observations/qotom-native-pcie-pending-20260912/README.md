# Native PCIe non-posted quiet capture — 2026-09-12

The protected Win7 Legacy boot reported six successful `PCIE-PENDING` records.
Indices 6, 7, 8, 9, 13 and 15 each completed two observations separated by the
bound 10 ms PM-timer delay. Device Status was 17, 17, 17, 16, 25 and 25
respectively, with Transactions Pending clear in every final sample.

The [design](../../../../docs/qotom-pcie-pending.md) revalidates Command `0003`,
identity, the complete capability list, Device Capabilities and every Device
Control/Status bit except Transactions Pending around each sample. It requires
successful typed root-port and endpoint BME results and the retained Realtek
stopped states. Each function receives fresh ECAM and timer arms that are
revoked before serial output.

This is bounded evidence that the six functions had no reported outstanding
non-posted request in two samples. It does not establish posted-write
completion, continuing firmware/AP/device exclusion, Broadcom coverage,
transaction drain, whole-machine DMA quarantine or platform admission. The
terminal remains `qotom-platform-pending`.

FreeBSD recovered automatically after 34.31192182103405 seconds of serial
quiet, boot time 1789193619 to 1789196801, with the request consumed. Independent
SSH verified the installed hashes, backup and `request=none`, then removed the
read-only mount. Serial: FTDI/null modem COM1, 38400 baud, 8N1, no flow control.

ELF SHA256:
`a8aa4fdd94279d3a4cc312361d8acbb7c49b081552b8943e745ac4d0ca836480`.
Raw capture SHA256:
`bc5903d6f7902373c4413f19545a8668c2b6a653dec714ed5bcfd7b1936b039d`.
Build and runner revision: `55de2bd7d45b6b9f80a7d2ee66f3f96a903c3b09`.
The clean build manifest contains 140 hashes. The complete ordinary and pinned
sanitizer capability suite, focused protected projection, guarded USB install,
FAT check, read-only verification, physical runner and independent recovery
inspection passed.
