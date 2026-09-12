# Native TXE firmware status — 2026-09-11

The protected Win7 Legacy capture reports status 0, firmware status DWORDs
`1f0000d5` and `69000000` (hexadecimal), read at 00:1a.0 offsets 40h and 48h.
Both identity/Command/class/layout checks passed. These raw values are not a
DMA-stop, transaction-drain, atomic-snapshot or firmware-exclusion witness.

The [observer design](../../../../docs/qotom-txe-status.md) specifies ten
configuration reads. No TXE MMIO access, write, reset or polling occurred.
The preceding HDA stage reported successful BME clear, 0006 to 0002.
The terminal remains `qotom-platform-pending`.

FreeBSD recovered after 34.323108143988065 seconds of serial quiet,
boot time 1789182881 to 1789184381, with the request consumed.
Independent SSH verified BIOS boot, installed image/configuration hashes and
request=none, then removed the read-only USB mount. Serial: FTDI/null modem
COM1, 38400 baud, 8N1, no flow control.

ELF SHA256:
`2b2953d3aa0395f7b7691d65ee47ec227a5efd6cee13f1e64c9ffa0f4f7d19e3`.
Build and runner revision: 9f8f0b0f1b96db7ddc2717d23b7d95852dc6550d; clean sources.
All 125 build hashes, the eight-site MSR-write audit and QEMU foreign-firmware
rejection passed. All 57 protected capture groups passed before building.
Guarded USB serial 11758C40, backup, old/new hashes and filesystem checks
passed before reboot.
