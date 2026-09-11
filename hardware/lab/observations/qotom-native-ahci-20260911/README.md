# Native AHCI global register observation — 2026-09-11

The protected Win7 Legacy boot completed the preceding USB and PCIe captures,
then observed the SATA controller at 00:13.0 with status 0. Exact PCI identity,
class, memory decode and ABAR checks passed before and after five MMIO reads.

| Register | Offset | Raw value |
| --- | --- | --- |
| CAP | 00 | c720ff01 |
| GHC | 04 | 80000002 |
| PI | 0c | 00000002 |
| VS | 10 | 00010300 |
| CAP2 | 24 | 00000038 |

Numbers are hexadecimal. GHC reports AHCI enabled and global interrupts enabled.
PI identifies only port 1 as implemented; VS reports AHCI 1.3. CAP2.BOH is clear.
No port registers, command engine state, outstanding commands or DMA drain were
observed. No SATA write, interrupt disable, stop or reset was performed. The
result remains `qotom-platform-pending` and grants no platform admission.

FreeBSD recovered after 34.31364832201507 seconds of serial quiet, boot time
1789168301 to 1789169440, with the request consumed. Independent SSH verified
installed image/configuration hashes and request=none, then removed the read-only
mount. Serial was FTDI/null modem COM1 at 38400 baud, 8N1.

ELF SHA256:
`ed5959168554891957b49d7aae7a0618f39874ba40eb5810a98ddfd8ab3dbc90`.
Build and runner revision: 202f95f4e78187253448f8458ba0d7b3ca79dbf8; sources were
clean at build. All 99 manifest hashes, the unchanged eight-site MSR-write audit
and QEMU foreign-firmware rejection passed. Guarded USB serial 11758C40, backup,
old/new hashes and filesystem checks passed before the protected boot.
