# Native AHCI port 1 observation — 2026-09-11

The protected Win7 Legacy boot completed the preceding USB, PCIe and AHCI global
captures, then observed SATA port 1 with status 0. Two complete global/resource
refreshes bracketed seven port reads, and the native contexts were disarmed
before the record was emitted.

| Register | Offset | Raw value |
| --- | --- | --- |
| CMD before | 198 | 00000006 |
| IE | 194 | 00000000 |
| TFD | 1a0 | 00000050 |
| SSTS | 1a8 | 00000123 |
| SACT | 1b4 | 00000000 |
| CI | 1b8 | 00000000 |
| CMD after | 198 | 00000006 |

Numbers are hexadecimal. In both CMD samples, ST/FRE/CR/FR were clear; the
command-list and FIS-receive engines reported stopped. The active and issued
command masks were zero. These are sequential observations, not an atomic
snapshot or proof of transaction drain or continuing firmware/AP exclusion.
Global interrupts remained enabled (GHC `80000002`). No SATA write, engine stop,
reset or BME clear was performed. The terminal remains `qotom-platform-pending`.
Register definitions follow Intel document 329670-002, sections 13.8.31–.33,
.35, .38 and .39, linked in [the observer design](../../../../docs/qotom-ahci-observation.md).

FreeBSD recovered after 34.305494194995845 seconds of serial quiet,
boot time 1789169440 to 1789170960, with the
request consumed. Independent SSH verified image/configuration hashes and
request=none, then removed the read-only mount. Serial was FTDI/null modem
COM1 at 38400 baud, 8N1.

ELF SHA256:
`f15d68953a4179897c7b9a075135c722a538e84c77d25bd4561eeba65e810a67`.
Build and runner revision: 1543c35f44b9338531c441518f66f608ed153d6c; build sources
were clean. All 103 build hashes, the unchanged eight-site MSR-write audit and
QEMU foreign-firmware rejection passed. Guarded USB serial 11758C40, backup,
old/new hashes and filesystem checks passed before the protected boot.
