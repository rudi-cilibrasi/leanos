# Native SATA bus-master disable — 2026-09-11

The protected Win7 Legacy capture refreshed the interrupt-disabled and stopped/
empty port profile, checked Command, wrote one word at 00:13.0 offset 4, verified
immediate readback, accepted the complete final global/resource/port refresh,
and checked Command again. The result reports status 0, attempted 1,
before `0007`, after `0003` (hexadecimal).

The write clears PCI Command.BME while retaining I/O and MMIO decoding. Its
16-bit width preserves adjacent PCI Status. No port write, engine-stop request,
reset or polling was introduced. The preceding AHCI interrupt-disable stage
reported GHC `80000002` to `80000000`, and the port sample was
CMD6/IE0/TFD50/SSTS123/SACT0/CI0/CMD6 (hexadecimal).

The [observer design](../../../../docs/qotom-ahci-observation.md) cites Intel
329670-002 section 13.5.2: SATA BME does not affect split-transaction completions.
These checks do not establish transaction drain, continuing firmware/AP exclusion
or system-wide DMA containment. The terminal remains `qotom-platform-pending`.

FreeBSD recovered after 34.31269214701024 seconds of serial quiet,
boot time 1789175379 to 1789176762, with the request consumed.
Independent SSH verified image/configuration hashes and request=none, then
removed the read-only mount. Serial was FTDI/null modem COM1 at 38400 baud, 8N1.

ELF SHA256:
`2a005a751847f83a735c5ba2fae8a92463a09a7a0704f318ba0cdd6df993c0a1`.
Build and runner revision: 0ce37666453a16b30ec8d45f7565723ca84b625c; sources
were clean at build. All 111 build hashes, the eight-site MSR-write audit,
single-word store disassembly and QEMU foreign-firmware rejection passed.
Guarded USB serial 11758C40, backup, old/new hashes and filesystem checks passed
before the protected boot.
