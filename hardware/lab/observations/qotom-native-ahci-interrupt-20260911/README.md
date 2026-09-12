# Native AHCI global interrupt disable — 2026-09-11

The protected Win7 Legacy capture refreshed the exact stopped/empty port profile,
wrote GHC once, verified immediate readback, then accepted the complete final
global/resource/port refresh. The record reports status 0, attempted 1,
before `80000002`, after `80000000` (hexadecimal).

The write clears GHC.IE, retains GHC.AE and leaves GHC.HR zero. The preceding
port capture reported CMD6/IE0/TFD50/SSTS123/SACT0/CI0/CMD6 (hexadecimal). The
helper rechecked that profile before and after the write. It performed no port
write, engine-stop request, reset or BME clear. These sequential checks do not
establish atomic state, transaction drain or continuing firmware/AP exclusion.
The terminal remains `qotom-platform-pending`.

The [observer design](../../../../docs/qotom-ahci-observation.md) links Intel
329670-002 section 13.8.2 for the GHC register definitions and describes the
75-read bound, consumed writer and ambiguous-failure handling.

FreeBSD recovered after 34.309270564990584 seconds of serial quiet,
boot time 1789173880 to 1789175379, with the request consumed.
Independent SSH verified image/configuration hashes and request=none, then
removed the read-only mount. Serial was FTDI/null modem COM1 at 38400 baud, 8N1.

ELF SHA256:
`917f6c3b53ffa8404a545db651a4c44c1c66add6310a789f08629797c0f73fc8`.
Build and runner revision: 50009b70fe34d52dd4a14d9e51141aae7ffea0b9; sources
were clean at build. All 107 build hashes, the eight-site MSR-write audit,
single-DWORD store disassembly and QEMU foreign-firmware rejection passed.
Guarded USB serial 11758C40, backup, old/new hashes and filesystem checks passed
before the protected boot.
