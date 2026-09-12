# Native root-port BME capture — 2026-09-11

The protected Win7 Legacy boot reports four successful ROOTPORT-BME records,
indices 6–9, each attempted 1, Command 0007 to 0003 (hexadecimal).
The [design](../../../../docs/qotom-rootport-bme.md) binds routing and PCIe
state before and after each single 16-bit write. This gates upstream memory
and I/O requests; completions and other request classes remain unaffected.
It is not a transaction-drain, firmware-exclusion or platform-admission proof.
The terminal remains `qotom-platform-pending`.

FreeBSD recovered automatically after 34.31038972502574 seconds of serial quiet,
boot time 1789184381 to 1789187141, with the request consumed. Independent SSH
verified BIOS boot and all installed hashes, then removed the read-only mount.
Serial: FTDI/null modem COM1, 38400 baud, 8N1, no flow control.

ELF SHA256:
`da6dff89a00f5e0d448761d1e0f9ac843b2ee66fab8d6ac28dd87d6d3d4b017a`.
Build and runner revision: f31463d8ef1824b4d7c2859afeb2b1aa51026527.
All 129 build hashes, eight MSR sites and QEMU foreign-firmware rejection passed.
The full protected suite passed 59 groups; native index-binding changes then
passed ordinary and pinned GCC ASan/UBSan tests before this clean build.
Guarded USB serial 11758C40, unique backup, old/new hashes and filesystem
checks passed before reboot. The capture runner exited successfully.
