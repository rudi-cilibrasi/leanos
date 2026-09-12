# Native HDA global observation — 2026-09-11

The protected Win7 Legacy capture reports status 0, GCTL `1` before and after,
GCAP `4401`, VMIN `0`, VMAJ `1`, INTCTL `0` (hexadecimal). Exact resource checks
before and after the six width-specific MMIO reads passed. GCAP reports four
input and four output streams, zero bidirectional streams and 64-bit addressing;
this is the actual native observation needed before selecting stream registers.

The [observer design](../../../../docs/qotom-hda-observation.md) describes the
Intel register contract and the conflicting stream-count text in the datasheet.
GCTL reports out of reset, and INTCTL was zero. No stream or ring register was
read, and no HDA write, reset or BME clear was performed. These samples do not
establish halted engines, transaction drain, continuing firmware/AP exclusion
or system-wide DMA containment. The terminal remains `qotom-platform-pending`.

The preceding SATA stage reported successful BME clear from `0007` to `0003`.
FreeBSD recovered after 34.30049141001655 seconds of serial quiet,
boot time 1789176762 to 1789178799, with the request consumed.
Independent SSH verified image/configuration hashes and request=none, then
removed the read-only mount. Serial was FTDI/null modem COM1 at 38400 baud, 8N1.

ELF SHA256:
`10eefd4102584d38a0d8e6f4d9babf57b3f9539527cafa366f1e691acd1ba13c`.
Build and runner revision: eac5ee61f80dba675d8c6c3e77414f5a8327ea32; sources
were clean at build. All 115 build hashes, the eight-site MSR-write audit,
width-specific load disassembly and QEMU foreign-firmware rejection passed.
All 51 protected capture groups passed before building. Guarded USB serial
11758C40, backup, old/new hashes and filesystem checks passed before reboot.
