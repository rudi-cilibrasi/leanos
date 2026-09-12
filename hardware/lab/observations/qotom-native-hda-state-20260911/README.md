# Native HDA ring and stream state — 2026-09-11

The protected Win7 Legacy capture reports status 0, CORBCTL `0`, RIRBCTL `0`,
DPLBASE `0`, and every one of the eight stream control/status DWORDs `00040000`
(hexadecimal). Both full global/resource refreshes passed against GCTL1,
GCAP4401, version1.0 and INTCTL0. All sampled ring and stream RUN bits were
clear, and position-buffer reporting was disabled. No HDA write, stop request,
reset or BME clear occurred.

The [observer design](../../../../docs/qotom-hda-state.md) describes the exact
47-read sequence, widths and resource/profile binding. These sequential samples
do not establish atomic state, transaction drain, continuing firmware/AP
exclusion or system-wide DMA containment. The terminal remains
`qotom-platform-pending`.

The preceding SATA stage reported successful BME clear from `0007` to `0003`.
FreeBSD recovered after 34.311853057006374 seconds of serial quiet,
boot time 1789178799 to 1789180063, with the request consumed.
Independent SSH verified image/configuration hashes and request=none, then
removed the read-only mount. Serial was FTDI/null modem COM1 at 38400 baud, 8N1.

ELF SHA256:
`85c208b2b448a5809e9555e5b5b9fc2ce36253fce5755b4e45e10ce6a381c226`.
Build and runner revision: 1df198627eb872109921c291eb0985a21b0108e9; sources
were clean at build. All 119 build hashes, the eight-site MSR-write audit,
width-specific load disassembly and QEMU foreign-firmware rejection passed.
All 53 protected capture groups passed before building. Guarded USB serial
11758C40, backup, old/new hashes and filesystem checks passed before reboot.
