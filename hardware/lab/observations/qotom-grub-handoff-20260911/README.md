# Physical legacy GRUB handoff on Qotom

Captured on 2026-09-11 UTC using clean source revision
`32731dbbee8259990883381c99189cb99d271c50`, the protected lab overlay,
and the FTDI/null-modem COM1 link at 38400 baud, 8N1, no flow control.
Firmware selection: Win7 Legacy, USB first. The USB filesystem and all six
installed file hashes were verified after remount before arming one trial.
The prior boot files were backed up on FreeBSD and mgnuc; backup SHA-256:
`de1a6a4a387b81a390ce28827816c15b1acae975fc158502218ceb7cc9e0121d`.

The kernel transported the actual 2,680-byte Multiboot2 information block at
physical address 2,728,208, with executing initial APIC ID 0. The raw SHA-256
is `531a72e236ba70d24eaf7ab30c498070f2bf2414102d50f8e53acf83e6118f9b`.
This is a native bootloader handoff observation, not a reconstruction from an
OS memory map. It does not establish atomicity against firmware/AP activity.

## Display and memory metadata

GRUB advertises framebuffer kind 2 (EGA text), address `0xb8000`, pitch 160,
80 columns, 25 rows, and 16 bits per character cell. These match the existing
optional early text backend's geometry. This resolves which surface the
legacy loader advertises; no operator-visible display result has yet been
recorded. It does not erase the previously captured FADT `NO_VGA` flag or
establish a general VGA capability across firmware modes. The early backend
remains scoped to the bootloader-advertised surface under the initial map,
before quarantine or page-table replacement.

The memory-map tag contains 19 entries of 24 bytes, version 0. The ACPI 2.0
RSDP tag has valid legacy and extended checksums. handoff-projection.json
retains each memory entry's exact bytes and fields plus the RSDP bytes and
root addresses. Referenced RSDT/XSDT/SDT contents were not captured in this
trial. Production memory/topology admission and the BSP/AP contract remain
open; a structurally valid tag chain is not admission evidence.

## Diagnostic and recovery outcome

CPU replay returned accepted (65536), MSR readback returned 1, and the PCI
reader captured 16 functions. The existing fifteen-function inventory
profile rejected the count (65536). FINAL remains
`FAIL reason=qotom-platform-pending`; platform admission and CPL3 are false.

The recorder measured 34.312 seconds of post-FINAL quiet before subsequent
firmware bytes. GRUB consumed the one-shot request and chained FreeBSD; SSH
returned with a new boot time and `request=none` was verified. This is
completed-run recovery with watchdog protection, not a deliberate hang test.
The historical `hang_recovery=true` result field labels the protected scenario
and does not prove watchdog expiry.

Seven transport/read-bound/integration tests, eight native QEMU diagnostic
cases, and five USB boot-path cases passed. The native read-bound tests use
ASan/UBSan. Manifests retain source/image/replay hashes and the original
physical byte stream with timestamps; derived projections do not replace it.
