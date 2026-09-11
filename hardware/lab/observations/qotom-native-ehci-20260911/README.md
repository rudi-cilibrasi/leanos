# Native Qotom EHCI capability capture

A protected Win7 Legacy USB boot read the three EHCI capability registers
through the separate read-only UC aperture after native inventory, BSP,
capability-list and AF checks completed. The observed values were:

- capability base `0x01000020`: EHCI 1.0, operational base offset `0x20`;
- HCSPARAMS `0x00200008`: eight reported ports;
- HCCPARAMS `0x00036881`: extended capability pointer `0x68`.

The pointer locates the start of a separate configuration-space list. Its
contents and firmware ownership semaphores have not yet been read. No
controller stop, reset, ownership write or operational-register access was
performed. FINAL remained `qotom-platform-pending`.

FreeBSD returned automatically after 34.32140916000935 seconds of serial quiet.
Boot time changed from 1789147616 to 1789148738; the one-shot request was consumed.
Independent read-only SSH verified the installed ELF and `request=none`.
Serial was FTDI/null modem COM1, 38400 baud, 8N1, no flow control.

ELF SHA256:
`98ca8356b613e4f0ff7bfd6f80a6f5e461c56ba37b5a5f59d66ac404a3bd7982`.
Build provenance remains bfe2c45 with dirty integration sources; capture runner
was 1be485c. The guarded installer checked USB serial 11758C40 and old/staged
hashes, backed up the boot files, and verified the filesystem and new hashes.

This establishes one bounded capability-register observation under the lab
mapping assumptions. It does not establish firmware ownership exclusion,
controller quiescence, DMA containment or platform/CPL3 admission. No
operator-visible display result was obtained. Hardware issues remain open.
