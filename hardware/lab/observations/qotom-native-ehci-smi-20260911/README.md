# Native Qotom EHCI SMI-disable capture

A protected Win7 Legacy USB boot completed EHCI firmware handoff, then
refreshed the ownership/list binding and wrote one zero dword to legacy
control/status at configuration offset `0x6c`. The observed control value
changed from `0x2000` to `0`, and the final full refresh passed. The native
SMI result was status 0, write attempted 1, before 8192, after 0.

The complete protected capture includes preceding firmware, BSP, PCI and EHCI
observations and agrees with generated inventory replay. FINAL remained
`qotom-platform-pending`. No controller stop or reset was requested.

FreeBSD returned automatically after 34.30501259598532 seconds of serial quiet.
Boot time changed from 1789152042 to 1789153139; the request was consumed.
Independent read-only SSH verified the installed ELF/configuration and
`request=none`. Serial was FTDI/null modem COM1, 38400 baud, 8N1, no flow control.

ELF SHA256:
`809788ba245bfb3fd332d95a4d21b95c10e933b161f2bd7f2fbeef0c3834d3b2`.
Build provenance remains bbf7d55 with dirty integration sources; capture runner
was 647e983. The guarded installer checked USB serial 11758C40 and old/staged
hashes, backed up boot files, and verified the filesystem and installed hashes.

This establishes a bounded readback observation of disabled EHCI legacy SMI
enables. It does not establish controller halt, drained transactions, continuing
firmware/AP exclusion, DMA containment or platform/CPL3 admission. No
operator-visible display result was obtained. Hardware issues remain open.
