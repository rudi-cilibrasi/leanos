# Native Qotom EHCI bus-master-disable capture

A protected Win7 Legacy boot refreshed successful EHCI handoff, disabled legacy
SMIs and the stopped operational sample, then requested one 16-bit PCI Command
write at 00:1d.0 offset 4. Command changed from `0x0406` to `0x0402`, clearing BME
while preserving memory decoding and INTx disable. The helper reported status 0,
attempted 1, before 1030, after 1026. Final operational/ownership refresh and
Command readback passed. No operational stop, reset or rollback was requested.

The preceding operational samples were command `0x80000`, status `0x1000`,
interrupt enable `0`, configuration `0`. These sequential observations and BME
readback do not establish continuing firmware/AP exclusion, fabric posted-write
drain, system-wide DMA containment or platform/CPL3 admission.

Protected replay passed and FreeBSD returned automatically after
34.306907985999715 seconds of serial quiet. Boot time changed from 1789155039 to
1789156060; the request was consumed. Independent read-only SSH verified the
installed ELF/configuration and request=none; the mount was removed. Serial was
FTDI/null modem COM1 at 38400 baud, 8N1, no flow control.

ELF SHA256:
`60c016683940c3b252a7243c384fc97d2e482ed2d2fe74b31b5d2dffd107fe83`.
Build provenance is f70292b with dirty integration sources; runner was 296229d.
The guarded installer checked USB serial 11758C40, old/staged hashes, backup,
filesystem and installed hashes. FINAL remains qotom-platform-pending.
