# Native Qotom EHCI handoff capture

A protected Win7 Legacy USB boot requested EHCI OS ownership with one byte
write. The preceding captured support was `0x00010001` at `0x68` and
control/status was `0x00082005`. The first poll and final refresh observed
support `0x01000001`: OS set and BIOS clear. Final control/status was `0x2000`.
This records release at the first poll; it does not measure the firmware's
response latency during the store or establish continuing firmware exclusion.
No forced BIOS clear, SMI control write, controller stop or reset was requested.

The native result was status 0, write attempted 1, polls 1. FINAL remained
`qotom-platform-pending`. The protected capture retained all prior firmware,
BSP, PCI and EHCI observations and matched generated inventory replay.

FreeBSD returned automatically after 36.7437389419938 seconds of serial quiet.
Boot time changed from 1789149591 to 1789152042; the request was consumed.
Independent read-only SSH verified the installed ELF/configuration and
`request=none`. Serial was FTDI/null modem COM1, 38400 baud, 8N1, no flow control.

ELF SHA256:
`0ff805e5f956ddbf6f82cd8b6c81128ce0097ec0fd3c809cc24907b8b3bf2897`.
Build provenance remains dd2daaf with dirty integration sources; capture runner
was 48198c8. The guarded installer checked USB serial 11758C40 and old/staged
hashes, backed up boot files, and verified the filesystem and installed hashes.

This is one bounded semaphore-release observation under the lab mapping and
timer assumptions. It does not establish DMA containment, controller quiescence,
firmware/AP exclusion or platform/CPL3 admission. No operator-visible display
result was obtained. The hardware issues remain open.
