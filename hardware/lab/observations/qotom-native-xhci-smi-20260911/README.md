# Native xHCI legacy SMI disable — 2026-09-11

The protected Win7 Legacy boot completed xHCI ownership handoff at poll two,
then disabled legacy SMI enables with one zero DWORD write to `0xd0908464`.
The SMI result is status 0, attempted 1, before `0x2000`, after `0`. Complete
before/after capability-list, resource and ownership checks passed. The preceding
EHCI observations and xHCI handoff also passed.

The diagnostic ends at `qotom-platform-pending`. This is a bounded SMI-disable
observation, not continuing firmware exclusion, controller halt, transaction
drain, DMA quarantine or platform admission. No xHCI operational write or BME
clear was performed. Writing zero does not acknowledge W1C event status.

FreeBSD recovered after 34.30911562999245 seconds of serial quiet; boot time
changed from 1789162720 to 1789163919. The request was consumed. Independent
SSH verified installed image/configuration and request=none, then removed the
read-only mount. Serial was FTDI/null modem COM1 at 38400 baud, 8N1.

ELF SHA256:
`310520a9aec783f084fdd48253f8ba293b3a06968d443375806b10387ad70f94`.
Build and runner revision: 0d3cca0caabc907df26dcd4c8f55574a0e761576; sources were
clean. All 85 manifest hashes, the unchanged eight-site MSR-write audit and
QEMU foreign-firmware rejection passed before installation. USB serial 11758C40,
guarded old/new hashes, backup and filesystem checks passed.
