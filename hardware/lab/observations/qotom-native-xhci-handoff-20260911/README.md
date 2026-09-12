# Native xHCI handoff accepted — 2026-09-11

The protected Win7 Legacy boot requested xHCI ownership once and observed
BIOS-clear/OS-owned support `0x01000801` at poll two. Complete final resource,
capability-list and semaphore verification passed: status 0, control `0x2000`,
and all verification detail fields zero. The corrected comparison permits
only documented live command-manager status at the identified vendor header.
The preceding rejected v1/v2 captures remain separate historical evidence.

The terminal is `qotom-platform-pending`. This establishes the bounded ownership
observation, not continuing firmware exclusion, xHCI shutdown, DMA drain,
quarantine or platform admission. No xHCI control/status or operational write
followed the ownership request. Earlier EHCI steps still passed, including the
stopped-state observation and Command `0x0406` to `0x0402` BME clear.

FreeBSD recovered after 34.32092714399914 seconds of serial quiet. Boot time
changed from 1789161776 to 1789162720; the request was consumed. Independent
SSH verified the installed ELF/configuration and request=none, then removed
the read-only mount. FTDI/null modem COM1 was configured at 38400 baud, 8N1.

ELF SHA256:
`823ae01d773058aec8ea12af0029e3632470be96051e98cdf462097005e0bdb3`.
Build and runner revision: dbeb9fcd4b6bc9fc6166222b67e505e5dfe182dc; build sources
were clean. All 81 build-manifest hashes, the unchanged eight-site MSR-write
audit and QEMU foreign-firmware rejection passed before installation.
USB serial 11758C40, guarded old/new hashes, backup and filesystem checks passed.
