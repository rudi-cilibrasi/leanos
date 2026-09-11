# Native Qotom xHCI capability capture

A protected Win7 Legacy boot completed the preceding EHCI BME experiment and
sampled seven xHCI capability DWORDs through the restricted read mapping.
Both PCI binding refreshes passed. Status 0 retained, in offset order:
`0x01000080`, `0x07000820`, `0x84000054`, `0x0200000a`, `0x200077c1`,
`0x00003000`, `0x00002000`.

These are physical values; the earlier synthetic tests used datasheet defaults
for some parameter fields. No xHCI ownership, operational, port or BME write
was requested. No pointers were followed. The observations do not establish
xHCI ownership, continuing firmware exclusion or system-wide DMA containment.

Protected replay passed and FreeBSD recovered automatically after
34.2981203100062 seconds of serial quiet. Boot time changed from 1789156060 to
1789157198; the request was consumed. Independent read-only SSH verified the
installed ELF/configuration and request=none; the mount was removed. Serial was
FTDI/null modem COM1, 38400 baud, 8N1, no flow control.

ELF SHA256:
`aeab1521c05f702627c0aff177d707e3e2cad94891e17a731fcf392f7a25c911`.
Build provenance is cfac296 with dirty integration sources; runner was 4fcfb89.
The guarded installer checked USB serial 11758C40, previous/staged hashes,
backup, filesystem and installed hashes. FINAL remains qotom-platform-pending.
