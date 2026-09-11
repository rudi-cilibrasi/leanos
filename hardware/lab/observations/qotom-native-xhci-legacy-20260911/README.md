# Native Qotom xHCI extended-capability capture

A protected Win7 Legacy boot completed the preceding EHCI BME experiment and
read six xHCI extended-capability headers. The bounded walk began at xECP offset
`0x8000`, followed relative DWORD links, and terminated at `0x8480`:

| Offset | Raw header |
| --- | --- |
| `0x8000` | `0x02000802` |
| `0x8020` | `0x03000802` |
| `0x8040` | `0x00010cc1` |
| `0x8070` | `0x0000fcc0` |
| `0x8460` | `0x00010801` |
| `0x8480` | `0x0005000a` |

The selected legacy structure is at `0x8460`; its control/status sample at
`0x8464` is `0x00002001`. BIOS-owned is set and OS-owned is clear in the support
header. Both complete PCI/capability refreshes passed. These sequential samples
do not establish ownership or continuing firmware exclusion. No xHCI writes,
operational access, or port access occurred. DMA quarantine remains unproved.

Protected replay passed and FreeBSD recovered automatically after
34.30660743601038 seconds of serial quiet. Boot time changed from 1789157198 to
1789159496, and the request was consumed. Independent read-only SSH inspection
confirmed the installed image/configuration and request=none; the mount was
removed. Serial was FTDI/null modem COM1, 38400 baud, 8N1, no flow control.

ELF SHA256:
`1733a83f4df5c538e568f8398884efe7df3c196b44f3f0bedcc6abef5aab6445`.
Build provenance is bc45646 with dirty integration sources; runner was ba753d8.
The guarded installer checked USB serial 11758C40, previous/staged hashes,
backup, filesystem and installed hashes. FINAL remains qotom-platform-pending.
