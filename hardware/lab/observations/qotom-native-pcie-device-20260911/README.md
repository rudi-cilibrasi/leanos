# Native PCIe Device register observation — 2026-09-11

The protected Win7 Legacy boot completed the preceding EHCI/xHCI observations,
then captured Device Capabilities and combined Device Control/Status for all
seven PCIe functions. Complete identity/list refreshes passed before and after
each payload. The other nine functions returned NOT_PRESENT with zero payload.

| BDF | Offset | Device Capabilities | Device Control/Status |
| --- | --- | --- | --- |
| 00:1c.0 | 40 | 00008000 | 00110000 |
| 00:1c.1 | 40 | 00008000 | 00110000 |
| 00:1c.2 | 40 | 00008000 | 00110000 |
| 00:1c.3 | 40 | 00008000 | 00100000 |
| 01:00.0 | 70 | 05908cc0 | 00192000 |
| 02:00.0 | d0 | 05908fa0 | 00190000 |
| 03:00.0 | 70 | 05908cc0 | 00192000 |

All numbers in the table are hexadecimal. None advertises PCIe Function Level
Reset (Device Capabilities bit28). Transactions Pending (combined dword bit21)
is clear in every sample. This does not establish transaction drain, continuing
firmware/AP exclusion or system-wide DMA quarantine. Device-specific shutdown
and remaining platform integration are still needed. No PCIe configuration write
or reset was performed. The diagnostic remains `qotom-platform-pending`.

FreeBSD recovered after 34.29963818998658 seconds of serial quiet, boot time
1789167041 to 1789168301, with the request consumed. Independent SSH verified
installed image/configuration hashes and request=none, then removed the read-only
mount. Serial was FTDI/null modem COM1 at 38400 baud, 8N1.

ELF SHA256:
`f26096ec00ab2a04b6d8fc5f204c15d78bc06ef52eed8bbfd4816dcdfb4f7c92`.
Build and runner revision: 387f2fb562d9d1f80d75673b23553a9a85d8b210; sources were
clean at build. All 95 manifest hashes, the unchanged eight-site MSR-write audit
and QEMU foreign-firmware rejection passed. Guarded USB serial 11758C40, backup,
old/new hashes and filesystem checks passed before the protected boot.
