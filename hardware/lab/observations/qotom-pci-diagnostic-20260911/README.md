# Physical Qotom PCI diagnostic capture

On 2026-09-11 UTC, Qotom booted the protected PCI diagnostic from USB in
Win7 Legacy BIOS mode. The reader completed its full PCI segment scan and
reported 16 functions. Generated CPU selection returned 65536 (accepted)
and control-register/MSR readback returned 1. PCI inventory replay returned
65536 (count rejection against the existing fifteen-function profile).
The final record is `FAIL reason=qotom-platform-pending`; platform admission
and CPL3 execution remain false.

The lab overlay reset after its terminal wait. The recorder measured
34.316 seconds from FINAL to the first subsequent serial byte. GRUB consumed
the request and chained the internal FreeBSD disk; SSH returned with a new
boot time, and the USB environment was verified as `request=none`.
The GRUB `hd0,gpt2` diagnostic precedes successful identification of `hd1`;
it did not prevent recovery.

This is completed-run recovery with watchdog protection. No deliberate hang
was injected in this trial. The runner's historical `hang_recovery=true`
field labels the protected scenario; it is not proof of a triggered watchdog.
No quarantine writes, DMA containment, production admission, or visible
monitor output are established by this capture.

The lab ELF was built from clean revision
`37e945d2ea41fbe91bf898c4d4adef5a3a3a5875`, using prepared generated inputs
from `4d54cc91b4bab758c2c990ff6c7f33e853880e55`. See build-manifest.json and
diagnostic-replay-inputs.json for provenance and executable hashes.
Serial connection: mgnuc FTDI FT232R BG03A20M, null modem, Qotom COM1,
38400 baud, 8N1, no flow control. USB serial: 11758C40.

## Observed inventory

| BDF | Vendor:device | Class | Command |
| --- | --- | --- | --- |
| 00:00.0 | 8086:0f00 | 060000 | 0007 |
| 00:02.0 | 8086:0f31 | 030000 | 0007 |
| 00:13.0 | 8086:0f23 | 010601 | 0007 |
| 00:14.0 | 8086:0f35 | 0c0330 | 0006 |
| 00:1a.0 | 8086:0f18 | 108000 | 0106 |
| 00:1b.0 | 8086:0f04 | 040300 | 0006 |
| 00:1c.0 | 8086:0f48 | 060400 | 0007 |
| 00:1c.1 | 8086:0f4a | 060400 | 0007 |
| 00:1c.2 | 8086:0f4c | 060400 | 0007 |
| 00:1c.3 | 8086:0f4e | 060400 | 0007 |
| 00:1d.0 | 8086:0f34 | 0c0320 | 0406 |
| 00:1f.0 | 8086:0f1c | 060100 | 0007 |
| 00:1f.3 | 8086:0f12 | 0c0500 | 0003 |
| 01:00.0 | 10ec:8168 | 020000 | 0007 |
| 02:00.0 | 14e4:4353 | 028000 | 0006 |
| 03:00.0 | 10ec:8168 | 020000 | 0007 |
