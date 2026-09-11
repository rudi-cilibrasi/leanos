# Native Qotom device-control audit

The physical native-inventory capture has BME set on fifteen functions. The
host router and LPC account for two; thirteen other functions still have BME
set. SMBus is the only function with that bit clear. This is register-state
evidence, not evidence of active DMA or quiescence. The
[machine-readable audit](../hardware/lab/qotom-native-device-control.json) retains
all Command/Status values and raw BAR dwords, using only two BAR slots for type-1
bridges. Regenerate it with `python3 scripts/audit-qotom-native-device-control.py`;
the script verifies the source capture hash before reading its headers.

| BDF | Vendor:device | Class | Command | BME |
| --- | --- | --- | --- | --- |
| 00:00.0 | 8086:0f00 | 060000 | 0007 | set |
| 00:02.0 | 8086:0f31 | 030000 | 0007 | set |
| 00:13.0 | 8086:0f23 | 010601 | 0007 | set |
| 00:14.0 | 8086:0f35 | 0c0330 | 0006 | set |
| 00:1a.0 | 8086:0f18 | 108000 | 0106 | set |
| 00:1b.0 | 8086:0f04 | 040300 | 0006 | set |
| 00:1c.0 | 8086:0f48 | 060400 | 0007 | set |
| 00:1c.1 | 8086:0f4a | 060400 | 0007 | set |
| 00:1c.2 | 8086:0f4c | 060400 | 0007 | set |
| 00:1c.3 | 8086:0f4e | 060400 | 0007 | set |
| 00:1d.0 | 8086:0f34 | 0c0320 | 0406 | set |
| 00:1f.0 | 8086:0f1c | 060100 | 0007 | set |
| 00:1f.3 | 8086:0f12 | 0c0500 | 0003 | clear |
| 01:00.0 | 10ec:8168 | 020000 | 0007 | set |
| 02:00.0 | 14e4:4353 | 028000 | 0006 | set |
| 03:00.0 | 10ec:8168 | 020000 | 0007 | set |

The [existing fixed-Command audit](qotom-lpc-command-constraint.md) prevents an
all-zero policy for the host router and LPC. Do not classify the thirteen other
functions as safely disableable merely because their BME bit is set.

Intel datasheet 329670-002, section 16.1.1, printed page 697, describes a TXE DMA
engine accessing system memory and programmed only by the TXE CPU. That section
does not establish that the host-visible PCI BME bit controls this engine.
Section 17.6.2, printed page 708, says root-port BME gates upstream memory/I/O
requests, but does not gate completions or other request classes.
[Primary source: Intel-authored datasheet](https://cdn.centralpoint.be/objects/pdf/9/96e/1597181_1_processoren-intel-celeron-processor-g1620t-2m-cache-240-ghz-cm8063701448300.pdf).
The inspected PDF hash is
`048182ec5a9faece8c78c0f087420065ff1a17ba1107785164e1f467608c6b39`.

Consequently, the next policy must account for the internal TXE engine and
outstanding downstream transactions explicitly. A host Command write/readback
trace alone does not supply those missing contracts. The thirteen other BME-set
functions also need controller-specific ownership, stopping and drain evidence;
this audit authorizes no write and creates no free-form device exemption.
The physical path remains at `qotom-platform-pending` for #330 and #291.
