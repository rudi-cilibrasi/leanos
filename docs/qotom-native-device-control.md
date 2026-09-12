# Native Qotom device-control audit

The initial physical native-inventory capture has BME set on fifteen functions. The
host router and LPC account for two; thirteen other functions have BME set in
that initial snapshot. SMBus is the only function with that bit clear. This is register-state
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

Consequently, the production policy must account for the internal TXE engine and
outstanding downstream transactions explicitly. A host Command write/readback
trace alone does not supply those missing contracts. The thirteen initially BME-set
functions need controller-specific ownership, stopping and drain evidence;
this audit authorizes no write and creates no free-form device exemption.
The physical path remains at `qotom-platform-pending` for #330 and #291.

## Verified transitions and remaining contracts

The table above and generated JSON deliberately preserve the initial inventory.
The later [Realtek boot capture](../hardware/lab/observations/qotom-native-realtek-bme-20260911)
contains all ten successful BME transitions in one serial stream. Its manifest
and protected replay were verified; the transition starting values match the
initial headers from that same boot. These are sequential transition
observations rather than an atomic final inventory or proof of continuing
state.

| Function | BDF | Initial Command | Verified BME readback | Evidence stage |
| --- | --- | --- | --- | --- |
| EHCI | 00:1d.0 | 0406 | 0402 | Ownership, SMI, stopped-state and BME |
| xHCI | 00:14.0 | 0006 | 0002 | Ownership, SMI, stopped-state and BME |
| SATA | 00:13.0 | 0007 | 0003 | Stopped/empty port, interrupt disable and BME |
| HDA | 00:1b.0 | 0006 | 0002 | Ring/stream state and BME |
| Four root ports | 00:1c.0–3 | 0007 | 0003 | Routing/PCIe refresh and upstream request gating |
| Two Realtek endpoints | 01:00.0, 03:00.0 | 0007 | 0003 | Routed stopped engine state and BME |
| Broadcom endpoint | 02:00.0 | 0006 | 0000, then PMCSR D3hot | Routed Command disable, delayed non-posted quiet and D3hot readback |

Two initially BME-set functions, in addition to the two fixed-Command
functions, still have no successful disable transition in this sequence:

| Functions | Missing device contract |
| --- | --- |
| Graphics 00:02.0 | Display/engine ownership, stopping, DMA gating and drain |
| TXE 00:1a.0 | Internal DMA control, firmware behavior and drain |

The [graphics-ring observation stage](qotom-graphics-state.md) now supplies a
bounded read-only snapshot of the RCS, VCS and BCS ring registers while keeping
the firmware display decode and graphics BME intact. It is evidence for choosing
the [bounded graphics BME candidate](qotom-graphics-bme.md), which refreshes the
same quiet state and clears only BME while preserving memory and I/O decode.
Until that candidate is physically validated, the table above remains the
authoritative successful-transition list. Even a successful Command readback
would not supply graphics ownership, posted-write drain or continuing firmware
exclusion.

Root-port BME readbacks establish the bounded upstream request-gating changes;
outstanding traffic and continuing routing/state still require their contracts.

The subsequent [PCIe non-posted quiet stage](qotom-pcie-pending.md) samples
Transactions Pending twice, 10 ms apart, on the four root ports and two Realtek
endpoints after those BME transitions. All six reached clear status in the
protected physical path and in independent replay. The
[Broadcom D3hot stage](qotom-broadcom-d3.md) separately disables all three
Command decode bits, obtains two delayed clear samples on `02:00.0`, and enters
D3hot. It does not establish internal engine shutdown, posted-write completion
or continuing firmware/AP exclusion.

TXE firmware status `1f0000d5`/`69000000` was read successfully in that boot;
it is not a shutdown witness. The seven PCIe functions do not advertise FLR
in the retained capability observation, so a generic FLR sequence is not an
available advertised mechanism. Clear Transactions Pending samples alone do
not establish device/fabric drain. The fixed host router and LPC still require
the distinct contracts above; SMBus's initially clear BME also needs its
capability/continuing-state contract.

The ten successful transitions do not discharge transaction drain or continuing
firmware/AP exclusion. All sixteen functions must be covered by the final
profile, including fixed-register and non-DMA cases with explicit justification.
No subset of these observations is a production admission witness; the native
terminal remains `qotom-platform-pending`.
