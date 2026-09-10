# PCI header observation boundary

`LeanOS.PCIHeaderObservation` decodes a supplied PCI configuration header and
retains the original BDF and all sixteen raw dwords. It supports conventional
endpoint and PCI-to-PCI bridge layouts, including the multifunction bit. The
register offsets follow the [Linux PCI register definitions](https://github.com/torvalds/linux/blob/master/include/uapi/linux/pci_regs.h).

This boundary supplies observations for the Qotom work in issue #330. It does
not read or write configuration space, enumerate buses, establish an atomic
snapshot, interpret window safety, quiesce a device, or admit a platform. The
kernel does not call this export yet. A later adapter must bind the PCI segment
and complete inventory, use the same immutable input for every field query,
and establish the device strategy before granting runtime authority.

## Scalar interface

The generated prototype for `leanos_pci_header_observe` takes 21 unsigned
64-bit arguments: field selector, declared dword count, bus, device, function,
and sixteen dwords. The declared count must be 16, BDF components must fit their
PCI widths, and each supplied dword must fit 32 bits. The full header type is
retained in the raw input; unsupported layouts are rejected rather than
interpreted as endpoints.

Always query field zero first. A value of 1 means decoding succeeded. Data
fields can legitimately contain values that overlap error codes, so a data
word cannot substitute for that status check.

| Field | Observation |
| --- | --- |
| 0 | Decode success tag, 1 |
| 1–3 | Vendor, device, 24-bit class code |
| 4–5 | PCI command and status |
| 6–8 | Revision, multifunction flag, layout (0 endpoint, 1 bridge) |
| 9–12 | Primary, secondary, subordinate bus and bridge control |
| 13–14 | Raw I/O base/limit pair and secondary status |
| 15–16 | Raw memory and prefetchable memory base/limit pairs |
| 17–19 | Prefetchable upper base, upper limit, and I/O upper base/limit pair |

Endpoint fields 9–19 are zero. Bridge windows are retained as raw register
pairs; no enabled range, overlap check, or forwarding guarantee is inferred.

Errors are `0x100` for an invalid BDF, `0x101` for the wrong dword count,
`0x102` for a value wider than a dword, `0x103` for the absent-function vendor
value, and `0x104` for an unsupported layout. A field selector outside 0–19
returns `0x105` before inspecting the supplied observation. For an in-range
selector, address and count checks precede dword and layout checks.

## Verification

The general proofs establish retention of the input, transport bounds, the
20-word output width, and the success tag. The capture replay validates the
retained Qotom listing and raw-file hashes before checking the 15 decoded
headers. Synthetic window values distinguish every field offset; malformed
cases exercise bounds and unsupported input.

The scalar corpus contains 26 cases checked in Lean and in generated C, with
20 observation fields and two invalid selectors per case. The hosted runner
uses the generated prototype, records export execution coverage, and supports
the repository's ordinary and pinned ASan/UBSan modes:

```sh
./scripts/check-pci-header-host.sh ordinary
./scripts/check-pci-header-host.sh sanitized
```

These are hosted decoder checks. They do not establish an allocation-free
freestanding implementation or a physical DMA quarantine result.
