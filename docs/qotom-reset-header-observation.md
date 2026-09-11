# Qotom reset-related capability observations

The [machine-readable audit](../hardware/lab/qotom-reset-header-observation.json)
decodes the retained native capture. Regenerate it with
`python3 scripts/audit-qotom-reset-observation.py`; its input hash is checked
against the capture manifest. This is offline interpretation, not a reset
experiment or a DMA admission decision.

EHCI `00:1d.0` (`8086:0f34`) has an Advanced Features header at `0x98`, raw
`0x03060013`: length 6, Transactions Pending support and Function Level Reset
support advertised. The control byte at `0x9c` and status byte at `0x9d` were
not captured. Support does not mean the pending bit is clear.

PCIe headers occur on the four root ports and three downstream endpoints.
Their header dwords do not contain Device Capabilities, so PCIe FLR support is
unknown from this capture. AHCI's captured list ends at its SATA capability;
it does not advertise an Advanced Features entry in that list.

The bit definitions and reset sequence are cross-checked against Linux's
[PCI register definitions](https://github.com/torvalds/linux/blob/master/include/uapi/linux/pci_regs.h)
and [pci_af_flr implementation](https://github.com/torvalds/linux/blob/master/drivers/pci/pci.c).
Linux checks both support bits, polls pending status, requests reset, then waits
for readiness. Its timeout path may proceed with reset anyway; that behavior
cannot establish a successful drain for LeanOS.

The next bounded EHCI experiment needs fresh identity/list validation,
control/status observation, USB legacy ownership exclusion, an explicit
stop-and-drain contract, and recovery validation. A pending-status timeout must
remain a failed quarantine result. USB recovery and firmware ownership must be
accounted for before any controller reset is attempted. The present audit
performs no hardware access and leaves issue #330 open.

## Bounded AF observer

`boot/pci-af-observation.h` provides a read-only observer for a previously
collected list and its immutable PCI header. It refreshes the identity/list,
requires exact agreement, selects a unique AF structure, and requires the
standard six-byte shape with both TP and FLR bits and no reserved capability
bits. It rejects a following capability header overlapping control/status.
The payload read stays within conventional configuration space. At most 53
configuration reads occur; no allocation or write callback is available.

A successful result retains the raw control/status dword and AF offset.
Neither pending-bit value is classified as quarantine success. The upper two
bytes are retained without interpretation. Every rejection returns zero for
the published offset and payload. Refreshing the list does not make hardware
reads atomic; serialized access, immutable inputs, and nonaliasing remain
caller obligations.

The ordinary and sanitizer tests cover all 65,536 header length/support bit
combinations, all payload-safe aligned offsets, the unsafe final slot,
collection/payload failures, all-ones payload, list drift, overlap, duplicate
AF entries, absent AF and invalid bounds. The builder's `--af-observation` option requires `--pci-capabilities` and
uses `build/qotom-af-lab`. It retains the complete lists in bounded private
storage and emits AF results only after the complete capability capture.
The runner's matching flag fingerprints the decoder and retains
`af-observation.json`. It validates framing and advertised structure against
preceding capability records; failed refresh/read outcomes remain reported
observations, not independently replayed hardware results. Synthetic protected
capture tests cover success, missing/malformed records, and a failed refresh.
A physical AF control/status capture remains outstanding.
