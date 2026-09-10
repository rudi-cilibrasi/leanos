# Qotom PCI inventory candidate

`LeanOS.QotomPCIInventory` compares a bounded, ordered list of decoded PCI
headers with the complete 15-function inventory captured on 2026-09-10 in
`hardware/lab/observations/qotom-pci-20260910/`. This candidate names the AHCI
controller 8086:0f23/class 010601. It does not accept the older IDE observation
8086:0f21/class 01018a or select a production boot profile.

The comparison binds each function's BDF, vendor/device/class identity,
multifunction bit, and endpoint/bridge layout. For each of the four bridges,
it also binds primary, secondary, subordinate, and bridge-control registers.
Every function must occur once in the captured canonical order. Missing or
extra functions fail the count check; relocation, duplication, reordering,
identity, multifunction, routing, and malformed-header failures carry typed
errors, with an index where applicable.

A successful witness retains the complete decoded headers and their original
16 dwords. Its proof binds the entire projected inventory to one baseline;
another theorem establishes its 15-function length. The general
`check_preserves_raw` theorem proves that any successful check returns exactly
the supplied raw headers in their original order, including every command and
window register. Command/status, revision,
BARs, and forwarding-window contents are observations for later policy. They
are not frozen to values supplied by a running FreeBSD instance.

This module assumes the caller supplies a complete enumeration. It does not
prove enumeration completeness, stop DMA, validate forwarding windows, check
command readback, select an IOMMU strategy, permit CPL3, or access hardware.
The kernel does not yet call it. Its success must not substitute for the
quarantine boundary required by issue #330.

Run `lake build LeanOS.QotomPCIInventory`, then
`python3 scripts/test-qotom-pci-inventory.py`. The replay first validates the
retained capture's raw digests and selector inventory through the existing
header replay. It checks the complete capture, every function's identity and
address mutations, bridge routing/control mutations, malformed headers,
missing/extra/reordered functions, and IDE/q35 mixtures. A positive mutation
also confirms that command/window values remain available to later checks.
Generated-C parity and production integration remain pending.
