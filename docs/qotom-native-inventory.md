# Native Qotom PCI inventory candidate

`LeanOS.QotomNativePCIInventory` binds the sixteen-function ECAM capture to a
separate witness type. Its baseline inserts the single-function EHCI endpoint
00:1d.0 (8086:0f34, class0c0320) into the historical AHCI inventory, preserving
canonical BDF order. The other fifteen identity, multifunction and bridge
routing/control projections match exactly. The historical fifteen-function
checker and all its consumers remain unchanged.

Successful checking retains every original header and proves exactly sixteen
functions with the complete baseline projection. Command/status, BARs and
forwarding windows remain observations for subsequent device policy; matching
this inventory does not prove quiescence, containment or permission for CPL3.
This is a model candidate, not yet an exported generated-C boundary or a
selected runtime profile.

The hash-bound native fixture passes model checking with exact raw-header
preservation. Forty-one negative examples cover missing/additional entries,
ordering, every identity/BDF, EHCI multifunction changes, bridge control changes,
and rejection of the native set by the historical checker. The model's general
raw-preservation and exact-count proofs also compile.

Build the module with `lake build LeanOS.QotomNativePCIInventory`, then run
`lake env python3 scripts/test-qotom-native-inventory.py`. Generated-C parity,
ABI integration, final native diagnostic selection and a fresh physical capture
remain required before treating this as the runtime inventory contract. The
host/LPC read-only Command exceptions and TXE/USB DMA ownership obligations
remain unresolved; increasing the inventory count does not resolve them.
