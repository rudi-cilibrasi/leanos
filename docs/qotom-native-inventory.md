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
The exported candidate checks a declared count of sixteen and an array of
304 words before reading any header. It consumes the array through the generated
C ABI. It is not a selected runtime profile or a freestanding transport.

The hash-bound native fixture passes model checking with exact raw-header
preservation. Forty-one negative examples cover missing/additional entries,
ordering, every identity/BDF, EHCI multifunction changes, bridge control changes,
and rejection of the native set by the historical checker. The model's general
raw-preservation and exact-count proofs also compile.

Build the module with `lake build LeanOS.QotomNativePCIInventory`, then run
`lake env python3 scripts/test-qotom-native-inventory.py`. Final native diagnostic selection and a fresh physical capture
remain required before treating this as the runtime inventory contract. The
host/LPC read-only Command exceptions and TXE/USB DMA ownership obligations
remain unresolved; increasing the inventory count does not resolve them.

The hosted boundary harness is registered as `qotom-native-inventory`, with
ordinary and sanitizer modes provided by `scripts/check-qotom-native-inventory-host.sh`.
The generated export has a distinct name and the harness exercises both the
native entry point and historical rejection. Thirty-six array-interface cases
compare model results with generated C, including count/size boundaries and
identity/address changes at all sixteen positions. Ordinary and pinned ASan/UBSan runs pass with identical output and both
exports covered. The CLI also replays the retained capture successfully and
rejects malformed decimal transport and non-dword values at every header
position. The 77-export vocabulary, harness registration and current invariant
index checks pass.

Capture replay selects this model explicitly with `--native-inventory` and the
native replay executable. The protected runner additionally requires
`--ecam-read`; it records the selected profile and decoder hash, and retains all
existing firmware and recovery checks. The default historical replay still
rejects a sixteen-function success. A historical executable cannot be passed
as the native model. The CLI accepts `--pci-replay
build/qotom-native-inventory-host/host` together with the selection flag.

Tests replay the retained physical bytes successfully through the native model
(result1), preserve historical count rejection (65536), reject cross-profile
executable/flag combinations, and retain indexed rejection at function15.
The complete protected replay also passes. This is a new offline interpretation
of the retained capture, not another boot or kernel-side inventory admission.
The generated-C array transport still allocates Lean objects; a freestanding
bridge and complete device/DMA policy remain necessary for runtime selection.
