# Reject detected PCI selector interference

The lab CF8 trace must report a failed configuration read when its post-read
selector differs from the requested address. The previous adapter counted and
printed that mismatch but returned success, allowing the enumerator to interpret
the suspect dword as an identity or header value. In particular, a suspect
seventeenth identity could produce a misleading capacity-exceeded result.

The adapter now retains the requested selector, observed selector and raw dword
in the existing trace, then returns failure immediately. The existing enumerator
reports `PCI_ENUMERATION_READ_FAILED` at that BDF/offset and leaves snapshot
count zero. It neither retries nor substitutes a value, and no partially read
snapshot is published. The serial trace format is unchanged.

This change is confined to the explicit lab read-trace adapter. The existing
mechanism-1 assembly reader and production q35 consumer are unchanged. A matching
post-read selector still cannot prove exclusion of SMM, NMI or another CPU,
nor detect a selector that changed and was restored during the transaction.
A reliable admitted access path and PCI/DMA policy remain outstanding in #330.

`tests/qotom-pci-read-trace.c` compiles the actual adapter with controlled I/O
responses and runs it through the real segment enumerator. It covers a complete
sixteen-function scan, interference on an apparent seventeenth identity,
interference inside a present function's header, raw trace retention, immediate
termination without retry, and invalid arguments without I/O. The ordinary and
pinned ASan/UBSan modes of `scripts/check-pci-enumeration.sh` run the regression.
Removing the new failure return reproduces the capacity-status assertion failure.

These are hosted regression results. Historical physical captures retain their
original status; no new physical outcome or removal of interference is claimed.
