# Bounded Qotom BSP consumer

`include/qotom_bsp_consumer.h` supplies the allocation-free C caller for the
proved scalar MADT entry stream and BSP finish exports. It consumes a borrowed
entry span after the fixed 44-byte MADT header, bounded by the existing 65,536
byte SDT limit. Null pointers, empty input and oversized spans fail before any
read. The executing-CPU observation is copied once at entry.

For each actual byte, all sixteen projections read one unchanged old-state
snapshot. Only after checking ABI, status, error, next offset and byte echo
does the consumer replace its twelve state words. The final BSP call receives
the actual terminal status/error and carried words. Rejection exposes no
accepted APIC ID, processor count or APIC-base value. The wrapper does not
invent a successful terminal state from the expected four-CPU inventory.

The caller must first select and copy the authoritative MADT, validate its
complete envelope with the existing generated validator, and keep the copy
immutable through this call. The entry span alone cannot establish those
facts. Likewise, the observation must come from safe reads on the executing
CPU; accepting supplied register values cannot establish their provenance.
These are the preconditions of the existing stream/finish proofs, not new
exceptions to platform admission.

The hosted scalar runner executes this same consumer across every existing
entry-mutation and compatible BSP-observation pair and compares its result
with the independent scalar projections. Wrong inventories, malformed entries,
unavailable reads, width errors and differing BSP state remain rejections.
The ordinary and pinned ASan/UBSan runs instrument both consumer and generated
code. A separate freestanding link probe retains the real consumer and both
exports, rejecting unresolved dependencies, unexpected symbols and writable
state. GCC may outline the private consumer; that one named helper is allowed.

The explicit production candidate now selects this component from
`boot_allocate` while retaining root/copy/envelope validation and fresh
same-CPU observations. The [production-boundary contract](qotom-bsp-production-boundary.md)
defines its final gate, linked-image audit and firmware/AP assumptions. The
ordinary q35 build remains on its existing singleton consumer. Malformed native
NMI routing, DMA containment, no-SMAP isolation and whole-platform admission
remain separate prerequisites under #331 and #291.
