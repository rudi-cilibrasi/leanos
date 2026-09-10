# Binding the initial PCI inventory to command readbacks

`QotomPCIQuarantineTransition` composes the complete Qotom AHCI inventory
checker with the ordered command/readback observation checker. It validates
both inputs before comparing configuration registers by function address.
Every raw dword except dword one must be identical before and after the
recorded command write. Dword one contains Command, whose readback must be
zero under the trace checker, and Status, which may change asynchronously.

The accepted witness preserves both original inputs exactly. It contains
fifteen initial headers and fifteen ordered steps; every step is bound to a
matching initial header. Initial inventory failures, trace failures, and
register drift have distinct errors, with drift retaining the trace index.
The checker does not freeze arbitrary BAR or window values to the retained
capture: equal values in both supplied observations can pass. It establishes
consistency, not that those register values are safe.

The hosted export `leanos_qotom_pci_quarantine_transition` consumes one Lean
array and a declared common count. Count must be fifteen and size exactly 660
before fields are read. The array starts with fifteen initial headers of
nineteen words (BDF plus sixteen dwords), followed by fifteen trace records of
twenty-five words as documented in `qotom-quarantine-observation.md`.
Success is 1; bad count and size return 0x10000 and 0x10001. Initial errors add
0x100000 to the inventory checker error, trace errors add 0x200000 to the
trace checker error, and register drift returns 0x300000 plus the trace index.
This boundary allocates hosted Lean objects; it is not a freestanding adapter.

Tests validate retained capture hashes, construct synthetic Command-cleared
readbacks, and check the whole inputs in Lean and generated C. They reject
initial identity changes, malformed fields, failed writes/readbacks, and
register drift in either input. They also cover volatile Status changes and
matching arbitrary register changes in both inputs. No physical PCI writes,
quiescence, or containment are established by these tests.

Issue #330 still requires authoritative enumeration and access ordering,
reviewed device and bridge assumptions, treatment of outstanding transactions,
serial/recovery policy, whole-platform runtime dispatch, and physical evidence.
The current checker cannot authenticate the provenance or timing of supplied
observations, or prove that devices remained unchanged after their readbacks.
