# Generation-bound capability handles

LeanOS capability handles pair a subject-local bounded slot with the
never-reused identity of the capability currently installed there. The kernel
selects the subject from trusted execution context; neither handle word can
select another subject's capability space. Handle secrecy is not assumed.

`LeanOS.CapabilityHandle.resolve` is the canonical holder-facing resolver. It
checks the trusted subject, slot bound, installed identity, requested object
kind, and live object registry before returning authority. Empty slots,
replaced generations, retired objects, wrong kinds, and invalid subjects fail
with typed results. Resolution is read-only, so every denial preserves the
complete capability state.

Holder-facing capability copy/revoke and endpoint send/receive/destroy paths
use generation-checked wrappers before entering their internal raw-slot state
transitions. Blocking IPC exposes the same checked boundaries. Raw slot lookup
is reserved for internal cleanup, invariant proofs, and compatibility inside
the model; it is not a holder authority boundary.

The model uses the append-only natural-number identity already maintained by
the capability derivation graph. It therefore has no finite wraparound inside
one modeled boot lifetime. A future fixed-width userspace encoding must add an
explicit exhaustion check and fail closed before reuse; persistence across a
reboot is outside this model.

The Lean theorems prove that successful resolution returns exactly the live
capability in the trusted subject's slot, that clearing or replacing a slot
denies the old handle, that direct or transitive subtree revocation denies a
descendant's old handle, that installing authority for another subject cannot
change resolution, and that simultaneously live issued handles cannot alias
different slots. Executable examples cover fresh use, equal words under a
different trusted subject, clear, and same-slot replacement. A negative
regression also demonstrates that the former raw-slot lookup accepts the
replacement while the generation-aware resolver rejects the stale handle.

These are model-level results. They do not establish a stable syscall bit
encoding, concurrent lookup/revocation safety, generated-code refinement, or
QEMU behavior. Capability-transfer installation and boot-reachable syscall
migration remain separate follow-up boundaries.
