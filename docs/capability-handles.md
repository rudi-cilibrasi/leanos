# Generation-bound capability handles

LeanOS capability handles pair a subject-local bounded slot with the
never-reused identity of the capability currently installed there. The kernel
selects the subject from trusted execution context; the handle word cannot
select another subject's capability space. Handle secrecy is not assumed.

The canonical userspace word is a `UInt64` with the slot in bits 0–15 and the
generation in bits 16–63. Slot `0xffff`, generation zero, and generation
`0xffffffffffff` are reserved and rejected. Thus usable slots are
`0x0000..0xfffe`, usable generations are `1..0xfffffffffffe`, and the exact
encoding is `slot + generation * 65536`. Capability allocation must fail
closed before the reserved maximum generation; wrapping, truncating, and
generation reuse are not allowed. Reboot persistence remains outside the
model.

`LeanOS.CapabilityHandle.resolve` is the canonical typed holder-facing
resolver. `encode` and `decode` implement the fixed-width boundary, and
`resolveCurrent` composes decoding with a `TrustedCaller` selected by entry or
scheduler context. These operations check the trusted subject, slot bound,
installed identity, requested object kind, and live object registry before
returning authority. Empty slots,
replaced generations, retired objects, wrong kinds, and invalid subjects fail
with typed results. Resolution is read-only, so every denial preserves the
complete capability state.

Holder-facing capability copy/revoke, endpoint send/receive/destroy, blocking
IPC, and sealed capability-transfer paths use generation-checked wrappers
before entering their internal raw-slot state transitions. Transfer offer
decodes both the endpoint and source words in the trusted sender's capability
space; receipt decodes the endpoint word while treating the destination as an
empty bounded output slot. Memory retirement and endpoint destruction use the
same `resolveCurrent` boundary. Raw slot lookup is reserved for internal
cleanup, invariant proofs, and compatibility inside the model; it is not a
holder authority boundary.

The capability graph still records identities as natural numbers internally.
Only identities in the finite canonical range can be issued as userspace
words. The codec therefore exposes exhaustion rather than silently reducing a
natural-number identity modulo 48 bits.

The Lean theorems prove codec round-trip and canonical uniqueness for every
encodable handle, and prove that successful current-caller resolution returns
exactly the live capability in the trusted caller's capability space. They
also prove that clearing or replacing a slot
denies the old handle, that direct or transitive subtree revocation denies a
descendant's old handle, that installing authority for another subject cannot
change resolution, and that simultaneously live issued handles cannot alias
different slots. Executable examples cover fresh use, reserved slot and
generation fields, out-of-domain encode rejection, equal words under a
different trusted caller, changed generation bits, clear, and same-slot
replacement. A negative regression also demonstrates that the former raw-slot
lookup accepts the replacement while the generation-aware resolver rejects the
stale handle.

These are model-level results. The bit layout is the issue's reviewed model
contract, not a promise of permanent ABI stability. This checkpoint does not
establish concurrent lookup/revocation safety, generated-code refinement, or
QEMU behavior. Boot-reachable capability copy/revoke and transfer syscall
adapters still need to expose only these word-level boundaries before the
syscall-routing issue is complete.
