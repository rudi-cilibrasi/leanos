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
natural-number identity modulo 48 bits. Capability copy and sealed-transfer
offer boundaries reject zero or reserved/exhausted generations before
allocation, and copy also rejects destination slots outside the encodable
16-bit domain. Accepted copy and offer theorems produce the corresponding
canonical fresh handle encoding. Receipt boundaries likewise reject reserved
destination slots and noncanonical sealed generations before consuming the
mailbox; every delivered attached receipt therefore admits the exact installed
handle encoding.

The Lean theorems prove codec round-trip and canonical uniqueness for every
encodable handle, and prove that successful current-caller resolution returns
exactly the live capability in the trusted caller's capability space. They
also prove that an accepted sealed transfer records successful full-word
resolution of both endpoint and source before its internal transition, and
that accepted copy, direct-revocation, and transitive-revocation boundaries
record the exact decoded authority and target generations before their raw
slot transitions. Malformed or denied authority and target words preserve
state. A denied endpoint-destruction word likewise cannot change state or
reach the raw lifetime operation. They prove that clearing or replacing a slot
denies the old handle, that direct or transitive subtree revocation denies a
descendant's old handle, that installing authority for another subject cannot
change resolution, and that simultaneously live issued handles cannot alias
different slots. Executable examples cover fresh use, reserved slot and
generation fields, out-of-domain encode rejection, equal words under a
different trusted caller, changed generation bits, clear, and same-slot
replacement. Direct and transitive revocation vectors cover accepted current
words, stale target replay, and reserved authority fields. A negative
regression also demonstrates that the former raw-slot lookup accepts the
replacement while the generation-aware resolver rejects the stale handle.
The repository-owned capability-boundary check additionally inspects the
boot-reachable map, nonblocking IPC, and blocking IPC dispatcher definitions.
It requires opaque `UInt64` handle words, `resolveCurrent`, and post-resolution
slot use, and rejects direct `Capability.lookup` or `handleWord.toNat`
fallbacks in those dispatchers. This is a narrow source-policy regression, not
a refinement proof for the generated binary.

These are model-level results. The bit layout is the issue's reviewed model
contract, not a promise of permanent ABI stability. This checkpoint does not
establish concurrent lookup/revocation safety, generated-code refinement, or
QEMU behavior. Capability copy/revoke and transfer are not operations in the
current boot syscall vocabulary; their model-facing public boundaries accept
only the canonical words documented above, so a future boot adapter must route
through those boundaries rather than exposing the internal raw-slot kernels.
