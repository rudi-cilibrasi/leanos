# Capability authority model

`LeanOS.Capability` is a sequential reference model. Each subject owns an
independent finite capability space whose capacity is stored in the model.
`capabilitySpace` enumerates exactly the in-range slots in ascending order;
`copyBounded` installs into a caller-selected in-range empty slot, while
`copyLowest` deterministically selects the lowest free slot. Together they
report invalid subject, out-of-range, full, and occupied outcomes separately,
and all rejections preserve the complete state. Each occupied slot contains an object identifier, its recorded
`ObjectKind`, and a nonempty valid subset of
`read`, `write`, `grant`, and `revoke`. Authority means that such a slot grants
the named object/right pair. Lookup distinguishes forged subjects from stale or
empty slots.

Every installed capability has a never-reused identity and either an explicit
root marker or one derivation parent. `copy` requires `grant`, delegates only a
nonempty rights subset into an empty slot, and appends a fresh child identity.
Direct `revoke` deletes only the selected slot. `revokeSubtree` requires revoke
authority for the same object and kind, then atomically clears the selected
identity and every live descendant. Independent roots and sibling subtrees
survive. Every denial, including a stale or repeated request, preserves the
complete state.

The state registry is authoritative for object kind. Object identity remains a
never-reused natural number (enforced by `MemoryLifecycle.issued`); retirement
removes its registry entry. `WellFormed` requires every capability's recorded
kind to equal the live registry kind. `authorizeKind` is the reusable typed
dispatch boundary: a memory capability presented to an address-space operation,
or the converse, is rejected before operation-specific state can change.
Memory supports read/write/grant/revoke rights; address-space capabilities in
this slice support only grant/revoke because lifecycle operations are deferred.

## Proved guarantees

- `WellFormed` requires unique live identities, matching append-only derivation
  metadata, parent/object/kind agreement, rights attenuation at parent edges,
  and strictly increasing parent-to-child identities, which rules out cycles.
- `copy_preserves_wellFormed`, `revoke_preserves_wellFormed`, and
  `revokeSubtree_preserves_wellFormed` prove preservation of that invariant.
- `copy_no_authority_amplification` proves every post-copy right either existed
  for that subject or came from the actor's pre-state authority.
- `revoke_no_authority_amplification` proves every post-revoke authority existed
  before revocation.
- `copy_rejected_unchanged`, `revoke_rejected_unchanged`, and
  `revokeSubtree_rejected_unchanged` prove that all
  rejected outcomes leave state unchanged.
- `copyBounded_outOfRange_unchanged` and `copyBounded_full_unchanged` prove the
  finite-space exhaustion paths preserve all state, including derivation
  metadata. `install_other_subject` and `clear_other_subject` prove a selected
  subject's slot mutation cannot alter an equal-numbered slot of another
  subject.

Executable traces cover capacities zero and one, independent filling of two
subjects, out-of-range indices, repeated full allocation, revoke-then-reuse,
and the regression difference between bounded installation and an unchecked
natural-number destination. They also cover `root → A → B → C`, attenuation, direct deletion's
known failure to revoke descendants, subtree revocation, independent roots,
repeated/stale requests, and slot reuse. Memory/address-space/endpoint root
creation uses the same identity store; whole-object destruction remains the
stronger operation and removes every live capability for the retired object.

## Bounds and temporal policy

This is an atomic sequential model: selection and removal form one transition,
so no copy or use can interleave with an accepted revoke. Parent walking uses
at most `nextIdentity` steps per live slot. A bounded free/full check is `O(C)`
for destination capacity `C`. With `S` inspected slots and `I = nextIdentity`,
subtree removal is `O(S·I)` time and retains `O(I)` append-only derivation
history. Bounding live slots does **not** bound lifetime identity metadata;
identity-history exhaustion and reclamation remain a precise non-goal.

Issue #71's future sealed in-flight transfers must use an atomic receive-side
capacity check: a full receiver leaves both capability state and the message
envelope unchanged. An envelope is not a live installed capability and does
not consume a slot before successful receive, but it must retain provenance
until that atomic installation succeeds.

## Boundaries and non-guarantees

The proofs concern only these Lean definitions under sequential evaluation.
They do not verify generated code, a runtime, compiler, kernel binary, or
hardware. Concurrency, races, subject-termination policy, and a concrete
bounded kernel representation are not modeled. Authority preservation is
not confidentiality, information-flow noninterference, object-content
integrity, total metadata bounds, timing resistance, or resistance to
other covert channels.
