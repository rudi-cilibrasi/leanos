# Capability authority model

`LeanOS.Capability` is a sequential reference model. Subjects own numbered
slots. Each occupied slot contains an object identifier, its recorded
`ObjectKind`, and a nonempty valid subset of
`read`, `write`, `grant`, and `revoke`. Authority means that such a slot grants
the named object/right pair. Lookup distinguishes forged subjects from stale or
empty slots.

The minimal operations are `copy`, which requires `grant` and delegates only a
nonempty subset into an empty slot, and direct `revoke`, which requires revoke
authority over the target object's slot. This captures controlled authority
creation and removal without prematurely choosing IPC or memory policy.
Revoke is not recursive. Every denial is typed and preserves the whole state.

The state registry is authoritative for object kind. Object identity remains a
never-reused natural number (enforced by `MemoryLifecycle.issued`); retirement
removes its registry entry. `WellFormed` requires every capability's recorded
kind to equal the live registry kind. `authorizeKind` is the reusable typed
dispatch boundary: a memory capability presented to an address-space operation,
or the converse, is rejected before operation-specific state can change.
Memory supports read/write/grant/revoke rights; address-space capabilities in
this slice support only grant/revoke because lifecycle operations are deferred.

## Proved guarantees

- `copy_preserves_wellFormed` and `revoke_preserves_wellFormed` prove both total
  operations preserve valid subjects, live object/kind agreement, and valid
  per-kind rights. Copy retains the source object and kind.
- `copy_no_authority_amplification` proves every post-copy right either existed
  for that subject or came from the actor's pre-state authority.
- `revoke_no_authority_amplification` proves every post-revoke authority existed
  before revocation.
- `copy_rejected_unchanged` and `revoke_rejected_unchanged` prove that all
  rejected outcomes leave state unchanged.

Examples test delegation, forged IDs, stale source and target slots, missing
grant, successful direct revocation, and the stale slot after revocation.

## Boundaries and non-guarantees

The proofs concern only these Lean definitions under sequential evaluation.
They do not verify generated code, a runtime, compiler, kernel binary, or
hardware. Object lifetime and identifier reuse, derivation trees, recursive
revocation, concurrency, and races are not modeled. Authority preservation is
not confidentiality, information-flow noninterference, object-content
integrity, availability, resource bounds, timing resistance, or resistance to
other covert channels.
