# Capability identities are never handed out twice

This section sets up the bookkeeping that shows a capability's identity number, once retired, is never given to a new capability. A handle names a capability by that number, so a handle to something destroyed keeps failing forever.

- `IdentityFrom.refl` — Bookkeeping: a capability store and its pending transfers trivially account for their own identity numbers.
- `IdentityFrom.trans` — If every identity after one step came from before it, and likewise for a second step, then every identity after both steps came from before the first.
- `IdentityFrom.of_shrink` — A step that only removes capabilities and pending transfers, without lowering the identity counter, introduces no new identity.
- `IdentityFrom.shrink_pending` — Dropping some pending transfers after a step keeps the identity accounting valid.
- `IdentityStep.refl` — A kernel state trivially accounts for its own capability identities.
- `IdentityStep.trans` — Identity accounting carries across two consecutive kernel steps.
- `IdentityStep.of_eq` — A kernel step that leaves the capability store and the pending transfers unchanged introduces no new identity.
- `IdentityStep.of_capabilities_eq` — Following a step with one that changes neither the capability store nor the pending transfers keeps the identity accounting.
- `IdentityStep.of_frames` — A kernel step whose declared write set excludes the capability store and the transfer store introduces no new identity.
- `IdentityStep.retired` — An identity that is allocated but held by no capability and no pending transfer stays that way across any step that only reuses old identities or hands out fresh ones.
- `stale_word_of_retired` — No subject can use a handle whose identity number is retired, whatever kind of object it expects.
- `Capability.copy_identityFrom` — Copying a capability only adds a capability with a brand-new identity number.
- `Capability.revoke_shrinks` — Revoking one capability only removes it and keeps the identity counter.
- `Capability.revokeSubtree_shrinks` — Revoking a whole family of derived capabilities only removes capabilities and keeps the identity counter.
- `Capability.revokeRuntimeSafe_identityFrom` — The kernel's checked single revocation introduces no new identity.
- `Capability.revokeSubtreeRuntimeSafe_shrinks` — The kernel's checked family revocation only removes capabilities and keeps the identity counter.
- `Capability.installRoot_identityFrom` — Installing the first capability for a new object uses a brand-new identity number.
