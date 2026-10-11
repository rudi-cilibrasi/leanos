# ADR 0026: The observer's view includes its authority, and receipt is not nested

- Status: Accepted, issue #479
- Date: 2026-10-10

## Context

After ADR 0025 two channels of #542 were still open, both on the observer's
own requests:

- **Subtree revocation of the observer's own capability.** Revocation removes
  every capability derived from the revoked one, in any subject's row, and
  cancels every sealed transfer derived from it. The observer's row can hold
  a capability derived from its own through another subject's delegation.
  An endpoint it names can carry a sealed transfer derived the same way. Two
  states the view cannot tell apart can differ only in that derivation, and
  the revocation then cancels the pending transfer in one of them
  (`CompositeSwitchedChannels.revokeSubtree_own_step_inconsistent`).
- **Transfer receipt.** Receipt installs the carried capability in the
  observer's row, and with it the carried object's view (its mailbox,
  pending transfer, blocking queue and frame backing). The view did not
  contain that object before receipt, so step consistency needed agreement on
  it as a premise (`CompositeOwnSteps.CarriedAgree`).

Neither difference is a leak the kernel could avoid by answering differently:

- Revocation is defined over the derivation history. Removing exactly the
  derived capabilities is what the operation is for.
- Receipt is defined to make the carried object reachable.

What was missing is the observer's view of its own authority.

## Decision

**The full view.** `CompositeFullView.observeFull` is `observe` plus, for
every capability in the observer's row:

- its lineage, the chain of identities it derives from;
- for the sealed transfer pending on the object it names, if any:
  - that transfer's lineage;
  - the carried object's view;
  - the lineage of the sealed transfer pending on the carried object.

Both additions are authority the observer already holds:

- The lineage of its capabilities decides what its revocation removes.
- A transfer pending on an endpoint it names is an offer to it, which it can
  accept at any time.

The lineage of an issued identity never changes, because the derivation
history is append-only and orders parents before children
(`CompositeFullView.lineage_of_extends`). It decides revocation's bounded
walk exactly (`descendsFrom_eq_lineage`).

**No nested receipt.** `FailStop.subjectGate` refuses a receipt that carries
another endpoint which has a sealed transfer of its own pending, with the
fixed result `SubjectGateResult.nestedTransferRefused` and no effect
(`CompositeState.refusesNestedTransfer`). A transfer that carries the
endpoint it is pending on is not refused: receipt consumes that very record.

- Without the refusal, receipt would make a second carried object reachable
  in the same step. Its view is part of no offer to the observer, so every
  depth of nesting would need to be in the view.
- The refusal reads only what the full view contains: the observer's handle,
  the transfer on the endpoint it names, and the transfer pending on the
  carried object (`CompositeFullIsolation.refusesNestedTransfer_congr`).

## Consequences

- **The full statement holds.** Take two runtime-well-formed states in which
  the observer is scheduled and the fail-stop mode is the same. Suppose they
  have equal full views and agree on the declared public inputs: the
  identity counter and the scheduler's bookkeeping. Then every request
  through the subject gate keeps the full views equal
  (`CompositeFullIsolation.full_step`). Every request also returns the same
  result, except that a user return may differ by halting the machine, the
  termination channel (`CompositeFullIsolation.full_output`).
  - Finite traces end fully low-equivalent (`CompositeFullTrace.finite_trace_full`).
  - Another subject's request is silent on the full view when it touches no
    object the observer is offered (`CompositeFullTrace.quietFull`).
- **The old pair is told apart.** On the canonical sample plan, the pair of
  `revokeSubtree_own_step_inconsistent` is not fully low-equivalent
  (`CompositeFullChannels.revokeSubtree_own_closed`). The negative fixture
  `tests/negative/CompositeFullSubtreeReopened.lean` restates the old premise
  on the full view, and the kernel rejects it.
- **The cost of the refusal.** A sender that offers another endpoint must
  let that endpoint's own pending transfer be received or cancelled first.
- **What does not change.** No syscall encoding, dispatcher table, oracle
  vector or export changes. The generated dispatcher and the booted kernel
  replay `authoritativeGate`. The one scripted receipt on the boot images
  (syscall 28 of the `capability-transfer` image, `docs/userspace-abi.md`)
  accepts a send-only descendant of the endpoint it is pending on, which the
  refusal never applies to, so its transcript is unchanged.
