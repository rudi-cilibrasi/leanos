# ADR 0025: The subject-facing gate refuses cross-subject requests

- Status: Accepted, issue #479
- Date: 2026-10-10

## Context

Issue #479 asks for one confidentiality theorem over the authoritative
composite state, and the maintainer decided that the information channels
proved in #542 must be closed in the kernel design rather than declared. Several
of those channels come from the same design gap:

- In the ordinary composite family, a subject can name another subject:
  - the destination of a capability delegation;
  - the victim of a direct or subtree revocation;
  - the subject created, terminated or admitted to the ready queue.
- The blocking wait cancellation and the deferred drain also take another
  subject as argument.
- None of these operations has an authority relation over the named subject:
  - a delegation can fill any subject's empty slot;
  - a revocation can clear any slot holding a capability to an object the
    caller may revoke;
  - creation, termination, queue admission, cancellation and drains check no
    caller at all.
- Their replies reveal that subject's slot occupancy, liveness, issuance,
  runnability and wait state. None of these is in the caller's view
  (`CompositeChannels`).
- Terminating another subject also cancels every pending sealed offer,
  including the caller's own (`terminate_step_inconsistent`). Subtree
  revocation of another subject's capability cancels the caller's pending
  transfer exactly when a derivation it cannot see links the two
  (`revokeSubtree_other_step_inconsistent`).

The kernel itself needs these transitions, without a caller:

- boot creates subjects;
- the spawn family (#489) copies the granted endpoint into the child's row
  and terminates a child;
- contained-fault cleanup retires a subject;
- the issued lifecycle family creates fresh identities.

The generated dispatcher replays the same transitions for its kernel-side
traces.

## Decision

`FailStop.authoritativeGate` stays the kernel's transition engine, unchanged.

`FailStop.subjectGate` is the gate a scheduled subject asks through.

- `AuthoritativeOperation.target` names the subject an operation is about, for
  eight operations: `capabilityCopy` (destination), `capabilityRevoke` and
  `capabilityRevokeSubtree` (victim), `createSubject`, `terminateSubject`,
  `scheduleAdd`, blocking `cancel`, and `drainDeferred`.
- The gate refuses a request when all of these hold
  (`CompositeState.refusesCrossSubject`):
  - the latch is running;
  - a subject is scheduled;
  - the request names a different subject.
- A refusal is one fixed result, `SubjectGateResult.crossSubjectRefused`. It
  is decided before anything of the target is read, and it changes nothing.
- Every other request is exactly `authoritativeGate`
  (`subjectGate_of_not_refused`).

Authorized cross-subject management goes through families that carry the
authority explicitly. These are unchanged:

- sealed transfer: the receiver accepts into a slot of its own row;
- subtree revocation of the caller's own lineage root: the caller keeps a
  second capability with revoke rights if it wants to keep the object;
- the spawn family: the parent/child record;
- the fault-handler binding.

## Consequences

- Every request of the scheduled observer that names another subject is step
  and output consistent with no further premise
  (`CompositeSubjectGate.own_step_cross`, `own_output_cross`). The `#542`
  pairs are re-evaluated through the subject gate
  (`cross_subject_channels_closed`, `revokeSubtree_other_closed`).
- The channel theorems over `authoritativeGate` stay. They are the
  adversarial record of the raw transitions: exposed to a subject, the
  engine leaked. The negative fixture
  `tests/negative/CompositeCrossSubjectReopened.lean` fails to re-prove them
  for the subject gate.
- No ring-3 syscall changes. No syscall exposes these ordinary operations to
  a subject (the scripted ABI of `docs/userspace-abi.md`). The fault-handler
  termination (syscall 65) and the endpoint directory's reply copy (syscall
  82) belong to their own families with their own authority checks.
- The kernel-internal Lean-to-C ABI is unchanged. The generated dispatcher
  replays `authoritativeGate` for kernel-side traces, so no oracle vector,
  adapter or export changes.
- Refusal reads only the latch mode, the scheduled subject and the request
  (`refusesCrossSubject_congr`), so another subject's refused request is
  silent for every observer (`CompositeSubjectGate.subjectGate_silent_observe`).
