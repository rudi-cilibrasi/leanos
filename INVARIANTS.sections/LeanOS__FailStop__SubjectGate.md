# The gate a running program asks through

The kernel's main transition engine is also what the kernel itself uses to create programs at boot, to give a newly spawned child its endpoint, to retire a child, and to clean up after a fault. A running program, by contrast, asks through the subject gate. Eight requests name another program: copying a permission into its slots, revoking one of its permissions or a whole tree from its slot, creating, terminating, or queueing it, cancelling its wait, and draining its parked cancellation. While a program is running, the subject gate refuses every such request that names a different program, with one fixed answer and no change, before it reads anything about that program. Every other request goes to the kernel's engine unchanged.

- `subjectGate_refused` — A refused request returns the state unchanged with the fixed refusal.
- `subjectGate_of_not_refused` — A request that is not refused is exactly the kernel's engine step, with its exact answer.
- `subjectGate_cases` — Every request is either refused without effect or is exactly the engine step.
- `refusesCrossSubject_congr` — Whether a request is refused depends only on the latch mode, the scheduled program, and the request itself.
- `refusesCrossSubject_eq_false_of_target` — A request that names no program, or names the scheduled program itself, is never refused.
- `refusesCrossSubject_true` — A refused request was made while the kernel was running and names a program other than the scheduled one.
- `subjectGate_preserves_authoritativeRuntimeWellFormed` — The subject gate keeps the kernel's complete safety invariant.
- `runSubjectOperations_preserves_authoritativeRuntimeWellFormed` — Every finite run of requests through the subject gate keeps that invariant.
