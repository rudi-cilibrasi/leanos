# The gate a running program asks through

The kernel's main transition engine is also what the kernel itself uses to create programs at boot, to give a newly spawned child its endpoint, to retire a child, and to clean up after a fault. A running program, by contrast, asks through the subject gate. Eight requests name another program: copying a permission into its slots, revoking one of its permissions or a whole tree from its slot, creating, terminating, or queueing it, cancelling its wait, and draining its parked cancellation. While a program is running, the subject gate refuses every such request that names a different program, with one fixed answer and no change, before it reads anything about that program. It also refuses, with another fixed answer and no change, to accept a handover that offers a different endpoint which has a handover of its own pending, so that accepting never makes reachable an object no offer carried. Every other request goes to the kernel's engine unchanged.

- `subjectGate_of_refusal` — A refused request returns the state unchanged with its fixed refusal.
- `subjectGate_of_no_refusal` — A request that is not refused is exactly the kernel's engine step, with its exact answer.
- `subjectGate_refused` — A request naming another program is refused with the fixed cross-program refusal and changes nothing.
- `subjectGate_of_not_refused` — A request that names no other program and is not a refused acceptance is exactly the kernel's engine step.
- `subjectGate_cases` — Every request is either refused without effect or is exactly the engine step.
- `refusesNestedTransfer_eq_false` — Only an acceptance can be refused for a nested handover.
- `refusesCrossSubject_congr` — Whether a request is refused for naming another program depends only on the latch mode, the scheduled program, and the request itself.
- `refusesCrossSubject_eq_false_of_target` — A request that names no program, or names the scheduled program itself, is never refused for naming another program.
- `refusesCrossSubject_true` — A request refused for naming another program was made while the kernel was running and names a program other than the scheduled one.
- `subjectGate_preserves_authoritativeRuntimeWellFormed` — The subject gate keeps the kernel's complete safety invariant.
- `runSubjectOperations_preserves_authoritativeRuntimeWellFormed` — Every finite run of requests through the subject gate keeps that invariant.
