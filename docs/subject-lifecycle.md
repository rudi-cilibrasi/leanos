# Subject lifecycle model

`LeanOS.SubjectLifecycle` is a finite, sequential model of trusted subject
creation and termination. Subject identifiers have append-only issued history:
once terminated, an identifier cannot become live again.

Creation publishes a fresh live identity only. It has no parent/child
relationship and does not inherit or copy capabilities, address spaces,
mappings, resource budgets, scheduler state, pending IPC, fault state, or
machine context. It therefore is not fork or an ambiguous clone substitute.
Process duplication remains explicitly out of scope until a new architecture
issue closes the readiness gate in [ADR 0010](adr/0010-defer-fork.md).

Termination is atomic in the model. It removes every capability held by the
subject; retires its exclusively owned memory and endpoint objects (including
capabilities delegated to other subjects); frees owned frames; removes owned
address spaces and mappings; clears endpoint mailboxes owned by, or containing
provenance from, the subject; and removes the subject from current and runnable
state. A capability held by another subject for an object not owned by the
terminated subject is preserved. Repeated termination and identifier replay
are typed, state-preserving rejections.

The Lean proofs establish rejection stability, stale lookup denial, complete
cleanup of the modeled resources, preservation of unrelated memory ownership,
and non-reuse of issued identity. Executable examples cover delegated
authority, a live mapping, a pending message, termination of the current
subject, repeated termination, and identifier replay.

The atomic [user-fault dispatch composition](fault-dispatch.md) invokes this
same termination state on exactly the kernel-owned current subject, then removes
that subject's ready-queue and resumable-context references before selecting a
survivor. No intermediate cleanup state is observable: stale bindings and
missing or stale survivor contexts return the complete pre-state, while every
inbound normalizer fatal result changes only the halt latch. Unrelated
survivor capability, memory, mapping, frame, endpoint, and suspended-context
state remains unchanged. Waiter and in-flight transfer cleanup are outside this
composition state and are not claimed here.

Termination clears the subject's installed slots, so every holder-visible
[generation-bound handle](capability-handles.md) for those slots becomes stale.
Reusing the bounded slot later can issue only a handle carrying a different,
never-reused capability identity; the old handle therefore cannot revive.

This is not executable ring-3 teardown and does not prove physical memory
zeroization. The trusted caller is the kernel lifecycle operation itself;
authorization policy for a future management capability is outside this first
model. The fault composition additionally assumes a normalized entry and
coherent authoritative scheduler/context/mapping projections. Concurrency,
scheduling fairness, destructors, generated code, machine exception delivery,
context restore, and the machine implementation remain outside the proved
claim.
