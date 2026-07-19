# Bounded scheduler model

`LeanOS.Scheduler` is a deterministic single-core round-robin model. Its ready
queue is executable, duplicate-free, and bounded by the state's fixed
`capacity`. The current subject is stored in the composed subject-lifecycle
state and never also occurs in the ready queue. Add, remove, yield, timer tick,
select-next, and current-subject termination are total and use typed errors.
Empty selection succeeds with no context.

Dispatch constructs `TrustedContext` only after selecting a queue head. The
subject and active address space are derived from scheduler and lifecycle
state; callers cannot supply either. Termination uses the lifecycle model's
atomic cleanup and also filters every queue occurrence. Removal atomically
removes every occurrence, clears a matching current subject, and marks it not
runnable. Rejected operations preserve the complete scheduler state.

[`LeanOS.FaultDispatch`](fault-dispatch.md) is the atomic user-fault consumer of
this policy. It first validates the normalized fault against the kernel-owned
current subject and active address space, then cleans that subject and invokes
`selectNext` exactly once. A nonempty post-cleanup queue dispatches its FIFO head
with that subject's owned resumable context; an empty queue returns typed idle.
Later queue positions and contexts remain ordered and unchanged. The composite
transition never accepts a caller-selected subject, address space, or context.

The well-formedness predicate composes lifecycle well-formedness with queue
uniqueness and capacity, live/runnable membership agreement, current-subject
validity, and address-space ownership. Lean proves successful dispatch returns
exactly the selected live subject's owned address space. It also proves that a
queued subject has a round-robin position strictly below `capacity`.

## Progress scope and evidence

The bound counts scheduling steps, not time. It assumes a finite fixed runnable
set, a scheduling step repeatedly occurs, and every selected subject eventually
yields or receives a tick. There is no higher-priority class in this model.
Under those assumptions, each step consumes one preceding queue element, so a
continuously runnable queued subject is selected in fewer than `capacity`
steps. This is not wall-clock, blocking-resource, interrupt-delivery, or
system-wide liveness, and it does not apply while runnable subjects are added
without bound.

Fault dispatch makes only the one-step claim that an already-queued valid head
is returned in the same composite transition. It adds no fairness, delivery,
deadlock-freedom, or real-time guarantee. This remains a Lean model property;
context restore, CR3/TLB instructions, compiler behavior, and hardware are not
refined by the scheduler or fault-dispatch proofs.

Executable Lean traces cover empty, single/multiple selection, repeated ticks,
cooperative yield, current termination, stale identity, duplicate enqueue, and
queue wraparound. The proofs and traces concern only the Lean model. They do
not verify assembly context switching, timer hardware, generated code, QEMU,
the compiler, or a kernel binary. No `unsafe`, `extern`, FFI, axiom, constant,
`sorry`, or `admit` declaration is introduced.

The [finite scheduled observer model](scheduled-observation.md) uses this
scheduler/lifecycle state as the sole authoritative source of the selected
subject and active address space. It exposes scheduler selections and observed
termination as public events rather than treating scheduling as confidential.
