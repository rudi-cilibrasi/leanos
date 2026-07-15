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

Executable Lean traces cover empty, single/multiple selection, repeated ticks,
cooperative yield, current termination, stale identity, duplicate enqueue, and
queue wraparound. The proofs and traces concern only the Lean model. They do
not verify assembly context switching, timer hardware, generated code, QEMU,
the compiler, or a kernel binary. No `unsafe`, `extern`, FFI, axiom, constant,
`sorry`, or `admit` declaration is introduced.
