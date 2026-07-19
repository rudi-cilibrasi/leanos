# Atomic user-fault cleanup and dispatch

`LeanOS.FaultDispatch` is the total, sequential model transaction that connects
the normalized inbound page-fault contract to the authoritative scheduler,
subject lifecycle, resumable-context bank, virtual mappings, and TLB state. It
does not parse a raw x86 frame or perform a machine return.

## Inputs and observable results

The transition consumes `InterruptEntry.Result` plus one
`ResumablePreemption.State`. An accepted containment path requires a normalized
vector-14, CPL3, `userFault` record with a hardware error word and saved user
RSP/SS. The record's subject and address space must equal the kernel-owned
current subject. That subject must still be live and runnable, and the
lifecycle, virtual-memory, and active-translation projections must all own that
same address space. Fault address, error payload, saved registers, and arbitrary
caller payloads never select either subject.

The observable action is exactly one of:

- `dispatch context`, where the context belongs to the deterministic ready-queue
  head and its live subject-owned address space becomes active;
- `idle`, only after cleanup leaves the ready queue empty;
- a typed, state-preserving `rejected reason`; or
- `fatal reason`, which preserves either the exact typed inbound
  `InterruptEntry.RejectReason`, the distinct `kernelOrigin` class, or the
  `alreadyHalted` class while changing only the irreversible halt latch.

The transition does not expose the intermediate cleaned state. Missing or stale
survivor contexts, stale current/address-space bindings, and wrong purpose
reject to the complete pre-state. Every `.fatal` result from the inbound
normalizer is terminal, including malformed frames, uncleared entry flags,
unsupported vectors, and nested entry, and its typed cause remains observable
as `FatalReason.entry reason`. Kernel page faults and an already-set halt latch
remain distinct as `kernelOrigin` and `alreadyHalted`. Fatal results retain the
complete scheduler/lifecycle, context bank, mapping, and translation state while
setting the latch.

## Cleanup and survivor boundary

Accepted user-fault cleanup reuses `ResumablePreemption.cleanupSubject`, which
in turn reuses the existing lifecycle termination policy. It removes the
faulting subject's live identity, runnable/current/ready references, resumable
context, held capabilities, exclusively owned memory and frames, owned address
spaces and mappings, owned endpoints, and modeled mailbox provenance. Issued
identity remains retired and cannot be selected again.

`Scheduler.selectNext` is the only survivor selector. A survivor must already be
live, runnable, queued, address-space-owned, and represented by a valid
kernel-owned context. Dispatch consumes exactly that context. Later queue
positions retain their order and context bytes, and unrelated capability,
memory, mapping, frame, and endpoint state is unchanged. Waiter and in-flight
capability-transfer cleanup are not represented by this state and remain an
explicit composition dependency rather than a second cleanup rule here.

## Proved and executable evidence

Lean proves totality, determinism, attacker-payload independence, atomic
rejection, fatal-store preservation and halt absorption, successful
non-resumption, exact FIFO survivor selection, survivor context/resource
preservation, dispatch safety, empty-queue idle behavior, and preservation of
the complete `ResumablePreemption.WellFormed` invariant for every result.

Executable model regressions cover one survivor, multiple survivors, no
survivor, stale current identity, wrong active address space, wrong purpose,
already-terminated current identity with a stale owner binding, a truncated raw
user frame made fatal by the normalizer, a kernel-origin page fault, unsupported
vector, nested entry, already-halted state, and exact assertions that those
terminal causes remain distinguishable while preserving authoritative stores;
unrelated authority/memory/mapping/IPC state, and the
unsafe split pattern in which an attacker chooses a context after separate
cleanup.

The stable `SC-FAULT-DISPATCH-NONRESUMPTION` claim is intentionally narrower
than this supporting theorem inventory: it advertises that every successful
composite result began with a live, runnable kernel-selected current subject
and removes that subject from live identity, the ready queue, the current slot,
and the resumable bank.

## Progress scope and trusted boundary

If a survivor is already at the ready-queue head and has a valid owned context,
the same transition returns it. If the queue is empty, it returns typed idle.
This is one-step deterministic progress under the scheduler's finite capacity;
it is not fairness, interrupt-delivery, deadlock-freedom, or a real-time bound.

All claims in this document are Lean model claims. Raw x86 exception delivery,
page walks, assembly frame construction, the correspondence from normalization
to this transition, context save/restore, CR3 writes and invalidation, `iretq`,
generated C, compiler/linker behavior, QEMU, firmware, hardware, and final-binary
refinement remain trusted or tested boundaries. Recovery, signals, demand
paging, exception upcalls, restart, SMP, nested interrupts, and kernel-fault
recovery are out of scope.
