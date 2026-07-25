# Atomic user-fault cleanup and dispatch

`LeanOS.FaultDispatch` is the total, sequential model transaction that connects
the normalized inbound contained-fault contract to the authoritative scheduler,
subject lifecycle, resumable-context bank, virtual mappings, and TLB state. It
does not parse a raw x86 frame or perform a machine return.

## Inputs and observable results

The transition consumes `InterruptEntry.Result` plus one
`ResumablePreemption.State`. An accepted containment path requires a normalized
CPL3 `userFault` record whose vector decodes through the manifest-bound
`InterruptEntry.containedReason?` table to exactly one typed reason: page
fault (vector 14, hardware error word required), divide error (vector 0, no
error word), or breakpoint (vector 3, no error word), each with saved user
RSP/SS. The reason is a finite typed value derived only from that vector;
attacker registers, user-stack words, syscall arguments, and the saved RIP
cannot select or relabel it. The record's subject and address space must equal
the kernel-owned current subject. That subject must still be live and
runnable, and the lifecycle, virtual-memory, and active-translation
projections must all own that same address space. Fault address, error
payload, saved registers, and arbitrary caller payloads never select either
subject.

The observable action is exactly one of:

- `dispatch reason context`, where the context belongs to the deterministic
  ready-queue head and its live subject-owned address space becomes active;
- `idle reason`, only after cleanup leaves the ready queue empty;
- a typed, state-preserving `rejected reason`; or
- `fatal reason`, which preserves either the exact typed inbound
  `InterruptEntry.RejectReason`, the distinct `kernelOrigin` class, or the
  `alreadyHalted` class while changing only the irreversible halt latch.

The typed contained reason is observable in every successful action but never
selects a cleanup, survivor, or address-space variant:
`success_state_reason_independent` proves that any two successful results from
the same pre-state publish exactly the same post-state, and
`success_reason_vector_binding` proves the reason/vector/error-shape agreement
without unfolding `dispatch`. Kernel-origin divide errors and breakpoints are
already terminal at the normalizer (`wrongOrigin`) under their user-only
origin policy; a kernel-origin page fault still normalizes to the distinct
supervisor diagnostic purpose and halts here as `kernelOrigin`.

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
kernel-owned context whose address space has the same authoritative virtual
owner. Dispatch consumes exactly that context. Later queue
positions retain their order and context bytes, and unrelated capability,
memory, mapping, frame, and endpoint state is unchanged. Waiter and in-flight
capability-transfer cleanup are not represented by this state and remain an
explicit composition dependency rather than a second cleanup rule here.

## Proved and executable evidence

Lean proves totality, determinism, attacker-payload independence, atomic
rejection, fatal-store preservation and halt absorption, successful
non-resumption (including a cleared runnable bit and universal removal of every
pre-fault-owned address space and mapping), exact FIFO survivor selection, survivor context/resource
preservation, dispatch safety, empty-queue idle behavior, and preservation of
the complete `ResumablePreemption.WellFormed` invariant for every result.
For the typed contained classes it additionally proves reason/vector/error
agreement (`success_reason_vector_binding`), reason-independent cleanup
(`success_state_reason_independent`), and, at the normalizer,
manifest-bound error-shape/restart-class binding
(`InterruptEntry.accepted_binds_manifest_shape`,
`InterruptEntry.accepted_contained_error_shape`), so issue-#104 composition
never unfolds either transition.

Executable model regressions cover one survivor, multiple survivors, no
survivor, stale current identity, wrong active address space, wrong purpose,
already-terminated current identity with a stale owner binding, a truncated raw
user frame made fatal by the normalizer, a survivor with a mismatched virtual
owner projection, a kernel-origin page fault, unsupported
vector, nested entry, already-halted state, and exact assertions that those
terminal causes remain distinguishable while preserving authoritative stores;
clearing of the faulting subject's runnable bit and a nonempty owned mapping;
unrelated authority/memory/mapping/IPC state; and the
unsafe split pattern in which an attacker chooses a context after separate
cleanup. The divide-error and breakpoint classes add accepted survivor and
idle traces byte-for-byte equal to the page-fault post-state, kernel-origin
terminal forms, spurious-error and wrong-restart-class normalizer rejections,
swapped reason/vector rejection, and stale current/address-space/survivor
rejections.

The stable `SC-FAULT-DISPATCH-NONRESUMPTION` claim advertises that every
successful composite result began with a live, runnable kernel-selected current
subject and removes that subject from live and runnable identity, the ready
queue, the current slot, the resumable bank, and every address space and mapping
that it owned in the pre-state. The companion
`SC-USER-FAULT-CLASS-CONTAINMENT` claim binds the typed reason of a successful
result to the manifest-decoded vector and reviewed error convention, restates
the same cleanup package for all three contained classes, and pins the
kernel-origin accepted frame to the absorbing `kernelOrigin` halt.

## Progress scope and trusted boundary

If a survivor is already at the ready-queue head and has a valid owned context,
the same transition returns it. If the queue is empty, it returns typed idle.
This is one-step deterministic progress under the scheduler's finite capacity;
it is not fairness, interrupt-delivery, deadlock-freedom, or a real-time bound.

All claims in this document are Lean model claims. Raw x86 exception delivery,
page walks, assembly frame construction, the correspondence from normalization
to this transition, context save/restore, CR3 writes and invalidation, `iretq`,
generated C, compiler/linker behavior, QEMU, firmware, hardware, and final-binary
refinement remain trusted or tested boundaries. The per-vector error-word and
saved-RIP restart-class conventions for #DE, #BP, and #PF are AMD64-manual
machine assumptions carried as normalized inputs; the terminated subject is
never resumed, so no transition rewrites RIP to authorize recovery or retry.
Recovery, signals, demand paging, exception upcalls, restart/instruction
retry, userspace handlers, debugger support, #DB, SMP, nested interrupts, and
kernel-fault recovery are out of scope; the machine IDT/C slice for vectors 0
and 3 is deferred to the follow-up machine issue.

## Shared containment vocabulary

`LeanOS.UserFaultContainmentVocabulary` binds the abstract reason-independence
result above to one concrete two-subject pre-state so the `#DE`, `#BP`, `#PF`,
and denied-port (`#GP`) machine scenarios share a single subject-termination
and peer-survival implementation. It normalizes real CPL3 divide-error
(vector 0, faulting-instruction restart class) and breakpoint (vector 3,
following-boundary restart class) raw snapshots through `InterruptEntry.normalize`
and reuses the `LeanOS.DirectPortContainment` witness state.
`shared_contained_classes_one_transition` proves that all four contained entry
shapes drive `FaultDispatch.dispatch` to dispatch the same survivor B with the
typed reason bound to the manifest vector, that the port-denial composition
reuses the identical vector-14 dispatch, and that every successful post-state is
byte-for-byte the page-fault post-state via `success_state_reason_independent`.
`kernel_origin_contained_entries_rejected` shows the same real `#DE`/`#BP`
snapshots at CPL0 are terminal `wrongOrigin` rejections rather than containment,
and `contained_classes_retire_faulting_select_survivor` restates the retirement
of subject A. The stable contract restates this as
`SC-USER-FAULT-SHARED-CONTAINMENT`, and the negative fixture
`tests/negative/SharedContainmentReasonSubstitution.lean` shows the typed reason
cannot be relabeled. The two live IDT-gate/real-instruction QEMU scenarios that
consume this vocabulary remain the follow-up machine slice.
