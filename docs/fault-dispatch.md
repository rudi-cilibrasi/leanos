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

## Active-address-space page-fault agreement

`dispatchPageFault` is the strengthened vector-14 entry point. It consumes the
exact version-one canonical words and independent trusted context from
`InterruptEntry.authorizeCanonicalPageFault`, a proof-carrying
`BootPageTablePlan.Plan`, a bounded `BootPageTablePlan.DecodedRoot` sampled
from the kernel-selected CR3, and the existing `ResumablePreemption.State`.
The transition adds no second page-table store, lifecycle view, scheduler, or
global invariant. The complete decoded report is checked against the
proof-carrying plan already retained by the #104 global runtime.

The active translation projection selects subject-A root 1 or subject-B root 2;
CR2 selects only a page inside that already selected root. The gate checks the
report's address-space identity, plan-derived CR3, selected WP/NXE/SMEP/SMAP
profile, and one live-plan agreement at the fault page:

- an absent planned leaf must also be absent from both the live virtual and
  lifecycle mappings;
- a supervisor planned leaf must not be shadowed by either mapping projection;
  and
- a user leaf must name an issued current memory object and equal its live
  binding, allocator owner, lifecycle mapping, lifecycle object/frame binding,
  frame owner/free status, read permission, and writable bit.

The exact matching TLB key/context must be absent and the bounded cache must
remain within capacity. This names the single-core completed-invalidation
precondition instead of choosing between stale cache data and a current walk.
Classification uses the page-local ancestor path and leaf decoded from the live
report, not a page table reconstructed from the safe plan. Reserved-bit and
out-of-range-frame outcomes therefore remain observable integrity classes.
Noncanonical CR2 records are rejected by the canonical snapshot gate before a
walk. Every other candidate denial is admitted only after the
whole decoded report validates against the plan, so malformed ancestors,
extra/missing leaves, wrong pointers, and permission/frame drift fail closed.
The classifier admits only four ordinary denials: non-present with `P=0`,
supervisor with `P=1`, read-only write with `P=1,W/R=1`, and NX instruction
fetch with `P=1,I/D=1`. An allowed access, reserved/frame-range
walk, invalid live report, wrong root, stale mapping/lifetime, matching
cached entry, unsupported canonical encoding, or error/walk mismatch is typed
integrity failure and sets the existing absorbing latch.

SMEP and SMAP are not claimed as live-walk outcomes at this boundary:
`dispatchPageFault` authorizes only CPL3 accesses, so its classifier context is
`.user`; SMEP/SMAP are supervisor-access checks covered by separate kernel
probes.

Successful agreement delegates to `FaultDispatch.dispatch`; it does not
reimplement cleanup or survivor selection.
`dispatchPageFault_success_sound` exposes the exact decoded record,
independent action authorization, active root, CR2 page, live mapping/TLB
checks, decoded error, classifier cause, and denial equality for every
successful outcome. `dispatchPageFault_integrity_fatal_atomicity` proves that
an integrity-fatal result changes only the halt latch,
`dispatchPageFault_fatal_atomicity` extends that frozen-store result to every
fatal class, `dispatchPageFault_rejected_unchanged` preserves stale nonfatal
bindings byte-for-byte, and
`dispatchPageFault_preserves_wellFormed` preserves the complete
`ResumablePreemption.WellFormed` predicate. Concrete executable witnesses cover
all four admitted denial classes, empty and multiple-survivor queues, plus
mismatched error, reserved error, kernel origin, forged address space, wrong
root, stale virtual or lifecycle mapping, incoherent-TLB, reserved-bit live
leaf, out-of-range live frame, malformed live-ancestor, and unissued mapped
object fatal results.
Proof-integrity fixtures reject accepting every present error, ignoring the
active walk, containing a reserved-bit fault, allowing a snapshot to substitute
another address space, containing a corrupt live-table report, or containing a
non-present fault while the lifecycle
still carries the concrete stale page-50/object-999 mapping. A separate
concrete fixture clears object 100's monotonic issuance bit while retaining all
of its mapping, capability, binding, allocator, and lifecycle projections; the
agreement gate must classify that stale-generation state as fatal.

This independently correct slice does not change the public input type of the
older shared `dispatch` function because #104 is concurrently making the one
global gate and owns publication of the compiled plan. The #104 integration
must route vector 14 through `dispatchPageFault`; divide error, breakpoint, and
the shared cleanup theorem remain unchanged. Until that cutover lands, the
older vector-only `dispatch` claim remains the weaker normalized-frame claim
documented above and is not promoted to active-page-table agreement.

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
