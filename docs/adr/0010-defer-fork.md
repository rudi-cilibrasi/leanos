# ADR 0010: Defer fork until the kernel core is complete

- Status: Accepted
- Date: 2026-07-18

## Decision

LeanOS intentionally does not provide `fork()`, a fork syscall, or a
clone-like operation with implicit or underspecified inheritance. This
exclusion applies to the Lean model, public syscall vocabulary, generated
adapters, boot paths, and documented interfaces. No syscall number or ABI is
reserved for process duplication.

The existing trusted subject-creation operation is not process duplication. It
introduces a fresh, never-reused subject identity without copying a parent's
capabilities, address space, mappings, scheduler context, IPC state, fault
state, or machine context. Explicit subject creation, scheduling, IPC, and
lifecycle work may continue without introducing inheritance semantics.

Before implementation can begin, a new architecture issue must close every
item in this readiness gate:

1. One authoritative composite kernel state covers subjects, capabilities,
   address spaces, mappings, physical ownership, resource budgets,
   scheduler/interrupt state, IPC, lifecycle history, and all user-visible
   machine context.
2. Creation, duplication, parent/child identity, inheritance, sharing,
   cleanup, failure, and resource exhaustion have explicit atomic semantics.
3. Every inherited or reset component is enumerated, including pending IPC,
   fault state, extended CPU state, device authority, and resources owned by
   future services.
4. The proof plan covers invariant preservation, confinement,
   no-authority-amplification, stale references, cleanup, and resource
   accounting.
5. The executable boundary has a canonical encoding and adversarial tests for
   partial failure, rollback, cleanup, and isolation.
6. The trusted computing base and model-to-binary gap are documented without
   treating build or emulator evidence as verification.

That future issue must record the evidence for the gate and make a new
architecture decision before a model, ABI, adapter, or boot path is added.

## Interface audit and claim boundary

At this decision, `LeanOS.Syscall.DecodedCall` contains only map, unmap, and
access-check operations, and unknown syscall numbers reject without changing
state. `LeanOS.SubjectLifecycle.create` only publishes a fresh live identity,
and the composite `createSubject` operation routes that same transition. No
first-party Lean export, generated adapter, boot protocol, or public document
promises fork or ambiguous clone behavior.

This ADR is a scope decision, not a proof that process duplication is safe or
that the audited implementation refines a kernel binary. It adds no trusted
code or trusted assumption.
