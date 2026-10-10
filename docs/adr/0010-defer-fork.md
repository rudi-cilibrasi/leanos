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

## Amendment (2026-10-07): readiness review for explicit spawn (issue #473)

The readiness review the gate requires was carried out in issue #473 against
`main` at the time of the 2026-10-07 roadmap. It covers **explicit spawn with
an empty inheritance set** only; fork and clone stay excluded either way.

### Gate status (2026-10-07)

| Item | Status | Evidence or gap |
| --- | --- | --- |
| 1. One authoritative composite state | **Gap** | `FailStop.CompositeState` holds execution, scheduler, preemption, virtual memory, IPC, capabilities, `SubjectLifecycle`, resumable contexts, transfers, blocking IPC and its contexts, deferred cancels, direct-port I/O, DMA snapshots and invalidation publication. `BoundedLifecycle`'s never-reused issuers and the frame budgets (`FrameBudget`, reached through `FrameBudgetScenario.Runtime` and `CompositeDispatcher` tokens) live outside it. |
| 2. Atomic creation, failure and exhaustion semantics | **Partial** | `BoundedLifecycle.createSubject` publishes a fresh identity atomically, with `createSubject_exhausted_unchanged` and `createSubject_rejected_unchanged`. No parent/child relation, inheritance, cleanup of a partly built child, or budget transfer has any semantics. |
| 3. Enumerated inheritance set | **Met by this amendment** | See the set below. |
| 4. Proof plan | **Gap** | The obligations are named below; none is proved for spawn. |
| 5. Canonical executable encoding with adversarial tests | **Gap** | `CompositeDispatcher.Command.createSubjectOne` (tag 0x0101) is an oracle/boundary command, not a ring-3 syscall. No spawn encoding exists. |
| 6. TCB and model-to-binary gap documented | **Met (unchanged)** | ADR 0001 and the README's trusted-boundary section; ADR 0023 records the first one-export refinement edge, which does not cover spawn. |

### Gate status update (2026-10-09, issue #499)

| Item | Status | Evidence or gap |
| --- | --- | --- |
| 1. One authoritative composite state | **Partial** | `FailStop.CompositeState` now holds the never-reused issuers (`issuers`), the frame commitment (`frameBudgets`), and the frame contents (`scrub`) as projections. `BoundedLifecycle.Runtime`, `FrameBudget.State`, and `FrameScrub.State` are each one projection of it (`lifecycleRuntime`, `budgetState`, `scrubState`), read against the composite's own lifecycle and memory. `LifecycleOperation.createSubject` draws its identity from the composite issuer, is atomic (`issueSubject_exhausted_unchanged`, `issueSubject_rejected_unchanged`), refines `BoundedLifecycle.createSubject` (`issueSubject_refines`), and gives the new subject a zero frame budget (`issueSubject_zero_budget`). `composite_identity_no_reuse` lifts `bounded_identity_no_reuse` to composite traces. The trace may contain only steps proved to keep the combined invariant: issued creation, every operation that writes neither lifecycle nor memory, and capability copy, revocation, transfer, map, and unmap. **Remaining:** that invariant is not yet proved for interrupt cleanup, `syscall`, `resumePreempt`, `protect`, termination, the scheduler steps, the blocking operations, and the deferred drain. The caller-identity `Operation.createSubject` still exists beside the issued path. The composite has no budget-charged memory allocation or release. `CompositeDispatcher`'s frame-budget tokens still denote `FrameBudgetScenario.Runtime`. |

### Gate status update (2026-10-10, issue #499)

| Item | Status | Evidence or gap |
| --- | --- | --- |
| 1. One authoritative composite state | **Partial (model obligations discharged)** | The resource invariant is now proved for every composite step. `authoritativeGate_historyAgrees` and `authoritativeGate_preserves_resourceRuntimeWellFormed` cover every authoritative step other than caller-identity creation, with no premise beyond the combined invariant: interrupt cleanup, `syscall`, `resumePreempt`, `protect`, both terminations, every scheduler step, the blocking operations, and the deferred drain. Termination keeps both issuers, the whole subject history, and every subject's frame usage and limit (`authoritativeGate_termination_accounts`, `authoritativeGate_budget_exact`). Every invalidation entry point but the current-unmap completion keeps the invariant (`InvalidationOperation.apply_preserves_resourceRuntimeWellFormed`). The current-unmap completion needs `CurrentUnmapAdmissible`, which the prepare-then-acknowledge path provides (`currentUnmapAdmissible_of_prepared`). The caller-identity `Operation.createSubject k` is unchanged and keeps the invariant exactly when `0 < k` and `k` is below the subject counter (`authoritativeGate_createSubject_preserves_resourceRuntimeWellFormed`, `authoritativeGate_createSubject_requires_bound`). `CompositeStep` now covers every public transition, and `composite_resource_trace` proves that along every trace of admissible steps the combined invariant holds, no identity is created twice by either path (`issued_never_recreated` for terminated identities), and every subject's budget is exactly conserved. **Remaining, all at the executable boundary or in allocation semantics:** `CompositeDispatcher`'s `createSubjectOne` still runs caller-identity creation from a state whose counter does not cover the identity, and its frame-budget tokens still denote `FrameBudgetScenario.Runtime`. The composite has no budget-charged allocation or release; that is #490. |

### Gate status update (2026-10-10, issue #489)

| Item | Status | Evidence or gap |
| --- | --- | --- |
| 2. Atomic creation, failure and exhaustion semantics | **Partial (spawn met in the model)** | `spawn` is one composite transition (`LeanOS.FailStop.Spawn`). It builds the child on candidate states and commits nothing unless every stage succeeds. Every failure point returns a typed `SpawnError` with the pre-state (`spawn_rejected_unchanged`): missing or stale spawn capability (`spawn_missing_right`, `spawn_stale_spawn_capability`), subject identities exhausted (`spawn_identity_exhausted`), slot table too small (`spawn_slot_table_full`), object identities exhausted (`spawn_address_space_exhausted`), address-space creation rejected, and a stale, malformed, wrong-kind, or ungrantable endpoint (`spawn_stale_endpoint_rejected`). A busy or halted latch rejects with the state unchanged (`spawnGate_unchanged_of_not_running`). The parent/child relation is recorded (`spawn_registry`). **Remaining:** budget transfer and subject-budget exhaustion (#490); cleanup of a terminated child's spawn record (#491). |
| 4. Proof plan | **Partial** | Discharged for the spawn transition: invariant preservation, including `Capability.WellFormed` and the composite and resource invariants (`spawnGate_preserves_resourceRuntimeWellFormed`, built on `installCreatedAddressSpace_preserves_authoritativeRuntimeWellFormed`); inheritance-set exactness (`spawn_child_capabilities`, `spawn_child_authority`); no authority amplification for the parent or any other subject (`spawn_no_authority_amplification`, `spawn_parent_unchanged`); fresh identity (`spawn_fresh_identity`); the empty start (`spawn_child_starts_empty`); and the whole-trace resource theorem with spawn steps (`spawn_resource_trace`). **Not discharged:** confinement of the child over later steps as a spawn-specific theorem (it follows only from the general capability-model results), stale child references across slot reuse (#491), cleanup on child termination, and spawn resource accounting against a parent budget (#490). |
| 5. Canonical executable encoding with adversarial tests | **Partial (hosted Lean oracle only)** | `LeanOS.SpawnOracle` defines the canonical command (tag `0x7001`; `decodeSpawn_encodeSpawn`, `encodeSpawn_decodeSpawn`), injective result codes (`decodeSpawnErrorCode_spawnErrorCode`), and adversarial vectors on the dispatcher's seed for every failure point, both issuer exhaustions, stale and malformed parent handles, a re-granted spawn capability, isolation, the child presenting the parent's handle, and never-reuse after termination (`spawn_vectors_pass`). `NegativeFixtures/SpawnIdentityRollback` forgets to roll back the identity and fails. **Not done:** the command is not in the generated boot dispatcher or its C exports (`boot_dispatcher_rejects_spawn_tag`), and there is no QEMU scenario. |

Items 1, 2, 4, and 5 all remain partial, so the ring-3 spawn syscall stays
gated.

### Spawn readiness decision

The gate is **not met**. Spawn work may proceed only through #489 (explicit
spawn), #490 (spawn resource accounting) and #491 (stale child authority).
These gaps are explicit preconditions of #489, which may not add a ring-3
spawn syscall until they are closed:

1. Lifecycle issuers and frame budgets are folded into
   `FailStop.CompositeState` (or reached from it by one authoritative
   projection) so that spawn is one composite transition (gate item 1).
2. Spawn has atomic semantics: every child component is built or none is,
   exhaustion of identities, slots or budget is a typed rejection with the
   state unchanged, and a failed spawn leaves no partial child (gate item 2).
3. The proof plan below is discharged for the spawn transition (gate item 4).
4. A canonical spawn encoding exists with adversarial oracle vectors for
   partial failure, exhaustion, stale parent handles and isolation
   (gate item 5).

### Inheritance set for explicit spawn

Nothing is inherited implicitly. The child receives exactly:

- **one endpoint capability**, chosen by the parent, attenuated by
  `Capability.copy` from a capability the parent holds with `grant`;
- **a zero frame budget**; any frames come later through an explicit budget
  transfer that #490 accounts for;
- **a clean extended CPU state** (the reviewed reset value);
- **no device authority** (`DeviceCapability.ungranted_subject_no_device_effects`
  then applies to it);
- **no pending IPC**: no queued sends, no waiter entries, no reply
  capabilities;
- **no fault state** and no fault-handler binding;
- **a fresh, never-reused identity** from the lifecycle issuer, with its
  parent recorded only as a parent/child relation, never as authority.

The 2026-10-10 amendment below adds the root capability of the child's own
new, empty address space, which the address-space invariant requires.

### Proof plan for #489

- Spawn preserves `Capability.WellFormed` and the composite invariants.
- No authority amplification: the child's capability space is exactly the one
  attenuated endpoint capability, and the parent's authority does not grow.
- Confinement: the child can affect only what that capability reaches.
- No stale references: a handle to a destroyed child fails, including across
  slot reuse (#491).
- Cleanup: terminating the child releases everything it was given.
- Resource accounting: a parent cannot exceed its subject or frame budget by
  spawning (#490).

Process-creation proposals use the issue template
`.github/ISSUE_TEMPLATE/process-creation.yml`, which requires the enumerated
inheritance set and the proof plan before a model is accepted.

## Amendment (2026-10-10): the spawn capability and the child's address space (issue #489)

### Decision: a new capability kind, not a rights bit

The spawn capability is a capability kind of its own, `SpawnCapability`,
held in the composite projection `CompositeState.spawn` (`SpawnRegistry`),
beside the generic slot registry. This follows ADR 0022, which layers device
capabilities over `Capability.State` the same way. The kernel grants and
revokes it (`SpawnOperation.grantAuthority`, `revokeAuthority`); subjects
cannot copy, transfer, or derive it. Each grant has a never-reused
`generation`, and a spawn presents that generation word, so a revoked and
re-granted spawn capability rejects the old word.

A rights bit was rejected. None of the three object kinds (`memory`,
`addressSpace`, `endpoint`) denotes the authority to create subjects, so the
bit would have no natural object. Adding a field to `Capability.Rights` would
also change `rightsSubset`, every rights literal, every delegation proof, and
the generated C of every boot module that handles capabilities. A new
`ObjectKind` was rejected for the same blast radius and because it would need
a kernel object with its own lifetime. A separate kind keeps spawn authority
out of delegation entirely, which is what #490 needs to attach a per-parent
subject budget to it later.

### Clarification of the inheritance set: the address-space root

The 2026-10-07 inheritance set gives the child "one endpoint capability" and
nothing else. The composite cannot also give the child an owned address
space under that wording: `VirtualMapping.LifecycleWellFormed` requires the
owner of every live address space to hold `revoke` over it. The child
therefore also receives the root capability of **its own new, empty address
space** (rights `{grant, revoke}`, exactly what `VirtualMapping.createAddressSpace`
installs). Over every object that existed before the spawn, the child's
authority is exactly the granted endpoint with the requested rights
(`spawn_child_authority`). This changes the enumerated set, so a reviewer
must accept it before #489 is closed.

### What the model does not yet give the child

- **A schedulable address space.** The scheduler admits a subject only when
  it owns the address space whose identifier equals its subject identifier.
  The child's address space comes from the object issuer, which is a
  different counter. The child is also not runnable, and no code is loaded.
  Admission belongs with the loader issue.
- **Extended CPU state, device authority, and fault-handler binding.** These
  live in models outside `CompositeState` (`ExtendedState`,
  `DeviceCapability`, `FaultHandler`). The child has no saved context of any
  kind, so its first context will be the reviewed reset value. The composite
  device projections are unchanged by spawn, and the child holds no device
  capability because it holds no capability other than the two above.
