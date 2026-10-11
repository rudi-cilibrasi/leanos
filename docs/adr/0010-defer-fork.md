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

### Gate status update (2026-10-10, issues #490 and #491)

| Item | Status | Evidence or gap |
| --- | --- | --- |
| 1. One authoritative composite state | **Partial** | The child table, the subject budget, and the control-generation counter are part of `CompositeState.spawn`, and frame slices and their return are composite transitions on the frame commitment (`grantFrames`, `terminateChild`). The whole-trace theorem covers them: along every admissible trace of composite steps and public spawn-family steps, both invariants hold, the allocator is exact, and no frame is newly committed (`child_resource_trace`). **Remaining:** the composite still has no budget-charged memory allocation or release, so no composite step changes a subject's usage; `CompositeDispatcher`'s frame-budget tokens still denote `FrameBudgetScenario.Runtime`. |
| 2. Atomic creation, failure and exhaustion semantics | **Met in the model** | The public spawn family (`ChildOperation`, `childGate`) adds the two missing pieces. Subject-budget exhaustion (`spawnCharged_subject_budget_exhausted`), frame-budget exhaustion (`grantFrames_frame_budget_exhausted`), and control-generation exhaustion (`spawnCharged_control_generation_exhausted`) are typed rejections with the pre-state, as is every other rejection of the family (`ChildOperation.apply_rejected_unchanged`, `childGate_unchanged_of_not_running`). Budget transfer moves frames between parent and child exactly (`grantFrames_limits`), and child termination removes the child's spawn records and child-table entry (`terminateChild_releases`). The executable boundary is item 5. |
| 4. Proof plan | **Partial** | Newly discharged: no stale references (`terminateChild_retires`, `retired_rejected_unchanged`, `stale_control_after_respawn`, and across every later step `child_resource_trace`; for capabilities `terminateChild_revokes`, `terminateChild_stale_word`, `stale_word_after_respawn`); cleanup on termination (`terminateChild_releases`); resource accounting (`ChildAccountingWellFormed`, kept by `childGate_preserves` and `CompositeStep.childAccounting`; `usage_add_childLimits_le`; `child_resource_trace`). **Not discharged:** confinement of the child over later steps as a spawn-specific theorem; capability-word staleness after arbitrary later steps (it is proved across the termination and a following spawn); and nested cleanup, since terminating a child does not terminate or reclaim the child's own children. |
| 5. Canonical executable encoding with adversarial tests | **Partial (hosted Lean oracle only)** | `LeanOS.SpawnAccountingOracle` runs `childGate` from command words: charged spawn (`0x7001`), frame grant (`0x7101`), and child termination (`0x7201`), with canonical encodings (`encodeGrant_decodeChild`, `encodeTerminate_decodeChild`) and injective result codes (`childErrorCodes_injective`). `child_vectors_pass` covers both exhaustions, a grant and its return, release on termination, stale control words after termination and after slot reuse, a stale parent capability over the child's address space, and isolation; every `SpawnOracle` vector gives the same result through it. `NegativeFixtures/SpawnAccounting` (budgetless spawn, minting grant, charge-keeping termination) fails. **Not done:** the commands are not in the generated boot dispatcher (`boot_dispatcher_rejects_child_tags`). The QEMU scenario of #491 is blocked by this gate: it needs spawn in a booted image, which only the gated syscall would give. |

Items 1, 4, and 5 remain partial, so the ring-3 spawn syscall stays gated.

### Gate status update (2026-10-10, gate items 1 and 4)

| Item | Status | Evidence or gap |
| --- | --- | --- |
| 1. One authoritative composite state | **Met in the model** | The composite now allocates and releases memory against the frame budgets it holds. `MemoryOperation` (`allocate`, `release`), run by `memoryGate` under the running latch, charges an allocation to a free frame committed to the acting subject (`allocateMemory_charges`), scrubs the frame before publication (`allocateMemory_fresh`), and on release retires the object everywhere and scrubs its frame (`releaseMemory_retires`, `releaseMemory_returns`). Both keep the combined invariant (`memoryGate_preserves`, built on `installAllocatedMemory_preserves_authoritativeRuntimeWellFormed` and `installReleasedMemory_preserves_authoritativeRuntimeWellFormed`), declare footprints that pass the frame rule and the read-set check (`memoryGate_frames`, `memoryGate_reads`), reject with the pre-state (`MemoryOperation.apply_rejected_unchanged`), including a full budget (`allocateMemory_frame_budget_exhausted`, `allocateMemory_full_rejected`) and exhausted object identities (`allocateMemory_object_identity_exhausted`), and are exactly `FrameBudget.allocate` and `FrameBudget.release` on the budget projection (`allocateMemory_refines`, `releaseMemory_refines`). Memory steps are in the whole-trace theorem (`child_resource_trace`, `ChildTraceStep.memory`). Caller-identity `createSubjectOne` is admissible on every dispatcher-reachable token in the dispatcher's resource view, the same states with the subject counter at 2, which no authoritative step reads (`authoritativeGate_resourceView`, `dispatcher_createSubject_admissible`, `dispatcher_resource_trace`); the dispatcher, its `initialState`, and its generated C are unchanged. **At the executable boundary (item 5):** `CompositeDispatcher`'s frame-budget tokens still denote the standalone `FrameBudgetScenario.Runtime`, whose allocate and release steps are the standalone model that the composite refines. |
| 4. Proof plan | **Met in the model** | Every obligation of the proof plan is discharged for the public spawn family together with the memory family. *Invariant preservation* and *resource accounting*: `child_resource_trace` (all three invariants, usage within limit, no frame created, subject budgets, entitlement bounds). *No amplification*: `spawn_no_authority_amplification`, `spawn_parent_unchanged`. *Confinement*: when the child acts, every operation of its syscall surface that does not designate an observer leaves the whole view of every subject sharing no object with the child unchanged, for one step and along runs (`child_step_confined`, `child_run_confined`); right after spawn the child names exactly the granted endpoint and its own address space (`spawn_child_names`, `spawned_child_confined`); its memory allocations are invisible to every other subject (`memory_allocate_confined`). *Stale references*: control words (`child_resource_trace`) and capability words naming the child or its objects stay unresolvable along every later trace of composite, spawn-family, and memory steps (`stale_word_forever`, from per-step identity provenance `CompositeStep.identityStep`, `childGate_identityStep`, `memoryGate_identityStep`). *Cleanup*: a child never holds spawn authority and never has children (`SpawnTreeWellFormed`, `charged_child_childless`, `child_spawn_rejected`), so terminating it orphans nothing (`terminateChild_no_orphans`); termination now also frees and scrubs the frames of the child's memory (`reclaimChildFrames_reclaims`) and releases everything it was given (`terminateChild_releases_everything`). **Stated exclusions of confinement** (`LeanOS.SpawnConfinement`): the public scheduler choice (a blocking receive that blocks), operations that designate the observer as a delegation destination or revocation victim, and `capabilityRevokeSubtree` and memory release, which retire derived authority wherever it went; timing and caches are not modeled. |

Items 1 and 4 are met in the model. Item 5 remains partial, so the ring-3
spawn syscall stays gated.

### Gate status update (2026-10-10, gate item 5)

| Item | Status | Evidence or gap |
| --- | --- | --- |
| 1. One authoritative composite state | **Met** | The executable-boundary caveat of the previous row is closed by a refinement. `LeanOS.FrameBudgetComposite` gives every frame-budget token (`0x4001`–`0x4b01`) a composite denotation replayed by composite gates (`memoryGate` allocation and release, the authoritative timer switch, authoritative termination, an authoritative map syscall) and proves a forward simulation for every edge (`budget_tokens_simulated`): the composite successor is the counterpart step (`compositeOf_edge`), its typed result is the edge's reply (`counterpart_matches_reply`), and the budget view (current subject, live subjects, each live subject's usage and limit) agrees at every token (`views_agree`); on the budget projection the composite steps are exactly `FrameBudget.allocate` and `FrameBudget.release` (`allocateMemory_refines`, `releaseMemory_refines`). The generated table and the QEMU frame-budget image are unchanged. **Stated difference:** the standalone `FrameScrub` state of that fixture, like its QEMU image, reuses A's physical frame for B after A's termination; the composite frees frames across subjects only through child termination, and keeps a terminated non-child's frame charged to it, which no live subject can allocate in either model. |
| 5. Canonical executable encoding with adversarial tests | **Met** | The spawn family is in the boot-compiled dispatcher (`leanos_composite_dispatch`, adapter 18) as eighteen state tokens (`0x7001`–`0x8101`) and 49 edges with the hosted oracles' tags `0x7001`, `0x7101`, `0x7201`, the memory tags `0x7301` and `0x7401`, and four bounded-boundary tags (kernel grant and revocation of spawn authority, timer switch, capability copy) (`LeanOS.SpawnBoundary`). *Canonical encoding:* `decodeFamily_encodeFamily`, `encodeFamily_decodeFamily`, `decodeState_encodeState`, and the reply decoding in `edges_dispatch`; the status byte and value word are the hosted oracles' (`edges_match_hosted_oracle`). *Refinement:* every edge is exactly one `childGate`, `memoryGate`, or authoritative step on the complete state its token names (`edge_refines`, `dispatcher_refines`), and every token satisfies the whole-trace theorem from a seed proved to satisfy the combined invariant (`spawn_boundary_trace`, `familySeed_resourceRuntimeWellFormed`). *Adversarial tests:* partial failure and rollback at every reachable spawn failure point, the frame grant, the memory family, and the kernel grant, each a stutter of the complete state (`rejected_edge_unchanged`); exhaustion of the subject budget, the frame budget, subject and object identities, and control generations; stale control words before and after child-table slot reuse and a stale memory handle after slot reuse; isolation of the child and of the bystander subject; termination cleanup with the returned frame allocated again on a scrubbed frame under a fresh identity (`boundary_checks_pass`); and 14 hostile encodings rejected before any gate (`spawn_negative_vectors_reject`). *Generated-C replay:* the 63 vectors are in the oracle corpus (627 vectors), replayed against the generated C by `check-oracle-host.sh` (ordinary and sanitized) and by every normal image's boot-time oracle replay under QEMU; `spawn_edge_vectors_match_model` ties each expected word to the model step. **Scope:** the boundary is a bounded table, not a general decoder; the slot-table-full and identity-rejection failures need seeds the table does not name and are covered by the hosted `SpawnOracle` vectors; reclamation of memory a child allocated itself is proved (`terminateChild_releases_everything`) but not exercised, since a child cannot run before a loader exists. |

All six items are met for explicit spawn with the enumerated inheritance set.
The architecture decision the gate requires is the amendment below.

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

## Amendment (2026-10-10): spawn accounting and child control handles (issues #490 and #491)

### The subject budget is carried by the spawn capability

`SpawnCapability.subjectBudget` is the most children its holder may have
charged to it at once. The kernel names it when it grants the capability
(`ChildOperation.grantAuthority subject budget`). The grant is rejected if
the budget exceeds the child table or the subject already has more children.
Revoking the capability does not kill the children; they stay charged to the
parent until it terminates them.

### Children are recorded in a per-parent child table

Each parent has a fixed kernel table of 64 slots
(`CompositeState.spawn.children`). An entry names the child, the generation
of the parent's control handle for it, and the frames the parent has charged
to it. Generations come from a never-reused counter. The parent names a
child only by its control word, a `CapabilityHandle` word of the slot and the
generation. A cleared or reused slot never matches an old word. The table is
the authority for the two child operations; `spawn.parent` and
`spawn.addressSpace` stay records only.

### Frames given to a child are a slice of the parent's budget

A frame grant commits some of the parent's free committed frames to the
child and adds them to the entry's charge. No frame is created, and no other
subject's commitment changes. Child termination commits every frame of the
child back to the parent. The accounting is hierarchical: each child's own
frames plus what it charged to its children stay within the charge its
parent recorded.

### The public spawn family

`ChildOperation` (`spawn`, `grantFrames`, `terminateChild`,
`grantAuthority`, `revokeAuthority`), run by `childGate`, is the family the
executable boundary uses. `SpawnOperation` and `spawnGate` from #489 remain
the unaccounted core that the charged spawn wraps.

### What this does not do

- It adds no budget-charged memory allocation or release to the composite.
- Terminating a child does not terminate the child's own children.
- It adds no syscall, no boot-dispatcher command, and no QEMU scenario.

## Amendment (2026-10-10): budget-charged memory, one-level spawn, and complete child cleanup (gate items 1 and 4)

### Memory is allocated against the composite budgets

`MemoryOperation` is a separate family, like `LifecycleOperation` and
`ChildOperation`, so `Operation` and `applyOperation` are unchanged. The
acting subject is the current subject of the execution latch; no command word
names the charged subject, the frame, or the object identity. Allocation
takes the object issuer's next identity and the first free frame committed to
the actor (`FrameBudget.firstAvailable` on the budget projection), scrubs the
frame, and publishes the object with a root capability in the actor's slot.
It also requires that the lifecycle attributes the frame to no one, so no
stale ownership record can be overwritten (`frameUnavailable`). Release
follows `MemoryLifecycle.release`: a memory capability with `revoke`, the
object's current binding and allocator owner, and the actor recorded as the
owner. It retires the object everywhere: every capability naming it in every
slot, every mapping of it, every pending sealed transfer carrying it, and
every cached translation (the full flush subject cleanup uses). The frame is
then free and scrubbed, and the identity stays issued.

### Spawn authority is held only outside child tables

The public grant (`grantBudgetedAuthority`) now refuses a subject recorded as
a spawned child. Spawn never passes spawn authority to the child, so no child
ever holds it and no child ever has children (`SpawnTreeWellFormed`). The
spawn tree of a parent is one level deep, and child termination is its whole
cleanup. Nested spawn is a later decision; it would need cascading
termination and reclamation through the child's table.

### Child termination reclaims the child's memory

Composite termination retires every memory object the terminated subject
owned but leaves its frame allocated. Child termination now frees, unbinds,
and scrubs every frame committed to the child that backs a dead object
(`reclaimChildFrames`) before the child's frames return to the parent. A frame
backing a live object is never reclaimed (`not_reclaimable_of_live`).

### The dispatcher's caller-identity creation

`CompositeDispatcher` replays `createSubject 1` from `bootRuntime`, whose
subject counter is 1, so the step is outside `CompositeStep.Admissible`.
Rather than change the dispatcher's seed, and with it the generated boot C,
`LeanOS.CompositeDispatcherResources` reads every dispatcher state with the
subject counter at 2. No authoritative step reads or writes the issuers, so
the dispatcher's states and these views differ only in that counter, and the
whole dispatcher path is an admissible composite trace from a seed satisfying
the combined invariant.

## Amendment (2026-10-10): the ring-3 spawn syscall may be added (issue #489)

### Evidence for the gate

Every gate item is met for explicit spawn with the enumerated inheritance set
(the 2026-10-07 set as clarified by the 2026-10-10 address-space amendment):

1. One authoritative composite state: the 2026-10-10 rows for gate items 1
   and 4 and for gate item 5 (`child_resource_trace`, `memoryGate_preserves`,
   `budget_tokens_simulated`).
2. Atomic creation, failure, and exhaustion semantics: the row for issues
   #490 and #491 (`ChildOperation.apply_rejected_unchanged`, the three
   exhaustion theorems, `terminateChild_releases_everything`).
3. The enumerated inheritance set: the 2026-10-07 amendment and the
   address-space clarification (`spawn_child_capabilities`,
   `spawn_child_authority`).
4. The proof plan: the row for gate items 1 and 4 (confinement, stale words
   along every later trace, no nested children, complete cleanup).
5. The executable boundary: the row for gate item 5 (`LeanOS.SpawnBoundary`,
   the 627-vector corpus replayed against the generated C, hosted and booted).
6. The trusted computing base and model-to-binary gap: ADR 0001, the README's
   trusted-boundary section, and ADR 0023. The generated dispatcher, its C,
   the compiler, and the QEMU replay remain trusted integration evidence, not
   verification of the binary.

### Decision for #489

The readiness decision of 2026-10-07 ("the gate is not met") is superseded
for explicit spawn. Issue #489 may add a ring-3 spawn syscall, under these
conditions:

- The syscall decodes exactly the canonical words of the spawn family:
  spawn (`0x7001`), frame grant (`0x7101`), and child termination (`0x7201`)
  with `decodeChild`, and memory allocation and release (`0x7301`, `0x7401`)
  if it exposes them, with `decodeFamily`. A word sequence that does not
  decode is rejected before any gate runs.
- Each decoded command runs exactly `childGate` or `memoryGate` with the
  latch's current subject as the actor; no word names the parent, the
  child's identity, a frame, or an object identity.
- The kernel grant and revocation of spawn authority (`0x7501`, `0x7601`),
  the timer switch (`0x7701`), and the capability copy (`0x7801`) are
  commands of the bounded dispatcher only. They are not syscalls: spawn
  authority stays a kernel-granted capability kind.
- The syscall's adapter joins the hosted generated-boundary replay with the
  spawn family's vectors, and the result words keep the hosted oracles'
  status codes and value words.
- The child stays unschedulable until a loader issue decides admission and
  code loading; a spawned child holds no spawn authority (one-level spawn).

Fork, clone, and any operation with implicit inheritance stay excluded; this
decision does not reopen them.
