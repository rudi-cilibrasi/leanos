# Fatal exception fail-stop model

`LeanOS.FailStop` is the authoritative composite execution latch around the
interrupt classifier. Its modes are `running`, `handling` a kernel-owned active
entry, and `halted` with a typed record. Entry and completion are explicit. A
normal syscall entry classification, timer event, incoming wrong-origin
rejection, or contained CPL3 page fault returns to `running`; the contained
fault still atomically applies the existing whole-subject cleanup policy.
Outgoing user return is a distinct `completeUserReturn` transaction: validation
failure records its purpose and reason, freezes every composite subsystem, and
enters the same absorbing halt gate. Kernel page faults and unsupported vectors
also halt.
The kernel-owned SMAP copy override is cleared on every entry and remains clear
after a fatal transition, so an interrupted diagnostic or copy window cannot
leak privileged access into a later context.

The bounded escalation policy models a page fault raised while handling a page
fault as a double fault. Every other exception during handling is forbidden
nested entry and halts. This is deliberately not Intel's complete exception
combination table. The halt record publishes only the reason, the kernel-owned
active entry, and incoming vector/origin diagnostics. Lifecycle, capabilities,
mappings, scheduler identity, saved context, mailbox, and resources remain the
pre-fault `core`; fatal atomicity proves that freeze.

Vector 2 has a separate terminal path. `dispatchNmi` consumes only the exact
accepted `InterruptEntry.normalizeNmi` result (or retains its typed rejection),
and is admitted from both `running` and every `handling` state. It never calls
ordinary entry completion, user-fault containment, scheduling, CR3/return
selection, or an operation-specific handler. An accepted NMI records the
prior mode plus the trusted normalized origin, active CR3, and IST2 identity;
it preserves the current subject/address-space/kernel-stack projection and
clears both return authority and the SMAP copy override. The composite theorem
freezes every business subsystem and absorbs all later operations.

Before the runtime IDT exists, the separate finite
[`LeanOS.BootInterruptPhase`](interrupt-model.md) contract owns dispatch: every
admitted bootstrap-phase event latches its own absorbing terminal record with
a bounded boot-phase reason, preserves the not-yet-published business state,
arms no return authority, and absorbs every later publication or event. That
early latch composes with, and never weakens, the runtime execution latch
described here; the runtime phase delegates unchanged to this model. Both
bootstrap latches now have demonstrated machine executions: the mandatory
`bootstrap32-ud` and `bootstrap64-nmi` evidence rows drive a real pre-paging
`ud2` and one monitor-injected masked-window NMI onto the pinned early
terminal stubs, which stop the guest with their phase-typed debug exits
without reaching the runtime IDT, ordinary C, or any business state.

If the state is already halted, another modeled NMI returns the identical
record and cannot manufacture a later snapshot. This sequential rule assumes
that a second physical NMI is blocked until architectural NMI return; no such
return exists in the model. It is not a statement about arbitrary machine
instruction interleavings or partially committed implementation mutations.

The composite state places scheduler/preemption, syscall virtual memory, IPC,
capability, mapping, and subject-lifecycle state under the same execution latch.
It also retains the boot-accepted PCI snapshot and latest authoritative control
observation; their exact DMA quarantine agreement is a conjunct of
`RuntimeWellFormed`. Trusted live PCI re-observation cannot become an ordinary
rejection: invalid or changed control state latches a typed DMA fatal record,
after which the ordinary composite gate absorbs every suffix.
`Operation` carries each subsystem's typed inputs, and `gate` invokes the real
subsystem transition internally; callers cannot supply an arbitrary post-state.
Once halted it returns the identical composite state and rejects every
operation. `halted_terminal_non_resumption` proves this for one composite step,
and the absorption theorem extends it to arbitrary typed operation suffixes, so
neither a CPL3 return nor an accepted mutation or trusted context restoration
can occur.
Attacker registers are absent from active-entry identity and cannot change
classification, escalation, diagnostics, or the terminal latch. A kernel fault
cannot be classified as user containment.

Executable examples cover valid syscall return, contained user page fault,
timer delivery, kernel fault, unsupported vector, modeled double fault,
attempted restart, and attempted syscall/timer/IPC/lifecycle operations after
halt. A negative theorem
exhibits why the previous action-only fatal result was insufficient: its
unchanged state could immediately accept a valid syscall return.

## Module layout

`import LeanOS.FailStop` still provides the whole model under the
`LeanOS.FailStop` namespace with unchanged declaration names, but the source is
split by subsystem into `LeanOS/FailStop/*.lean` (issue #499). Most modules
form one import chain, in this order:

| Module | Contents |
| --- | --- |
| `Latch` | Execution latch, ordinary and NMI entry, user-return transaction |
| `Composite` | `CompositeState`, its named projections, `RuntimeWellFormed`, boot runtime |
| `BlockingIPC` | Blocking receive, send, cancel, and the typed blocking gate |
| `Operations` | Publication helpers, `Operation`, `applyOperation` |
| `Footprint` | `Operation.footprint`, helper frame lemmas, `applyOperation_frames`, `AgreeOn` |
| `Gate` | `operationReply`, the ordinary `gate`, DMA control observation |
| `IPC` | Accepted user-return, IPC, and sealed-transfer slices |
| `Capabilities` | Capability copy, revocation, and subject creation slices |
| `Memory` | Map, unmap, protect slices, and `runOperations` |
| `OperationRegistry` | Per-operation runtime-preservation registry |
| `Scheduler` | Termination cleanup and scheduler families |
| `Faults` | Resumable preemption and interrupt preservation |
| `DeferredBlocking` | Runtime trace inventory and deferred blocking invariant |
| `AuthoritativeGate` | `authoritativeGate`, its footprints, invalidation publication and its footprints |
| `AuthoritativeTraces` | Blocking slices, admissibility, and authoritative traces |
| `Evidence` | Executable regressions and the dispatcher's initial states |

Twenty modules branch off the chain and build in parallel with it:

| Module | Imports | Contents |
| --- | --- | --- |
| `ProjectionInvariants` | `Gate` | `ProjectionInvariant`, `RuntimeWellFormed` split by projection |
| `ReadSets` | `AuthoritativeGate` | Read-independence theorems for every gate family |
| `Resources` | `ReadSets`, `AuthoritativeTraces` | Issuers, frame budgets, frame contents, and issued subject creation |
| `ResourceSteps` | `Resources` | Resource invariants for every composite step and whole traces |
| `SpawnAddressSpace` | `Resources` | Composite creation of an empty address space and its invariant preservation |
| `MemoryAllocation` | `SpawnAddressSpace` | Composite publication of an allocated memory object and its invariant preservation |
| `MemoryRelease` | `MemoryAllocation` | Composite publication of a released memory object and its invariant preservation |
| `MemoryOperations` | `MemoryRelease` | The memory family: budget-charged allocation and release with scrub, gate, footprints, read sets, exhaustion, refinement of `FrameBudget` |
| `Spawn` | `SpawnAddressSpace` | Explicit spawn (#489), the spawn family and gate, rollback |
| `SpawnInvariants` | `Spawn`, `ResourceSteps` | Spawn keeps the combined invariant |
| `SpawnAuthority` | `SpawnInvariants` | Inheritance-set exactness, no amplification, fresh identity, empty start |
| `SpawnTraces` | `SpawnAuthority` | Whole traces that may spawn |
| `SpawnAccounting` | `SpawnAuthority` | Charged spawn, child control handles, frame slices, child termination (#490, #491) |
| `SpawnAccountingInvariants` | `SpawnAccounting` | The spawn accounting invariant and its preservation |
| `SpawnChildCleanup` | `SpawnAccountingInvariants` | Stale control words and capabilities after child termination; cleanup |
| `SpawnTree` | `SpawnChildCleanup`, `MemoryOperations` | Children never have children; complete cleanup on child termination |
| `SpawnAccountingTraces` | `SpawnTree` | Whole traces of the public spawn family and the memory family |
| `CapabilityIdentities` | `SpawnAccounting` | Capability-identity provenance (`IdentityStep`), retired identities, stale words |
| `CapabilityIdentitySteps` | `CapabilityIdentities`, `SpawnChildCleanup` | Identity provenance of every composite and spawn-family step |
| `SpawnGate` | `SpawnAccountingTraces`, `CapabilityIdentitySteps` | Identity provenance of memory steps and whole traces; stale words along every later trace |

`AuthoritativeGate` imports `ProjectionInvariants` as well as
`DeferredBlocking`. No module exceeds about 3,500 lines. Helpers that a later
module uses are public declarations in the same namespace; the remaining
helpers stay private to their module.

## Footprints and the frame rule

Every typed `Operation` declares a footprint using the
`LeanOS.CompositeFootprint` vocabulary: the projections of `CompositeState` it
reads and the subset it may write (`Operation.footprint`). The blocking
operations (`CompositeBlockingOperation.footprint`) and the deferred drain
complete the declaration for every `AuthoritativeOperation`. The
conditional invalidation-publication entry points
(`authoritativePrepare*`, `authoritativeAcknowledge*`, and
`authoritativePublishReuse`) are not gate constructors; `InvalidationOperation`
names each of them, and `InvalidationOperation.footprint` declares their
footprints. Preparation, acknowledgement, and reuse write only
`invalidationPublication`. `prepareCurrentUnmap` also reads `execution`, and
the active `acknowledgeCurrentUnmap` completion also republishes the mapping
projections. Footprints are built with `Footprint.ofLists`, so writes are reads
by construction. Named groups such as `publicationProjections`,
`cleanupProjections`, and `mappingProjections` name the projections that one
publication helper republishes together.

### Write sets: the frame rule

The frame rule `applyOperation_frames` proves that every projection outside
an operation's write set is literally unchanged. `gate_frames`,
`blockingGate_frames`, and `authoritativeGate_frames` extend it to every gate
outcome, including busy and halted stutters, and
`InvalidationOperation.apply_frames` covers the invalidation-publication entry
points on accepted and rejected outcomes alike. The proof is assembled from one
frame lemma per publication helper, such as `installLifecycle_frames` and
`installTransfers_frames`. Each helper lemma is discharged by the
`composite_frame` tactic, which case-splits the finite projection vocabulary,
so the per-operation proof never names a projection.

### Read sets: read independence

Read sets are machine-checked too. `CompositeState.AgreeOn support left right`
says that two states agree on every projection in `support`. The
read-independence theorems in `ReadSets` say that two states that agree on an
operation's declared reads produce the same reply and post-states that agree on
its declared writes:

- `applyOperation_reads` and `operationReply_reads` for every `Operation`.
- `gate_reads`, `blockingGate_reads`, and `authoritativeGate_reads` for the
  gates. The gates also read the latch mode, which is a premise.
- `applyBlockingOperation_reads`, `drainDeferredCancellation_reads`, and
  `applyAuthoritativeOperation_reads` for the blocking families.
- `InvalidationOperation.apply_reads` for the invalidation-publication entry
  points. It also proves that acceptance and the requested machine effect
  depend only on the declared reads.

With the frame rule, the declared footprint therefore determines the whole
post-state. Written projections are a function of the read projections, and
every other projection is unchanged.

Each proof destructures both states and identifies every field covered by the
agreement hypothesis with the `agree_subst` tactic. Branch conditions over
agreed projections are then syntactically shared, so one `split` decides each
of them for both states. A read missing from a declaration leaves a branch
condition or a written value that mentions an unshared field, and the proof
fails. Three state-wide helpers are first rewritten into forms over their
projections: `returnPlanLiveOf`, `selectLiveExecution`, and
`liveReturnExecution`. Helpers whose result carries a whole state get their own
read lemmas: `dispatchIPC_reads`, `restoreBlockingPeer_reads`, and
`publishReleasedBlockingContext_reads`.

### Invariants by projection

A `ProjectionInvariant` (module `ProjectionInvariants`) is one conjunct of a
composite invariant together with its support, the projections it reads. Its
`dependsOn` field proves that the conjunct reads nothing else. These theorems
connect conjuncts to the frame rule:

- `ProjectionInvariant.preserved_of_frames`: a transition whose write set
  misses the support preserves the conjunct, by the frame rule alone.
- `ProjectionInvariant.All.preserved_of_frames`: a transition preserves a list
  of conjuncts once each *touched* conjunct is proved. Whether a conjunct is
  touched (`untouchedBy`) is a closed Boolean computation on the declared
  footprint.

`runtimeInvariants` splits `RuntimeWellFormed` into 14 supported conjuncts:
coherence, one well-formedness conjunct per subsystem, halt agreement, return
plan liveness, blocking coherence, and the direct-port/DMA authority.
`runtimeWellFormed_iff_all` proves that the split is exact.
`authoritativeInvariants` adds the deferred-cancellation and publication
conjuncts, and `authoritativeRuntimeWellFormed_iff_all` proves that split
exact. The lifting is used in these places:

- `gate_preserves_authorityInvariant`: every gate step keeps the authority
  conjunct.
- The `authoritativePrepare*`, `authoritativeAcknowledge*`, and
  `authoritativePublishReuse` preservation theorems prove only the publication
  conjunct, through `authoritativeRuntimeWellFormed_preserved_of_publicationFrames`.
  The other 15 conjuncts are lifted.
- `InvalidationOperation.preserves_runtimeWellFormed`: every entry point
  except `acknowledgeCurrentUnmap` keeps `RuntimeWellFormed` and the
  deferred-cancellation classification without inspecting the protocol.
- The authoritative gate's publication preservation is lifted from
  `authoritativeGate_frames`. It replaced four retention lemmas.

Theorems about projections that an operation does not write are lifted rather
than re-proved:

- `applyOperation_project_untouched` reads one untouched projection.
- `applyOperation_preserves_of_dependsOn` and `gate_preserves_of_dependsOn`
  preserve any predicate that depends only on untouched projections
  (`CompositeState.DependsOn`).
- `applyOperation_directPortIO`, `applyOperation_dmaAccepted`,
  `applyOperation_dmaObserved`, `gate_preserves_dmaQuarantined`,
  `authoritativeGate_dmaAuthority`, and the invalidation-publication retention
  lemmas are corollaries of the frame rule.

### Adding a projection

1. Add the field to `CompositeState`, the constructor to
   `CompositeFootprint.Projection`, and one case each to
   `CompositeProjectionType` and `CompositeState.project`. Add one line each
   to the `agree_subst` tactic and to `CompositeState.eq_of_agreeOn_all`.
2. Add the projection to the read and write lists of each operation that reads
   or changes it.
   - For every other operation, the helper frame lemmas re-check the new case
     by unfolding, and `applyOperation_frames` is unchanged.
   - The read-independence proofs are unchanged too. An unread projection is
     simply not identified by `agree_subst`, and nothing written depends on
     it.
3. State the new projection's invariant as a `ProjectionInvariant` whose
   support names the projections it reads. Use `projection_depends_on` to
   prove `dependsOn`.
4. Strengthen the invariant by adding the conjunct to a list such as
   `authoritativeInvariants`, rather than adding a positional conjunct to
   `RuntimeWellFormed`. For every operation whose write set misses the new
   support, `ProjectionInvariant.All.preserved_of_frames` discharges the new
   conjunct, so its existing preservation proof is unchanged. Only the
   operations that write the support need a new proof.

**What is still whole-state.** `RuntimeWellFormed` itself remains a
positional conjunction. About 60 existing per-operation preservation proofs
destructure it by position, such as `hstate.2.2.2.2.1`. `runtimeWellFormed_iff_all`
lets new proofs work per conjunct, and lifts the untouched conjuncts. The
existing proofs have not been rewritten into that form, so inserting a
conjunct *into* `RuntimeWellFormed` would still touch them. That is why step 4
adds conjuncts to a list instead.

### Lifecycle issuers, frame budgets, and frame contents

Before issue #499 these lived outside `CompositeState`. The issuers were in
`BoundedLifecycle.Runtime`. The budgets and scrub state were in
`FrameBudgetScenario.Runtime`, reached through `CompositeDispatcher` state
tokens. #536 wrote a four-step plan for bringing them in. Steps 1 to 3 are now
done, in a narrower form than written. Step 4 is not done. The modules are
`Resources` (the projections, issued creation, and the steps covered by the
frame rule) and `ResourceSteps` (every other step and whole traces).

**Step 1: three new projections.** `CompositeState` has three new fields, each
with a default:

- `issuers` (`LifecycleIssuers`): the subject and object `LifetimeIssuer`s.
- `frameBudgets` (`FrameBudgets`): the fixed frame commitment of
  `FrameBudget.State`.
- `scrub` (`FrameContents`): the frame bytes and lifetime write flags of
  `FrameScrub.State`.

The budgets and contents have no memory of their own. Each subsystem state is
one projection of the composite, read against the composite's own lifecycle
and virtual memory: `lifecycleRuntime`, `budgetState`, and `scrubState`. There
is therefore still one physical-ownership model.

No existing operation declares a read or write of the new projections. The
following theorems check that by evaluating the footprints:

- `Operation.footprint_unread_resources`
- `AuthoritativeOperation.footprint_unread_resources`
- `InvalidationOperation.footprint_unread_resources`

`authoritativeGate_resources` and `InvalidationOperation.apply_resources`
follow from the frame rule. Every existing frame, read-independence, and
preservation proof was left unchanged. The only edits were one line each in
`agree_subst` and `CompositeState.eq_of_agreeOn_all`.

**Step 2: invariants.** `resourceInvariants` lists four `ProjectionInvariant`
conjuncts. `ResourceWellFormed` is their conjunction, and
`ResourceRuntimeWellFormed` adds `AuthoritativeRuntimeWellFormed`
(`resourceRuntimeWellFormed_iff_all`).

| Conjunct | Support | Says |
| --- | --- | --- |
| `issuersInvariant` | `issuers` | Both counters are at most the reserved terminal identity |
| `issuerAgreementInvariant` | `issuers`, `lifecycle`, `virtualMemory` | Every issued subject identity, and every identity in either object history, is positive and below its counter |
| `budgetAgreementInvariant` | `frameBudgets`, `lifecycle`, `virtualMemory` | Every committed frame is a modeled, unreserved allocator frame, committed to an issued subject |
| `scrubInvariant` | `scrub`, `virtualMemory` | `FrameScrub.ScrubInvariant` over the composite memory |

The conjuncts are a separate list and are not added to `authoritativeInvariants`,
so no existing `AuthoritativeRuntimeWellFormed` proof changes. Which steps keep
`ResourceWellFormed` is proved as follows:

- **By the frame rule alone** (`authoritativeGate_preserves_resourceWellFormed_of_framed`):
  every authoritative operation that writes neither `lifecycle` nor
  `virtualMemory`. `resourceFramed_ordinary` lists them: IPC, NMI, return
  selection and return, queue admission, and restart. The invalidation entry
  points other than `acknowledgeCurrentUnmap` qualify as well
  (`InvalidationOperation.apply_preserves_resourceWellFormed`).
- **By history agreement**
  (`authoritativeGate_preserves_resourceWellFormed_of_keepsHistory`): capability
  copy, revocation, subtree revocation, sealed-transfer offer and accept, map,
  and unmap. These operations write `lifecycle` and `virtualMemory`, but they
  change no issued history, no allocator state, and no binding
  (`applyOperation_historyAgrees`).
- **Directly:** issued subject creation, described in step 3.
- `bootRuntime_resourceRuntimeWellFormed`: the boot runtime satisfies the
  combined invariant.

**Every other step** (module `ResourceSteps`). The remaining steps write
`lifecycle` or `virtualMemory`, and most of them republish a lifecycle or a
memory taken from the resumable or blocking views. Their proofs therefore use
the coherence and blocking-lifecycle facts of `AuthoritativeRuntimeWellFormed`
together with one subsystem lemma per transition: no scheduler, resumable,
blocking, cleanup, syscall, or protection transition changes
`issuedSubjects`, and none changes the memory registry or the issued address
spaces (`Scheduler.tick_issuedSubjects`, `ResumablePreemption.switch_history`,
`BlockingIPCContext.receiveOrBlock_issuedSubjects`,
`Syscall.dispatch_virtualHistory`, `TLB.protect_virtualHistory`, and others).

- `authoritativeGate_historyAgrees`: every authoritative step except
  caller-identity creation keeps every history the resource conjuncts read
  (`ResourceHistoryAgrees`). That covers interrupt cleanup, `syscall`,
  `resumePreempt`, `protect`, `terminateSubject`, `terminateCurrent`,
  `scheduleRemove`, `scheduleNext`, `scheduleYield`, `scheduleTick`, blocking
  send, receive, and cancel, and the deferred drain.
  `authoritativeGate_preserves_resourceRuntimeWellFormed` follows with no
  premise beyond the combined invariant.
- **Termination** keeps both issuers and the whole subject history, so a
  terminated identity stays issued and below the counter, and it keeps every
  subject's frame usage and limit (`authoritativeGate_termination_accounts`).
  `authoritativeGate_budget_exact` keeps usage and limit for every
  authoritative step: no step writes the commitment or the allocator.
- **Caller-identity `Operation.createSubject k`** is unchanged. It is the
  oracle path that `CompositeDispatcher` replays (`createSubjectOne` runs
  `createSubject 1`) and that #535's unwinding proofs reason about, and
  restricting it would change generated C. Instead it is proved under an
  explicit hypothesis: it keeps the combined invariant when `0 < k` and `k` is
  below the subject counter
  (`authoritativeGate_createSubject_preserves_resourceRuntimeWellFormed`). The
  issuer then already covers `k`, and `SubjectLifecycle.create` rejects any
  identity that was ever issued. The bound is necessary: an accepted creation
  that leaves the issuer agreement intact had a bounded identity
  (`authoritativeGate_createSubject_requires_bound`).
- **Invalidation publication.** Every entry point except
  `acknowledgeCurrentUnmap` keeps the combined invariant
  (`InvalidationOperation.apply_preserves_resourceRuntimeWellFormed`).
  `acknowledgeCurrentUnmap` installs the pending successor's virtual memory,
  which the publication protocol computed from its own `published` view, so
  it needs that successor's memory histories to agree with the composite's
  (`PendingHistoryAgrees`,
  `authoritativeAcknowledgeCurrentUnmap_historyAgrees`). Its preservation of
  `AuthoritativeRuntimeWellFormed` was already conditional (see
  `CompositeState.InvalidationProjectionCoherent`); `CurrentUnmapAdmissible`
  names both premises, and `currentUnmapAdmissible_of_prepared` discharges
  them on the established prepare-then-acknowledge path.

**Step 3: issued creation.** `LifecycleOperation.createSubject` takes no
identity. `issueSubject` issues the subject counter's current value and runs
the composite `createSubject` transition with exactly that identity. It
commits the advanced counter only together with an accepted creation, and
`lifecycleGate` runs it under the running latch. It has a declared footprint:
`publicationProjections` plus `issuers`. The following are proved about it:

- **Frame rule and read independence:** `issueSubject_frames`,
  `lifecycleGate_frames`, `issueSubject_reads`, `lifecycleGate_reads`.
- **Atomic failure:** `issueSubject_exhausted_unchanged`,
  `issueSubject_rejected_unchanged`, and `lifecycleGate_unchanged_of_not_issued`.
  An exhausted or rejected creation, or a busy or halted latch, leaves the
  whole composite unchanged, both issuers included.
  `issueSubject_exhausted_iff`: exhaustion is decided by the issuer alone.
- **Fresh identity:** `issueSubject_issued`, `issueSubject_fresh`, and
  `issueSubject_total`. Under the agreement invariant, a live issuer always
  issues its next identity, and that identity was never issued.
- **Refinement:** `issueSubject_refines`. The result, both issuers, the
  lifecycle, and the mailboxes equal those of `BoundedLifecycle.createSubject`
  on `lifecycleRuntime`. The composite also republishes the capability
  registry into its memory view.
- **Invariants:** `lifecycleGate_preserves_resourceRuntimeWellFormed`.
- **Never-reuse lifted:** `composite_identity_no_reuse` lifts
  `BoundedLifecycle.bounded_identity_no_reuse` to composite traces
  (`CompositeStep`, `runSteps`). A step is an issued lifecycle operation, an
  authoritative operation, or an invalidation entry point. The trace may
  contain any step that keeps the combined invariant
  (`CompositeStep.Preserving`). Along such a trace:
  - the combined invariant holds at the end;
  - the issued identities strictly increase;
  - every issued identity is above every subject in the starting history;
  - an exhausted issuer stays exhausted.

  `issuedAlong_strictly_increasing` and `runSteps_exhausted_absorbing` hold for
  every trace, with no invariant, because no authoritative operation or
  invalidation entry point writes the issuers.
- **Budgets:** `budget_conservation` lifts `FrameBudget.usage_le_limit`,
  commitment disjointness, and allocator conservation to every composite
  state. `authoritativeGate_budget_unchanged` and
  `issueSubject_budget_unchanged` keep each subject's usage and limit exactly.
  The first covers every authoritative step that does not write
  `virtualMemory`, and the second covers issued creation.
  `issueSubject_zero_budget`: a newly issued subject has limit and usage zero,
  which is the zero-budget clause of the #489 inheritance set.

**Whole traces** (module `ResourceSteps`). `CompositeStep.Admissible` is
the premise a step needs from the state it runs in: the bound for
caller-identity creation, `CurrentUnmapAdmissible` for the current-unmap
completion, and nothing for every other step
(`CompositeStep.unconditional`). `composite_resource_trace`: along every trace
whose steps are each admissible (`AdmissibleAlong`), from a state satisfying
the combined invariant,

- the combined invariant holds at the end;
- no identity is created twice by either creation path, and none that was
  issued before the trace is created again (`createdAlong`, `Nodup`);
- the identities drawn from the issuer strictly increase;
- the issued subject history only grows;
- every subject's frame usage and limit are exactly unchanged, and usage is
  within the limit at the end.

`issued_never_recreated`: an identity already in the issued history, such as
a terminated one, is never created again by either path.
`composite_resource_trace_unconditional` states the result with no step
premise for traces that avoid the two conditional steps.

**What is narrower than the plan.**

- **Allocation and release.** The plan gave them explicit constructors. They
  have none, because the composite has no memory-allocation transition to
  route them through. A budget-charged allocation that keeps `Coherent` and
  `RuntimeWellFormed` is new composite semantics. That work belongs to #490.
- **Step 4 is not done.** It would move `CompositeDispatcher`'s frame-budget
  state tokens (`0x4001` to `0x4b01`) onto the new projections. Those tokens
  still denote `FrameBudgetScenario.Runtime` states, whose frames are a
  separate scenario pool. The scenario's tokens exercise budget-charged
  allocation, exhaustion, and release, and the composite has no such
  transition for them to denote until #490 adds one. Moving them would also
  change the dispatcher's generated C, its oracle vectors, and its boundary
  exports. Neither the `Resources` nor the `ResourceSteps` change alters
  generated boot C beyond the wider `CompositeState` constructor.
- **Caller-identity creation is unrestricted at the executable boundary.**
  The proofs cover it only under the issuer bound, and the dispatcher's
  `createSubjectOne` runs it from a state whose counter does not cover the
  identity. Routing that command through `LifecycleOperation.createSubject`
  changes the dispatcher, so it belongs with step 4.

### Explicit spawn (#489)

ADR 0010's amendment of 2026-10-10 records the decisions. `CompositeState`
gains one more projection, `spawn : SpawnRegistry`, which no existing
operation reads or writes (`footprints_unread_spawn`). It holds the
kernel-granted spawn capabilities (`authority`, with a never-reused
`generation`), the parent of each spawned child, and each child's address
space. The spawn capability is a capability kind of its own beside the generic
slot registry, as ADR 0022 layers device capabilities; subjects cannot copy or
transfer it.

`spawn state request` (module `Spawn`) is one composite transition, a separate
family (`SpawnOperation`, run by `spawnGate` under the running latch). It does
not change `Operation`, `applyOperation`, or caller-identity `createSubject`.
For the current subject (the parent) it: checks the spawn capability; issues
the subject issuer's next identity through `issueSubject`; checks the child's
slot space holds slots 0 and 1; issues the object issuer's next identity and
creates it as an empty address space owned by the child, with its root
capability in slot 1 (`installCreatedAddressSpace`, module
`SpawnAddressSpace`, the first composite address-space creation); resolves
the parent's endpoint handle word, requires `grant` and a valid subset of
rights, and installs the `Capability.copy` in the child's slot 0 through the
composite `capabilityCopy` publication; and records `spawn.parent` and
`spawn.addressSpace`. Every stage runs on a candidate state; any failure
returns the typed `SpawnError` and the pre-state.

| Property | Theorems |
| --- | --- |
| Rollback at every failure point | `spawn_rejected_unchanged`, `spawn_missing_right`, `spawn_stale_spawn_capability`, `spawn_identity_exhausted`, `spawn_slot_table_full`, `spawn_address_space_exhausted`, `spawn_stale_endpoint_rejected`, `spawnGate_unchanged_of_not_running` |
| Address-space creation keeps the invariant | `installCreatedAddressSpace_preserves_runtimeWellFormed`, `installCreatedAddressSpace_preserves_authoritativeRuntimeWellFormed` |
| Spawn keeps the combined invariant | `spawn_preserves_resourceRuntimeWellFormed`, `spawnGate_preserves_resourceRuntimeWellFormed` |
| Inheritance-set exactness | `spawn_child_capabilities`, `spawn_child_authority` |
| No authority amplification | `spawn_other_slots_unchanged`, `spawn_no_authority_amplification`, `spawn_parent_unchanged`, `spawn_registry` |
| Fresh identity | `spawn_fresh_identity` (built on the issuer agreement behind `composite_identity_no_reuse`) |
| The child starts empty | `spawn_child_starts_empty`, `spawn_keeps` |
| Relation, not authority | `spawnAuthorize_ignores_records`, `footprints_unread_spawn` |
| Whole traces | `spawn_resource_trace` (`SpawnTraceStep` adds the spawn family to `CompositeStep`; `runSpawnSteps_composite` embeds composite traces) |

**The child holds two capabilities, not one.** `VirtualMapping.LifecycleWellFormed`
requires the owner of an address space to hold `revoke` over it, so the
child's own empty address space comes with its root capability (`{grant,
revoke}`, from `VirtualMapping.createAddressSpace`). The child's authority over
every object that existed before the spawn is exactly the granted endpoint
with the requested rights (`spawn_child_authority`).

**The child cannot run yet.** Spawn leaves it not runnable
(`spawn_child_starts_empty`). The scheduler also admits only a subject that
owns the address space whose identifier equals its subject identifier
(`Scheduler.ownsAddressSpace`), and the child's address space is drawn from
the object issuer, a different counter. Loading code and admission are the
loader issue.

**Executable boundary.** `LeanOS.SpawnOracle` gives the canonical encoding
(tag `0x7001`, `decodeSpawn_encodeSpawn`, `encodeSpawn_decodeSpawn`), injective
result codes, and adversarial vectors on the dispatcher's seed: every failure
point, both issuer exhaustions, stale and malformed parent handles, a
re-granted spawn capability, isolation of the other subjects, the child
presenting the parent's handle, and never-reuse after termination
(`spawn_vectors_pass`). The version-one command decoder of the original
dispatcher trace does not decode the tag (`boot_dispatcher_rejects_spawn_tag`);
the same tag reaches the generated dispatcher only through the spawn family's
own state tokens (see "Spawn at the generated boundary" below), and there is
no syscall. The negative fixture
`NegativeFixtures/SpawnIdentityRollback` keeps the issued child on a failed
grant and fails the rollback check.

**Not done here.** Budget transfer and the subject budget (#490) and stale
child handles and cleanup (#491) are the next section. The ring-3 syscall
stays gated by ADR 0010.

### Spawn accounting and child control (#490, #491)

`ChildOperation`, run by `childGate` under the running latch (module
`SpawnAccounting`), is the public spawn family. It wraps the #489 `spawn`,
which is unchanged, and adds two operations on a child named by a control
word. `SpawnOperation` and `spawnGate` remain as the unaccounted core: the
hosted boundary (`LeanOS.SpawnAccountingOracle`) and the whole-trace theorem
below use `childGate`.

The state is in `CompositeState.spawn`, which no other operation reads or
writes:

- `SpawnCapability.subjectBudget`: the most children the holder may have
  charged to it at once. `ChildOperation.grantAuthority subject budget` names
  it, and is rejected if the subject already has more children, the budget
  exceeds the table, or the subject is itself a spawned child. The #489 grant
  leaves it zero.
- `children parent slot`: each parent's child table, a fixed kernel table of
  `childSlots` (64) slots. An entry (`ChildEntry`) names the child, the
  generation of its control word, and the frames the parent charged to it.
- `nextChildGeneration`: a never-reused counter for control generations.

The operations:

- **`spawn request`** (`spawnCharged`): the #489 authorization; then the
  parent's charged children (`childCount`) must be fewer than its subject
  budget, else `subjectBudgetExhausted` with the pre-state; then the #489
  spawn; then the child is recorded in the first free slot with charge zero.
  The parent receives the control word (`controlWord`), a
  `CapabilityHandle` word of the slot and the entry's generation.
- **`grantFrames control frames`**: the first `frames` free frames committed
  to the parent are committed to the child, and the entry's charge grows by
  the number moved. Too few free frames is `frameBudgetExhausted` with the
  pre-state. The child receives a slice of the parent's budget: no frame is
  created and no other subject's commitment changes (`grantFrames_limits`).
- **`terminateChild control`**: the composite termination transition runs on
  the child; every frame committed to the child that backs a dead object (the
  child's own memory) is freed, unbound, and scrubbed (`reclaimChildFrames`);
  every frame committed to the child is committed to the parent again
  (`releaseChild_limits`); and the entry and the child's spawn records are
  removed. A child already terminated by another path is reaped the same way.

A parent's **entitlement** is its own frame limit plus the charges in its
child table. `ChildAccountingWellFormed` says: every entry is in the table,
has a generation below the counter, names an issued child other than the
parent, and the child's entitlement is within the entry's charge; no child
is in two entries; a never-issued subject has an empty table; and a parent
holding a spawn capability has at most its subject budget of children.

| Obligation | Theorems |
| --- | --- |
| Typed exhaustion with the pre-state | `spawnCharged_subject_budget_exhausted`, `grantFrames_frame_budget_exhausted`, `spawnCharged_control_generation_exhausted`, `ChildOperation.apply_rejected_unchanged`, `childGate_unchanged_of_not_running` |
| Both invariants kept by every step | `childGate_preserves`, `CompositeStep.childAccounting` |
| Live children within the subject budget | `ChildAccountingWellFormed.budget`, kept by `spawnCharged_preserves` and `grantBudgetedAuthority_preserves` |
| Children's budgets plus the parent's usage within its entitlement | `usage_add_childLimits_le` |
| Frame slices move frames, never create them | `grantFrames_limits`, `releaseChild_limits`, `child_resource_trace` (frame list exact, committed frames only shrink) |
| Terminating a child returns its charge and releases what it was given | `terminateChild_releases`, `terminateChild_releases_everything` |
| Children never have children | `SpawnTreeWellFormed`, `childGate_spawnTree`, `charged_child_childless`, `child_spawn_rejected`, `terminateChild_no_orphans` |
| Stale control words | `terminateChild_retires`, `retired_rejected_unchanged`, `childGate_advances`, `CompositeStep.advances`, `stale_control_after_respawn` |
| Stale capabilities naming the child | `terminateChild_revokes`, `terminateChild_stale_word`, `stale_word_after_respawn`, `stale_word_forever` |
| Whole traces | `child_resource_trace` (`ChildTraceStep` adds `childGate` and `memoryGate` to `CompositeStep`; `runChildSteps_composite` embeds composite traces) |

`child_resource_trace` proves, along every admissible trace of composite
steps, public spawn-family steps, and memory steps from a state satisfying
the combined, accounting, and spawn-tree invariants: all three at the end; no
identity created twice; the subject history only grows; the frame list exact
and no frame newly committed; every subject's usage within its limit; no
child with children; every subject budget respected; every parent's usage
plus its children's limits within its entitlement; a subject that was issued
and not a charged child at the start never gains entitlement; and every
retired control word still retired.

**Stale child authority.** After `terminateChild`, the control word's slot
is empty (`terminateChild_retires`). A later spawn may reuse the slot, but
its entry takes the next generation, so the old word names nothing
(`TableAdvances.retired`), and both control operations reject it with the
pre-state (`retired_rejected_unchanged`). The composite termination also
removes every capability the child held and every capability any subject held
over an object the child owned: an endpoint, an address space, or memory
(`terminateChild_revokes`). A handle word that named such a capability, such
as a parent's endpoint to the child, no longer resolves
(`terminateChild_stale_word`), and still does not after a new child is
spawned (`stale_word_after_respawn`). None of this depends on the child's
address-space root: a child holding only the granted endpoint is covered the
same way.

**Executable boundary.** `LeanOS.SpawnAccountingOracle` runs `childGate`
from command words: spawn (tag `0x7001`, the `SpawnOracle` encoding), grant
frames (`0x7101`), and terminate child (`0x7201`), with canonical encodings
(`decodeChild_encodeGrant`, `encodeGrant_decodeChild`,
`decodeChild_encodeTerminate`, `encodeTerminate_decodeChild`) and injective
result codes (`childErrorCodes_injective`). `child_vectors_pass` checks the
`SpawnOracle` vectors through the charged oracle, both exhaustions, a frame
grant and its return, release on termination, the stale control word after
termination and after slot reuse, a parent capability over the child's
address space going stale and staying stale, and another subject presenting
the control word. The original trace's version-one decoder rejects both new
tags (`boot_dispatcher_rejects_child_tags`); the generated dispatcher reaches
them only through the spawn family's tokens (next sections). The negative fixture
`NegativeFixtures/SpawnAccounting` has a spawn that ignores the subject
budget, a grant that mints a frame, and a termination that keeps the charge;
each fails its check.

**Children never have children.** Spawn never passes spawn authority to the
child, and the public grant refuses a spawned child, so
`SpawnTreeWellFormed` holds along every trace: every table entry's child is
recorded with that parent, every holder of spawn authority is issued, and a
recorded child holds no spawn authority and has an empty table. A child
cannot spawn (`child_spawn_rejected`), and terminating a child orphans
nothing (`terminateChild_no_orphans`).

**Stale capability words along every later trace.** `IdentityStep` says
that every capability identity after a step was present before, in a slot or
a pending sealed transfer, or is at least the old counter. Every step of
every family has it (`CompositeStep.identityStep`, `childGate_identityStep`,
`memoryGate_identityStep`), so it holds along whole traces
(`runChildSteps_identityStep`). The identity of every capability a child
termination removes is retired (`terminateChild_identityRetired`), stays
retired (`IdentityStep.retired`), and a word naming it never resolves again
(`stale_word_forever`).

**Confinement.** `LeanOS.SpawnConfinement` states confinement over the
observer views of `LeanOS.CompositeObservation`. When the child acts, an
operation of its syscall surface that does not designate an observer leaves
unchanged the whole view of every subject that names no object the child
names (`child_step_confined`, `child_run_confined`); at spawn the child names
exactly the granted endpoint and its own address space
(`spawn_child_names`, `spawned_child_confined`); and its memory allocations
are invisible to every other subject (`memory_allocate_confined`). The
module lists the exclusions: the public scheduler choice, designation of the
observer, `capabilityRevokeSubtree` and memory release, timing, and caches.

**Booted images.** Every normal image replays the whole oracle corpus,
including the spawn family's vectors, through its boot-compiled
`leanos_composite_dispatch` (see "Spawn at the generated boundary"). A
scenario in which ring-3 code spawns needs the gated syscall.

### Budget-charged memory (gate item 1)

`MemoryOperation`, run by `memoryGate` under the running latch (module
`MemoryOperations`), is the composite's memory family. Like the spawn
family it is separate from `Operation`. The acting subject is the latch's
current subject (`memoryActor`).

- **`allocate slot`**: the registry checks of `FrameBudget.allocate`; the
  object issuer's next identity, unused under every kind; the first free
  frame committed to the actor (`FrameBudget.firstAvailable`), else
  `frameBudgetExhausted`; and a frame the lifecycle attributes to no one.
  The frame is scrubbed, the object is published bound to it with a root
  capability in the actor's slot (`installAllocatedMemory`), the lifetime is
  marked unwritten, and the object issuer advances.
- **`release slot`**: the checks of `MemoryLifecycle.release` and the actor
  recorded as owner. The object is retired everywhere: capabilities in every
  slot, mappings, pending sealed transfers, and cached translations
  (`installReleasedMemory`). The frame is free and scrubbed, and the identity
  stays issued.

| Property | Theorems |
| --- | --- |
| Rejection keeps the pre-state | `MemoryOperation.apply_rejected_unchanged`, `memoryGate_unchanged_of_not_running` |
| Typed exhaustion | `allocateMemory_frame_budget_exhausted`, `allocateMemory_full_rejected`, `allocateMemory_object_identity_exhausted` |
| Footprint, frame rule, read set | `MemoryOperation.footprint`, `memoryGate_frames`, `MemoryOperation.apply_reads`, `memoryGate_reads` |
| Combined invariant | `installAllocatedMemory_preserves_authoritativeRuntimeWellFormed`, `installReleasedMemory_preserves_authoritativeRuntimeWellFormed`, `allocateMemory_preserves`, `releaseMemory_preserves`, `memoryGate_preserves` |
| Charging and return | `allocateMemory_charges`, `releaseMemory_returns`, `budgetLimit_of_frames` |
| Scrub and fresh identities | `allocateMemory_fresh`, `releaseMemory_retires`, `allocateMemory_capability` |
| Refinement of the standalone budget model | `allocateMemory_refines`, `releaseMemory_refines` |
| Whole traces | `child_resource_trace`, `memoryGate_keeps`, `memoryGate_childAccounting`, `memoryGate_spawnTree` |

`NegativeFixtures/MemoryAllocation` has an allocation that skips the scrub
and one that takes another subject's frame when the budget is full; each
fails its check, and `allocateMemory` passes both.

**The dispatcher's caller-identity creation.** `CompositeDispatcher` replays
`createSubject 1` from `bootRuntime`, whose subject counter is 1.
`LeanOS.CompositeDispatcherResources` reads every dispatcher state with the
subject counter at 2 (`resourceView`). No authoritative step reads or writes
the issuers (`authoritativeGate_resourceView`), so every dispatcher edge is
admissible in that view (`dispatcher_createSubject_admissible`,
`dispatcher_edge_admissible`) and `composite_resource_trace` covers the whole
dispatcher path (`dispatcher_resource_trace`). The dispatcher and its
generated C are unchanged.

**The frame-budget tokens.** The dispatcher's frame-budget tokens
(`0x4001`–`0x4b01`) still run `FrameBudgetScenario.dispatch`, the table the
QEMU frame-budget image drives. `LeanOS.FrameBudgetComposite` gives each token
a composite denotation, `compositeOf`, replayed from a composite seed by the
composite counterpart of each scenario command (`memoryGate` allocation and
release, the dispatcher's authoritative timer switch, authoritative
termination, and an authoritative map syscall with the old handle word), and
proves a forward simulation (`budget_tokens_simulated`): the composite
successor of every edge is the counterpart step (`compositeOf_edge`), the
counterpart's typed result is the edge's reply (`counterpart_matches_reply`),
and at every token the budget view agrees (`views_agree`): which subject is
current, which is live, and each live subject's frame usage and limit. On the
budget projection each composite allocation and release is exactly the
`FrameBudget` step the scenario runs (`allocateMemory_refines`,
`releaseMemory_refines`). The view leaves out two differences.
`FrameBudget.terminate` frees the dead subject's frame, while composite
termination of a subject that is not a spawned child keeps it owned by the
retired object; commitments never move except between parent and child, so
no live subject can allocate that frame in either model. And the standalone
`FrameScrub` state, like the QEMU image, reuses one physical frame for A's
object and then B's fresh object; in the composite, B's fresh object is on
B's own committed frame, and frames return across subjects only through child
termination.

### Spawn at the generated boundary (gate item 5)

`LeanOS.SpawnBoundary` puts the spawn family into the boot-compiled
`CompositeDispatcher.dispatch` (`leanos_composite_dispatch`, oracle adapter
18) as eighteen state tokens `0x7001`–`0x8101` and a table of 49 edges
(`spawnDispatchRaw`). Each token names the complete `CompositeState` reached
by replaying gate steps from one of four seeds: the dispatcher seed with the
issuers past its histories and frame 4 committed to subject 2
(`spawnSeed`), and three exhaustion seeds with the subject issuer, the object
issuer, or the control-generation counter at its bound, which no bounded
trace reaches.

| Tag | Command | Step |
| --- | --- | --- |
| `0x7001` | spawn (as in `SpawnOracle`) | `childGate (.spawn _)` |
| `0x7101` | grant frames | `childGate (.grantFrames _ _)` |
| `0x7201` | terminate child | `childGate (.terminateChild _)` |
| `0x7301`, `0x7401` | allocate, release memory | `memoryGate` |
| `0x7501`, `0x7601` | kernel grant, revocation of spawn authority | `childGate` |
| `0x7701` | timer switch | the dispatcher's authoritative `resumePreempt` |
| `0x7801` | capability copy | authoritative `capabilityCopy` |

The reply's status byte is the hosted oracles' (`0x01` accepted, `0x80 + code`
rejected), and result word one is their value word (`edges_match_hosted_oracle`).
The command codec is canonical (`decodeFamily_encodeFamily`,
`encodeFamily_decodeFamily`), and so are the state tokens and reply words
(`decodeState_encodeState`, `edges_dispatch`).

| Property | Theorems |
| --- | --- |
| The generated table is the edge table | `edges_dispatch`, `edges_decode` |
| Each edge is one gate step on the named state | `edge_refines`, `dispatcher_refines` |
| Rejections keep the complete state and the token | `rejected_edge_unchanged`, `familyStep_stutter` |
| Every token satisfies the whole-trace theorem | `spawn_boundary_trace`, `familySeed_resourceRuntimeWellFormed` |
| Isolation, cleanup, reuse, stale handles | `boundary_checks_pass` (module `SpawnBoundaryChecks`) |
| The hosted generated-C replay checks the model | `spawn_edge_vectors_match_model`, `spawn_negative_vectors_reject` (module `Oracle`) |

The edges cover every failure point reachable from the seeds with rollback:
missing, stale, and re-granted spawn capabilities; malformed, stale,
out-of-range, and wrong-kind endpoint handles; invalid and non-subset rights
and an endpoint without grant; subject-budget, frame-budget, subject-identity,
object-identity, and control-generation exhaustion; and a kernel grant to a
spawned child. They cover stale control words before and after child-table
slot reuse, a stale memory handle after its slot is reused, child isolation
(the child's slots are exactly the inheritance set, and no state of the family
changes what the bystander subject 1 holds), the bystander presenting the
parent's control word, and termination cleanup: the child's identity,
capabilities, address space, records, and table entry are gone, its frame is
committed to the parent again, free and scrubbed, and the parent allocates it
again under a never-issued object identity. The child cannot run before a
loader exists, so reclamation of memory the child itself allocated
(`reclaimChildFrames`) is covered by `terminateChild_releases_everything`, not
by a vector. The slot-table-full and identity-rejection failures need seeds
the bounded table does not name; the hosted `SpawnOracle` vectors cover them.

The hosted generated-C replay (`check-oracle-host.sh`) and every normal
image's boot-time oracle replay run all 63 spawn vectors (49 edges and 14
hostile encodings) through the generated dispatcher.

## Diagnostic and trusted boundary

Boot-only WP/SMEP recovery remains a pre-runtime diagnostic behavior outside
this model. It must be disabled before subjects run and does not refine
`halted`; production fatal entry has no clear or restart transition.

These are Lean model proofs, not proof that x86 delivers an exception or NMI
into the model. IDT/TSS/IST setup, NMI delivery/blocking/coalescing and frame
construction, assembly entry/exit, exception delivery, compiler, generated
code, firmware, QEMU, and hardware remain trusted. No `unsafe`,
`extern`, FFI declaration, axiom, or constant is added.
