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

Four modules branch off the chain and build in parallel with it:

| Module | Imports | Contents |
| --- | --- | --- |
| `ProjectionInvariants` | `Gate` | `ProjectionInvariant`, `RuntimeWellFormed` split by projection |
| `ReadSets` | `AuthoritativeGate` | Read-independence theorems for every gate family |
| `Resources` | `ReadSets`, `AuthoritativeTraces` | Issuers, frame budgets, frame contents, and issued subject creation |
| `ResourceSteps` | `Resources` | Resource invariants for every composite step and whole traces |

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

## Diagnostic and trusted boundary

Boot-only WP/SMEP recovery remains a pre-runtime diagnostic behavior outside
this model. It must be disabled before subjects run and does not refine
`halted`; production fatal entry has no clear or restart transition.

These are Lean model proofs, not proof that x86 delivers an exception or NMI
into the model. IDT/TSS/IST setup, NMI delivery/blocking/coalescing and frame
construction, assembly entry/exit, exception delivery, compiler, generated
code, firmware, QEMU, and hardware remain trusted. No `unsafe`,
`extern`, FFI declaration, axiom, or constant is added.
