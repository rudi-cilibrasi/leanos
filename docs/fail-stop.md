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

Two modules branch off the chain and build in parallel with it:

| Module | Imports | Contents |
| --- | --- | --- |
| `ProjectionInvariants` | `Gate` | `ProjectionInvariant`, `RuntimeWellFormed` split by projection |
| `ReadSets` | `AuthoritativeGate` | Read-independence theorems for every gate family |

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

### State outside the composite

`BoundedLifecycle` (the subject and object identity issuers), the per-subject
frame budgets, and the frame-scrub state still live outside `CompositeState`.
The issuers are in `BoundedLifecycle.Runtime`. The budgets and scrub state are
in `FrameBudgetScenario.Runtime`, reached through `CompositeDispatcher` state
tokens. This matters for item 1 of the #473 spawn gate. The plan to bring them
in uses the machinery above:

1. Add `issuers`, `frameBudgets`, and `scrub` projections, following the
   checklist above. No existing operation reads or writes them. Every existing
   frame, read-independence, and preservation proof is therefore unchanged.
2. State each subsystem's well-formedness as a `ProjectionInvariant` with
   singleton support. State the cross-projection agreement as a separate
   conjunct: issued identities bound the lifecycle's `issuedSubjects`, and
   budgets bound owned frames. Its support also names `lifecycle` and
   `virtualMemory`. Add both to the authoritative list. Only the operations
   that write `lifecycle` or `virtualMemory` must re-prove the agreement
   conjunct. These are creation, termination, cleanup, and mapping.
3. Route `createSubject` through `BoundedLifecycle.createSubject` and give
   allocation and release explicit `Operation` constructors with footprints.
   Their frame lemmas follow from helper lemmas, as for every other operation.
4. Move `CompositeDispatcher`'s state tokens onto the new projections.
   `CompositeDispatcher` is a boot-compiled module, so this step changes its
   generated C. It needs the hosted-boundary replay and an image rebuild.

Steps 1 to 3 need no change to generated code.

## Diagnostic and trusted boundary

Boot-only WP/SMEP recovery remains a pre-runtime diagnostic behavior outside
this model. It must be disabled before subjects run and does not refine
`halted`; production fatal entry has no clear or restart transition.

These are Lean model proofs, not proof that x86 delivers an exception or NMI
into the model. IDT/TSS/IST setup, NMI delivery/blocking/coalescing and frame
construction, assembly entry/exit, exception delivery, compiler, generated
code, firmware, QEMU, and hardware remain trusted. No `unsafe`,
`extern`, FFI declaration, axiom, or constant is added.
