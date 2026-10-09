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
split by subsystem into `LeanOS/FailStop/*.lean` (issue #499). The modules
form one import chain, in this order:

| Module | Contents |
| --- | --- |
| `Latch` | Execution latch, ordinary and NMI entry, user-return transaction |
| `Composite` | `CompositeState`, its named projections, `RuntimeWellFormed`, boot runtime |
| `BlockingIPC` | Blocking receive, send, cancel, and the typed blocking gate |
| `Operations` | Publication helpers, `Operation`, `applyOperation` |
| `Footprint` | `Operation.footprint`, helper frame lemmas, `applyOperation_frames` |
| `Gate` | `operationReply`, the ordinary `gate`, DMA control observation |
| `IPC` | Accepted user-return, IPC, and sealed-transfer slices |
| `Capabilities` | Capability copy, revocation, and subject creation slices |
| `Memory` | Map, unmap, protect slices, and `runOperations` |
| `OperationRegistry` | Per-operation runtime-preservation registry |
| `Scheduler` | Termination cleanup and scheduler families |
| `Faults` | Resumable preemption and interrupt preservation |
| `DeferredBlocking` | Runtime trace inventory and deferred blocking invariant |
| `AuthoritativeGate` | `authoritativeGate`, its footprints, invalidation publication |
| `AuthoritativeTraces` | Blocking slices, admissibility, and authoritative traces |
| `Evidence` | Executable regressions and the dispatcher's initial states |

No module exceeds about 3,400 lines. Helpers that a later module uses are
public declarations in the same namespace; the remaining helpers stay private
to their module.

## Footprints and the frame rule

Every typed `Operation` declares a footprint using the
`LeanOS.CompositeFootprint` vocabulary: the projections of `CompositeState` it
reads and the subset it may write (`Operation.footprint`). The blocking
operations (`CompositeBlockingOperation.footprint`) and the deferred drain
complete the declaration for every `AuthoritativeOperation`. Footprints are
built with `Footprint.ofLists`, so writes are reads by construction. Named
groups such as `publicationProjections`, `cleanupProjections`, and
`mappingProjections` name the projections that one publication helper
republishes together.

The frame rule `applyOperation_frames` proves that every projection outside
an operation's write set is literally unchanged. `gate_frames`,
`blockingGate_frames`, and `authoritativeGate_frames` extend it to every gate
outcome, including busy and halted stutters. The proof is assembled from one
frame lemma per publication helper, such as `installLifecycle_frames` and
`installTransfers_frames`. Each helper lemma is discharged by the
`composite_frame` tactic, which case-splits the finite projection vocabulary,
so the per-operation proof never names a projection.

Theorems about projections that an operation does not write are lifted rather
than re-proved:

- `applyOperation_project_untouched` reads one untouched projection.
- `applyOperation_preserves_of_dependsOn` and `gate_preserves_of_dependsOn`
  preserve any predicate that depends only on untouched projections
  (`CompositeState.DependsOn`).
- `applyOperation_directPortIO`, `applyOperation_dmaAccepted`,
  `applyOperation_dmaObserved`, `gate_preserves_dmaQuarantined`,
  `authoritativeGate_dmaAuthority`, and the invalidation-publication retention
  lemmas are now corollaries of the frame rule.

To add a projection:

1. Add the field to `CompositeState`, the constructor to
   `CompositeFootprint.Projection`, and one case each to
   `CompositeProjectionType` and `CompositeState.project`.
2. Add the projection to the write list of each operation that changes it.
   For every other operation, the helper frame lemmas re-check the new case by
   unfolding, and `applyOperation_frames` is unchanged.
3. State theorems about the new projection with
   `applyOperation_preserves_of_dependsOn` instead of re-proving the
   whole-state preservation theorems.

The read sets are declared but not yet machine-checked. A read-independence
theorem, saying that two states that agree on an operation's reads produce
results that agree on its writes, is future work. The `CompositeFootprint`
vocabulary already requires writes to be reads, so it can be added without
changing any declaration.

## Diagnostic and trusted boundary

Boot-only WP/SMEP recovery remains a pre-runtime diagnostic behavior outside
this model. It must be disabled before subjects run and does not refine
`halted`; production fatal entry has no clear or restart transition.

These are Lean model proofs, not proof that x86 delivers an exception or NMI
into the model. IDT/TSS/IST setup, NMI delivery/blocking/coalescing and frame
construction, assembly entry/exit, exception delivery, compiler, generated
code, firmware, QEMU, and hardware remain trusted. No `unsafe`,
`extern`, FFI declaration, axiom, or constant is added.
