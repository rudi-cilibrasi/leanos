import LeanOS.FailStop.Composite

/-!
# Fail-stop composite: authoritative blocking IPC

Blocking endpoint publication, the context-owning receive, send, and cancel
boundaries, and the execution-latched typed blocking gate, together with their
preservation proofs over the blocking runtime invariant.
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

/-! ## Authoritative blocking-IPC publication

`BlockingIPC.State` owns the waiter queues, completion reservations, and the
scheduler transition that blocks or wakes a subject.  The older data-only IPC
projection remains present while sealed-transfer composition is migrated, but
it is not used to decide blocking behavior. -/

/-- Strengthened runtime predicate for the authoritative blocking-IPC slice. -/
def BlockingRuntimeWellFormed (state : CompositeState) : Prop :=
  RuntimeWellFormed state ∧
  BlockingIPCContext.WellFormed state.blockingIPCContext

/-- Strengthened blocking slice including contexts detached by contained-fault
cleanup.  A saved context is therefore classified as either an indexed waiter
or a validated, live-but-quiescent deferred cancellation. -/
def DeferredBlockingRuntimeWellFormed (state : CompositeState) : Prop :=
  RuntimeWellFormed state ∧ state.DeferredCancellationWellFormed

/-- The boot-produced runtime also initializes the authoritative blocking
store with empty waiter/completion indexes over the same scheduler. -/
theorem bootRuntime_blockingRuntimeWellFormed input plan
    (hcompiled : BootPageTablePlan.compile input = .ok plan) :
    BlockingRuntimeWellFormed (bootRuntime plan) := by
  refine ⟨bootRuntime_runtimeWellFormed input plan hcompiled, ?_⟩
  simp [CompositeState.blockingIPCContext, bootRuntime,
    BlockingIPCContext.WellFormed, BlockingIPCContext.ContextAgreement,
    BlockingIPC.WellFormed, Scheduler.WellFormed,
    SubjectLifecycle.WellFormed, Capability.WellFormed,
    Capability.SlotsWellFormed, Capability.DerivationsWellFormed,
    Capability.LiveIdentitiesUnique, Capability.SlotSpacesWellFormed,
    BlockingIPC.authorizedReceive, bootLifecycle, bootCapabilities]

/-- Boot starts with neither indexed waiters nor deferred cancellations. -/
theorem bootRuntime_deferredBlockingRuntimeWellFormed input plan
    (hcompiled : BootPageTablePlan.compile input = .ok plan) :
    DeferredBlockingRuntimeWellFormed (bootRuntime plan) := by
  refine ⟨bootRuntime_runtimeWellFormed input plan hcompiled, ?_⟩
  simp [CompositeState.DeferredCancellationWellFormed,
    BlockingIPCContext.DeferredWellFormed, CompositeState.blockingIPCContext,
    bootRuntime, BlockingIPCContext.WellFormed,
    BlockingIPCContext.ContextAgreement, BlockingIPC.WellFormed,
    Scheduler.WellFormed, SubjectLifecycle.WellFormed, Capability.WellFormed,
    Capability.SlotsWellFormed, Capability.DerivationsWellFormed,
    Capability.LiveIdentitiesUnique, Capability.SlotSpacesWellFormed,
    BlockingIPC.authorizedReceive, BlockingIPCContext.emptyDeferred,
    bootLifecycle, bootCapabilities]

/-- Publish the complete blocking store first, then synchronize its scheduler
and lifecycle to every overlapping composite projection.  Waiters and reserved
completions are copied literally; they are never reconstructed by filtering. -/
def publishBlockingIPC (state : CompositeState)
    (blockingIPC : BlockingIPC.State) : CompositeState :=
  installScheduler { state with blockingIPC } blockingIPC.scheduler

/-- Publish the raw blocking store and its exact saved-context bank in the
same composite mutation.  Scheduler synchronization is deliberately shared
with the established raw publication path. -/
def publishBlockingIPCContext (state : CompositeState)
    (blocking : BlockingIPCContext.State) : CompositeState :=
  let scheduler := blocking.ipc.scheduler
  let lifecycle := scheduler.lifecycle
  let translations :=
    if lifecycle.current.isSome then state.resumable.translations
    else { state.resumable.translations with active := none, entries := [] }
  { state with
    execution := { state.execution with
      core := { state.execution.core with lifecycle }
      returnAuthorityArmed := false
      copyOverride := false }
    scheduler
    preemption := { state.preemption with scheduler }
    lifecycle
    resumable := { state.resumable with scheduler, translations }
    blockingIPC := blocking.ipc
    blockingContexts := blocking.blocked }

structure DeferredDrainOutcome where
  state : CompositeState
  result : BlockingIPCContext.DrainResult

/-- Publish a successful deferred cancellation drain through every duplicated
scheduler/lifecycle projection and the authoritative resumable bank.  The
lower transition has already reserved both finite capacities. -/
def publishDeferredDrain (state : CompositeState)
    (outcome : BlockingIPCContext.DrainOutcome) : CompositeState :=
  let published := publishBlockingIPCContext state outcome.state
  { published with
    resumable := { published.resumable with contexts := outcome.resumable }
    deferredCancels := outcome.deferred }

/-- Typed composite drain for a contained-fault peer.  Every rejected branch
returns the literal composite pre-state.  Success is published only after the
lower gate has revalidated authority, uniqueness, ready capacity, and
resumable-bank capacity. -/
def drainDeferredCancellation (state : CompositeState)
    (subject : BlockingIPC.SubjectId) : DeferredDrainOutcome :=
  let outcome := BlockingIPCContext.drainDeferred state.blockingIPCContext
    state.deferredCancels state.resumable.contexts state.resumable.capacity subject
  match outcome.result with
  | .rejected reason => ⟨state, .rejected reason⟩
  | .drained saved => ⟨publishDeferredDrain state outcome, .drained saved⟩

/-- Deferred cancellation drains cannot replace either proof-carrying PCI
authority field.  Successful publication changes only scheduler, lifecycle,
context, and deferred-cancellation projections; every denial is atomic. -/
@[simp] theorem drainDeferredCancellation_dmaAuthority state subject :
    (drainDeferredCancellation state subject).state.dmaAccepted =
        state.dmaAccepted ∧
      (drainDeferredCancellation state subject).state.dmaObserved =
        state.dmaObserved := by
  simp only [drainDeferredCancellation]
  generalize houtcome : BlockingIPCContext.drainDeferred
    state.blockingIPCContext state.deferredCancels state.resumable.contexts
    state.resumable.capacity subject = outcome
  cases outcome with
  | mk next nextDeferred nextResumable result =>
      cases result <;>
        simp [publishDeferredDrain, publishBlockingIPCContext]

theorem drainDeferredCancellation_rejected_unchanged state subject reason
    (h : (drainDeferredCancellation state subject).result = .rejected reason) :
    (drainDeferredCancellation state subject).state = state := by
  simp only [drainDeferredCancellation] at h ⊢
  generalize houtcome : BlockingIPCContext.drainDeferred state.blockingIPCContext
    state.deferredCancels state.resumable.contexts state.resumable.capacity subject = outcome at h ⊢
  cases outcome with
  | mk next nextDeferred nextResumable result =>
      cases result <;> simp_all

/-- Successful publication installs exactly the retained context, emits typed
cancellation, removes only that deferred entry, and keeps all scheduler views
identical. -/
theorem drainDeferredCancellation_drained_exact state subject saved
    (h : (drainDeferredCancellation state subject).result = .drained saved) :
    let next := (drainDeferredCancellation state subject).state
    state.deferredCancels.retained subject = some saved ∧
      next.deferredCancels.retained subject = none ∧
      next.blockingIPC.completion subject = some .cancelled ∧
      next.resumable.contexts = saved :: state.resumable.contexts ∧
      next.resumable.scheduler = next.scheduler ∧
      next.blockingIPC.scheduler = next.scheduler ∧
      next.scheduler.lifecycle = next.lifecycle ∧
      next.execution.core.lifecycle = next.lifecycle ∧
      next.preemption.scheduler = next.scheduler := by
  simp only [drainDeferredCancellation] at h ⊢
  generalize houtcome : BlockingIPCContext.drainDeferred state.blockingIPCContext
    state.deferredCancels state.resumable.contexts state.resumable.capacity subject = outcome at h ⊢
  cases outcome with
  | mk next nextDeferred nextResumable result =>
      cases result with
      | rejected reason => simp at h
      | drained actual =>
          injection h with hactual
          subst actual
          simp only
          have hresult :
              (BlockingIPCContext.drainDeferred state.blockingIPCContext
                state.deferredCancels state.resumable.contexts
                state.resumable.capacity subject).result = .drained saved := by
            rw [houtcome]
          have hexact := BlockingIPCContext.drainDeferred_drained_exact
            state.blockingIPCContext state.deferredCancels state.resumable.contexts
            state.resumable.capacity subject saved hresult
          rw [houtcome] at hexact
          rcases hexact with ⟨hretained, hremoved, _hrunnable, _hready,
            hcancelled, hcontexts⟩
          simp only [publishDeferredDrain]
          refine ⟨hretained, hremoved, hcancelled, hcontexts, ?_⟩
          exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A composite success proves both finite reservations in the pre-state and
the exact resumable-bank append in the published post-state. -/
theorem drainDeferredCancellation_reserves_capacities state subject saved
    (hcoherent : state.BlockingIPCCoherent)
    (h : (drainDeferredCancellation state subject).result = .drained saved) :
    ¬ state.scheduler.capacity ≤ state.scheduler.ready.length ∧
      ¬ state.resumable.capacity ≤ state.resumable.contexts.length ∧
      (drainDeferredCancellation state subject).state.scheduler.ready =
        state.scheduler.ready ++ [subject] ∧
      (drainDeferredCancellation state subject).state.resumable.contexts =
        saved :: state.resumable.contexts := by
  simp only [drainDeferredCancellation] at h ⊢
  generalize houtcome : BlockingIPCContext.drainDeferred state.blockingIPCContext
    state.deferredCancels state.resumable.contexts state.resumable.capacity subject = outcome at h ⊢
  cases outcome with
  | mk next nextDeferred nextResumable result =>
      cases result with
      | rejected reason => simp at h
      | drained actual =>
          injection h with hactual
          subst actual
          simp only
          have hresult :
              (BlockingIPCContext.drainDeferred state.blockingIPCContext
                state.deferredCancels state.resumable.contexts
                state.resumable.capacity subject).result = .drained saved := by
            rw [houtcome]
          have hcapacity := BlockingIPCContext.drainDeferred_drained_reserves_capacity
            state.blockingIPCContext state.deferredCancels state.resumable.contexts
            state.resumable.capacity subject saved hresult
          rw [houtcome] at hcapacity
          rcases hcapacity with
            ⟨_valid, _live, _owner, _unique, hreadyRoom, hbankRoom,
              hready, hcontexts⟩
          have hblocking : state.blockingIPC.scheduler = state.scheduler := hcoherent.1
          simp only [publishDeferredDrain]
          refine ⟨?_, hbankRoom, ?_, hcontexts⟩
          · simpa [CompositeState.blockingIPCContext, hblocking] using hreadyRoom
          · simpa [publishBlockingIPCContext, CompositeState.blockingIPCContext,
              hblocking] using hready

/-- Publish the blocking half of subject termination without reconstructing
either waiter or saved-context state.  The dependency transition removes the
subject from both projections, and the established publisher synchronizes its
post-termination scheduler through every overlapping composite view. -/
def publishTerminatedBlockingSubject (state : CompositeState)
    (subject : BlockingIPC.SubjectId) : CompositeState :=
  match (SubjectLifecycle.terminate state.blockingIPC.scheduler.lifecycle subject).result with
  | .rejected _ => state
  | .accepted =>
      publishBlockingIPCContext state
        (BlockingIPCContext.terminate state.blockingIPCContext subject)

/-- A lifecycle rejection reaches no scheduler, waiter, or context publisher. -/
theorem publishTerminatedBlockingSubject_rejected_unchanged state subject reason
    (hrejected :
      (SubjectLifecycle.terminate state.blockingIPC.scheduler.lifecycle subject).result =
        .rejected reason) :
    publishTerminatedBlockingSubject state subject = state := by
  simp [publishTerminatedBlockingSubject, hrejected]

/-- Accepted lifecycle termination cannot be published with a stale waiter or
blocked context for the dead identity.  Both absences belong to the same
composite post-state. -/
theorem publishTerminatedBlockingSubject_cleans_self state subject
    (haccepted :
      (SubjectLifecycle.terminate state.blockingIPC.scheduler.lifecycle subject).result =
        .accepted) :
    (publishTerminatedBlockingSubject state subject).blockingIPC.waiterEndpoint subject = none ∧
      (publishTerminatedBlockingSubject state subject).blockingContexts subject = none := by
  simp only [publishTerminatedBlockingSubject, haccepted]
  change
    (BlockingIPCContext.terminate state.blockingIPCContext subject).ipc.waiterEndpoint subject =
        none ∧
      (BlockingIPCContext.terminate state.blockingIPCContext subject).blocked subject = none
  exact BlockingIPCContext.terminate_accepted_cleans_self
    state.blockingIPCContext subject haccepted

@[simp] theorem publishBlockingIPCContext_context state blocking :
    (publishBlockingIPCContext state blocking).blockingIPCContext = blocking := by
  rfl

@[simp] theorem publishBlockingIPCContext_scheduler state blocking :
    (publishBlockingIPCContext state blocking).scheduler = blocking.ipc.scheduler := by
  rfl

@[simp] theorem publishBlockingIPCContext_translationVirtual state blocking :
    (publishBlockingIPCContext state blocking).resumable.translations.virtual =
      state.resumable.translations.virtual := by
  simp only [publishBlockingIPCContext]
  split <;> rfl

@[simp] theorem publishBlockingIPCContext_resumableScheduler state blocking :
    (publishBlockingIPCContext state blocking).resumable.scheduler =
      blocking.ipc.scheduler := by
  rfl

@[simp] theorem publishBlockingIPCContext_virtualMemory state blocking :
    (publishBlockingIPCContext state blocking).virtualMemory = state.virtualMemory := by
  rfl

@[simp] theorem publishBlockingIPCContext_translationHalted state blocking :
    (publishBlockingIPCContext state blocking).resumable.halted =
      state.resumable.halted := by
  rfl

@[simp] theorem publishBlockingIPC_blockingIPC state blockingIPC :
    (publishBlockingIPC state blockingIPC).blockingIPC = blockingIPC := by
  rfl

@[simp] theorem publishBlockingIPC_scheduler state blockingIPC :
    (publishBlockingIPC state blockingIPC).scheduler = blockingIPC.scheduler := by
  rfl

@[simp] theorem publishBlockingIPC_waiters state blockingIPC endpoint :
    (publishBlockingIPC state blockingIPC).blockingIPC.waiters endpoint =
      blockingIPC.waiters endpoint := by
  rfl

@[simp] theorem publishBlockingIPC_waiterEndpoint state blockingIPC subject :
    (publishBlockingIPC state blockingIPC).blockingIPC.waiterEndpoint subject =
      blockingIPC.waiterEndpoint subject := by
  rfl

@[simp] theorem publishBlockingIPC_completion state blockingIPC subject :
    (publishBlockingIPC state blockingIPC).blockingIPC.completion subject =
      blockingIPC.completion subject := by
  rfl

theorem publishBlockingIPC_coherent state blockingIPC :
    (publishBlockingIPC state blockingIPC).BlockingIPCCoherent := by
  simp [CompositeState.BlockingIPCCoherent, publishBlockingIPC,
    installScheduler, installLifecycle]

theorem publishBlockingIPCContext_coherent state blocking :
    (publishBlockingIPCContext state blocking).BlockingIPCCoherent := by
  simp [CompositeState.BlockingIPCCoherent, publishBlockingIPCContext,
    publishBlockingIPC, installScheduler, installLifecycle]

/-- Publishing a blocking-store update whose scheduler is unchanged preserves
the complete legacy runtime invariant.  The current-subject premise keeps the
resumable TLB projection unchanged; the publisher only closes transient return
and copy authority and replaces blocking state that `RuntimeWellFormed` does
not otherwise inspect. -/
theorem publishBlockingIPCContext_sameScheduler_preserves_runtimeWellFormed
    state blocking
    (hstate : RuntimeWellFormed state)
    (hscheduler : blocking.ipc.scheduler = state.scheduler)
    (hcurrent : state.scheduler.lifecycle.current.isSome = true) :
    RuntimeWellFormed (publishBlockingIPCContext state blocking) := by
  have hclosed : RuntimeWellFormed
      { state with execution :=
          { state.execution with returnAuthorityArmed := false, copyOverride := false } } := by
    unfold RuntimeWellFormed CompositeState.Coherent WellFormed at hstate ⊢
    rcases hstate with
      ⟨hcoherent, ⟨hcore, _hbound, hentry⟩, hlifecycle, hcapabilities,
        hvirtual, hipc, hschedulerWellFormed, hpreemption, hresumable,
        htransfers, hterminal, hlive⟩
    exact ⟨hcoherent, ⟨hcore, by simp, hentry⟩, hlifecycle, hcapabilities,
      hvirtual, hipc, hschedulerWellFormed, hpreemption, hresumable,
      htransfers, hterminal,
      ⟨by simp, by simpa [CompositeState.BlockingIPCCoherent] using hlive.2⟩⟩
  rcases hclosed with
    ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
      hschedulerWellFormed, hpreemption, hresumable, htransfers, hterminal,
      hlive, _hblocking, hportControls⟩
  rcases hcoherent with
    ⟨hexecutionLifecycle, hschedulerLifecycle, hpreemptionScheduler,
      hcapabilitiesLifecycle, hmemoryCapabilities, hipcVirtual,
      hipcCapabilities, hresumableScheduler, htranslationVirtual,
      htransferEndpoints, hauthority, hdeadMailbox, hliveSender⟩
  have hcurrentLifecycle : state.lifecycle.current.isSome = true := by
    rw [hschedulerLifecycle] at hcurrent
    exact hcurrent
  have hcoreUpdate :
      { state.execution.core with lifecycle := state.lifecycle } = state.execution.core := by
    rw [← hexecutionLifecycle]
  have hcoreSchedulerUpdate :
      { state.execution.core with lifecycle := state.scheduler.lifecycle } =
        state.execution.core := by
    rw [hschedulerLifecycle]
    exact hcoreUpdate
  have hpreemptionUpdate :
      { state.preemption with scheduler := state.scheduler } = state.preemption := by
    rw [← hpreemptionScheduler]
  have hresumableUpdate :
      { state.resumable with scheduler := state.scheduler } = state.resumable := by
    rw [← hresumableScheduler]
  have hcoherentTail :
      state.execution.core.lifecycle = state.scheduler.lifecycle ∧
      state.preemption.scheduler = state.scheduler ∧
      state.capabilities = state.scheduler.lifecycle.capabilities ∧
      state.virtualMemory.memory.capabilities = state.scheduler.lifecycle.capabilities ∧
      state.ipc.virtualMemory = state.virtualMemory ∧
      state.ipc.endpoints.capabilities = state.scheduler.lifecycle.capabilities ∧
      state.resumable.scheduler = state.scheduler ∧
      state.resumable.translations.virtual = state.virtualMemory ∧
      state.transfers.toEndpointState = state.ipc.endpoints ∧
      (∀ subject, state.scheduler.lifecycle.current = some subject →
        state.execution.core.context.currentSubject = subject ∧
        state.execution.core.context.activeAddressSpace = subject) ∧
      (∀ object, state.scheduler.lifecycle.capabilities.objects object ≠ true →
        state.ipc.endpoints.mailbox object = none) ∧
      (∀ object envelope, state.ipc.endpoints.mailbox object = some envelope →
        state.scheduler.lifecycle.capabilities.subjects envelope.sender = true) := by
    rw [hschedulerLifecycle]
    exact ⟨hexecutionLifecycle, hpreemptionScheduler, hcapabilitiesLifecycle,
      hmemoryCapabilities, hipcVirtual, hipcCapabilities, hresumableScheduler,
      htranslationVirtual, htransferEndpoints, hauthority, hdeadMailbox,
      hliveSender⟩
  have hlifecycleScheduler :
      SubjectLifecycle.WellFormed state.scheduler.lifecycle := by
    rw [hschedulerLifecycle]
    exact hlifecycle
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    publishBlockingIPCContext_coherent state blocking, ?_⟩
  · simpa [CompositeState.Coherent, publishBlockingIPCContext, hscheduler,
      hcurrent, hcoreSchedulerUpdate, hpreemptionUpdate, hresumableUpdate] using
      hcoherentTail
  · simpa [publishBlockingIPCContext, hscheduler, hcurrent,
      hcoreSchedulerUpdate] using hexecution
  · simpa [publishBlockingIPCContext, hscheduler] using hlifecycleScheduler
  · simpa [publishBlockingIPCContext] using hcapabilities
  · simpa [publishBlockingIPCContext] using hvirtual
  · simpa [publishBlockingIPCContext] using hipc
  · simpa [publishBlockingIPCContext, hscheduler] using hschedulerWellFormed
  · simpa [publishBlockingIPCContext, hscheduler, hpreemptionUpdate] using hpreemption
  · simpa [publishBlockingIPCContext, hscheduler, hcurrent,
      hresumableUpdate] using hresumable
  · simpa [publishBlockingIPCContext] using htransfers
  · simpa [publishBlockingIPCContext, hscheduler, hcurrent,
      hresumableUpdate] using hterminal
  · simp [publishBlockingIPCContext]
  · simpa [publishBlockingIPCContext] using hportControls

/-- Publishing the terminal half of a block preserves the complete runtime
invariant when no peer is ready.  The outgoing current subject is marked
non-runnable and saved only in the blocking bank; the resumable bank therefore
keeps its existing entries while the active translation is cleared. -/
theorem publishBlockingIPCContext_idleBlock_preserves_runtimeWellFormed
    state blocking caller
    (hstate : RuntimeWellFormed state)
    (hblocking : BlockingIPCContext.WellFormed blocking)
    (hcurrent : state.scheduler.lifecycle.current = some caller)
    (hready : state.scheduler.ready = [])
    (hscheduler : blocking.ipc.scheduler =
      { state.scheduler with
        lifecycle := { state.scheduler.lifecycle with
          runnable := SubjectLifecycle.setBool
            state.scheduler.lifecycle.runnable caller false
          current := none } }) :
    RuntimeWellFormed (publishBlockingIPCContext state blocking) := by
  rcases hstate with
    ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
      hschedulerWellFormed, hpreemption, hresumable, htransfers, hterminal,
      hlive, hblockingCoherent, hportControls⟩
  rcases hcoherent with
    ⟨hexecutionLifecycle, hschedulerLifecycle, hpreemptionScheduler,
      hcapabilitiesLifecycle, hmemoryCapabilities, hipcVirtual,
      hipcCapabilities, hresumableScheduler, htranslationVirtual,
      htransferEndpoints, hauthority, hdeadMailbox, hliveSender⟩
  rcases hresumable with
    ⟨_hresumableSchedulerWellFormed, hcapacity, hunique, hvalid, habsent,
      hreadyContexts, htranslation, hvirtualAgreement, hkinds, _htlb⟩
  have hnextScheduler : Scheduler.WellFormed blocking.ipc.scheduler := hblocking.1.1
  have hcallerAbsent :
      ResumablePreemption.contextFor state.resumable.contexts caller = none :=
    habsent caller (by simpa [hresumableScheduler] using hcurrent)
  have hnoCallerContext : ∀ context ∈ state.resumable.contexts,
      context.owner ≠ caller := by
    intro context hcontext heq
    subst caller
    have hsome : (ResumablePreemption.contextFor
        state.resumable.contexts context.owner).isSome := by
      rw [ResumablePreemption.contextFor, List.find?_isSome]
      exact ⟨context, hcontext, by simp⟩
    simp [hcallerAbsent] at hsome
  have hresumableNext : ResumablePreemption.WellFormed
      (publishBlockingIPCContext state blocking).resumable := by
    refine ⟨by simpa [publishBlockingIPCContext] using hnextScheduler,
      by simpa [publishBlockingIPCContext] using hcapacity,
      by simpa [publishBlockingIPCContext] using hunique, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro context hcontext
      have hold := hvalid context (by simpa [publishBlockingIPCContext] using hcontext)
      rcases hold with ⟨hframe, hspace, hlive, hrunnable, howner⟩
      refine ⟨hframe, hspace, ?_, ?_, ?_⟩
      · simpa [publishBlockingIPCContext, hscheduler, hresumableScheduler] using hlive
      · have hne := hnoCallerContext context
          (by simpa [publishBlockingIPCContext] using hcontext)
        simpa [publishBlockingIPCContext, hscheduler, hresumableScheduler,
          SubjectLifecycle.setBool, hne] using hrunnable
      · simpa [publishBlockingIPCContext, hscheduler, hresumableScheduler] using howner
    · intro subject hselected
      simp [publishBlockingIPCContext, hscheduler] at hselected
    · constructor
      · intro subject hmember
        simp [publishBlockingIPCContext, hscheduler, hready] at hmember
      · intro context hcontext hsuspended
        have hold := hreadyContexts.2 context
          (by simpa [publishBlockingIPCContext] using hcontext) hsuspended
        simp [hresumableScheduler, hready] at hold
    · constructor
      · simpa [publishBlockingIPCContext, hscheduler, hresumableScheduler] using
          htranslation.1
      · simp [publishBlockingIPCContext, hscheduler]
    · rcases hvirtualAgreement with ⟨hcaps, hwf⟩
      exact ⟨by simpa [publishBlockingIPCContext, hscheduler, hresumableScheduler] using hcaps,
        by
          simp only [publishBlockingIPCContext]
          split <;> exact hwf⟩
    · unfold ResumablePreemption.ResourceKindAgreement at hkinds ⊢
      simpa [publishBlockingIPCContext, hscheduler, hresumableScheduler] using hkinds
    · simp [publishBlockingIPCContext, hscheduler, TLB.Coherent]
  have hnextLifecycle : SubjectLifecycle.WellFormed
      blocking.ipc.scheduler.lifecycle := hnextScheduler.1
  have hnextExecution : WellFormed
      (publishBlockingIPCContext state blocking).execution := by
    rcases hexecution with ⟨_, _, hmode⟩
    exact ⟨by simpa [Interrupt.WellFormed, publishBlockingIPCContext] using hnextLifecycle,
      by simp [publishBlockingIPCContext],
      by simpa [publishBlockingIPCContext] using hmode⟩
  have hnextPreemption : Preemption.WellFormed
      (publishBlockingIPCContext state blocking).preemption := by
    exact ⟨by simpa [publishBlockingIPCContext] using hnextScheduler,
      by simpa [publishBlockingIPCContext] using hpreemption.2⟩
  have hnextCoherent : (publishBlockingIPCContext state blocking).Coherent := by
    unfold CompositeState.Coherent
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [publishBlockingIPCContext, hscheduler, hschedulerLifecycle] using
        hcapabilitiesLifecycle
    · simpa [publishBlockingIPCContext, hscheduler, hschedulerLifecycle] using
        hmemoryCapabilities
    · simpa [publishBlockingIPCContext] using hipcVirtual
    · simpa [publishBlockingIPCContext, hscheduler, hschedulerLifecycle] using
        hipcCapabilities
    · simpa using htranslationVirtual
    · simpa [publishBlockingIPCContext] using htransferEndpoints
    · intro subject hselected
      simp [publishBlockingIPCContext, hscheduler] at hselected
    · intro object hdead
      apply hdeadMailbox object
      simpa [publishBlockingIPCContext, hscheduler, hschedulerLifecycle] using hdead
    · intro object envelope hmailbox
      have hold := hliveSender object envelope (by
        simpa [publishBlockingIPCContext] using hmailbox)
      simpa [publishBlockingIPCContext, hscheduler, hschedulerLifecycle] using hold
  refine ⟨hnextCoherent, hnextExecution, hnextLifecycle, ?_, ?_, ?_, hnextScheduler,
    hnextPreemption, hresumableNext, ?_, ?_, ?_,
    publishBlockingIPCContext_coherent state blocking, ?_⟩
  · simpa [publishBlockingIPCContext, hscheduler, hschedulerLifecycle] using hcapabilities
  · simpa [publishBlockingIPCContext] using hvirtual
  · simpa [publishBlockingIPCContext] using hipc
  · simpa [publishBlockingIPCContext] using htransfers
  · simpa [publishBlockingIPCContext] using hterminal
  · simp [publishBlockingIPCContext]
  · simpa [publishBlockingIPCContext] using hportControls

/-- Restore a released blocking context into the authoritative resumable bank
before making its owner visible as ready.  Every check is finite and mirrors
the corresponding `ResumablePreemption.WellFormed` obligation. -/
def publishReleasedBlockingContext (state : CompositeState)
    (blocking : BlockingIPCContext.State) (saved : ResumableContext.Context) :
    Except ResumablePreemption.Error CompositeState :=
  if !Interrupt.validSavedUserFrame saved.frame || saved.addressSpace != saved.owner ||
      saved.kind != .suspended then
    .error .staleDestination
  else if blocking.ipc.scheduler.lifecycle.capabilities.subjects saved.owner != true ||
      blocking.ipc.scheduler.lifecycle.runnable saved.owner != true ||
      blocking.ipc.scheduler.lifecycle.addressOwner saved.addressSpace != some saved.owner ||
      !(saved.owner ∈ blocking.ipc.scheduler.ready) then
    .error .staleDestination
  else if (ResumablePreemption.contextFor state.resumable.contexts saved.owner).isSome then
    .error .duplicateSave
  else if state.resumable.capacity ≤ state.resumable.contexts.length then
    .error .bankFull
  else
    let published := publishBlockingIPCContext state blocking
    .ok { published with resumable := { published.resumable with
      contexts := saved :: state.resumable.contexts } }

theorem publishReleasedBlockingContext_restores_exact state blocking saved next
    (hpublished : publishReleasedBlockingContext state blocking saved = .ok next) :
    ResumablePreemption.contextFor next.resumable.contexts saved.owner = some saved ∧
      next.blockingIPCContext = blocking := by
  unfold publishReleasedBlockingContext at hpublished
  split at hpublished <;> try contradiction
  split at hpublished <;> try contradiction
  split at hpublished <;> try contradiction
  split at hpublished <;> try contradiction
  simp only [Except.ok.injEq] at hpublished
  subst next
  constructor
  · simp [ResumablePreemption.contextFor]
  · rfl

/-- Publishing a released waiter cannot overflow the authoritative resumable
bank or introduce a second context for the same owner.  These are the two
structural context-bank obligations discharged entirely by the publisher's
finite duplicate and capacity checks; later wake-preservation proofs can use
them without unfolding the blocking transition. -/
theorem publishReleasedBlockingContext_preserves_bankStructure
    state blocking saved next
    (hstate : ResumablePreemption.WellFormed state.resumable)
    (hpublished : publishReleasedBlockingContext state blocking saved = .ok next) :
    next.resumable.contexts.length ≤ next.resumable.capacity ∧
      next.resumable.contexts.Pairwise
        (fun first second => first.owner ≠ second.owner) := by
  rcases hstate with ⟨_, hcapacity, hunique, _, _, _, _, _, _, _⟩
  unfold publishReleasedBlockingContext at hpublished
  split at hpublished <;> try contradiction
  split at hpublished <;> try contradiction
  next hduplicate =>
    split at hpublished <;> try contradiction
    next hfull =>
      split at hpublished <;> try contradiction
      simp only [Except.ok.injEq] at hpublished
      subst next
      constructor
      · change (saved :: state.resumable.contexts).length ≤
          state.resumable.capacity
        simp only [List.length_cons]
        omega
      · apply List.pairwise_cons.mpr
        constructor
        · intro context hcontext heq
          apply hfull
          rw [ResumablePreemption.contextFor, List.find?_isSome]
          exact ⟨context, hcontext, by simp [heq]⟩
        · exact hunique

/-- The released context installed by a successful publication is valid for
the scheduler and lifecycle that the same publication makes authoritative.
In particular, liveness, runnable status, and address-space ownership are
checked against the post-wake/post-cancellation scheduler rather than inferred
from the stale pre-release runtime projection. -/
theorem publishReleasedBlockingContext_published_valid
    state blocking saved next
    (hpublished : publishReleasedBlockingContext state blocking saved = .ok next) :
    ResumablePreemption.validContext next.resumable saved := by
  unfold publishReleasedBlockingContext at hpublished
  split at hpublished <;> try contradiction
  next hframe =>
    split at hpublished <;> try contradiction
    next hauthority =>
      split at hpublished <;> try contradiction
      split at hpublished <;> try contradiction
      simp only [Except.ok.injEq] at hpublished
      subst next
      simp_all [publishBlockingIPCContext, ResumablePreemption.validContext]

/-- Publishing a released waiter preserves the complete composite invariant
when the dependency scheduler performs the canonical wake mutation: it keeps
the current subject and all authority projections fixed, marks exactly the
released owner runnable, and appends that owner to the ready queue. -/
theorem publishReleasedBlockingContext_wake_preserves_runtimeWellFormed
    state blocking saved next
    (hstate : RuntimeWellFormed state)
    (hblocking : BlockingIPCContext.WellFormed blocking)
    (hscheduler : blocking.ipc.scheduler =
      { state.scheduler with
        ready := state.scheduler.ready ++ [saved.owner]
        lifecycle := { state.scheduler.lifecycle with
          runnable := SubjectLifecycle.setBool
            state.scheduler.lifecycle.runnable saved.owner true } })
    (hpublished : publishReleasedBlockingContext state blocking saved = .ok next) :
    RuntimeWellFormed next := by
  rcases hstate with
    ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
      hschedulerWellFormed, hpreemption, hresumable, htransfers, hterminal,
      hlive, hblockingCoherent, hportControls⟩
  rcases hcoherent with
    ⟨hexecutionLifecycle, hschedulerLifecycle, hpreemptionScheduler,
      hcapabilitiesLifecycle, hmemoryCapabilities, hipcVirtual,
      hipcCapabilities, hresumableScheduler, htranslationVirtual,
      htransferEndpoints, hauthority, hdeadMailbox, hliveSender⟩
  rcases hresumable with
    ⟨hresumableWellFormedScheduler, _hcapacity, _hunique, hvalid, habsent, hready,
      htranslation, hvirtualAgreement, hkinds, htlb⟩
  have hnextScheduler : Scheduler.WellFormed blocking.ipc.scheduler := hblocking.1.1
  have hbank := publishReleasedBlockingContext_preserves_bankStructure
    state blocking saved next
    (show ResumablePreemption.WellFormed state.resumable from
      ⟨hresumableWellFormedScheduler, _hcapacity, _hunique, hvalid, habsent, hready,
        htranslation, hvirtualAgreement, hkinds, htlb⟩)
    hpublished
  have hsavedValid := publishReleasedBlockingContext_published_valid
    state blocking saved next hpublished
  have hnextShape : next =
      { publishBlockingIPCContext state blocking with
        resumable := { (publishBlockingIPCContext state blocking).resumable with
          contexts := saved :: state.resumable.contexts } } := by
    unfold publishReleasedBlockingContext at hpublished
    split at hpublished <;> try contradiction
    split at hpublished <;> try contradiction
    split at hpublished <;> try contradiction
    split at hpublished <;> try contradiction
    simpa using hpublished.symm
  have hsavedReady : saved.owner ∈ blocking.ipc.scheduler.ready := by
    unfold publishReleasedBlockingContext at hpublished
    split at hpublished <;> try contradiction
    next hframe =>
      split at hpublished <;> try contradiction
      next hauthority => simp_all
  have hbankShape :
      (saved :: state.resumable.contexts).length ≤ state.resumable.capacity ∧
        (saved :: state.resumable.contexts).Pairwise
          (fun first second => first.owner ≠ second.owner) := by
    simpa [hnextShape, publishBlockingIPCContext] using hbank
  have hresumableNext : ResumablePreemption.WellFormed next.resumable := by
    rw [hnextShape]
    refine ⟨hnextScheduler, hbankShape.1, hbankShape.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro context hcontext
      simp only [List.mem_cons] at hcontext
      rcases hcontext with rfl | hcontext
      · simpa [hnextShape] using hsavedValid
      · obtain ⟨hframe, hspace, hliveContext, hrunnable, howner⟩ :=
          hvalid context hcontext
        have hne : context.owner ≠ saved.owner := by
          exact Ne.symm ((List.pairwise_cons.mp hbankShape.2).1 context hcontext)
        refine ⟨hframe, hspace, ?_, ?_, ?_⟩
        · simpa [publishBlockingIPCContext, hscheduler, hresumableScheduler,
            hschedulerLifecycle] using hliveContext
        · simpa [publishBlockingIPCContext, hscheduler, hresumableScheduler,
            SubjectLifecycle.setBool, hne] using hrunnable
        · simpa [publishBlockingIPCContext, hscheduler, hresumableScheduler,
            hschedulerLifecycle] using howner
    · intro subject hcurrent
      simp only [ResumablePreemption.contextFor, List.find?_cons]
      have hsubject : saved.owner ≠ subject := by
        intro heq
        subst subject
        exact (hnextScheduler.2.2.2.2 saved.owner hcurrent).2.2.2 hsavedReady
      rw [show (saved.owner == subject) = false by simp [hsubject]]
      apply habsent subject
      simpa [publishBlockingIPCContext, hscheduler, hresumableScheduler] using hcurrent
    · constructor
      · intro subject hmember
        simp [publishBlockingIPCContext, hscheduler] at hmember
        rcases hmember with hold | rfl
        · obtain ⟨context, hcontext, howner⟩ := hready.1 subject (by
            simpa [hresumableScheduler] using hold)
          exact ⟨context, by simp [hcontext], howner⟩
        · exact ⟨saved, by simp⟩
      · intro context hcontext hsuspended
        simp only [List.mem_cons] at hcontext
        rcases hcontext with rfl | hcontext
        · exact hsavedReady
        · have hold := hready.2 context hcontext hsuspended
          have hold' : context.owner ∈ state.scheduler.ready := by
            simpa [hresumableScheduler] using hold
          simp [publishBlockingIPCContext, hscheduler, hold']
    · rcases htranslation with ⟨howner, hactive⟩
      constructor
      · simpa [hscheduler, hresumableScheduler] using howner
      · cases hcurrent : state.scheduler.lifecycle.current with
        | none => simp [publishBlockingIPCContext, hscheduler, hcurrent]
        | some subject =>
            simpa [publishBlockingIPCContext, hscheduler, hresumableScheduler,
              hcurrent] using hactive
    · rcases hvirtualAgreement with ⟨hcaps, hwf⟩
      constructor
      · simpa [hscheduler, hresumableScheduler] using hcaps
      · simpa using hwf
    · unfold ResumablePreemption.ResourceKindAgreement at hkinds ⊢
      simpa [publishBlockingIPCContext, hscheduler, hresumableScheduler] using hkinds
    · by_cases hcurrent : state.scheduler.lifecycle.current.isSome = true
      · simpa [publishBlockingIPCContext, hscheduler, hcurrent] using htlb
      · have hcurrentFalse : state.scheduler.lifecycle.current.isSome = false := by
          simpa using hcurrent
        simp [publishBlockingIPCContext, hscheduler, hcurrentFalse, TLB.Coherent]
  have hnextLifecycle : SubjectLifecycle.WellFormed blocking.ipc.scheduler.lifecycle :=
    hnextScheduler.1
  have hnextExecution : WellFormed
      (publishBlockingIPCContext state blocking).execution := by
    rcases hexecution with ⟨_, _, hmode⟩
    refine ⟨?_, by simp [publishBlockingIPCContext], ?_⟩
    · change SubjectLifecycle.WellFormed blocking.ipc.scheduler.lifecycle
      exact hnextLifecycle
    · simpa [publishBlockingIPCContext] using hmode
  have hnextPreemption : Preemption.WellFormed
      (publishBlockingIPCContext state blocking).preemption := by
    exact ⟨hnextScheduler, by simpa [publishBlockingIPCContext] using hpreemption.2⟩
  have hnextCoherent :
      (publishBlockingIPCContext state blocking).Coherent := by
    unfold CompositeState.Coherent
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [publishBlockingIPCContext, hscheduler, hschedulerLifecycle] using
        hcapabilitiesLifecycle
    · simpa [publishBlockingIPCContext, hscheduler, hschedulerLifecycle] using
        hmemoryCapabilities
    · simpa [publishBlockingIPCContext] using hipcVirtual
    · simpa [publishBlockingIPCContext, hscheduler, hschedulerLifecycle] using
        hipcCapabilities
    · simpa using htranslationVirtual
    · simpa [publishBlockingIPCContext] using htransferEndpoints
    · intro subject hcurrent
      apply hauthority subject
      simpa [publishBlockingIPCContext, hscheduler, hschedulerLifecycle] using hcurrent
    · intro object hdead
      apply hdeadMailbox object
      simpa [publishBlockingIPCContext, hscheduler, hschedulerLifecycle] using hdead
    · intro object envelope hmailbox
      have hold := hliveSender object envelope (by
        simpa [publishBlockingIPCContext] using hmailbox)
      simpa [publishBlockingIPCContext, hscheduler, hschedulerLifecycle] using hold
  rw [hnextShape] at hresumableNext ⊢
  refine ⟨hnextCoherent, hnextExecution, hnextLifecycle, ?_, ?_, ?_, hnextScheduler,
    hnextPreemption, hresumableNext, ?_, ?_, by simp [publishBlockingIPCContext],
    publishBlockingIPCContext_coherent state blocking, ?_⟩
  · simpa [publishBlockingIPCContext, hscheduler, hschedulerLifecycle] using hcapabilities
  · simpa [publishBlockingIPCContext] using hvirtual
  · simpa [publishBlockingIPCContext] using hipc
  · simpa [publishBlockingIPCContext] using htransfers
  · simpa [publishBlockingIPCContext] using hterminal
  · simpa [publishBlockingIPCContext] using hportControls

/-- The capacity-checked drain closes the contained-fault cleanup loop: every
typed denial is atomic, while success moves exactly one quiescent retained
context into the resumable bank and preserves both the global runtime
invariant and the classification of all remaining deferred contexts. -/
theorem drainDeferredCancellation_preserves_deferredBlockingRuntimeWellFormed
    state subject (hstate : DeferredBlockingRuntimeWellFormed state) :
    DeferredBlockingRuntimeWellFormed
      (drainDeferredCancellation state subject).state := by
  simp only [drainDeferredCancellation]
  generalize houtcome : BlockingIPCContext.drainDeferred state.blockingIPCContext
    state.deferredCancels state.resumable.contexts state.resumable.capacity subject = outcome
  cases outcome with
  | mk next nextDeferred nextResumable result =>
      cases result with
      | rejected reason => exact hstate
      | drained saved =>
          simp only
          have hresult :
              (BlockingIPCContext.drainDeferred state.blockingIPCContext
                state.deferredCancels state.resumable.contexts
                state.resumable.capacity subject).result = .drained saved := by
            rw [houtcome]
          have hexact := BlockingIPCContext.drainDeferred_drained_exact
            state.blockingIPCContext state.deferredCancels state.resumable.contexts
            state.resumable.capacity subject saved hresult
          have hcapacity := BlockingIPCContext.drainDeferred_drained_reserves_capacity
            state.blockingIPCContext state.deferredCancels state.resumable.contexts
            state.resumable.capacity subject saved hresult
          have hschedulerExact :=
            BlockingIPCContext.drainDeferred_drained_scheduler_exact
              state.blockingIPCContext state.deferredCancels state.resumable.contexts
              state.resumable.capacity subject saved hresult
          have hdeferredExact :=
            BlockingIPCContext.drainDeferred_drained_deferred_exact
              state.blockingIPCContext state.deferredCancels state.resumable.contexts
              state.resumable.capacity subject saved hresult
          have hdeferred := BlockingIPCContext.drainDeferred_preserves_deferredWellFormed
            state.blockingIPCContext state.deferredCancels state.resumable.contexts
            state.resumable.capacity subject hstate.2.1
          rw [houtcome] at hexact hcapacity hschedulerExact hdeferredExact hdeferred
          change nextDeferred =
            BlockingIPCContext.setRetained state.deferredCancels subject none at hdeferredExact
          rcases hexact with
            ⟨hretained, hremoved, hrunnable, hready, _hcompletion, hcontexts⟩
          rcases hcapacity with
            ⟨hvalid, _hlive, howns, _hunique, _hreadyRoom, hbankRoom,
              hscheduler, _hcontexts⟩
          have howner : saved.owner = subject :=
            BlockingIPCContext.validSaved_owner subject saved hvalid
          have hvalidParts := hvalid
          simp only [BlockingIPCContext.validSaved, Bool.and_eq_true,
            beq_iff_eq] at hvalidParts
          have hkind : saved.kind = .suspended := by
            exact BlockingIPCContext.validSaved_kind subject saved hvalid
          have hkindNe : (saved.kind != .suspended) = false := by
            rw [hkind]
            rfl
          have hnextLive : next.ipc.scheduler.lifecycle.capabilities.subjects subject = true := by
            rw [hschedulerExact]
            simpa [CompositeState.blockingIPCContext] using _hlive
          have hnextAddress :
              next.ipc.scheduler.lifecycle.addressOwner saved.addressSpace = some subject := by
            have haddress :
                state.blockingIPC.scheduler.lifecycle.addressOwner subject = some subject := by
              simpa [CompositeState.blockingIPCContext,
                Scheduler.ownsAddressSpace_eq_some_iff] using howns
            rw [hschedulerExact]
            simpa [CompositeState.blockingIPCContext, hvalidParts.1.1.2] using haddress
          have habsent := hstate.2.2.2 subject saved hretained
          have hblockedExact : next.blocked = state.blockingContexts := by
            simp only [BlockingIPCContext.drainDeferred] at houtcome
            split at houtcome <;> try simp_all
            all_goals try (split at houtcome <;> try simp_all)
            all_goals try (split at houtcome <;> try simp_all)
            all_goals try (split at houtcome <;> try simp_all)
            all_goals try (split at houtcome <;> try simp_all)
            all_goals try (split at houtcome <;> try simp_all)
            all_goals try (split at houtcome <;> try simp_all)
            all_goals rcases houtcome with ⟨rfl, rfl, rfl, rfl⟩
            all_goals rfl
          have hbaseRuntime : RuntimeWellFormed
              { state with deferredCancels := nextDeferred } := by
            change RuntimeWellFormed state
            exact hstate.1
          let published : CompositeState :=
            { publishBlockingIPCContext { state with deferredCancels := nextDeferred } next with
              resumable :=
                { (publishBlockingIPCContext
                    { state with deferredCancels := nextDeferred } next).resumable with
                  contexts := saved :: state.resumable.contexts } }
          have hpublished :
              publishReleasedBlockingContext
                  { state with deferredCancels := nextDeferred } next saved =
                .ok published := by
            unfold publishReleasedBlockingContext
            rw [ite_eq_right (by simp [hvalidParts, hkindNe])]
            rw [ite_eq_right (by
              simp [hnextLive, hnextAddress, hready, howner]
              exact hrunnable)]
            rw [ite_eq_right (by simp [habsent, howner])]
            rw [ite_eq_right hbankRoom]
          have hruntime : RuntimeWellFormed published :=
            publishReleasedBlockingContext_wake_preserves_runtimeWellFormed
              { state with deferredCancels := nextDeferred } next saved published
              hbaseRuntime hdeferred.1 (by
                simpa [howner, CompositeState.blockingIPCContext,
                  hstate.1.blockingScheduler] using hschedulerExact) hpublished
          have hshape : publishDeferredDrain state
              { state := next, deferred := nextDeferred, resumable := nextResumable,
                result := .drained saved } = published := by
            unfold publishDeferredDrain published publishBlockingIPCContext
            rw [hcontexts]
          rw [hshape]
          change DeferredBlockingRuntimeWellFormed published
          refine ⟨hruntime, hdeferred, ?_, ?_⟩
          · intro candidate actual hblocked
            have hblockedOld : state.blockingContexts candidate = some actual := by
              simpa [published, publishBlockingIPCContext, hblockedExact] using hblocked
            have hne : candidate ≠ subject := by
              intro heq
              subst candidate
              have hsome : (state.blockingIPCContext.blocked subject).isSome = true := by
                simp [CompositeState.blockingIPCContext, hblockedOld]
              have hnone := hstate.2.1.2.1 subject hsome
              rw [hretained] at hnone
              contradiction
            have holdAbsent := hstate.2.2.1 candidate actual hblockedOld
            simp only [published, publishBlockingIPCContext]
            simp only [ResumablePreemption.contextFor, List.find?_cons]
            rw [show (saved.owner == candidate) = false by simp [howner, Ne.symm hne]]
            exact holdAbsent
          intro candidate actual hcanceled
          have hne : candidate ≠ subject := by
            intro heq
            subst candidate
            have hold : nextDeferred.retained subject = some actual := by
              simpa [published, publishBlockingIPCContext] using hcanceled
            rw [hremoved] at hold
            contradiction
          simp only [published, publishBlockingIPCContext]
          simp only [ResumablePreemption.contextFor, List.find?_cons]
          rw [show (saved.owner == candidate) = false by simp [howner, Ne.symm hne]]
          have hcanceled' : nextDeferred.retained candidate = some actual := by
            simpa [published, publishBlockingIPCContext] using hcanceled
          have hcanceledOld : state.deferredCancels.retained candidate = some actual := by
            have hd : nextDeferred =
                BlockingIPCContext.setRetained state.deferredCancels subject none :=
              hdeferredExact
            rw [hd] at hcanceled'
            simpa [BlockingIPCContext.setRetained, hne] using hcanceled'
          exact hstate.2.2.2 candidate actual hcanceledOld

theorem publishReleasedBlockingContext_blockingCoherent state blocking saved next
    (hpublished : publishReleasedBlockingContext state blocking saved = .ok next) :
    next.BlockingIPCCoherent := by
  rw [show next.BlockingIPCCoherent =
      (publishBlockingIPCContext state blocking).BlockingIPCCoherent by
    simp only [CompositeState.BlockingIPCCoherent]
    unfold publishReleasedBlockingContext at hpublished
    split at hpublished <;> try contradiction
    split at hpublished <;> try contradiction
    split at hpublished <;> try contradiction
    split at hpublished <;> try contradiction
    simp only [Except.ok.injEq] at hpublished
    subst next
    rfl]
  exact publishBlockingIPCContext_coherent state blocking

/-- A published wake retains the exact reserved envelope and makes the same
receiver runnable in the scheduler observed by the rest of the composite. -/
theorem publishBlockingIPC_wake_coherent state blockingIPC endpoint receiver envelope :
    let next := publishBlockingIPC state
      (BlockingIPC.wakeState blockingIPC endpoint receiver envelope)
    next.blockingIPC.completion receiver = some (.delivered envelope) ∧
      next.scheduler.lifecycle.runnable receiver = true ∧
      next.blockingIPC.scheduler = next.scheduler := by
  simp [BlockingIPC.wake_reserves_exact_envelope,
    BlockingIPC.wake_marks_receiver_runnable]

inductive BlockingIPCCall where
  | receive (handleWord : UInt64)
  | send (handleWord word0 word1 : UInt64)
  deriving DecidableEq, Repr

/-- Finite public observation of a blocking transition.  Receive retains the
dependency's typed `delivered`/`blocked`/rejected result; send distinguishes a
mailbox enqueue from the successful wake of one FIFO receiver. -/
inductive CompositeBlockingIPCReply where
  | receive (result : BlockingIPC.WordReceiveResult)
  | sendHandleRejected (reason : CapabilityHandle.WordResolveDenial)
  | sendRejected (reason : BlockingIPC.Error)
  | sent
  | woke (receiver : BlockingIPC.SubjectId)
  deriving DecidableEq, Repr

structure CompositeBlockingIPCOutcome where
  state : CompositeState
  reply : CompositeBlockingIPCReply

/-- The finite blocking-IPC replies that denote an ordinary, nonfatal
rejection.  Keeping this classifier separate from successful delivery,
blocking, enqueue, and wake replies prevents a generic wrapper from treating a
state-changing success as a rejection (or vice versa). -/
inductive CompositeBlockingIPCRejection : CompositeBlockingIPCReply → Prop
  | receiveHandle reason :
      CompositeBlockingIPCRejection (.receive (.handleRejected reason))
  | receive reason :
      CompositeBlockingIPCRejection (.receive (.completed (.rejected reason)))
  | sendHandle reason :
      CompositeBlockingIPCRejection (.sendHandleRejected reason)
  | send reason :
      CompositeBlockingIPCRejection (.sendRejected reason)

/-- Total authoritative blocking dispatcher.  Caller identity is projected
from the execution latch.  On success the dependency's scheduler is published
atomically with its waiter/completion state; every typed rejection returns the
identical composite state. -/
def dispatchBlockingIPC (state : CompositeState)
    (call : BlockingIPCCall) : CompositeBlockingIPCOutcome :=
  let caller := state.execution.core.context.currentSubject
  match call with
  | .receive handleWord =>
      let outcome := BlockingIPC.receiveOrBlockWord state.blockingIPC caller handleWord
      match outcome.result with
      | .handleRejected reason => { state, reply := .receive (.handleRejected reason) }
      | .completed (.rejected reason) =>
          { state, reply := .receive (.completed (.rejected reason)) }
      | .completed result =>
          { state := publishBlockingIPC state outcome.state
            reply := .receive (.completed result) }
  | .send handleWord word0 word1 =>
      let payload : BlockingIPC.Payload := { word0, word1 }
      let outcome := BlockingIPC.sendWord state.blockingIPC caller handleWord payload
      match outcome.result with
      | .handleRejected reason => { state, reply := .sendHandleRejected reason }
      | .completed (.rejected reason) => { state, reply := .sendRejected reason }
      | .completed .accepted =>
          let reply :=
            match CapabilityHandle.resolveCurrent
                state.blockingIPC.scheduler.lifecycle.capabilities
                { caller } handleWord .endpoint with
            | .error _ => CompositeBlockingIPCReply.sent
            | .ok resolution =>
                match state.blockingIPC.waiters resolution.capability.object with
                | [] => .sent
                | receiver :: _ => .woke receiver
          { state := publishBlockingIPC state outcome.state, reply }

/-- Every ordinary blocking-IPC rejection is globally atomic.  In particular,
the composite boundary does not publish dependency-local cleanup performed
while observing a cancelled completion; callers see the exact pre-state until
a successful operation consumes or replaces that authoritative completion. -/
theorem dispatchBlockingIPC_rejection_atomic state call reply
    (hrejected : CompositeBlockingIPCRejection reply)
    (hreply : (dispatchBlockingIPC state call).reply = reply) :
    (dispatchBlockingIPC state call).state = state := by
  cases call with
  | receive handleWord =>
      cases hresult : (BlockingIPC.receiveOrBlockWord state.blockingIPC
          state.execution.core.context.currentSubject handleWord).result with
      | handleRejected reason => simp [dispatchBlockingIPC, hresult]
      | completed result =>
          cases result with
          | rejected reason => simp [dispatchBlockingIPC, hresult]
          | delivered envelope =>
              cases hrejected <;> simp [dispatchBlockingIPC, hresult] at hreply
          | blocked =>
              cases hrejected <;> simp [dispatchBlockingIPC, hresult] at hreply
  | send handleWord word0 word1 =>
      cases hresult : (BlockingIPC.sendWord state.blockingIPC
          state.execution.core.context.currentSubject handleWord { word0, word1 }).result with
      | handleRejected reason => simp [dispatchBlockingIPC, hresult]
      | completed result =>
          cases result with
          | rejected reason => simp [dispatchBlockingIPC, hresult]
          | accepted =>
              cases hresolve : CapabilityHandle.resolveCurrent
                  state.blockingIPC.scheduler.lifecycle.capabilities
                  { caller := state.execution.core.context.currentSubject }
                  handleWord .endpoint with
              | error reason =>
                  cases hrejected <;>
                    simp [dispatchBlockingIPC, hresult, hresolve] at hreply
              | ok resolution =>
                  cases hwaiters : state.blockingIPC.waiters
                      resolution.capability.object with
                  | nil =>
                      cases hrejected <;>
                        simp [dispatchBlockingIPC, hresult, hresolve, hwaiters] at hreply
                  | cons receiver rest =>
                      cases hrejected <;>
                        simp [dispatchBlockingIPC, hresult, hresolve, hwaiters] at hreply

/-- A dependency-level block is surfaced as `blocked`, and the exact state
containing the waiter registration and scheduler selection is published. -/
theorem dispatchBlockingIPC_blocked_exact state handleWord
    (hblocked : (BlockingIPC.receiveOrBlockWord state.blockingIPC
      state.execution.core.context.currentSubject handleWord).result =
        .completed .blocked) :
    dispatchBlockingIPC state (.receive handleWord) =
      { state := publishBlockingIPC state
          (BlockingIPC.receiveOrBlockWord state.blockingIPC
            state.execution.core.context.currentSubject handleWord).state
        reply := .receive (.completed .blocked) } := by
  simp [dispatchBlockingIPC, hblocked]

/-- An accepted send to a nonempty FIFO queue reports the exact receiver that
the dependency wakes and publishes the matching completion/scheduler state. -/
theorem dispatchBlockingIPC_woke_exact state handleWord word0 word1 resolution receiver rest
    (hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities
      { caller := state.execution.core.context.currentSubject }
      handleWord .endpoint = .ok resolution)
    (hwaiters : state.blockingIPC.waiters resolution.capability.object =
      receiver :: rest)
    (haccepted : (BlockingIPC.sendWord state.blockingIPC
      state.execution.core.context.currentSubject handleWord { word0, word1 }).result =
        .completed .accepted) :
    dispatchBlockingIPC state (.send handleWord word0 word1) =
      { state := publishBlockingIPC state
          (BlockingIPC.sendWord state.blockingIPC
            state.execution.core.context.currentSubject handleWord { word0, word1 }).state
        reply := .woke receiver } := by
  simp [dispatchBlockingIPC, haccepted, hresolve, hwaiters]

/-- Every authoritative blocking transition leaves the blocking scheduler and
the composite scheduler equal, including all typed rejection paths. -/
theorem dispatchBlockingIPC_scheduler_coherent state call
    (hcoherent : state.BlockingIPCCoherent) :
    (dispatchBlockingIPC state call).state.BlockingIPCCoherent := by
  rcases hcoherent with ⟨hscheduler, hlifecycle⟩
  cases call with
  | receive handleWord =>
      cases hresult : (BlockingIPC.receiveOrBlockWord state.blockingIPC
        state.execution.core.context.currentSubject handleWord).result with
      | handleRejected reason =>
          simpa [dispatchBlockingIPC, hresult] using
            (show state.BlockingIPCCoherent from ⟨hscheduler, hlifecycle⟩)
      | completed result =>
          cases result with
          | rejected reason =>
              simpa [dispatchBlockingIPC, hresult] using
                (show state.BlockingIPCCoherent from ⟨hscheduler, hlifecycle⟩)
          | delivered envelope =>
              simpa [dispatchBlockingIPC, hresult] using
                publishBlockingIPC_coherent state
                  (BlockingIPC.receiveOrBlockWord state.blockingIPC
                    state.execution.core.context.currentSubject handleWord).state
          | blocked =>
              simpa [dispatchBlockingIPC, hresult] using
                publishBlockingIPC_coherent state
                  (BlockingIPC.receiveOrBlockWord state.blockingIPC
                    state.execution.core.context.currentSubject handleWord).state
  | send handleWord word0 word1 =>
      cases hresult : (BlockingIPC.sendWord state.blockingIPC
        state.execution.core.context.currentSubject handleWord { word0, word1 }).result with
      | handleRejected reason =>
          simpa [dispatchBlockingIPC, hresult] using
            (show state.BlockingIPCCoherent from ⟨hscheduler, hlifecycle⟩)
      | completed result =>
          cases result with
          | rejected reason =>
              simpa [dispatchBlockingIPC, hresult] using
                (show state.BlockingIPCCoherent from ⟨hscheduler, hlifecycle⟩)
          | accepted =>
              simpa [dispatchBlockingIPC, hresult] using
                publishBlockingIPC_coherent state
                  (BlockingIPC.sendWord state.blockingIPC
                    state.execution.core.context.currentSubject handleWord
                    { word0, word1 }).state

/-! ## Context-owning public blocking receive

The legacy dispatcher above records the raw blocking state used by the finite
evidence traces.  The public composite operation below instead crosses the
typed successor: it constructs saved-context identity from the execution
latch, publishes the waiter store and context bank together, and returns a
finite typed reply. -/

inductive CompositeBlockingReceiveReply where
  | handleRejected (reason : CapabilityHandle.WordResolveDenial)
  | contextRejected (reason : BlockingIPCContext.ContextError)
  | rejected (reason : BlockingIPC.Error)
  | switchRequired
  | delivered (envelope : BlockingIPC.Envelope)
  | blocked
  deriving DecidableEq, Repr

structure CompositeBlockingReceiveOutcome where
  state : CompositeState
  reply : CompositeBlockingReceiveReply

/-- General-purpose registers and the hardware frame may carry user data, but
the subject, address-space identity, and context kind are selected solely from
the authoritative execution state. -/
def CompositeState.blockingSavedContext (state : CompositeState)
    (frame : Interrupt.HardwareFrame) (registers : ResumableContext.Registers) :
    ResumableContext.Context :=
  { owner := state.execution.core.context.currentSubject
    addressSpace := state.execution.core.context.activeAddressSpace
    frame
    registers
    kind := .suspended }

@[simp] theorem blockingSavedContext_owner (state : CompositeState) frame registers :
    (state.blockingSavedContext frame registers).owner =
      state.execution.core.context.currentSubject := rfl

@[simp] theorem blockingSavedContext_addressSpace (state : CompositeState) frame registers :
    (state.blockingSavedContext frame registers).addressSpace =
      state.execution.core.context.activeAddressSpace := rfl

/-- Complete a blocking scheduler handoff by consuming the context owned by
the scheduler-selected peer and switching the modeled CR3/TLB projection to
that peer's address space.  The selected identity is read only from the
post-block scheduler; neither the handle word nor the saved registers can
choose it. -/
def restoreBlockingPeer (state : CompositeState)
    (blocking : BlockingIPCContext.State) : Except ResumablePreemption.Error CompositeState :=
  match blocking.ipc.scheduler.lifecycle.current with
  | none => .error .noDestination
  | some selected =>
      match ResumablePreemption.contextFor state.resumable.contexts selected with
      | none => .error .noDestination
      | some destination =>
          if destination.owner != selected || destination.addressSpace != selected ||
              Interrupt.validSavedUserFrame destination.frame != true ||
              blocking.ipc.scheduler.lifecycle.capabilities.subjects destination.owner != true ||
              blocking.ipc.scheduler.lifecycle.runnable destination.owner != true ||
              blocking.ipc.scheduler.lifecycle.addressOwner destination.addressSpace !=
                some destination.owner ||
              state.resumable.translations.virtual.owner destination.addressSpace !=
                some destination.owner then
            .error .staleDestination
          else
            let published := publishBlockingIPCContext state blocking
            .ok { published with
              execution := { published.execution with
                core := { published.execution.core with
                  context := { published.execution.core.context with
                    currentSubject := destination.owner
                    activeAddressSpace := destination.addressSpace } }
                returnAuthorityArmed := false }
              resumable := { published.resumable with
                contexts := ResumablePreemption.eraseContext
                  state.resumable.contexts destination.owner
                translations := TLB.switch state.resumable.translations
                  destination.addressSpace } }

/-- A completed block handoff restores exactly the scheduler-selected peer,
consumes its saved bank entry, and models the required CR3 reload. -/
theorem restoreBlockingPeer_exact state blocking next
    (hrestore : restoreBlockingPeer state blocking = .ok next) :
    ∃ selected destination,
      blocking.ipc.scheduler.lifecycle.current = some selected ∧
      ResumablePreemption.contextFor state.resumable.contexts selected = some destination ∧
      next.execution.core.context.currentSubject = selected ∧
      next.execution.core.context.activeAddressSpace = destination.addressSpace ∧
      next.resumable.translations.active = some destination.addressSpace ∧
      next.resumable.translations.entries = [] ∧
      ResumablePreemption.contextFor next.resumable.contexts selected = none ∧
      next.blockingIPCContext = blocking := by
  simp only [restoreBlockingPeer] at hrestore
  split at hrestore <;> try contradiction
  next selected hselected =>
    split at hrestore <;> try contradiction
    next destination hdestination =>
      split at hrestore <;> try contradiction
      simp only [Except.ok.injEq] at hrestore
      subst next
      have howner : destination.owner = selected := by simp_all
      refine ⟨selected, destination, hselected, hdestination, howner, rfl, ?_, ?_, ?_, rfl⟩
      · simp [TLB.switch]
      · simp [TLB.switch]
      · rw [howner]
        exact ResumablePreemption.contextFor_erase_self _ _

theorem restoreBlockingPeer_context_exact state blocking next
    (hrestore : restoreBlockingPeer state blocking = .ok next) :
    next.blockingIPCContext = blocking := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hcontext⟩ :=
    restoreBlockingPeer_exact state blocking next hrestore
  exact hcontext

/-- The selected-peer restore consumes exactly the selected identity from the
resumable-context bank. -/
theorem restoreBlockingPeer_resumableContexts_exact state blocking next
    (hrestore : restoreBlockingPeer state blocking = .ok next) :
    ∃ selected destination,
      blocking.ipc.scheduler.lifecycle.current = some selected ∧
      ResumablePreemption.contextFor state.resumable.contexts selected =
        some destination ∧
      destination.owner = selected ∧
      next.resumable.contexts =
        ResumablePreemption.eraseContext state.resumable.contexts selected := by
  simp only [restoreBlockingPeer] at hrestore
  split at hrestore <;> try contradiction
  next selected hselected =>
    split at hrestore <;> try contradiction
    next destination hdestination =>
      split at hrestore <;> try contradiction
      simp only [Except.ok.injEq] at hrestore
      subst next
      have howner : destination.owner = selected := by simp_all
      refine ⟨selected, destination, hselected, hdestination, howner, ?_⟩
      simp [howner]

theorem restoreBlockingPeer_deferredExact state blocking next
    (hrestore : restoreBlockingPeer state blocking = .ok next) :
    next.deferredCancels = state.deferredCancels := by
  simp only [restoreBlockingPeer] at hrestore
  split at hrestore <;> try contradiction
  split at hrestore <;> try contradiction
  split at hrestore <;> try contradiction
  simp only [Except.ok.injEq] at hrestore
  subst next
  rfl

theorem restoreBlockingPeer_blockingCoherent state blocking next
    (hrestore : restoreBlockingPeer state blocking = .ok next) :
    next.BlockingIPCCoherent := by
  have hcontext := restoreBlockingPeer_context_exact state blocking next hrestore
  rw [show next.BlockingIPCCoherent =
      (publishBlockingIPCContext state blocking).BlockingIPCCoherent by
    simp only [CompositeState.BlockingIPCCoherent]
    unfold restoreBlockingPeer at hrestore
    split at hrestore <;> try contradiction
    split at hrestore <;> try contradiction
    split at hrestore <;> try contradiction
    simp only [Except.ok.injEq] at hrestore
    subst next
    rfl]
  exact publishBlockingIPCContext_coherent state blocking

/-- Publishing the selected half of a blocking receive preserves every global
runtime projection.  The outgoing caller is absent from the resumable bank,
the selected head is consumed from that bank, and the modeled TLB switches to
the same identity made current by the authoritative blocking scheduler. -/
theorem restoreBlockingPeer_preserves_runtimeWellFormed
    state blocking next caller selected rest
    (hstate : RuntimeWellFormed state)
    (hblocking : BlockingIPCContext.WellFormed blocking)
    (hcurrent : state.scheduler.lifecycle.current = some caller)
    (hready : state.scheduler.ready = selected :: rest)
    (hscheduler : blocking.ipc.scheduler =
      { state.scheduler with
        ready := rest
        lifecycle := { state.scheduler.lifecycle with
          runnable := SubjectLifecycle.setBool
            state.scheduler.lifecycle.runnable caller false
          current := some selected } })
    (hrestore : restoreBlockingPeer state blocking = .ok next) :
    RuntimeWellFormed next := by
  obtain ⟨actual, destination, hselected, hdestination, _, _, _, _, _, _⟩ :=
    restoreBlockingPeer_exact state blocking next hrestore
  have hactual : actual = selected := by
    rw [hscheduler] at hselected
    simpa using hselected.symm
  have hblockingSelected : blocking.ipc.scheduler.lifecycle.current = some selected := by
    rw [hscheduler]
  have hdestinationSelected : ResumablePreemption.contextFor
      state.resumable.contexts selected = some destination := by
    simpa [hactual] using hdestination
  have hdestinationOwner : destination.owner = selected :=
    ResumablePreemption.contextFor_owner _ _ _ hdestinationSelected
  rcases hstate with
    ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
      hschedulerWellFormed, hpreemption, hresumable, htransfers, hterminal,
      hlive, hblockingCoherent, hportControls⟩
  rcases hcoherent with
    ⟨hexecutionLifecycle, hschedulerLifecycle, hpreemptionScheduler,
      hcapabilitiesLifecycle, hmemoryCapabilities, hipcVirtual,
      hipcCapabilities, hresumableScheduler, htranslationVirtual,
      htransferEndpoints, hauthority, hdeadMailbox, hliveSender⟩
  rcases hresumable with
    ⟨hresumableSchedulerWellFormed, hcapacity, hunique, hvalid, habsent,
      hreadyContexts, htranslation, hvirtualAgreement, hkinds, htlb⟩
  have hdestinationSpace : destination.addressSpace = selected := by
    have hold := hvalid destination
      (List.mem_of_find?_eq_some hdestinationSelected)
    exact hold.2.1.trans hdestinationOwner
  have hnextScheduler : Scheduler.WellFormed blocking.ipc.scheduler := hblocking.1.1
  have hcallerAbsent :
      ResumablePreemption.contextFor state.resumable.contexts caller = none :=
    habsent caller (by simpa [hresumableScheduler] using hcurrent)
  have hcallerNotStored : ∀ context ∈ state.resumable.contexts,
      context.owner ≠ caller := by
    intro context hcontext heq
    subst caller
    have hsome : (ResumablePreemption.contextFor
        state.resumable.contexts context.owner).isSome := by
      rw [ResumablePreemption.contextFor, List.find?_isSome]
      exact ⟨context, hcontext, by simp⟩
    simp [hcallerAbsent] at hsome
  have hnextShape : next =
      let published := publishBlockingIPCContext state blocking
      { published with
        execution := { published.execution with
          core := { published.execution.core with
            context := { published.execution.core.context with
              currentSubject := destination.owner
              activeAddressSpace := destination.addressSpace } }
          returnAuthorityArmed := false }
        resumable := { published.resumable with
          contexts := ResumablePreemption.eraseContext
            state.resumable.contexts destination.owner
          translations := TLB.switch state.resumable.translations
            destination.addressSpace } } := by
    unfold restoreBlockingPeer at hrestore
    simp only [hblockingSelected, hdestinationSelected] at hrestore
    split at hrestore <;> try contradiction
    simpa using hrestore.symm
  have hresumableNext : ResumablePreemption.WellFormed next.resumable := by
    rw [hnextShape]
    refine ⟨hnextScheduler, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [publishBlockingIPCContext, ResumablePreemption.eraseContext] using
        Nat.le_trans (List.length_filter_le _ _) hcapacity
    · exact hunique.filter (fun context => context.owner != destination.owner)
    · intro context hcontext
      have hcontextOld : context ∈ state.resumable.contexts := by
        simpa [ResumablePreemption.eraseContext] using (List.mem_filter.mp hcontext).1
      have hold := hvalid context hcontextOld
      have hnotCaller := hcallerNotStored context hcontextOld
      rcases hold with ⟨hframe, hspace, hliveContext, hrunnable, howner⟩
      refine ⟨hframe, hspace, ?_, ?_, ?_⟩
      · simpa [publishBlockingIPCContext, hscheduler, hresumableScheduler,
          hschedulerLifecycle] using hliveContext
      · simpa [publishBlockingIPCContext, hscheduler, hresumableScheduler,
          hschedulerLifecycle, SubjectLifecycle.setBool, hnotCaller] using hrunnable
      · simpa [publishBlockingIPCContext, hscheduler, hresumableScheduler,
          hschedulerLifecycle] using howner
    · intro subject hsubject
      have : subject = selected := by
        simpa [publishBlockingIPCContext, hscheduler] using hsubject.symm
      subst subject
      simpa [publishBlockingIPCContext, hdestinationOwner] using
        ResumablePreemption.contextFor_erase_self state.resumable.contexts selected
    · constructor
      · intro subject hmember
        change subject ∈ blocking.ipc.scheduler.ready at hmember
        rw [hscheduler] at hmember
        change subject ∈ rest at hmember
        have hold : subject ∈ state.scheduler.ready := by
          rw [hready]
          simp [hmember]
        obtain ⟨context, hcontext, howner⟩ := hreadyContexts.1 subject
          (by simpa [hresumableScheduler] using hold)
        have hsubjectNe : subject ≠ selected := by
          intro heq
          have hnodup := hschedulerWellFormed.2.1
          rw [hready] at hnodup
          exact (List.nodup_cons.mp hnodup).1 (heq ▸ hmember)
        have hne : context.owner ≠ destination.owner := by
          simpa [howner, hdestinationOwner] using hsubjectNe
        exact ⟨context, by simpa [publishBlockingIPCContext,
          ResumablePreemption.eraseContext, hne] using hcontext, howner⟩
      · intro context hcontext hsuspended
        have hcontextOld : context ∈ state.resumable.contexts := by
          exact (List.mem_filter.mp hcontext).1
        have hold := hreadyContexts.2 context hcontextOld hsuspended
        have hne : context.owner ≠ selected := by
          simpa [hdestinationOwner] using (List.mem_filter.mp hcontext).2
        rw [hresumableScheduler, hready] at hold
        simpa [publishBlockingIPCContext, hscheduler, hne] using hold
    · constructor
      · simpa [publishBlockingIPCContext, hscheduler, hresumableScheduler,
          hdestinationSpace, TLB.switch] using htranslation.1
      · simp [publishBlockingIPCContext, hscheduler, hdestinationSpace, TLB.switch]
    · rcases hvirtualAgreement with ⟨hcaps, hwf⟩
      exact ⟨by simpa [publishBlockingIPCContext, hscheduler, hresumableScheduler,
        hschedulerLifecycle, TLB.switch] using hcaps, by simpa [TLB.switch] using hwf⟩
    · unfold ResumablePreemption.ResourceKindAgreement at hkinds ⊢
      simpa [publishBlockingIPCContext, hscheduler, hresumableScheduler,
        hschedulerLifecycle] using hkinds
    · exact TLB.switch_coherent state.resumable.translations destination.addressSpace
  have hnextLifecycle : SubjectLifecycle.WellFormed blocking.ipc.scheduler.lifecycle :=
    hnextScheduler.1
  have hnextExecution : WellFormed next.execution := by
    rw [hnextShape]
    rcases hexecution with ⟨_, _, hmode⟩
    refine ⟨?_, by simp [publishBlockingIPCContext], ?_⟩
    · exact hnextLifecycle
    · simpa [publishBlockingIPCContext] using hmode
  have hnextPreemption : Preemption.WellFormed next.preemption := by
    rw [hnextShape]
    exact ⟨by simpa [publishBlockingIPCContext] using hnextScheduler,
      by simpa [publishBlockingIPCContext] using hpreemption.2⟩
  have hnextCoherent : next.Coherent := by
    rw [hnextShape]
    unfold CompositeState.Coherent
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [publishBlockingIPCContext, hscheduler, hschedulerLifecycle] using
        hcapabilitiesLifecycle
    · simpa [publishBlockingIPCContext, hscheduler, hschedulerLifecycle] using
        hmemoryCapabilities
    · simpa [publishBlockingIPCContext] using hipcVirtual
    · simpa [publishBlockingIPCContext, hscheduler, hschedulerLifecycle] using
        hipcCapabilities
    · simpa [TLB.switch] using htranslationVirtual
    · simpa [publishBlockingIPCContext] using htransferEndpoints
    · intro subject hsubject
      have : subject = selected := by
        simpa [publishBlockingIPCContext, hscheduler] using hsubject.symm
      subst subject
      simp [hdestinationOwner, hdestinationSpace]
    · intro object hdead
      apply hdeadMailbox object
      simpa [publishBlockingIPCContext, hscheduler, hschedulerLifecycle] using hdead
    · intro object envelope hmailbox
      have hold := hliveSender object envelope (by
        simpa [publishBlockingIPCContext] using hmailbox)
      simpa [publishBlockingIPCContext, hscheduler, hschedulerLifecycle] using hold
  refine ⟨hnextCoherent, hnextExecution, ?_, ?_, ?_, ?_, ?_,
    hnextPreemption, hresumableNext, ?_, ?_, ?_,
    restoreBlockingPeer_blockingCoherent state blocking next hrestore, ?_⟩
  · rw [hnextShape]
    exact hnextLifecycle
  · rw [hnextShape]
    simpa [publishBlockingIPCContext, hscheduler, hschedulerLifecycle] using hcapabilities
  · rw [hnextShape]
    simpa [publishBlockingIPCContext] using hvirtual
  · rw [hnextShape]
    simpa [publishBlockingIPCContext] using hipc
  · rw [hnextShape]
    exact hnextScheduler
  · rw [hnextShape]
    simpa [publishBlockingIPCContext] using htransfers
  · rw [hnextShape]
    simpa [publishBlockingIPCContext] using hterminal
  · rw [hnextShape]
    simp [publishBlockingIPCContext]
  · rw [hnextShape]
    simpa [publishBlockingIPCContext] using hportControls

def dispatchBlockingReceive (state : CompositeState) (handleWord : UInt64)
    (frame : Interrupt.HardwareFrame) (registers : ResumableContext.Registers) :
    CompositeBlockingReceiveOutcome :=
  let caller := state.execution.core.context.currentSubject
  match CapabilityHandle.resolveCurrent state.blockingIPC.scheduler.lifecycle.capabilities
      { caller } handleWord .endpoint with
  | .error reason => { state, reply := .handleRejected reason }
  | .ok resolution =>
      let outcome := BlockingIPCContext.receiveOrBlock state.blockingIPCContext caller
        resolution.handle.slot (state.blockingSavedContext frame registers)
      match outcome.result with
      | .contextRejected reason => { state, reply := .contextRejected reason }
      | .completed (.rejected reason) => { state, reply := .rejected reason }
      | .completed (.delivered envelope) =>
          { state := publishBlockingIPCContext state outcome.state
            reply := .delivered envelope }
      | .completed .blocked =>
          if outcome.state.ipc.scheduler.lifecycle.current.isSome then
            match restoreBlockingPeer state outcome.state with
            | .error _ => { state, reply := .switchRequired }
            | .ok next => { state := next, reply := .blocked }
          else
            { state := publishBlockingIPCContext state outcome.state
              reply := .blocked }

inductive CompositeBlockingReceiveRejection : CompositeBlockingReceiveReply → Prop
  | handle reason : CompositeBlockingReceiveRejection (.handleRejected reason)
  | context reason : CompositeBlockingReceiveRejection (.contextRejected reason)
  | ipc reason : CompositeBlockingReceiveRejection (.rejected reason)
  | switchRequired : CompositeBlockingReceiveRejection .switchRequired

theorem dispatchBlockingReceive_rejected_atomic state handleWord frame registers reply
    (hrejected : CompositeBlockingReceiveRejection reply)
    (hreply : (dispatchBlockingReceive state handleWord frame registers).reply = reply) :
    (dispatchBlockingReceive state handleWord frame registers).state = state := by
  cases hrejected
  all_goals
    simp only [dispatchBlockingReceive] at hreply ⊢
    split <;> simp_all
    generalize houtcome : BlockingIPCContext.receiveOrBlock _ _ _ _ = outcome at hreply ⊢
    cases outcome with
    | mk next result =>
        cases result with
        | contextRejected reason => simp_all
        | completed result =>
            cases result with
            | delivered envelope => simp_all
            | rejected reason => simp_all
            | blocked =>
                by_cases hsome : next.ipc.scheduler.lifecycle.current.isSome = true
                · cases hrestore : restoreBlockingPeer state next <;>
                    simp [hsome, hrestore] at hreply ⊢
                · simp [hsome] at hreply ⊢

/-- A completed receive consumes only an already-reserved completion or
mailbox envelope.  Its scheduler remains authoritative, so publishing the
updated blocking store preserves every global runtime projection. -/
theorem dispatchBlockingReceive_delivered_preserves_runtimeWellFormed
    state handleWord frame registers envelope
    (hstate : RuntimeWellFormed state)
    (hdelivered :
      (dispatchBlockingReceive state handleWord frame registers).reply =
        .delivered envelope) :
    RuntimeWellFormed
      (dispatchBlockingReceive state handleWord frame registers).state := by
  cases hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities
      { caller := state.execution.core.context.currentSubject } handleWord .endpoint with
  | error reason => simp [dispatchBlockingReceive, hresolve] at hdelivered
  | ok resolution =>
      let saved := state.blockingSavedContext frame registers
      cases houtcome : BlockingIPCContext.receiveOrBlock state.blockingIPCContext
          state.execution.core.context.currentSubject resolution.handle.slot saved with
      | mk next result =>
          cases result with
          | contextRejected reason =>
              simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hdelivered
          | completed result =>
              cases result with
              | rejected reason =>
                  simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hdelivered
              | blocked =>
                  by_cases hsome : next.ipc.scheduler.lifecycle.current.isSome = true
                  · cases hrestore : restoreBlockingPeer state next <;>
                      simp [dispatchBlockingReceive, hresolve, saved, houtcome, hsome,
                        hrestore] at hdelivered
                  · simp [dispatchBlockingReceive, hresolve, saved, houtcome, hsome]
                      at hdelivered
              | delivered actual =>
                  simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hdelivered
                  subst actual
                  have hexact := BlockingIPCContext.receive_delivered_ipc_exact
                    state.blockingIPCContext state.execution.core.context.currentSubject
                    resolution.handle.slot saved envelope (by simp [houtcome])
                  have hnextIPC :
                      next.ipc = (BlockingIPC.receiveOrBlock state.blockingIPC
                        state.execution.core.context.currentSubject
                        resolution.handle.slot).state := by
                    have hnext := hexact.1
                    rw [houtcome] at hnext
                    simpa [CompositeState.blockingIPCContext] using hnext
                  have hscheduler : next.ipc.scheduler = state.scheduler := by
                    rw [hnextIPC,
                      BlockingIPC.receive_delivered_scheduler_unchanged
                        state.blockingIPC state.execution.core.context.currentSubject
                        resolution.handle.slot envelope hexact.2]
                    exact hstate.blockingScheduler
                  have hcurrent : state.scheduler.lifecycle.current.isSome = true := by
                    have hselected := BlockingIPC.receive_delivered_current
                      state.blockingIPC state.execution.core.context.currentSubject
                      resolution.handle.slot envelope hexact.2
                    rw [hstate.blockingScheduler] at hselected
                    simp [hselected]
                  simpa [dispatchBlockingReceive, hresolve, saved, houtcome] using
                    publishBlockingIPCContext_sameScheduler_preserves_runtimeWellFormed
                      state next hstate hscheduler hcurrent

/-- A typed receive that reports a block into an idle scheduler preserves the
complete runtime invariant.  The dependency result fixes the pre-block caller
and exact scheduler mutation; observing no selected peer in the published
post-state rules out the restoration branch. -/
theorem dispatchBlockingReceive_idle_block_preserves_runtimeWellFormed
    state handleWord frame registers
    (hstate : BlockingRuntimeWellFormed state)
    (hblocked :
      (dispatchBlockingReceive state handleWord frame registers).reply = .blocked)
    (hidle :
      (dispatchBlockingReceive state handleWord frame registers).state.scheduler.lifecycle.current =
        none) :
    RuntimeWellFormed
      (dispatchBlockingReceive state handleWord frame registers).state := by
  cases hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities
      { caller := state.execution.core.context.currentSubject } handleWord .endpoint with
  | error reason => simp [dispatchBlockingReceive, hresolve] at hblocked
  | ok resolution =>
      let saved := state.blockingSavedContext frame registers
      cases houtcome : BlockingIPCContext.receiveOrBlock state.blockingIPCContext
          state.execution.core.context.currentSubject resolution.handle.slot saved with
      | mk next result =>
          cases result with
          | contextRejected reason =>
              simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hblocked
          | completed result =>
              cases result with
              | rejected reason =>
                  simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hblocked
              | delivered envelope =>
                  simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hblocked
              | blocked =>
                  by_cases hsome : next.ipc.scheduler.lifecycle.current.isSome = true
                  · cases hrestore : restoreBlockingPeer state next with
                    | error reason =>
                        simp [dispatchBlockingReceive, hresolve, saved, houtcome, hsome,
                          hrestore] at hblocked
                    | ok published =>
                        obtain ⟨selected, destination, hselected, _, _, _, _, _, _, hcontext⟩ :=
                          restoreBlockingPeer_exact state next published hrestore
                        have hpublishedCurrent :
                            published.scheduler.lifecycle.current = some selected := by
                          rw [← (restoreBlockingPeer_blockingCoherent
                            state next published hrestore).1]
                          change published.blockingIPC.scheduler.lifecycle.current = some selected
                          have hipc : published.blockingIPC = next.ipc := congrArg
                            BlockingIPCContext.State.ipc hcontext
                          rw [hipc]
                          exact hselected
                        simp only [dispatchBlockingReceive, hresolve, saved, houtcome, hsome,
                          hrestore] at hidle
                        simp [hpublishedCurrent] at hidle
                  · have hexact := BlockingIPCContext.receive_blocked_ipc_exact
                      state.blockingIPCContext state.execution.core.context.currentSubject
                      resolution.handle.slot saved (by simp [houtcome])
                    have hnextIPC :
                        next.ipc = (BlockingIPC.receiveOrBlock state.blockingIPC
                          state.execution.core.context.currentSubject
                          resolution.handle.slot).state := by
                      have hold := hexact.1
                      rw [houtcome] at hold
                      simpa [CompositeState.blockingIPCContext] using hold
                    have hnextIdle : next.ipc.scheduler.lifecycle.current = none := by
                      cases hcurrent : next.ipc.scheduler.lifecycle.current <;>
                        simp_all
                    have hidleExact := BlockingIPC.receive_blocked_idle_scheduler_exact
                      state.blockingIPC state.execution.core.context.currentSubject
                      resolution.handle.slot hexact.2 (by simpa [hnextIPC] using hnextIdle)
                    have hcurrent := BlockingIPC.receive_blocked_current
                      state.blockingIPC state.execution.core.context.currentSubject
                      resolution.handle.slot hexact.2
                    have hcaller : state.scheduler.lifecycle.current =
                        some state.execution.core.context.currentSubject := by
                      simpa [hstate.1.blockingScheduler] using hcurrent
                    have hscheduler : next.ipc.scheduler =
                        { state.scheduler with
                          lifecycle := { state.scheduler.lifecycle with
                            runnable := SubjectLifecycle.setBool
                              state.scheduler.lifecycle.runnable
                              state.execution.core.context.currentSubject false
                            current := none } } := by
                      rw [hnextIPC, hidleExact.2, hstate.1.blockingScheduler]
                    simpa [dispatchBlockingReceive, hresolve, saved, houtcome, hsome] using
                      publishBlockingIPCContext_idleBlock_preserves_runtimeWellFormed
                        state next state.execution.core.context.currentSubject hstate.1
                        (by
                          have hpreserved := BlockingIPCContext.receive_preserves_wellFormed
                            state.blockingIPCContext
                            state.execution.core.context.currentSubject
                            resolution.handle.slot saved hstate.2
                          simpa [houtcome] using hpreserved)
                        hcaller (by simpa [hstate.1.blockingScheduler] using hidleExact.1)
                        hscheduler

/-- A typed block that immediately hands execution to a ready peer preserves
the global invariant.  The dependency fixes that peer as the old queue head;
the restore publisher consumes exactly its kernel-owned context and switches
the active translation to the same authoritative identity. -/
theorem dispatchBlockingReceive_selected_block_preserves_runtimeWellFormed
    state handleWord frame registers selected
    (hstate : BlockingRuntimeWellFormed state)
    (hblocked :
      (dispatchBlockingReceive state handleWord frame registers).reply = .blocked)
    (hselected :
      (dispatchBlockingReceive state handleWord frame registers).state.scheduler.lifecycle.current =
        some selected) :
    RuntimeWellFormed
      (dispatchBlockingReceive state handleWord frame registers).state := by
  cases hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities
      { caller := state.execution.core.context.currentSubject } handleWord .endpoint with
  | error reason => simp [dispatchBlockingReceive, hresolve] at hblocked
  | ok resolution =>
      let saved := state.blockingSavedContext frame registers
      cases houtcome : BlockingIPCContext.receiveOrBlock state.blockingIPCContext
          state.execution.core.context.currentSubject resolution.handle.slot saved with
      | mk next result =>
          cases result with
          | contextRejected reason =>
              simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hblocked
          | completed result =>
              cases result with
              | rejected reason =>
                  simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hblocked
              | delivered envelope =>
                  simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hblocked
              | blocked =>
                  by_cases hsome : next.ipc.scheduler.lifecycle.current.isSome = true
                  · cases hrestore : restoreBlockingPeer state next with
                    | error reason =>
                        simp [dispatchBlockingReceive, hresolve, saved, houtcome, hsome,
                          hrestore] at hblocked
                    | ok published =>
                        have hexact := BlockingIPCContext.receive_blocked_ipc_exact
                          state.blockingIPCContext state.execution.core.context.currentSubject
                          resolution.handle.slot saved (by simp [houtcome])
                        have hnextIPC :
                            next.ipc = (BlockingIPC.receiveOrBlock state.blockingIPC
                              state.execution.core.context.currentSubject
                              resolution.handle.slot).state := by
                          have hold := hexact.1
                          rw [houtcome] at hold
                          simpa [CompositeState.blockingIPCContext] using hold
                        have hpublishedSelected :
                            published.scheduler.lifecycle.current = some selected := by
                          simpa [dispatchBlockingReceive, hresolve, saved, houtcome, hsome,
                            hrestore] using hselected
                        have hnextSelected : next.ipc.scheduler.lifecycle.current =
                            some selected := by
                          rw [← (restoreBlockingPeer_blockingCoherent
                            state next published hrestore).1] at hpublishedSelected
                          have hcontext := restoreBlockingPeer_context_exact
                            state next published hrestore
                          change published.blockingIPC.scheduler.lifecycle.current =
                            some selected at hpublishedSelected
                          have hipc : published.blockingIPC = next.ipc := congrArg
                            BlockingIPCContext.State.ipc hcontext
                          simpa [hipc] using hpublishedSelected
                        obtain ⟨rest, hready, hschedulerExact⟩ :=
                          BlockingIPC.receive_blocked_selected_scheduler_exact
                            state.blockingIPC state.execution.core.context.currentSubject
                            resolution.handle.slot selected hexact.2
                            (by simpa [hnextIPC] using hnextSelected)
                        have hcurrent := BlockingIPC.receive_blocked_current
                          state.blockingIPC state.execution.core.context.currentSubject
                          resolution.handle.slot hexact.2
                        have hcaller : state.scheduler.lifecycle.current =
                            some state.execution.core.context.currentSubject := by
                          simpa [hstate.1.blockingScheduler] using hcurrent
                        have hscheduler : next.ipc.scheduler =
                            { state.scheduler with
                              ready := rest
                              lifecycle := { state.scheduler.lifecycle with
                                runnable := SubjectLifecycle.setBool
                                  state.scheduler.lifecycle.runnable
                                  state.execution.core.context.currentSubject false
                                current := some selected } } := by
                          rw [hnextIPC, hschedulerExact, hstate.1.blockingScheduler]
                        simpa [dispatchBlockingReceive, hresolve, saved, houtcome, hsome,
                          hrestore] using
                          restoreBlockingPeer_preserves_runtimeWellFormed
                            state next published state.execution.core.context.currentSubject
                            selected rest hstate.1
                            (by
                              have hpreserved := BlockingIPCContext.receive_preserves_wellFormed
                                state.blockingIPCContext
                                state.execution.core.context.currentSubject
                                resolution.handle.slot saved hstate.2
                              simpa [houtcome] using hpreserved)
                            hcaller (by simpa [hstate.1.blockingScheduler] using hready)
                            hscheduler hrestore
                  · have hnextIdle : next.ipc.scheduler.lifecycle.current = none := by
                      cases hcurrent : next.ipc.scheduler.lifecycle.current <;> simp_all
                    have hpublishedIdle :
                        (publishBlockingIPCContext state next).scheduler.lifecycle.current =
                          none := by
                      simpa [publishBlockingIPCContext] using hnextIdle
                    simp only [dispatchBlockingReceive, hresolve, saved, houtcome, hsome]
                      at hselected
                    simp [hsome, hpublishedIdle] at hselected
                    rw [hnextIdle] at hselected
                    contradiction

theorem dispatchBlockingReceive_preserves_blockingWellFormed state handleWord frame registers
    (hstate : BlockingIPCContext.WellFormed state.blockingIPCContext) :
    BlockingIPCContext.WellFormed
      (dispatchBlockingReceive state handleWord frame registers).state.blockingIPCContext := by
  cases hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities
      { caller := state.execution.core.context.currentSubject } handleWord .endpoint with
  | error reason => simpa [dispatchBlockingReceive, hresolve] using hstate
  | ok resolution =>
      let saved := state.blockingSavedContext frame registers
      have hpreserved := BlockingIPCContext.receive_preserves_wellFormed
        state.blockingIPCContext state.execution.core.context.currentSubject
        resolution.handle.slot saved hstate
      cases houtcome : BlockingIPCContext.receiveOrBlock state.blockingIPCContext
          state.execution.core.context.currentSubject resolution.handle.slot saved with
      | mk next result =>
          have hnext : BlockingIPCContext.WellFormed next := by
            simpa [houtcome] using hpreserved
          cases result with
          | contextRejected reason =>
              simpa [dispatchBlockingReceive, hresolve, saved, houtcome] using hstate
          | completed result =>
              cases result with
              | rejected reason =>
                  simpa [dispatchBlockingReceive, hresolve, saved, houtcome] using hstate
              | delivered envelope =>
                  simpa [dispatchBlockingReceive, hresolve, saved, houtcome] using hnext
              | blocked =>
                  by_cases hsome : next.ipc.scheduler.lifecycle.current.isSome = true
                  · cases hrestore : restoreBlockingPeer state next with
                    | error reason =>
                        simpa [dispatchBlockingReceive, hresolve, saved, houtcome, hsome,
                          hrestore] using hstate
                    | ok published =>
                        have hcontext := restoreBlockingPeer_context_exact
                          state next published hrestore
                        simpa [dispatchBlockingReceive, hresolve, saved, houtcome, hsome,
                          hrestore, hcontext] using hnext
                  · simpa [dispatchBlockingReceive, hresolve, saved, houtcome, hsome] using hnext

theorem dispatchBlockingReceive_preserves_coherent state handleWord frame registers
    (hstate : state.BlockingIPCCoherent) :
    (dispatchBlockingReceive state handleWord frame registers).state.BlockingIPCCoherent := by
  cases hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities
      { caller := state.execution.core.context.currentSubject } handleWord .endpoint with
  | error reason => simpa [dispatchBlockingReceive, hresolve] using hstate
  | ok resolution =>
      let saved := state.blockingSavedContext frame registers
      cases houtcome : BlockingIPCContext.receiveOrBlock state.blockingIPCContext
          state.execution.core.context.currentSubject resolution.handle.slot saved with
      | mk next result =>
          cases result with
          | contextRejected reason =>
              simpa [dispatchBlockingReceive, hresolve, saved, houtcome] using hstate
          | completed result =>
              cases result with
              | rejected reason =>
                  simpa [dispatchBlockingReceive, hresolve, saved, houtcome] using hstate
              | delivered envelope =>
                  simpa [dispatchBlockingReceive, hresolve, saved, houtcome] using
                    publishBlockingIPCContext_coherent state next
              | blocked =>
                  by_cases hsome : next.ipc.scheduler.lifecycle.current.isSome = true
                  · cases hrestore : restoreBlockingPeer state next with
                    | error reason =>
                        simpa [dispatchBlockingReceive, hresolve, saved, houtcome, hsome,
                          hrestore] using hstate
                    | ok published =>
                        simpa [dispatchBlockingReceive, hresolve, saved, houtcome, hsome,
                          hrestore] using restoreBlockingPeer_blockingCoherent
                            state next published hrestore
                  · simpa [dispatchBlockingReceive, hresolve, saved, houtcome, hsome] using
                      publishBlockingIPCContext_coherent state next

/-- Bounded invariant owned by the typed blocking-receive boundary.  Successful
blocking now consumes the selected peer's resumable context atomically; folding
this predicate into `RuntimeWellFormed` still requires every non-IPC lifecycle
and capability publisher to synchronize the blocking projections as well. -/
def BlockingReceiveWellFormed (state : CompositeState) : Prop :=
  BlockingIPCContext.WellFormed state.blockingIPCContext ∧
    state.BlockingIPCCoherent

theorem dispatchBlockingReceive_preserves_wellFormed state handleWord frame registers
    (hstate : BlockingReceiveWellFormed state) :
    BlockingReceiveWellFormed
      (dispatchBlockingReceive state handleWord frame registers).state := by
  exact ⟨dispatchBlockingReceive_preserves_blockingWellFormed
      state handleWord frame registers hstate.1,
    dispatchBlockingReceive_preserves_coherent
      state handleWord frame registers hstate.2⟩

/-- A published block stores the exact frame/register payload under identities
chosen by the execution latch; no handle word can select another owner or
address space. -/
theorem dispatchBlockingReceive_blocked_uses_kernel_context state handleWord frame registers
    (hblocked : (dispatchBlockingReceive state handleWord frame registers).reply = .blocked) :
    let caller := state.execution.core.context.currentSubject
    let saved := state.blockingSavedContext frame registers
    (dispatchBlockingReceive state handleWord frame registers).state.blockingContexts caller =
        some saved ∧
      saved.owner = caller ∧
      saved.addressSpace = state.execution.core.context.activeAddressSpace := by
  dsimp only
  cases hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities
      { caller := state.execution.core.context.currentSubject } handleWord .endpoint with
  | error reason => simp [dispatchBlockingReceive, hresolve] at hblocked
  | ok resolution =>
      let saved := state.blockingSavedContext frame registers
      cases houtcome : BlockingIPCContext.receiveOrBlock state.blockingIPCContext
          state.execution.core.context.currentSubject resolution.handle.slot saved with
      | mk next result =>
          cases result with
          | contextRejected reason =>
              simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hblocked
          | completed result =>
              cases result with
              | rejected reason =>
                  simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hblocked
              | delivered envelope =>
                  simp [dispatchBlockingReceive, hresolve, saved, houtcome] at hblocked
              | blocked =>
                  by_cases hsome : next.ipc.scheduler.lifecycle.current.isSome = true
                  · cases hrestore : restoreBlockingPeer state next with
                    | error reason =>
                        simp [dispatchBlockingReceive, hresolve, saved, houtcome, hsome,
                          hrestore] at hblocked
                    | ok published =>
                        have hexact := BlockingIPCContext.receive_blocked_exact
                          state.blockingIPCContext state.execution.core.context.currentSubject
                          resolution.handle.slot saved (by simp [houtcome])
                        have hcontext := restoreBlockingPeer_context_exact
                          state next published hrestore
                        simp only [dispatchBlockingReceive, hresolve, saved, houtcome, hsome,
                          hrestore, ite_true]
                        refine ⟨?_, rfl, rfl⟩
                        change published.blockingIPCContext.blocked
                          state.execution.core.context.currentSubject = some saved
                        rw [hcontext]
                        simpa [houtcome] using hexact.2
                  · have hexact := BlockingIPCContext.receive_blocked_exact
                      state.blockingIPCContext state.execution.core.context.currentSubject
                      resolution.handle.slot saved (by simp [houtcome])
                    simpa [dispatchBlockingReceive, hresolve, saved, houtcome, hsome,
                      publishBlockingIPCContext] using hexact.2

/-! ## Context-owning wake and cancellation

The matching send and cancellation boundaries consume the saved context in
the same typed transition that removes the waiter.  Publication therefore
cannot expose a runnable receiver while retaining its blocked-context entry.
-/

inductive CompositeBlockingSendReply where
  | handleRejected (reason : CapabilityHandle.WordResolveDenial)
  | contextRejected (reason : BlockingIPCContext.ContextError)
  | restoreRejected (reason : ResumablePreemption.Error)
  | rejected (reason : BlockingIPC.Error)
  | sent
  | woke (context : ResumableContext.Context)
  deriving DecidableEq, Repr

structure CompositeBlockingSendOutcome where
  state : CompositeState
  reply : CompositeBlockingSendReply

def dispatchBlockingSend (state : CompositeState) (handleWord word0 word1 : UInt64) :
    CompositeBlockingSendOutcome :=
  let caller := state.execution.core.context.currentSubject
  match CapabilityHandle.resolveCurrent state.blockingIPC.scheduler.lifecycle.capabilities
      { caller } handleWord .endpoint with
  | .error reason => { state, reply := .handleRejected reason }
  | .ok resolution =>
      let outcome := BlockingIPCContext.send state.blockingIPCContext caller
        resolution.handle.slot { word0, word1 }
      match outcome.result with
      | .ipcRejected reason => { state, reply := .rejected reason }
      | .contextRejected reason => { state, reply := .contextRejected reason }
      | .accepted =>
          match outcome.released with
          | none => { state := publishBlockingIPCContext state outcome.state, reply := .sent }
          | some saved =>
              match publishReleasedBlockingContext state outcome.state saved with
              | .error reason => { state, reply := .restoreRejected reason }
              | .ok next => { state := next, reply := .woke saved }

inductive CompositeBlockingSendRejection : CompositeBlockingSendReply -> Prop
  | handle reason : CompositeBlockingSendRejection (.handleRejected reason)
  | context reason : CompositeBlockingSendRejection (.contextRejected reason)
  | restore reason : CompositeBlockingSendRejection (.restoreRejected reason)
  | ipc reason : CompositeBlockingSendRejection (.rejected reason)

theorem dispatchBlockingSend_rejected_atomic state handleWord word0 word1 reply
    (hrejected : CompositeBlockingSendRejection reply)
    (hreply : (dispatchBlockingSend state handleWord word0 word1).reply = reply) :
    (dispatchBlockingSend state handleWord word0 word1).state = state := by
  cases hrejected
  all_goals
    simp only [dispatchBlockingSend] at hreply ⊢
    split <;> simp_all
    generalize houtcome : BlockingIPCContext.send _ _ _ _ = outcome at hreply ⊢
    cases outcome with
    | mk next result released =>
        cases result <;> simp_all
        cases released <;> simp_all
        split <;> simp_all

theorem dispatchBlockingSend_preserves_wellFormed state handleWord word0 word1
    (hstate : BlockingReceiveWellFormed state) :
    BlockingReceiveWellFormed
      (dispatchBlockingSend state handleWord word0 word1).state := by
  rcases hstate with ⟨hblocking, hcoherent⟩
  cases hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities
      { caller := state.execution.core.context.currentSubject } handleWord .endpoint with
  | error reason =>
      simpa [dispatchBlockingSend, hresolve] using
        (show BlockingReceiveWellFormed state from ⟨hblocking, hcoherent⟩)
  | ok resolution =>
      let payload : BlockingIPC.Payload := { word0, word1 }
      have hpreserved := BlockingIPCContext.send_preserves_wellFormed
        state.blockingIPCContext state.execution.core.context.currentSubject
        resolution.handle.slot payload hblocking
      cases houtcome : BlockingIPCContext.send state.blockingIPCContext
          state.execution.core.context.currentSubject resolution.handle.slot payload with
      | mk next result released =>
          have hnext : BlockingIPCContext.WellFormed next := by
            simpa [houtcome] using hpreserved
          cases result with
          | ipcRejected reason =>
              simpa [dispatchBlockingSend, hresolve, payload, houtcome] using
                (show BlockingReceiveWellFormed state from ⟨hblocking, hcoherent⟩)
          | contextRejected reason =>
              simpa [dispatchBlockingSend, hresolve, payload, houtcome] using
                (show BlockingReceiveWellFormed state from ⟨hblocking, hcoherent⟩)
          | accepted =>
              cases released with
              | none =>
                  exact ⟨by simpa [dispatchBlockingSend, hresolve, payload, houtcome] using hnext,
                    by simpa [dispatchBlockingSend, hresolve, payload, houtcome] using
                      publishBlockingIPCContext_coherent state next⟩
              | some saved =>
                  cases hrestore : publishReleasedBlockingContext state next saved with
                  | error reason =>
                      simpa [dispatchBlockingSend, hresolve, payload, houtcome, hrestore] using
                        (show BlockingReceiveWellFormed state from ⟨hblocking, hcoherent⟩)
                  | ok published =>
                      exact ⟨by
                          have hcontext :=
                            (publishReleasedBlockingContext_restores_exact state next saved
                              published hrestore).2
                          simpa [dispatchBlockingSend, hresolve, payload, houtcome, hrestore,
                            hcontext] using hnext,
                        by simpa [dispatchBlockingSend, hresolve, payload, houtcome, hrestore] using
                          publishReleasedBlockingContext_blockingCoherent
                            state next saved published hrestore⟩

/-- A successful mailbox-only blocking send preserves the complete global
runtime invariant.  Unlike a wake, this mutation does not change the
authoritative scheduler: it only publishes the exact mailbox post-state after
the typed context boundary confirms that no blocked receiver was released. -/
theorem dispatchBlockingSend_sent_preserves_runtimeWellFormed
    state handleWord word0 word1
    (hstate : RuntimeWellFormed state)
    (hsent : (dispatchBlockingSend state handleWord word0 word1).reply = .sent) :
    RuntimeWellFormed
      (dispatchBlockingSend state handleWord word0 word1).state := by
  cases hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities
      { caller := state.execution.core.context.currentSubject } handleWord .endpoint with
  | error reason => simp [dispatchBlockingSend, hresolve] at hsent
  | ok resolution =>
      let payload : BlockingIPC.Payload := { word0, word1 }
      cases houtcome : BlockingIPCContext.send state.blockingIPCContext
          state.execution.core.context.currentSubject resolution.handle.slot payload with
      | mk next result released =>
          cases result with
          | ipcRejected reason =>
              simp [dispatchBlockingSend, hresolve, payload, houtcome] at hsent
          | contextRejected reason =>
              simp [dispatchBlockingSend, hresolve, payload, houtcome] at hsent
          | accepted =>
              cases released with
              | some saved =>
                  cases hrestore : publishReleasedBlockingContext state next saved <;>
                    simp [dispatchBlockingSend, hresolve, payload, houtcome, hrestore] at hsent
              | none =>
                  have haccepted :
                      (BlockingIPCContext.send state.blockingIPCContext
                        state.execution.core.context.currentSubject resolution.handle.slot
                        payload).result = .accepted := by
                    simp [houtcome]
                  have hunreleased :
                      (BlockingIPCContext.send state.blockingIPCContext
                        state.execution.core.context.currentSubject resolution.handle.slot
                        payload).released = none := by
                    simp [houtcome]
                  have hscheduler : next.ipc.scheduler = state.scheduler := by
                    have hsame :=
                      BlockingIPCContext.send_accepted_unreleased_scheduler_unchanged
                        state.blockingIPCContext state.execution.core.context.currentSubject
                        resolution.handle.slot payload haccepted hunreleased
                    rw [houtcome] at hsame
                    simpa [CompositeState.blockingIPCContext, hstate.blockingScheduler] using hsame
                  have hcurrent : state.scheduler.lifecycle.current.isSome = true := by
                    have hrawAccepted :
                        (BlockingIPC.send state.blockingIPC
                          state.execution.core.context.currentSubject resolution.handle.slot
                          payload).result = .accepted := by
                      exact (BlockingIPCContext.send_accepted_ipc_exact
                        state.blockingIPCContext state.execution.core.context.currentSubject
                        resolution.handle.slot payload haccepted).2
                    simp only [BlockingIPC.send] at hrawAccepted
                    split at hrawAccepted <;>
                      simp_all [BlockingIPC.reject, hstate.blockingScheduler]
                  simpa [dispatchBlockingSend, hresolve, payload, houtcome] using
                    publishBlockingIPCContext_sameScheduler_preserves_runtimeWellFormed
                      state next hstate hscheduler hcurrent

/-- A composite wake publishes the exact context consumed from the blocked
bank and clears that receiver's entry atomically. -/
theorem dispatchBlockingSend_woke_exact state handleWord word0 word1 saved
    (hstate : BlockingReceiveWellFormed state)
    (hwoke : (dispatchBlockingSend state handleWord word0 word1).reply = .woke saved) :
    ∃ receiver,
      state.blockingContexts receiver = some saved ∧
      (dispatchBlockingSend state handleWord word0 word1).state.blockingContexts receiver = none ∧
      ResumablePreemption.contextFor
        (dispatchBlockingSend state handleWord word0 word1).state.resumable.contexts receiver =
          some saved := by
  cases hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities
      { caller := state.execution.core.context.currentSubject } handleWord .endpoint with
  | error reason => simp [dispatchBlockingSend, hresolve] at hwoke
  | ok resolution =>
      let payload : BlockingIPC.Payload := { word0, word1 }
      cases houtcome : BlockingIPCContext.send state.blockingIPCContext
          state.execution.core.context.currentSubject resolution.handle.slot payload with
      | mk next result released =>
          cases result with
          | ipcRejected reason => simp [dispatchBlockingSend, hresolve, payload, houtcome] at hwoke
          | contextRejected reason =>
              simp [dispatchBlockingSend, hresolve, payload, houtcome] at hwoke
          | accepted =>
              cases released with
              | none => simp [dispatchBlockingSend, hresolve, payload, houtcome] at hwoke
              | some actual =>
                  cases hrestore : publishReleasedBlockingContext state next actual with
                  | error reason =>
                      simp [dispatchBlockingSend, hresolve, payload, houtcome, hrestore] at hwoke
                  | ok published =>
                    simp [dispatchBlockingSend, hresolve, payload, houtcome, hrestore] at hwoke
                    subst actual
                    obtain ⟨endpoint, receiver, rest, _, _, hstored, _, hcleared⟩ :=
                      BlockingIPCContext.send_released_exact state.blockingIPCContext
                        state.execution.core.context.currentSubject resolution.handle.slot payload saved
                        (by simp [houtcome])
                    have hcontext :=
                      (publishReleasedBlockingContext_restores_exact state next saved
                        published hrestore)
                    refine ⟨receiver, hstored, ?_, ?_⟩
                    · simp only [dispatchBlockingSend, hresolve, payload, houtcome, hrestore]
                      change published.blockingIPCContext.blocked receiver = none
                      rw [hcontext.2]
                      simpa [houtcome] using hcleared
                    · have howner : saved.owner = receiver := by
                        exact BlockingIPCContext.validSaved_owner receiver saved
                          (hstate.1.2.2 receiver saved hstored)
                      simpa [dispatchBlockingSend, hresolve, payload, houtcome, hrestore,
                        howner] using hcontext.1

/-- A typed wake exposes only the released context that passed the finite
post-wake validity checks against the scheduler published in the same state. -/
theorem dispatchBlockingSend_woke_context_valid state handleWord word0 word1 saved
    (hwoke : (dispatchBlockingSend state handleWord word0 word1).reply = .woke saved) :
    ResumablePreemption.validContext
      (dispatchBlockingSend state handleWord word0 word1).state.resumable saved := by
  cases hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities
      { caller := state.execution.core.context.currentSubject } handleWord .endpoint with
  | error reason => simp [dispatchBlockingSend, hresolve] at hwoke
  | ok resolution =>
      let payload : BlockingIPC.Payload := { word0, word1 }
      cases houtcome : BlockingIPCContext.send state.blockingIPCContext
          state.execution.core.context.currentSubject resolution.handle.slot payload with
      | mk next result released =>
          cases result with
          | ipcRejected reason => simp [dispatchBlockingSend, hresolve, payload, houtcome] at hwoke
          | contextRejected reason =>
              simp [dispatchBlockingSend, hresolve, payload, houtcome] at hwoke
          | accepted =>
              cases released with
              | none => simp [dispatchBlockingSend, hresolve, payload, houtcome] at hwoke
              | some actual =>
                  cases hrestore : publishReleasedBlockingContext state next actual with
                  | error reason =>
                      simp [dispatchBlockingSend, hresolve, payload, houtcome, hrestore] at hwoke
                  | ok published =>
                      simp [dispatchBlockingSend, hresolve, payload, houtcome, hrestore] at hwoke
                      subst actual
                      simpa [dispatchBlockingSend, hresolve, payload, houtcome, hrestore] using
                        publishReleasedBlockingContext_published_valid
                          state next saved published hrestore

/-- A successful wake preserves the complete runtime invariant: the exact
saved receiver context is moved from the waiter bank into the resumable bank
at the same time that the authoritative scheduler marks its owner runnable. -/
theorem dispatchBlockingSend_woke_preserves_runtimeWellFormed
    state handleWord word0 word1 saved
    (hstate : BlockingRuntimeWellFormed state)
    (hwoke : (dispatchBlockingSend state handleWord word0 word1).reply = .woke saved) :
    RuntimeWellFormed
      (dispatchBlockingSend state handleWord word0 word1).state := by
  cases hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities
      { caller := state.execution.core.context.currentSubject } handleWord .endpoint with
  | error reason => simp [dispatchBlockingSend, hresolve] at hwoke
  | ok resolution =>
      let payload : BlockingIPC.Payload := { word0, word1 }
      have hpreserved := BlockingIPCContext.send_preserves_wellFormed
        state.blockingIPCContext state.execution.core.context.currentSubject
        resolution.handle.slot payload hstate.2
      cases houtcome : BlockingIPCContext.send state.blockingIPCContext
          state.execution.core.context.currentSubject resolution.handle.slot payload with
      | mk blocking result released =>
          have hblocking : BlockingIPCContext.WellFormed blocking := by
            simpa [houtcome] using hpreserved
          cases result with
          | ipcRejected reason => simp [dispatchBlockingSend, hresolve, payload, houtcome] at hwoke
          | contextRejected reason =>
              simp [dispatchBlockingSend, hresolve, payload, houtcome] at hwoke
          | accepted =>
              cases released with
              | none => simp [dispatchBlockingSend, hresolve, payload, houtcome] at hwoke
              | some actual =>
                  cases hrestore : publishReleasedBlockingContext state blocking actual with
                  | error reason =>
                      simp [dispatchBlockingSend, hresolve, payload, houtcome, hrestore] at hwoke
                  | ok published =>
                      simp [dispatchBlockingSend, hresolve, payload, houtcome, hrestore] at hwoke
                      subst actual
                      have haccepted :
                          (BlockingIPCContext.send state.blockingIPCContext
                            state.execution.core.context.currentSubject resolution.handle.slot
                            payload).result = .accepted := by
                        simp [houtcome]
                      have hreleased :
                          (BlockingIPCContext.send state.blockingIPCContext
                            state.execution.core.context.currentSubject resolution.handle.slot
                            payload).released = some saved := by
                        simp [houtcome]
                      obtain ⟨endpoint, receiver, rest, hendpoint, hqueue, hstored, _, _⟩ :=
                        BlockingIPCContext.send_released_exact state.blockingIPCContext
                          state.execution.core.context.currentSubject resolution.handle.slot
                          payload saved hreleased
                      have howner : saved.owner = receiver := by
                        exact BlockingIPCContext.validSaved_owner receiver saved
                          (hstate.2.2.2 receiver saved hstored)
                      have hipcAccepted := BlockingIPCContext.send_accepted_ipc_exact
                        state.blockingIPCContext
                        state.execution.core.context.currentSubject resolution.handle.slot
                        payload haccepted
                      have hipcExact := hipcAccepted.1
                      have hrawAccepted := hipcAccepted.2
                      have hsharedScheduler : state.blockingIPC.scheduler = state.scheduler :=
                        hstate.1.blockingScheduler
                      have hschedulerExact : blocking.ipc.scheduler =
                          { state.scheduler with
                            ready := state.scheduler.ready ++ [saved.owner]
                            lifecycle := { state.scheduler.lifecycle with
                              runnable := SubjectLifecycle.setBool
                                state.scheduler.lifecycle.runnable saved.owner true } } := by
                        rw [howner]
                        rw [houtcome] at hipcExact
                        rw [hipcExact]
                        simp only [BlockingIPC.send] at hrawAccepted ⊢
                        split at * <;> try simp_all [BlockingIPC.reject]
                        split at * <;> try simp_all [BlockingIPC.reject]
                        next cap hlookup =>
                          split at * <;> try simp_all [BlockingIPC.reject]
                          split at * <;> try simp_all [BlockingIPC.reject]
                          split at * <;> try simp_all [BlockingIPC.reject]
                          have hcapEndpoint : cap.object = endpoint := by
                            have hfacts : cap.kind = .endpoint ∧ cap.object = endpoint := by
                              simpa [BlockingIPC.endpointOf, hlookup] using hendpoint
                            exact hfacts.2
                          subst endpoint
                          rw [hqueue] at hrawAccepted ⊢
                          simp only at hrawAccepted ⊢
                          by_cases hfull :
                              state.scheduler.capacity ≤ state.scheduler.ready.length
                          · have hfullContext : state.blockingIPCContext.ipc.scheduler.capacity ≤
                                state.blockingIPCContext.ipc.scheduler.ready.length := by
                              simpa [CompositeState.blockingIPCContext, hsharedScheduler] using hfull
                            rw [ite_eq_left hfullContext] at hrawAccepted
                            contradiction
                          · have hroomContext : ¬ state.blockingIPCContext.ipc.scheduler.capacity ≤
                                state.blockingIPCContext.ipc.scheduler.ready.length := by
                              simpa [CompositeState.blockingIPCContext, hsharedScheduler] using hfull
                            simp [hfull, hroomContext, BlockingIPC.wakeState,
                              CompositeState.blockingIPCContext, hsharedScheduler]
                      simpa [dispatchBlockingSend, hresolve, payload, houtcome, hrestore] using
                        publishReleasedBlockingContext_wake_preserves_runtimeWellFormed
                          state blocking saved published hstate.1 hblocking hschedulerExact hrestore

inductive CompositeBlockingCancelReply where
  | notWaiting
  | contextRejected (reason : BlockingIPCContext.ContextError)
  | restoreRejected (reason : ResumablePreemption.Error)
  | rejected (reason : BlockingIPC.Error)
  | cancelled (context : ResumableContext.Context)
  deriving DecidableEq, Repr

structure CompositeBlockingCancelOutcome where
  state : CompositeState
  reply : CompositeBlockingCancelReply

def dispatchBlockingCancel (state : CompositeState) (subject : BlockingIPC.SubjectId) :
    CompositeBlockingCancelOutcome :=
  let outcome := BlockingIPCContext.cancel state.blockingIPCContext subject
  match outcome.result with
  | .notWaiting => { state, reply := .notWaiting }
  | .ipcRejected reason => { state, reply := .rejected reason }
  | .contextRejected reason => { state, reply := .contextRejected reason }
  | .cancelled =>
      match outcome.released with
      | none => { state, reply := .contextRejected .missingSaved }
      | some saved =>
          match publishReleasedBlockingContext state outcome.state saved with
          | .error reason => { state, reply := .restoreRejected reason }
          | .ok next => { state := next, reply := .cancelled saved }

inductive CompositeBlockingCancelRejection : CompositeBlockingCancelReply -> Prop
  | notWaiting : CompositeBlockingCancelRejection .notWaiting
  | context reason : CompositeBlockingCancelRejection (.contextRejected reason)
  | restore reason : CompositeBlockingCancelRejection (.restoreRejected reason)
  | ipc reason : CompositeBlockingCancelRejection (.rejected reason)

theorem dispatchBlockingCancel_rejected_atomic state subject reply
    (hrejected : CompositeBlockingCancelRejection reply)
    (hreply : (dispatchBlockingCancel state subject).reply = reply) :
    (dispatchBlockingCancel state subject).state = state := by
  cases hrejected
  all_goals
    simp only [dispatchBlockingCancel] at hreply ⊢
    generalize houtcome : BlockingIPCContext.cancel _ _ = outcome at hreply ⊢
    cases outcome with
    | mk next result released =>
        cases result <;> simp_all
        cases released <;> simp_all
        split <;> simp_all

theorem dispatchBlockingCancel_preserves_wellFormed state subject
    (hstate : BlockingReceiveWellFormed state) :
    BlockingReceiveWellFormed (dispatchBlockingCancel state subject).state := by
  rcases hstate with ⟨hblocking, hcoherent⟩
  have hpreserved := BlockingIPCContext.cancel_preserves_wellFormed
    state.blockingIPCContext subject hblocking
  cases houtcome : BlockingIPCContext.cancel state.blockingIPCContext subject with
  | mk next result released =>
      have hnext : BlockingIPCContext.WellFormed next := by simpa [houtcome] using hpreserved
      cases result with
      | notWaiting =>
          simpa [dispatchBlockingCancel, houtcome] using
            (show BlockingReceiveWellFormed state from ⟨hblocking, hcoherent⟩)
      | ipcRejected reason =>
          simpa [dispatchBlockingCancel, houtcome] using
            (show BlockingReceiveWellFormed state from ⟨hblocking, hcoherent⟩)
      | contextRejected reason =>
          simpa [dispatchBlockingCancel, houtcome] using
            (show BlockingReceiveWellFormed state from ⟨hblocking, hcoherent⟩)
      | cancelled =>
          cases released with
          | none =>
              simpa [dispatchBlockingCancel, houtcome] using
                (show BlockingReceiveWellFormed state from ⟨hblocking, hcoherent⟩)
          | some saved =>
              cases hrestore : publishReleasedBlockingContext state next saved with
              | error reason =>
                  simpa [dispatchBlockingCancel, houtcome, hrestore] using
                    (show BlockingReceiveWellFormed state from ⟨hblocking, hcoherent⟩)
              | ok published =>
                  have hcontext :=
                    (publishReleasedBlockingContext_restores_exact state next saved
                      published hrestore).2
                  exact ⟨by simpa [dispatchBlockingCancel, houtcome, hrestore, hcontext] using hnext,
                    by simpa [dispatchBlockingCancel, houtcome, hrestore] using
                      publishReleasedBlockingContext_blockingCoherent
                        state next saved published hrestore⟩

theorem dispatchBlockingCancel_cancelled_exact state subject saved
    (hstate : BlockingReceiveWellFormed state)
    (hcancelled : (dispatchBlockingCancel state subject).reply = .cancelled saved) :
    state.blockingContexts subject = some saved ∧
      (dispatchBlockingCancel state subject).state.blockingContexts subject = none ∧
      ResumablePreemption.contextFor
        (dispatchBlockingCancel state subject).state.resumable.contexts subject = some saved := by
  cases houtcome : BlockingIPCContext.cancel state.blockingIPCContext subject with
  | mk next result released =>
      cases result with
      | notWaiting => simp [dispatchBlockingCancel, houtcome] at hcancelled
      | ipcRejected reason => simp [dispatchBlockingCancel, houtcome] at hcancelled
      | contextRejected reason => simp [dispatchBlockingCancel, houtcome] at hcancelled
      | cancelled =>
          cases released with
          | none => simp [dispatchBlockingCancel, houtcome] at hcancelled
          | some actual =>
              cases hrestore : publishReleasedBlockingContext state next actual with
              | error reason =>
                  simp [dispatchBlockingCancel, houtcome, hrestore] at hcancelled
              | ok published =>
                  simp [dispatchBlockingCancel, houtcome, hrestore] at hcancelled
                  subst actual
                  have hexact := BlockingIPCContext.cancel_cancelled_exact
                    state.blockingIPCContext subject saved (by simp [houtcome]) (by simp [houtcome])
                  have hcontext := publishReleasedBlockingContext_restores_exact
                    state next saved published hrestore
                  have howner : saved.owner = subject := by
                    exact BlockingIPCContext.validSaved_owner subject saved
                      (hstate.1.2.2 subject saved hexact.1)
                  refine ⟨hexact.1, ?_, ?_⟩
                  · simp only [dispatchBlockingCancel, houtcome, hrestore]
                    change published.blockingIPCContext.blocked subject = none
                    rw [hcontext.2]
                    simpa [houtcome] using hexact.2
                  · simpa [dispatchBlockingCancel, houtcome, hrestore, howner] using hcontext.1

/-- A typed cancellation restores only a context valid for the scheduler that
the cancellation publishes atomically. -/
theorem dispatchBlockingCancel_cancelled_context_valid state subject saved
    (hcancelled : (dispatchBlockingCancel state subject).reply = .cancelled saved) :
    ResumablePreemption.validContext
      (dispatchBlockingCancel state subject).state.resumable saved := by
  cases houtcome : BlockingIPCContext.cancel state.blockingIPCContext subject with
  | mk next result released =>
      cases result with
      | notWaiting => simp [dispatchBlockingCancel, houtcome] at hcancelled
      | ipcRejected reason => simp [dispatchBlockingCancel, houtcome] at hcancelled
      | contextRejected reason => simp [dispatchBlockingCancel, houtcome] at hcancelled
      | cancelled =>
          cases released with
          | none => simp [dispatchBlockingCancel, houtcome] at hcancelled
          | some actual =>
              cases hrestore : publishReleasedBlockingContext state next actual with
              | error reason =>
                  simp [dispatchBlockingCancel, houtcome, hrestore] at hcancelled
              | ok published =>
                  simp [dispatchBlockingCancel, houtcome, hrestore] at hcancelled
                  subst actual
                  simpa [dispatchBlockingCancel, houtcome, hrestore] using
                    publishReleasedBlockingContext_published_valid
                      state next saved published hrestore

/-- A successful cancellation preserves the complete runtime invariant: the
exact saved subject context moves from the blocked bank into the resumable
bank while the authoritative scheduler publishes the canonical wake. -/
theorem dispatchBlockingCancel_cancelled_preserves_runtimeWellFormed
    state subject saved
    (hstate : BlockingRuntimeWellFormed state)
    (hcancelled : (dispatchBlockingCancel state subject).reply = .cancelled saved) :
    RuntimeWellFormed (dispatchBlockingCancel state subject).state := by
  have hpreserved := BlockingIPCContext.cancel_preserves_wellFormed
    state.blockingIPCContext subject hstate.2
  cases houtcome : BlockingIPCContext.cancel state.blockingIPCContext subject with
  | mk blocking result released =>
      have hblocking : BlockingIPCContext.WellFormed blocking := by
        simpa [houtcome] using hpreserved
      cases result with
      | notWaiting => simp [dispatchBlockingCancel, houtcome] at hcancelled
      | ipcRejected reason => simp [dispatchBlockingCancel, houtcome] at hcancelled
      | contextRejected reason => simp [dispatchBlockingCancel, houtcome] at hcancelled
      | cancelled =>
          cases released with
          | none => simp [dispatchBlockingCancel, houtcome] at hcancelled
          | some actual =>
              cases hrestore : publishReleasedBlockingContext state blocking actual with
              | error reason =>
                  simp [dispatchBlockingCancel, houtcome, hrestore] at hcancelled
              | ok published =>
                  simp [dispatchBlockingCancel, houtcome, hrestore] at hcancelled
                  subst actual
                  have hreleased :
                      (BlockingIPCContext.cancel state.blockingIPCContext subject).released =
                        some saved := by
                    simp [houtcome]
                  have hcancelledContext :
                      (BlockingIPCContext.cancel state.blockingIPCContext subject).result =
                        .cancelled := by
                    simp [houtcome]
                  have hexact := BlockingIPCContext.cancel_cancelled_exact
                    state.blockingIPCContext subject saved hcancelledContext hreleased
                  have howner : saved.owner = subject := by
                    exact BlockingIPCContext.validSaved_owner subject saved
                      (hstate.2.2.2 subject saved hexact.1)
                  have hipcExact := BlockingIPCContext.cancel_cancelled_ipc_exact
                    state.blockingIPCContext subject hcancelledContext
                  have hrawState :
                      blocking.ipc =
                        (BlockingIPC.cancelSubjectTyped state.blockingIPC subject).state := by
                    rw [houtcome] at hipcExact
                    exact hipcExact.1
                  have hrawCancelled :
                      (BlockingIPC.cancelSubjectTyped state.blockingIPC subject).result =
                        .cancelled := hipcExact.2
                  have hscheduler : blocking.ipc.scheduler =
                      { state.scheduler with
                        ready := state.scheduler.ready ++ [saved.owner]
                        lifecycle := { state.scheduler.lifecycle with
                          runnable := SubjectLifecycle.setBool
                            state.scheduler.lifecycle.runnable saved.owner true } } := by
                    rw [hrawState, howner]
                    simpa [hstate.1.blockingScheduler] using
                      BlockingIPC.cancelSubjectTyped_cancelled_scheduler_exact
                        state.blockingIPC subject hstate.2.1 hrawCancelled
                  simpa [dispatchBlockingCancel, houtcome, hrestore] using
                    publishReleasedBlockingContext_wake_preserves_runtimeWellFormed
                      state blocking saved published hstate.1 hblocking hscheduler hrestore

/-- A successful cancellation preserves both the complete composite runtime
invariant and the exact authoritative waiter/saved-context agreement. -/
theorem dispatchBlockingCancel_cancelled_preserves_blockingRuntimeWellFormed
    state subject saved
    (hstate : BlockingRuntimeWellFormed state)
    (hcancelled : (dispatchBlockingCancel state subject).reply = .cancelled saved) :
    BlockingRuntimeWellFormed (dispatchBlockingCancel state subject).state := by
  refine ⟨dispatchBlockingCancel_cancelled_preserves_runtimeWellFormed
      state subject saved hstate hcancelled, ?_⟩
  have hcoherent : state.BlockingIPCCoherent := by
    rcases hstate.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hblocking⟩
    exact hblocking.1
  exact (dispatchBlockingCancel_preserves_wellFormed state subject
    ⟨hstate.2, hcoherent⟩).1

/-! ## Execution-latched typed blocking gate -/

inductive CompositeBlockingOperation where
  | receive (handleWord : UInt64) (frame : Interrupt.HardwareFrame)
      (registers : ResumableContext.Registers)
  | send (handleWord word0 word1 : UInt64)
  | cancel (subject : BlockingIPC.SubjectId)
  deriving DecidableEq, Repr

inductive CompositeBlockingOperationReply where
  | receive (reply : CompositeBlockingReceiveReply)
  | send (reply : CompositeBlockingSendReply)
  | cancel (reply : CompositeBlockingCancelReply)
  deriving DecidableEq, Repr

inductive CompositeBlockingGateResult where
  | completed (reply : CompositeBlockingOperationReply)
  | rejectedBusy
  | rejectedHalted (record : HaltRecord)
  deriving DecidableEq, Repr

structure CompositeBlockingGateOutcome where
  state : CompositeState
  result : CompositeBlockingGateResult

/-- The finite blocking-gate results that denote an ordinary nonfatal denial.
Fatal absorption remains a distinct terminal result; successful delivery,
blocking, enqueue, wake, and cancellation are intentionally not classified as
rejections. -/
inductive CompositeBlockingGateRejection : CompositeBlockingGateResult → Prop where
  | busy : CompositeBlockingGateRejection .rejectedBusy
  | receive {reply} (hrejected : CompositeBlockingReceiveRejection reply) :
      CompositeBlockingGateRejection (.completed (.receive reply))
  | send {reply} (hrejected : CompositeBlockingSendRejection reply) :
      CompositeBlockingGateRejection (.completed (.send reply))
  | cancel {reply} (hrejected : CompositeBlockingCancelRejection reply) :
      CompositeBlockingGateRejection (.completed (.cancel reply))

/-- Exact composite post-state selected by one typed blocking operation.  This
is public so a refinement layer cannot pair a successful blocking reply with a
caller-selected or dependency-local post-state. -/
def applyBlockingOperation (state : CompositeState) : CompositeBlockingOperation → CompositeState
  | .receive handleWord frame registers =>
      (dispatchBlockingReceive state handleWord frame registers).state
  | .send handleWord word0 word1 =>
      (dispatchBlockingSend state handleWord word0 word1).state
  | .cancel subject =>
      (dispatchBlockingCancel state subject).state

/-- Exact typed observation selected by one blocking operation.  Successful
delivery, blocking, enqueue, wake, and cancellation remain distinguishable
from every finite dependency-local rejection. -/
def blockingOperationReply (state : CompositeState) :
    CompositeBlockingOperation → CompositeBlockingOperationReply
  | .receive handleWord frame registers =>
      .receive (dispatchBlockingReceive state handleWord frame registers).reply
  | .send handleWord word0 word1 =>
      .send (dispatchBlockingSend state handleWord word0 word1).reply
  | .cancel subject =>
      .cancel (dispatchBlockingCancel state subject).reply

/-- Total typed blocking gate under the same irreversible execution latch as
the ordinary composite gate.  No operation input carries caller identity,
address-space identity, or a saved-context owner. -/
def blockingGate (state : CompositeState) (operation : CompositeBlockingOperation) :
    CompositeBlockingGateOutcome :=
  match state.execution.mode with
  | .handling _ => { state, result := .rejectedBusy }
  | .halted record => { state, result := .rejectedHalted record }
  | .running =>
      { state := applyBlockingOperation state operation
        result := .completed (blockingOperationReply state operation) }

theorem blockingGate_running_exact state operation
    (hmode : state.execution.mode = .running) :
    blockingGate state operation =
      { state := applyBlockingOperation state operation
        result := .completed (blockingOperationReply state operation) } := by
  simp [blockingGate, hmode]

private theorem restoreBlockingPeer_dmaAuthority state blocking next
    (hnext : restoreBlockingPeer state blocking = .ok next) :
    next.dmaAccepted = state.dmaAccepted ∧
      next.dmaObserved = state.dmaObserved := by
  unfold restoreBlockingPeer at hnext
  repeat' first | split at hnext
  all_goals try contradiction
  all_goals injection hnext with hnext
  all_goals subst next
  all_goals exact ⟨rfl, rfl⟩

private theorem publishReleasedBlockingContext_dmaAuthority
    state blocking saved next
    (hnext : publishReleasedBlockingContext state blocking saved = .ok next) :
    next.dmaAccepted = state.dmaAccepted ∧
      next.dmaObserved = state.dmaObserved := by
  unfold publishReleasedBlockingContext at hnext
  repeat' first | split at hnext
  all_goals try contradiction
  all_goals injection hnext with hnext
  all_goals subst next
  all_goals exact ⟨rfl, rfl⟩

/-- Blocking receive, send/wake, and cancellation retain the accepted and
observed PCI authority fields for every typed success, denial, and outer-latch
result.  This is a structural operation law and needs no global compatibility
premise. -/
@[simp] theorem blockingGate_dmaAuthority state operation :
    (blockingGate state operation).state.dmaAccepted = state.dmaAccepted ∧
      (blockingGate state operation).state.dmaObserved = state.dmaObserved := by
  cases hmode : state.execution.mode with
  | handling entry => simp [blockingGate, hmode]
  | halted record => simp [blockingGate, hmode]
  | running =>
      cases operation <;>
        simp only [blockingGate, hmode, applyBlockingOperation,
          dispatchBlockingReceive, dispatchBlockingSend, dispatchBlockingCancel]
      all_goals
        repeat' first | split
        all_goals first
          | exact ⟨rfl, rfl⟩
          | exact restoreBlockingPeer_dmaAuthority _ _ _ ‹_›
          | exact publishReleasedBlockingContext_dmaAuthority _ _ _ _ ‹_›

/-- A completed blocking result proves that the execution latch was running
and fixes both the exact typed dependency reply and exact composite post-state.
Thus an IPC/context/scheduler rejection cannot be relabeled as a successful
block, delivery, wake, or cancellation. -/
theorem blockingGate_completed_sound state operation reply
    (hcompleted : (blockingGate state operation).result = .completed reply) :
    state.execution.mode = .running ∧
      reply = blockingOperationReply state operation ∧
      (blockingGate state operation).state = applyBlockingOperation state operation := by
  cases hmode : state.execution.mode with
  | running => simp [blockingGate, hmode] at hcompleted ⊢; simp [blockingGate, hmode, hcompleted]
  | handling active => simp [blockingGate, hmode] at hcompleted
  | halted record => simp [blockingGate, hmode] at hcompleted

/-- A delivery reported by the outer typed gate preserves the complete global
runtime invariant.  The completed-result contract prevents a wrapper from
pairing this reply with any state other than the exact delivery publication. -/
theorem blockingGate_receive_delivered_preserves_runtimeWellFormed
    state handleWord frame registers envelope
    (hstate : RuntimeWellFormed state)
    (hcompleted : (blockingGate state (.receive handleWord frame registers)).result =
      .completed (.receive (.delivered envelope))) :
    RuntimeWellFormed
      (blockingGate state (.receive handleWord frame registers)).state := by
  have hsound := blockingGate_completed_sound state
    (.receive handleWord frame registers) (.receive (.delivered envelope)) hcompleted
  have hdelivered :
      (dispatchBlockingReceive state handleWord frame registers).reply =
        .delivered envelope := by
    simpa [blockingOperationReply] using hsound.2.1.symm
  rw [hsound.2.2]
  simpa [applyBlockingOperation] using
    dispatchBlockingReceive_delivered_preserves_runtimeWellFormed
      state handleWord frame registers envelope hstate hdelivered

/-- A completed mailbox-only send at the outer typed gate preserves the full
global invariant and is tied to the exact dependency-local mutation. -/
theorem blockingGate_send_sent_preserves_runtimeWellFormed
    state handleWord word0 word1
    (hstate : RuntimeWellFormed state)
    (hcompleted : (blockingGate state (.send handleWord word0 word1)).result =
      .completed (.send .sent)) :
    RuntimeWellFormed
      (blockingGate state (.send handleWord word0 word1)).state := by
  have hsound := blockingGate_completed_sound state
    (.send handleWord word0 word1) (.send .sent) hcompleted
  have hsent :
      (dispatchBlockingSend state handleWord word0 word1).reply = .sent := by
    simpa [blockingOperationReply] using hsound.2.1.symm
  rw [hsound.2.2]
  simpa [applyBlockingOperation] using
    dispatchBlockingSend_sent_preserves_runtimeWellFormed
      state handleWord word0 word1 hstate hsent

/-- A wake reported by the outer gate publishes a context that is valid for
the exact scheduler/lifecycle post-state paired with that typed result. -/
theorem blockingGate_send_woke_context_valid
    state handleWord word0 word1 saved
    (hcompleted : (blockingGate state (.send handleWord word0 word1)).result =
      .completed (.send (.woke saved))) :
    ResumablePreemption.validContext
      (blockingGate state (.send handleWord word0 word1)).state.resumable saved := by
  have hsound := blockingGate_completed_sound state
    (.send handleWord word0 word1) (.send (.woke saved)) hcompleted
  have hwoke :
      (dispatchBlockingSend state handleWord word0 word1).reply = .woke saved := by
    simpa [blockingOperationReply] using hsound.2.1.symm
  rw [hsound.2.2]
  simpa [applyBlockingOperation] using
    dispatchBlockingSend_woke_context_valid state handleWord word0 word1 saved hwoke

/-- The outer typed wake preserves both the global runtime invariant and the
exact waiter/context agreement, so the released context cannot be published
into a scheduler projection that disagrees with the blocking store. -/
theorem blockingGate_send_woke_preserves_blockingRuntimeWellFormed
    state handleWord word0 word1 saved
    (hstate : BlockingRuntimeWellFormed state)
    (hcompleted : (blockingGate state (.send handleWord word0 word1)).result =
      .completed (.send (.woke saved))) :
    BlockingRuntimeWellFormed
      (blockingGate state (.send handleWord word0 word1)).state := by
  have hsound := blockingGate_completed_sound state
    (.send handleWord word0 word1) (.send (.woke saved)) hcompleted
  have hwoke :
      (dispatchBlockingSend state handleWord word0 word1).reply = .woke saved := by
    simpa [blockingOperationReply] using hsound.2.1.symm
  refine ⟨?_, ?_⟩
  · rw [hsound.2.2]
    simpa [applyBlockingOperation] using
      dispatchBlockingSend_woke_preserves_runtimeWellFormed
        state handleWord word0 word1 saved hstate hwoke
  · have hcoherent : state.BlockingIPCCoherent := by
      rcases hstate.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hblocking⟩
      exact hblocking.1
    rw [hsound.2.2]
    simpa [applyBlockingOperation] using
      (dispatchBlockingSend_preserves_wellFormed state handleWord word0 word1
        ⟨hstate.2, hcoherent⟩).1

/-- A cancellation reported by the outer gate likewise binds its restored
context to the exact authoritative post-state. -/
theorem blockingGate_cancel_cancelled_context_valid state subject saved
    (hcompleted : (blockingGate state (.cancel subject)).result =
      .completed (.cancel (.cancelled saved))) :
    ResumablePreemption.validContext
      (blockingGate state (.cancel subject)).state.resumable saved := by
  have hsound := blockingGate_completed_sound state
    (.cancel subject) (.cancel (.cancelled saved)) hcompleted
  have hcancelled :
      (dispatchBlockingCancel state subject).reply = .cancelled saved := by
    simpa [blockingOperationReply] using hsound.2.1.symm
  rw [hsound.2.2]
  simpa [applyBlockingOperation] using
    dispatchBlockingCancel_cancelled_context_valid state subject saved hcancelled

/-- A cancellation completed by the outer typed gate preserves the integrated
global runtime plus authoritative blocking-context invariant. -/
theorem blockingGate_cancel_cancelled_preserves_blockingRuntimeWellFormed
    state subject saved
    (hstate : BlockingRuntimeWellFormed state)
    (hcompleted : (blockingGate state (.cancel subject)).result =
      .completed (.cancel (.cancelled saved))) :
    BlockingRuntimeWellFormed
      (blockingGate state (.cancel subject)).state := by
  have hsound := blockingGate_completed_sound state
    (.cancel subject) (.cancel (.cancelled saved)) hcompleted
  have hcancelled :
      (dispatchBlockingCancel state subject).reply = .cancelled saved := by
    simpa [blockingOperationReply] using hsound.2.1.symm
  rw [hsound.2.2]
  simpa [applyBlockingOperation] using
    dispatchBlockingCancel_cancelled_preserves_blockingRuntimeWellFormed
      state subject saved hstate hcancelled

theorem blockingGate_mode_rejection_atomic state operation
    (hrejected : (blockingGate state operation).result = .rejectedBusy ∨
      ∃ record, (blockingGate state operation).result = .rejectedHalted record) :
    (blockingGate state operation).state = state := by
  cases hmode : state.execution.mode with
  | running =>
      cases operation <;> simp [blockingGate, hmode] at hrejected
  | handling entry => simp [blockingGate, hmode]
  | halted record => simp [blockingGate, hmode]

/-- Every ordinary blocking-gate rejection is globally atomic.  This theorem
classifies denial at the outer typed gate rather than relying on a caller to
recognize dependency-local replies; consequently a stale handle, invalid
saved-context transition, unavailable peer switch, restore failure, IPC
denial, empty cancellation, or busy latch all return the identical composite
state. -/
theorem blockingGate_rejection_atomic state operation
    (hrejected : CompositeBlockingGateRejection (blockingGate state operation).result) :
    (blockingGate state operation).state = state := by
  cases hmode : state.execution.mode with
  | handling entry => simp [blockingGate, hmode]
  | halted record =>
      simp only [blockingGate, hmode] at hrejected
      cases hrejected
  | running =>
      cases operation with
      | receive handleWord frame registers =>
          cases houtcome : dispatchBlockingReceive state handleWord frame registers with
          | mk next reply =>
              simp only [blockingGate, hmode, applyBlockingOperation,
                blockingOperationReply, houtcome] at hrejected ⊢
              cases hrejected with
              | receive hreply =>
                  have hatomic := dispatchBlockingReceive_rejected_atomic
                    state handleWord frame registers reply hreply (by simp [houtcome])
                  simpa [houtcome] using hatomic
      | send handleWord word0 word1 =>
          cases houtcome : dispatchBlockingSend state handleWord word0 word1 with
          | mk next reply =>
              simp only [blockingGate, hmode, applyBlockingOperation,
                blockingOperationReply, houtcome] at hrejected ⊢
              cases hrejected with
              | send hreply =>
                  have hatomic := dispatchBlockingSend_rejected_atomic
                    state handleWord word0 word1 reply hreply (by simp [houtcome])
                  simpa [houtcome] using hatomic
      | cancel subject =>
          cases houtcome : dispatchBlockingCancel state subject with
          | mk next reply =>
              simp only [blockingGate, hmode, applyBlockingOperation,
                blockingOperationReply, houtcome] at hrejected ⊢
              cases hrejected with
              | cancel hreply =>
                  have hatomic := dispatchBlockingCancel_rejected_atomic
                    state subject reply hreply (by simp [houtcome])
                  simpa [houtcome] using hatomic

/-- Every classified blocking-gate denial preserves the complete composite
runtime invariant.  This is the global-invariant slice available before the
mutating block, wake, and cancellation publishers are folded into
`RuntimeWellFormed`: rejection is literal state identity, so no projection can
drift while reporting an ordinary nonfatal denial. -/
theorem blockingGate_rejection_preserves_runtimeWellFormed state operation
    (hstate : RuntimeWellFormed state)
    (hrejected : CompositeBlockingGateRejection (blockingGate state operation).result) :
    RuntimeWellFormed (blockingGate state operation).state := by
  rw [blockingGate_rejection_atomic state operation hrejected]
  exact hstate

/-- Every block, wake, cancel, typed rejection, and latch rejection preserves
the authoritative waiter/context agreement and its scheduler projection. -/
theorem blockingGate_preserves_wellFormed state operation
    (hstate : BlockingReceiveWellFormed state) :
    BlockingReceiveWellFormed (blockingGate state operation).state := by
  cases hmode : state.execution.mode with
  | handling entry => simpa [blockingGate, hmode] using hstate
  | halted record => simpa [blockingGate, hmode] using hstate
  | running =>
      cases operation with
      | receive handleWord frame registers =>
          simpa [blockingGate, hmode, applyBlockingOperation] using
            dispatchBlockingReceive_preserves_wellFormed
              state handleWord frame registers hstate
      | send handleWord word0 word1 =>
          simpa [blockingGate, hmode, applyBlockingOperation] using
            dispatchBlockingSend_preserves_wellFormed
              state handleWord word0 word1 hstate
      | cancel subject =>
          simpa [blockingGate, hmode, applyBlockingOperation] using
            dispatchBlockingCancel_preserves_wellFormed state subject hstate

/-- A completed delivery preserves the integrated blocking/runtime invariant:
global projections, the authoritative waiter store, and the exact
saved-context bank remain well formed in one post-state. -/
theorem blockingGate_receive_delivered_preserves_blockingRuntimeWellFormed
    state handleWord frame registers envelope
    (hstate : BlockingRuntimeWellFormed state)
    (hcompleted : (blockingGate state (.receive handleWord frame registers)).result =
      .completed (.receive (.delivered envelope))) :
    BlockingRuntimeWellFormed
      (blockingGate state (.receive handleWord frame registers)).state := by
  refine ⟨blockingGate_receive_delivered_preserves_runtimeWellFormed
      state handleWord frame registers envelope hstate.1 hcompleted, ?_⟩
  have hcoherent : state.BlockingIPCCoherent := by
    rcases hstate.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hblocking⟩
    exact hblocking.1
  exact (blockingGate_preserves_wellFormed state
    (.receive handleWord frame registers) ⟨hstate.2, hcoherent⟩).1

/-- An accepted idle block at the outer typed gate preserves the integrated
global runtime and blocking-context invariant.  The post-state observation
that no peer was selected binds this claim to the terminal publication branch,
not to a restored-peer handoff. -/
theorem blockingGate_receive_idle_block_preserves_blockingRuntimeWellFormed
    state handleWord frame registers
    (hstate : BlockingRuntimeWellFormed state)
    (hcompleted : (blockingGate state (.receive handleWord frame registers)).result =
      .completed (.receive .blocked))
    (hidle :
      (blockingGate state (.receive handleWord frame registers)).state.scheduler.lifecycle.current =
        none) :
    BlockingRuntimeWellFormed
      (blockingGate state (.receive handleWord frame registers)).state := by
  have hsound := blockingGate_completed_sound state
    (.receive handleWord frame registers) (.receive .blocked) hcompleted
  have hblocked :
      (dispatchBlockingReceive state handleWord frame registers).reply = .blocked := by
    simpa [blockingOperationReply] using hsound.2.1.symm
  have hidleDispatch :
      (dispatchBlockingReceive state handleWord frame registers).state.scheduler.lifecycle.current =
        none := by
    rw [hsound.2.2] at hidle
    simpa [applyBlockingOperation] using hidle
  refine ⟨?_, ?_⟩
  · rw [hsound.2.2]
    simpa [applyBlockingOperation] using
      dispatchBlockingReceive_idle_block_preserves_runtimeWellFormed
        state handleWord frame registers hstate hblocked hidleDispatch
  · have hcoherent : state.BlockingIPCCoherent := by
      rcases hstate.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hblocking⟩
      exact hblocking.1
    exact (blockingGate_preserves_wellFormed state
      (.receive handleWord frame registers) ⟨hstate.2, hcoherent⟩).1

/-- An accepted block with an immediately selected peer preserves the same
integrated invariant through the outer typed gate.  The selected identity is
an observation of the authoritative post-state, never an operation input. -/
theorem blockingGate_receive_selected_block_preserves_blockingRuntimeWellFormed
    state handleWord frame registers selected
    (hstate : BlockingRuntimeWellFormed state)
    (hcompleted : (blockingGate state (.receive handleWord frame registers)).result =
      .completed (.receive .blocked))
    (hselected :
      (blockingGate state (.receive handleWord frame registers)).state.scheduler.lifecycle.current =
        some selected) :
    BlockingRuntimeWellFormed
      (blockingGate state (.receive handleWord frame registers)).state := by
  have hsound := blockingGate_completed_sound state
    (.receive handleWord frame registers) (.receive .blocked) hcompleted
  have hblocked :
      (dispatchBlockingReceive state handleWord frame registers).reply = .blocked := by
    simpa [blockingOperationReply] using hsound.2.1.symm
  have hselectedDispatch :
      (dispatchBlockingReceive state handleWord frame registers).state.scheduler.lifecycle.current =
        some selected := by
    rw [hsound.2.2] at hselected
    simpa [applyBlockingOperation] using hselected
  refine ⟨?_, ?_⟩
  · rw [hsound.2.2]
    simpa [applyBlockingOperation] using
      dispatchBlockingReceive_selected_block_preserves_runtimeWellFormed
        state handleWord frame registers selected hstate hblocked hselectedDispatch
  · have hcoherent : state.BlockingIPCCoherent := by
      rcases hstate.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hblocking⟩
      exact hblocking.1
    exact (blockingGate_preserves_wellFormed state
      (.receive handleWord frame registers) ⟨hstate.2, hcoherent⟩).1

/-- Every typed successful block preserves the integrated global invariant.
The authoritative post-state is total: it either has no current peer and uses
the idle publication, or names the peer restored by the selected path. -/
theorem blockingGate_receive_blocked_preserves_blockingRuntimeWellFormed
    state handleWord frame registers
    (hstate : BlockingRuntimeWellFormed state)
    (hcompleted : (blockingGate state (.receive handleWord frame registers)).result =
      .completed (.receive .blocked)) :
    BlockingRuntimeWellFormed
      (blockingGate state (.receive handleWord frame registers)).state := by
  cases hcurrent :
      (blockingGate state (.receive handleWord frame registers)).state.scheduler.lifecycle.current with
  | none =>
      exact blockingGate_receive_idle_block_preserves_blockingRuntimeWellFormed
        state handleWord frame registers hstate hcompleted hcurrent
  | some selected =>
      exact blockingGate_receive_selected_block_preserves_blockingRuntimeWellFormed
        state handleWord frame registers selected hstate hcompleted hcurrent

/-- The total typed blocking gate preserves the integrated global runtime and
authoritative waiter/context invariant for every operation and every result.
This closes the operation-specific inventory above: delivery, blocking,
enqueue, wake, and cancellation use their exact success lemmas, while every
finite denial and both execution-latch rejections are literal no-ops. -/
theorem blockingGate_preserves_blockingRuntimeWellFormed state operation
    (hstate : BlockingRuntimeWellFormed state) :
    BlockingRuntimeWellFormed (blockingGate state operation).state := by
  have hcoherent : state.BlockingIPCCoherent := by
    rcases hstate.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hblocking⟩
    exact hblocking.1
  cases hmode : state.execution.mode with
  | handling entry => simpa [blockingGate, hmode] using hstate
  | halted record => simpa [blockingGate, hmode] using hstate
  | running =>
      cases operation with
      | receive handleWord frame registers =>
          cases hreply : (dispatchBlockingReceive state handleWord frame registers).reply with
          | handleRejected reason =>
              have hrejected : CompositeBlockingGateRejection
                  (blockingGate state (.receive handleWord frame registers)).result := by
                simpa [blockingGate, hmode, blockingOperationReply, hreply] using
                  (CompositeBlockingGateRejection.receive
                    (CompositeBlockingReceiveRejection.handle reason))
              rw [blockingGate_rejection_atomic state
                (.receive handleWord frame registers) hrejected]
              exact hstate
          | contextRejected reason =>
              have hrejected : CompositeBlockingGateRejection
                  (blockingGate state (.receive handleWord frame registers)).result := by
                simpa [blockingGate, hmode, blockingOperationReply, hreply] using
                  (CompositeBlockingGateRejection.receive
                    (CompositeBlockingReceiveRejection.context reason))
              rw [blockingGate_rejection_atomic state
                (.receive handleWord frame registers) hrejected]
              exact hstate
          | rejected reason =>
              have hrejected : CompositeBlockingGateRejection
                  (blockingGate state (.receive handleWord frame registers)).result := by
                simpa [blockingGate, hmode, blockingOperationReply, hreply] using
                  (CompositeBlockingGateRejection.receive
                    (CompositeBlockingReceiveRejection.ipc reason))
              rw [blockingGate_rejection_atomic state
                (.receive handleWord frame registers) hrejected]
              exact hstate
          | switchRequired =>
              have hrejected : CompositeBlockingGateRejection
                  (blockingGate state (.receive handleWord frame registers)).result := by
                simpa [blockingGate, hmode, blockingOperationReply, hreply] using
                  (CompositeBlockingGateRejection.receive
                    CompositeBlockingReceiveRejection.switchRequired)
              rw [blockingGate_rejection_atomic state
                (.receive handleWord frame registers) hrejected]
              exact hstate
          | delivered envelope =>
              apply blockingGate_receive_delivered_preserves_blockingRuntimeWellFormed
                state handleWord frame registers envelope hstate
              simp [blockingGate, hmode, blockingOperationReply, hreply]
          | blocked =>
              apply blockingGate_receive_blocked_preserves_blockingRuntimeWellFormed
                state handleWord frame registers hstate
              simp [blockingGate, hmode, blockingOperationReply, hreply]
      | send handleWord word0 word1 =>
          cases hreply : (dispatchBlockingSend state handleWord word0 word1).reply with
          | handleRejected reason =>
              have hrejected : CompositeBlockingGateRejection
                  (blockingGate state (.send handleWord word0 word1)).result := by
                simpa [blockingGate, hmode, blockingOperationReply, hreply] using
                  (CompositeBlockingGateRejection.send
                    (CompositeBlockingSendRejection.handle reason))
              rw [blockingGate_rejection_atomic state
                (.send handleWord word0 word1) hrejected]
              exact hstate
          | contextRejected reason =>
              have hrejected : CompositeBlockingGateRejection
                  (blockingGate state (.send handleWord word0 word1)).result := by
                simpa [blockingGate, hmode, blockingOperationReply, hreply] using
                  (CompositeBlockingGateRejection.send
                    (CompositeBlockingSendRejection.context reason))
              rw [blockingGate_rejection_atomic state
                (.send handleWord word0 word1) hrejected]
              exact hstate
          | restoreRejected reason =>
              have hrejected : CompositeBlockingGateRejection
                  (blockingGate state (.send handleWord word0 word1)).result := by
                simpa [blockingGate, hmode, blockingOperationReply, hreply] using
                  (CompositeBlockingGateRejection.send
                    (CompositeBlockingSendRejection.restore reason))
              rw [blockingGate_rejection_atomic state
                (.send handleWord word0 word1) hrejected]
              exact hstate
          | rejected reason =>
              have hrejected : CompositeBlockingGateRejection
                  (blockingGate state (.send handleWord word0 word1)).result := by
                simpa [blockingGate, hmode, blockingOperationReply, hreply] using
                  (CompositeBlockingGateRejection.send
                    (CompositeBlockingSendRejection.ipc reason))
              rw [blockingGate_rejection_atomic state
                (.send handleWord word0 word1) hrejected]
              exact hstate
          | sent =>
              refine ⟨?_, ?_⟩
              · apply blockingGate_send_sent_preserves_runtimeWellFormed
                  state handleWord word0 word1 hstate.1
                simp [blockingGate, hmode, blockingOperationReply, hreply]
              · exact (blockingGate_preserves_wellFormed state
                  (.send handleWord word0 word1) ⟨hstate.2, hcoherent⟩).1
          | woke saved =>
              apply blockingGate_send_woke_preserves_blockingRuntimeWellFormed
                state handleWord word0 word1 saved hstate
              simp [blockingGate, hmode, blockingOperationReply, hreply]
      | cancel subject =>
          cases hreply : (dispatchBlockingCancel state subject).reply with
          | notWaiting =>
              have hrejected : CompositeBlockingGateRejection
                  (blockingGate state (.cancel subject)).result := by
                simpa [blockingGate, hmode, blockingOperationReply, hreply] using
                  (CompositeBlockingGateRejection.cancel
                    CompositeBlockingCancelRejection.notWaiting)
              rw [blockingGate_rejection_atomic state (.cancel subject) hrejected]
              exact hstate
          | contextRejected reason =>
              have hrejected : CompositeBlockingGateRejection
                  (blockingGate state (.cancel subject)).result := by
                simpa [blockingGate, hmode, blockingOperationReply, hreply] using
                  (CompositeBlockingGateRejection.cancel
                    (CompositeBlockingCancelRejection.context reason))
              rw [blockingGate_rejection_atomic state (.cancel subject) hrejected]
              exact hstate
          | restoreRejected reason =>
              have hrejected : CompositeBlockingGateRejection
                  (blockingGate state (.cancel subject)).result := by
                simpa [blockingGate, hmode, blockingOperationReply, hreply] using
                  (CompositeBlockingGateRejection.cancel
                    (CompositeBlockingCancelRejection.restore reason))
              rw [blockingGate_rejection_atomic state (.cancel subject) hrejected]
              exact hstate
          | rejected reason =>
              have hrejected : CompositeBlockingGateRejection
                  (blockingGate state (.cancel subject)).result := by
                simpa [blockingGate, hmode, blockingOperationReply, hreply] using
                  (CompositeBlockingGateRejection.cancel
                    (CompositeBlockingCancelRejection.ipc reason))
              rw [blockingGate_rejection_atomic state (.cancel subject) hrejected]
              exact hstate
          | cancelled saved =>
              apply blockingGate_cancel_cancelled_preserves_blockingRuntimeWellFormed
                state subject saved hstate
              simp [blockingGate, hmode, blockingOperationReply, hreply]

end LeanOS.FailStop
