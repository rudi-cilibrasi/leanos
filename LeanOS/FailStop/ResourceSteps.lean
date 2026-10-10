import LeanOS.FailStop.Resources

/-!
# Fail-stop composite: resource invariants for every step and whole traces

`LeanOS.FailStop.Resources` added the issuer, frame-budget, and frame-content
projections and proved `ResourceWellFormed` for the steps that leave the
subject history and memory alone.  This module finishes the job for item 1 of
the ADR 0010 spawn gate (#473, #499):

- **Every authoritative step.**  `authoritativeGate_historyAgrees` proves that
  every authoritative step except caller-identity creation keeps every history
  the resource conjuncts read: both issuers, the frame commitment, the frame
  contents, the subject history, both object histories, the frame allocator,
  and every object binding.  That covers interrupt cleanup, `syscall`,
  `resumePreempt`, `protect`, both terminations, the scheduler steps, the
  blocking operations, and the deferred drain.  It needs only the coherence
  and blocking-lifecycle facts of `AuthoritativeRuntimeWellFormed`, because
  those steps republish a lifecycle or memory taken from the resumable or
  blocking views.  `authoritativeGate_preserves_resourceRuntimeWellFormed`
  follows.
- **Caller-identity creation.**  `Operation.createSubject k` is unchanged; it
  is what `CompositeDispatcher` replays and what #535's unwinding proofs
  reason about.  It keeps the combined invariant exactly when `k` is positive
  and below the subject counter
  (`authoritativeGate_createSubject_preserves_resourceRuntimeWellFormed`), and
  that bound is necessary (`authoritativeGate_createSubject_requires_bound`).
- **Invalidation publication.**  Every entry point but the active current-unmap
  completion keeps the combined invariant
  (`InvalidationOperation.apply_preserves_resourceRuntimeWellFormed`).  The
  current-unmap completion installs the pending successor's memory, so it
  needs `CurrentUnmapAdmissible`; the established prepare-then-acknowledge path
  provides it (`currentUnmapAdmissible_of_prepared`).
- **Whole traces.**  `CompositeStep` now also carries the invalidation entry
  points, so a trace can contain every public transition.
  `composite_resource_trace` proves that along every trace of admissible
  steps the combined invariant holds, no identity is created twice by either
  creation path, the issued history only grows, and every subject's frame
  usage and limit are exactly unchanged.
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

/-! ## Subsystem transitions keep the subject history -/

/-- Selecting the next subject never changes the issued subject history. -/
theorem Scheduler.selectNext_issuedSubjects (state : Scheduler.State) :
    (Scheduler.selectNext state).state.lifecycle.issuedSubjects =
      state.lifecycle.issuedSubjects := by
  unfold Scheduler.selectNext
  repeat' split
  all_goals simp [Scheduler.reject]

/-- A scheduler tick never changes the issued subject history. -/
theorem Scheduler.tick_issuedSubjects (state : Scheduler.State) :
    (Scheduler.tick state).state.lifecycle.issuedSubjects =
      state.lifecycle.issuedSubjects := by
  unfold Scheduler.tick Scheduler.yield
  split
  · simp [Scheduler.reject]
  · split
    · simp [Scheduler.reject]
    · next subject _ _ =>
        have := Scheduler.selectNext_issuedSubjects
          { state with ready := state.ready ++ [subject]
                       lifecycle := { state.lifecycle with current := none } }
        generalize Scheduler.selectNext _ = outcome at this ⊢
        cases outcome with
        | mk next result => cases result <;> simp_all [Scheduler.reject]

/-- Removing a subject from the run queue never changes the issued subject
history. -/
theorem Scheduler.remove_issuedSubjects (state : Scheduler.State) subject :
    (Scheduler.remove state subject).state.lifecycle.issuedSubjects =
      state.lifecycle.issuedSubjects := by
  unfold Scheduler.remove
  split <;> simp [Scheduler.reject]

/-- A timer switch, on every outcome, keeps the issued subject history and the
virtual memory of the translation view. -/
theorem ResumablePreemption.switch_history (state : ResumablePreemption.State)
    interruptState frame registers :
    (ResumablePreemption.switch state interruptState frame registers).state.scheduler.lifecycle.issuedSubjects =
        state.scheduler.lifecycle.issuedSubjects ∧
      (ResumablePreemption.switch state interruptState frame registers).state.translations.virtual =
        state.translations.virtual := by
  have tick := Scheduler.tick_issuedSubjects state.scheduler
  unfold ResumablePreemption.switch
  generalize Scheduler.tick state.scheduler = scheduled at tick ⊢
  rcases scheduled with ⟨scheduled, result⟩
  rcases result with (_ | selected) | reason
  all_goals (repeat' split) <;>
    try simp_all [ResumablePreemption.reject, ResumablePreemption.halt, TLB.switch]
  all_goals (repeat' split) <;> simp_all [TLB.switch]

/-- A resumable-aware removal, on every outcome, keeps the issued subject
history and the virtual memory of the translation view. -/
theorem ResumablePreemption.remove_history (state : ResumablePreemption.State) subject :
    (ResumablePreemption.remove state subject).state.scheduler.lifecycle.issuedSubjects =
        state.scheduler.lifecycle.issuedSubjects ∧
      (ResumablePreemption.remove state subject).state.translations.virtual =
        state.translations.virtual := by
  have removed := Scheduler.remove_issuedSubjects state.scheduler subject
  unfold ResumablePreemption.remove
  generalize Scheduler.remove state.scheduler subject = outcome at removed ⊢
  rcases outcome with ⟨next, result⟩
  cases result with
  | rejected reason => exact ⟨rfl, rfl⟩
  | accepted context =>
      dsimp only at removed ⊢
      split
      · exact ⟨removed, rfl⟩
      · exact ⟨rfl, rfl⟩

/-- `Scheduler.selectNext_issuedSubjects` for a named outcome. -/
theorem Scheduler.selectNext_eq_issuedSubjects {state : Scheduler.State} {outcome}
    (h : Scheduler.selectNext state = outcome) :
    outcome.state.lifecycle.issuedSubjects = state.lifecycle.issuedSubjects := by
  rw [← h]; exact Scheduler.selectNext_issuedSubjects state

/-- Blocking receive never changes the issued subject history. -/
theorem BlockingIPC.receiveOrBlock_issuedSubjects (state : BlockingIPC.State) caller slot :
    (BlockingIPC.receiveOrBlock state caller slot).state.scheduler.lifecycle.issuedSubjects =
      state.scheduler.lifecycle.issuedSubjects := by
  unfold BlockingIPC.receiveOrBlock
  dsimp only
  repeat' split
  all_goals first
    | rfl
    | (rename_i heq; have := Scheduler.selectNext_eq_issuedSubjects heq
       simpa [BlockingIPC.blockState] using this)
    | simp [Scheduler.selectNext_issuedSubjects, BlockingIPC.blockState]

/-- Blocking send never changes the issued subject history. -/
theorem BlockingIPC.send_issuedSubjects (state : BlockingIPC.State) caller slot payload :
    (BlockingIPC.send state caller slot payload).state.scheduler.lifecycle.issuedSubjects =
      state.scheduler.lifecycle.issuedSubjects := by
  unfold BlockingIPC.send
  repeat' split
  all_goals simp [BlockingIPC.reject, BlockingIPC.wakeState]

/-- Waiter cancellation never changes the issued subject history. -/
theorem BlockingIPC.cancelSubject_issuedSubjects (state : BlockingIPC.State) subject :
    (BlockingIPC.cancelSubject state subject).scheduler.lifecycle.issuedSubjects =
      state.scheduler.lifecycle.issuedSubjects := by
  unfold BlockingIPC.cancelSubject
  split
  · rfl
  · dsimp only
    split <;> rfl

/-- Typed waiter cancellation never changes the issued subject history. -/
theorem BlockingIPC.cancelSubjectTyped_issuedSubjects (state : BlockingIPC.State) subject :
    (BlockingIPC.cancelSubjectTyped state subject).state.scheduler.lifecycle.issuedSubjects =
      state.scheduler.lifecycle.issuedSubjects := by
  unfold BlockingIPC.cancelSubjectTyped
  split
  · rfl
  · split
    · rfl
    · exact BlockingIPC.cancelSubject_issuedSubjects state subject


/-- Context-carrying blocking receive never changes the issued subject history. -/
theorem BlockingIPCContext.receiveOrBlock_issuedSubjects (state : BlockingIPCContext.State)
    caller slot saved :
    (BlockingIPCContext.receiveOrBlock state caller slot saved).state.ipc.scheduler.lifecycle.issuedSubjects =
      state.ipc.scheduler.lifecycle.issuedSubjects := by
  have := BlockingIPC.receiveOrBlock_issuedSubjects state.ipc caller slot
  unfold BlockingIPCContext.receiveOrBlock
  generalize BlockingIPC.receiveOrBlock state.ipc caller slot = outcome at this ⊢
  rcases outcome with ⟨next, result⟩
  cases result <;> dsimp only <;> (repeat' split) <;> simp_all

/-- Context-carrying blocking send never changes the issued subject history. -/
theorem BlockingIPCContext.send_issuedSubjects (state : BlockingIPCContext.State)
    caller slot payload :
    (BlockingIPCContext.send state caller slot payload).state.ipc.scheduler.lifecycle.issuedSubjects =
      state.ipc.scheduler.lifecycle.issuedSubjects := by
  have := BlockingIPC.send_issuedSubjects state.ipc caller slot payload
  unfold BlockingIPCContext.send
  generalize BlockingIPC.send state.ipc caller slot payload = outcome at this ⊢
  rcases outcome with ⟨next, result⟩
  cases result <;> dsimp only <;> (repeat' split) <;> simp_all

/-- Context-carrying cancellation never changes the issued subject history. -/
theorem BlockingIPCContext.cancel_issuedSubjects (state : BlockingIPCContext.State) subject :
    (BlockingIPCContext.cancel state subject).state.ipc.scheduler.lifecycle.issuedSubjects =
      state.ipc.scheduler.lifecycle.issuedSubjects := by
  have := BlockingIPC.cancelSubjectTyped_issuedSubjects state.ipc subject
  unfold BlockingIPCContext.cancel
  generalize BlockingIPC.cancelSubjectTyped state.ipc subject = outcome at this ⊢
  rcases outcome with ⟨next, result⟩
  cases result <;> dsimp only <;> (repeat' split) <;> simp_all

/-- The deferred-cancellation drain never changes the issued subject history. -/
theorem BlockingIPCContext.drainDeferred_issuedSubjects (state : BlockingIPCContext.State)
    deferred resumable capacity subject :
    (BlockingIPCContext.drainDeferred state deferred resumable capacity subject).state.ipc.scheduler.lifecycle.issuedSubjects =
      state.ipc.scheduler.lifecycle.issuedSubjects := by
  unfold BlockingIPCContext.drainDeferred
  repeat' split
  all_goals rfl

/-! ## Resource histories -/

/-- The virtual-memory histories the resource conjuncts read. -/
def VirtualHistoryAgrees (before after : VirtualMapping.State) : Prop :=
  after.memory.issued = before.memory.issued ∧
    after.issuedAddressSpace = before.issuedAddressSpace ∧
    after.memory.allocator = before.memory.allocator ∧
    after.memory.binding = before.memory.binding

/-- Every virtual-memory state agrees with itself. -/
theorem VirtualHistoryAgrees.refl (state : VirtualMapping.State) :
    VirtualHistoryAgrees state state := ⟨rfl, rfl, rfl, rfl⟩

/-- Equal memory registries and issued address spaces agree. -/
theorem VirtualHistoryAgrees.of_memory {before after : VirtualMapping.State}
    (memory : after.memory = before.memory)
    (spaces : after.issuedAddressSpace = before.issuedAddressSpace) :
    VirtualHistoryAgrees before after := by
  rw [VirtualHistoryAgrees, memory, spaces]; exact ⟨rfl, rfl, rfl, rfl⟩

/-- Assemble `ResourceHistoryAgrees` from its resource, subject-history, and
memory-history parts. -/
theorem resourceHistoryAgrees_of {before after : CompositeState}
    (issuers : after.issuers = before.issuers)
    (budgets : after.frameBudgets = before.frameBudgets)
    (scrub : after.scrub = before.scrub)
    (subjects : after.lifecycle.issuedSubjects = before.lifecycle.issuedSubjects)
    (virtual : VirtualHistoryAgrees before.virtualMemory after.virtualMemory) :
    ResourceHistoryAgrees before after :=
  ⟨issuers, budgets, scrub, subjects, virtual.1, virtual.2.1, virtual.2.2.1, virtual.2.2.2⟩

/-- History agreement composes along consecutive transitions. -/
theorem ResourceHistoryAgrees.trans {first second third : CompositeState}
    (left : ResourceHistoryAgrees first second) (right : ResourceHistoryAgrees second third) :
    ResourceHistoryAgrees first third := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := left
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := right
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6,
    b7.trans a7, b8.trans a8⟩

/-- Every user syscall outcome keeps the memory registry and the issued
address spaces: map and unmap change mappings only. -/
theorem Syscall.dispatch_virtualHistory (state : VirtualMapping.State) context call :
    VirtualHistoryAgrees state (Syscall.dispatch state context call).state := by
  unfold Syscall.dispatch Syscall.dispatchDecoded
  repeat' split
  all_goals first
    | exact VirtualHistoryAgrees.refl _
    | exact VirtualHistoryAgrees.of_memory (VirtualMapping.map_registry ..).1
        (VirtualMapping.map_registry ..).2
    | exact VirtualHistoryAgrees.of_memory (VirtualMapping.unmap_registry ..).1
        (VirtualMapping.unmap_registry ..).2

/-- Permission reduction keeps the memory registry and the issued address
spaces. -/
theorem TLB.protect_virtualHistory (state : TLB.State) actor addressSpace page permissions :
    VirtualHistoryAgrees state.virtual
      (TLB.protect state actor addressSpace page permissions).state.virtual := by
  unfold TLB.protect
  repeat' split
  all_goals first
    | exact VirtualHistoryAgrees.refl _
    | exact VirtualHistoryAgrees.of_memory rfl rfl

/-! ## Composite publishers keep the resource histories -/

/-- Publishing a blocking store whose lifecycle keeps the subject history
keeps every resource history: it writes neither memory nor a resource
projection. -/
theorem publishBlockingIPCContext_historyAgrees (state : CompositeState)
    (blocking : BlockingIPCContext.State)
    (subjects : blocking.ipc.scheduler.lifecycle.issuedSubjects =
      state.lifecycle.issuedSubjects) :
    ResourceHistoryAgrees state (publishBlockingIPCContext state blocking) :=
  resourceHistoryAgrees_of rfl rfl rfl subjects (VirtualHistoryAgrees.refl _)

/-- Restoring the scheduler-selected peer after a block keeps every resource
history when the published blocking lifecycle does. -/
theorem restoreBlockingPeer_historyAgrees (state : CompositeState)
    (blocking : BlockingIPCContext.State) (next : CompositeState)
    (subjects : blocking.ipc.scheduler.lifecycle.issuedSubjects =
      state.lifecycle.issuedSubjects)
    (restored : restoreBlockingPeer state blocking = .ok next) :
    ResourceHistoryAgrees state next := by
  unfold restoreBlockingPeer at restored
  repeat' split at restored
  all_goals try contradiction
  all_goals injection restored with restored
  all_goals subst next
  all_goals exact resourceHistoryAgrees_of rfl rfl rfl subjects (VirtualHistoryAgrees.refl _)

/-- Publishing a released waiter keeps every resource history when the
published blocking lifecycle does. -/
theorem publishReleasedBlockingContext_historyAgrees (state : CompositeState)
    (blocking : BlockingIPCContext.State) saved (next : CompositeState)
    (subjects : blocking.ipc.scheduler.lifecycle.issuedSubjects =
      state.lifecycle.issuedSubjects)
    (published : publishReleasedBlockingContext state blocking saved = .ok next) :
    ResourceHistoryAgrees state next := by
  unfold publishReleasedBlockingContext at published
  repeat' split at published
  all_goals try contradiction
  all_goals injection published with published
  all_goals subst next
  all_goals exact resourceHistoryAgrees_of rfl rfl rfl subjects (VirtualHistoryAgrees.refl _)

/-- The coherence facts the history proofs use. -/
theorem CompositeState.Coherent.resumableLifecycle {state : CompositeState}
    (coherent : state.Coherent) :
    state.resumable.scheduler.lifecycle = state.lifecycle := by
  rw [coherent.2.2.2.2.2.2.2.1]; exact coherent.2.1

/-- Under coherence the resumable translation view observes the composite
virtual memory. -/
theorem CompositeState.Coherent.resumableVirtual {state : CompositeState}
    (coherent : state.Coherent) :
    state.resumable.translations.virtual = state.virtualMemory :=
  coherent.2.2.2.2.2.2.2.2.1

/-- Cleanup publication keeps every resource history: termination keeps the
issued subject history, and cleanup changes only capabilities, owners, and
mappings of memory. -/
theorem installTerminatedResumable_cleanup_historyAgrees (state : CompositeState) subject
    (coherent : state.Coherent) :
    ResourceHistoryAgrees state
      (installTerminatedResumable state
        (ResumablePreemption.cleanupSubject state.resumable subject)) := by
  have lifecycle := coherent.resumableLifecycle
  have virtual := coherent.resumableVirtual
  refine resourceHistoryAgrees_of rfl rfl rfl ?_ ?_
  · simp [installTerminatedResumable, ResumablePreemption.cleanupSubject,
      SubjectLifecycle.terminateState, lifecycle]
  · simp [installTerminatedResumable, ResumablePreemption.cleanupSubject, VirtualHistoryAgrees,
      virtual]

/-- Explicit termination publication keeps every resource history. -/
theorem installTerminatedSubject_historyAgrees (state : CompositeState) subject
    (coherent : state.Coherent) :
    ResourceHistoryAgrees state
      (installTerminatedSubject state subject
        (ResumablePreemption.cleanupSubject state.resumable subject)) := by
  have cleaned := installTerminatedResumable_cleanup_historyAgrees state subject coherent
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := cleaned
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩

/-- Contained interrupt cleanup keeps every resource history. -/
theorem publishInterruptCleanup_historyAgrees (state : CompositeState) subject
    (coherent : state.Coherent) :
    ResourceHistoryAgrees state (publishInterruptCleanup state subject) := by
  have cleaned := installTerminatedResumable_cleanup_historyAgrees state subject coherent
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := cleaned
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩

/-- Publishing a resumable state keeps every resource history when its
lifecycle and translation memory do. -/
theorem installResumable_historyAgrees (state : CompositeState)
    (resumable : ResumablePreemption.State)
    (subjects : resumable.scheduler.lifecycle.issuedSubjects = state.lifecycle.issuedSubjects)
    (virtual : VirtualHistoryAgrees state.virtualMemory resumable.translations.virtual) :
    ResourceHistoryAgrees state (installResumable state resumable) :=
  resourceHistoryAgrees_of rfl rfl rfl subjects virtual

/-- Publishing a mapping-only change keeps every resource history when the
new memory histories agree. -/
theorem installVirtualMemory_historyAgrees (state : CompositeState)
    (virtualMemory : VirtualMapping.State) translations
    (virtual : VirtualHistoryAgrees state.virtualMemory virtualMemory) :
    ResourceHistoryAgrees state (installVirtualMemory state virtualMemory translations) :=
  resourceHistoryAgrees_of rfl rfl rfl rfl virtual

/-- Return-authority selection writes only the execution latch. -/
theorem selectLiveReturnAuthority_historyAgrees (state : CompositeState) purpose :
    ResourceHistoryAgrees state (selectLiveReturnAuthority state purpose) := by
  rw [selectLiveReturnAuthority_eq_execution_update]
  exact ResourceHistoryAgrees.refl state


/-- Composite blocking receive keeps every resource history. -/
theorem dispatchBlockingReceive_historyAgrees (state : CompositeState) handleWord frame registers
    (blocking : state.blockingIPC.scheduler.lifecycle.issuedSubjects =
      state.lifecycle.issuedSubjects) :
    ResourceHistoryAgrees state (dispatchBlockingReceive state handleWord frame registers).state := by
  unfold dispatchBlockingReceive
  dsimp only
  split
  · exact ResourceHistoryAgrees.refl state
  · next resolution _ =>
      have subjects := BlockingIPCContext.receiveOrBlock_issuedSubjects state.blockingIPCContext
        state.execution.core.context.currentSubject resolution.handle.slot
        (state.blockingSavedContext frame registers)
      generalize BlockingIPCContext.receiveOrBlock _ _ _ _ = outcome at subjects ⊢
      have subjects' : outcome.state.ipc.scheduler.lifecycle.issuedSubjects =
          state.lifecycle.issuedSubjects := subjects.trans blocking
      rcases outcome with ⟨next, result⟩
      dsimp only at subjects' ⊢
      repeat' split
      all_goals first
        | exact ResourceHistoryAgrees.refl state
        | exact publishBlockingIPCContext_historyAgrees state next subjects'
        | exact restoreBlockingPeer_historyAgrees state next _ subjects' ‹_›

/-- Composite blocking send keeps every resource history. -/
theorem dispatchBlockingSend_historyAgrees (state : CompositeState) handleWord word0 word1
    (blocking : state.blockingIPC.scheduler.lifecycle.issuedSubjects =
      state.lifecycle.issuedSubjects) :
    ResourceHistoryAgrees state (dispatchBlockingSend state handleWord word0 word1).state := by
  unfold dispatchBlockingSend
  dsimp only
  split
  · exact ResourceHistoryAgrees.refl state
  · next resolution _ =>
      have subjects := BlockingIPCContext.send_issuedSubjects state.blockingIPCContext
        state.execution.core.context.currentSubject resolution.handle.slot { word0, word1 }
      generalize BlockingIPCContext.send _ _ _ _ = outcome at subjects ⊢
      have subjects' : outcome.state.ipc.scheduler.lifecycle.issuedSubjects =
          state.lifecycle.issuedSubjects := subjects.trans blocking
      rcases outcome with ⟨next, result, released⟩
      dsimp only at subjects' ⊢
      repeat' split
      all_goals first
        | exact ResourceHistoryAgrees.refl state
        | exact publishBlockingIPCContext_historyAgrees state next subjects'
        | exact publishReleasedBlockingContext_historyAgrees state next _ _ subjects' ‹_›

/-- Composite blocking cancellation keeps every resource history. -/
theorem dispatchBlockingCancel_historyAgrees (state : CompositeState) subject
    (blocking : state.blockingIPC.scheduler.lifecycle.issuedSubjects =
      state.lifecycle.issuedSubjects) :
    ResourceHistoryAgrees state (dispatchBlockingCancel state subject).state := by
  unfold dispatchBlockingCancel
  dsimp only
  have subjects := BlockingIPCContext.cancel_issuedSubjects state.blockingIPCContext subject
  generalize BlockingIPCContext.cancel _ _ = outcome at subjects ⊢
  have subjects' : outcome.state.ipc.scheduler.lifecycle.issuedSubjects =
      state.lifecycle.issuedSubjects := subjects.trans blocking
  rcases outcome with ⟨next, result, released⟩
  dsimp only at subjects' ⊢
  repeat' split
  all_goals first
    | exact ResourceHistoryAgrees.refl state
    | exact publishReleasedBlockingContext_historyAgrees state next _ _ subjects' ‹_›

/-- The composite deferred-cancellation drain keeps every resource history. -/
theorem drainDeferredCancellation_historyAgrees (state : CompositeState) subject
    (blocking : state.blockingIPC.scheduler.lifecycle.issuedSubjects =
      state.lifecycle.issuedSubjects) :
    ResourceHistoryAgrees state (drainDeferredCancellation state subject).state := by
  unfold drainDeferredCancellation
  dsimp only
  have subjects := BlockingIPCContext.drainDeferred_issuedSubjects state.blockingIPCContext
    state.deferredCancels state.resumable.contexts state.resumable.capacity subject
  generalize BlockingIPCContext.drainDeferred _ _ _ _ _ = outcome at subjects ⊢
  have subjects' : outcome.state.ipc.scheduler.lifecycle.issuedSubjects =
      state.lifecycle.issuedSubjects := subjects.trans blocking
  split
  · exact ResourceHistoryAgrees.refl state
  · exact resourceHistoryAgrees_of rfl rfl rfl subjects' (VirtualHistoryAgrees.refl _)

/-! ## Every authoritative step keeps the resource histories -/

/-- A framed transition that writes none of the projections the resource
conjuncts read keeps every resource history. -/
theorem historyAgrees_of_frames {footprint : CompositeFootprint.Footprint}
    {before after : CompositeState}
    (frames : CompositeState.Frames footprint before after)
    (untouched : ∀ projection, projection ∈ [CompositeFootprint.Projection.issuers,
      .frameBudgets, .scrub, .lifecycle, .virtualMemory] → footprint.writes projection = false) :
    ResourceHistoryAgrees before after := by
  have issuers : after.issuers = before.issuers := frames .issuers (untouched _ (by simp))
  have budgets : after.frameBudgets = before.frameBudgets :=
    frames .frameBudgets (untouched _ (by simp))
  have scrub : after.scrub = before.scrub := frames .scrub (untouched _ (by simp))
  have lifecycle : after.lifecycle = before.lifecycle :=
    frames .lifecycle (untouched _ (by simp))
  have virtual : after.virtualMemory = before.virtualMemory :=
    frames .virtualMemory (untouched _ (by simp))
  exact resourceHistoryAgrees_of issuers budgets scrub (by rw [lifecycle])
    (by rw [virtual]; exact VirtualHistoryAgrees.refl _)

/-- An ordinary operation framed away from the resource conjuncts keeps every
resource history. -/
theorem applyOperation_historyAgrees_of_framed (state : CompositeState) (operation : Operation)
    (framed : (AuthoritativeOperation.ordinary operation).resourceFramed = true) :
    ResourceHistoryAgrees state (applyOperation state operation) := by
  have unread := Operation.footprint_unread_resources operation
  simp only [AuthoritativeOperation.resourceFramed, AuthoritativeOperation.footprint,
    Bool.and_eq_true, Bool.not_eq_true'] at framed
  refine historyAgrees_of_frames (applyOperation_frames state operation) ?_
  intro projection member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact operation.footprint.unread_is_untouched _ unread.1
  · exact operation.footprint.unread_is_untouched _ unread.2.1
  · exact operation.footprint.unread_is_untouched _ unread.2.2
  · exact framed.1
  · exact framed.2

/-- Every ordinary operation except caller-identity creation keeps every
resource history from a coherent state. -/
theorem applyOperation_historyAgrees_of_coherent (state : CompositeState) (operation : Operation)
    (coherent : state.Coherent) (notCreate : ∀ subject, operation ≠ .createSubject subject) :
    ResourceHistoryAgrees state (applyOperation state operation) := by
  have lifecycle := coherent.resumableLifecycle
  have virtual := coherent.resumableVirtual
  have virtualRefl : VirtualHistoryAgrees state.virtualMemory
      state.resumable.translations.virtual := by
    rw [virtual]; exact VirtualHistoryAgrees.refl _
  by_cases keeps : operation.keepsHistory = true
  · exact applyOperation_historyAgrees state operation keeps
  cases operation
  case createSubject subject => exact absurd rfl (notCreate subject)
  case interrupt frame =>
    simp only [applyOperation]
    split
    · split
      · exact publishInterruptCleanup_historyAgrees state _ coherent
      · exact ResourceHistoryAgrees.refl state
    · exact resourceHistoryAgrees_of rfl rfl rfl (by simp [installResumable, lifecycle])
        (by simpa [installResumable] using virtualRefl)
    all_goals exact ResourceHistoryAgrees.refl state
  case nmi | selectUserReturn | userReturn | ipc | scheduleAdd | restart =>
    exact applyOperation_historyAgrees_of_framed state _ (by
      simp only [AuthoritativeOperation.resourceFramed, AuthoritativeOperation.footprint,
        Operation.footprint]; decide)
  case syscall call =>
    simp only [applyOperation]
    have history := Syscall.dispatch_virtualHistory state.virtualMemory state.syscallContext call
    generalize Syscall.dispatch _ _ _ = outcome at history ⊢
    repeat' split
    all_goals first
      | exact ResourceHistoryAgrees.refl state
      | exact selectLiveReturnAuthority_historyAgrees state _
      | exact (installVirtualMemory_historyAgrees state _ _ history).trans
          (selectLiveReturnAuthority_historyAgrees _ _)
  case resumePreempt frame registers =>
    simp only [applyOperation]
    have history := ResumablePreemption.switch_history state.resumable state.execution.core
      frame registers
    generalize ResumablePreemption.switch _ _ _ _ = outcome at history ⊢
    have subjects : outcome.state.scheduler.lifecycle.issuedSubjects =
        state.lifecycle.issuedSubjects := by rw [history.1, lifecycle]
    have virtual' : VirtualHistoryAgrees state.virtualMemory outcome.state.translations.virtual := by
      rw [history.2]; exact virtualRefl
    repeat' split
    all_goals first
      | exact ResourceHistoryAgrees.refl state
      | exact installResumable_historyAgrees state _ subjects virtual'
      | exact resourceHistoryAgrees_of rfl rfl rfl (by simpa [installResumable] using subjects)
          (by simpa [installResumable] using virtual')
  case protect page permissions =>
    simp only [applyOperation]
    have history := TLB.protect_virtualHistory state.resumable.translations
      state.execution.core.context.currentSubject
      state.execution.core.context.activeAddressSpace page permissions
    rw [virtual] at history
    split
    · exact ResourceHistoryAgrees.refl state
    · exact installVirtualMemory_historyAgrees state _ _ history
  case terminateSubject subject =>
    simp only [applyOperation]
    split
    · exact ResourceHistoryAgrees.refl state
    · exact installTerminatedSubject_historyAgrees state subject coherent
  case terminateCurrent =>
    simp only [applyOperation]
    repeat' split
    all_goals first
      | exact ResourceHistoryAgrees.refl state
      | exact installTerminatedSubject_historyAgrees state _ coherent
  case scheduleRemove subject =>
    simp only [applyOperation]
    have history := ResumablePreemption.remove_history state.resumable subject
    generalize ResumablePreemption.remove _ _ = outcome at history ⊢
    split
    · exact ResourceHistoryAgrees.refl state
    · exact resourceHistoryAgrees_of rfl rfl rfl
        (by simp [installSchedulerRemoval, history.1, lifecycle]) (VirtualHistoryAgrees.refl _)
  case scheduleNext =>
    simp only [applyOperation]
    split
    · exact ResourceHistoryAgrees.refl state
    · exact ResourceHistoryAgrees.refl state
    · next selected accepted =>
        exact absurd (schedulerDispatch_accepted_is_none state _ accepted) (by simp)
  case scheduleYield =>
    simp only [applyOperation]
    split
    · exact ResourceHistoryAgrees.refl state
    · next context accepted => exact absurd accepted (schedulerYield_ne_accepted state context)
  case scheduleTick =>
    simp only [applyOperation]
    split
    · exact ResourceHistoryAgrees.refl state
    · next context accepted => exact absurd accepted (schedulerTick_ne_accepted state context)
  all_goals simp [Operation.keepsHistory] at keeps


/-- The ordinary gate either stutters or runs `applyOperation`. -/
theorem gate_stutters_or_applies (state : CompositeState) (operation : Operation) :
    (gate state operation).state = state ∨
      (gate state operation).state = applyOperation state operation := by
  cases operation <;> cases hmode : state.execution.mode <;> simp [gate, hmode]

/-- **Resource histories through the authoritative gate.**  Every
authoritative step other than caller-identity creation keeps the issuers, the
frame commitment, the frame contents, the subject history, both object
histories, the frame allocator, and every object binding. -/
theorem authoritativeGate_historyAgrees (state : CompositeState)
    (operation : AuthoritativeOperation) (holds : AuthoritativeRuntimeWellFormed state)
    (notCreate : ∀ subject, operation ≠ .ordinary (.createSubject subject)) :
    ResourceHistoryAgrees state (authoritativeGate state operation).state := by
  have coherent : state.Coherent := holds.left.1
  have blocking : state.blockingIPC.scheduler.lifecycle.issuedSubjects =
      state.lifecycle.issuedSubjects := by rw [holds.left.blockingLifecycle]
  cases operation with
  | ordinary operation =>
      rw [authoritativeGate_ordinary_state]
      rcases gate_stutters_or_applies state operation with same | applied
      · rw [same]; exact ResourceHistoryAgrees.refl state
      · rw [applied]
        exact applyOperation_historyAgrees_of_coherent state operation coherent
          (fun subject eq => notCreate subject (by rw [eq]))
  | blocking operation =>
      rw [authoritativeGate_blocking_state]
      cases hmode : state.execution.mode <;> simp only [blockingGate, hmode]
      all_goals first
        | exact ResourceHistoryAgrees.refl state
        | cases operation <;> simp only [applyBlockingOperation]
      · exact dispatchBlockingReceive_historyAgrees state _ _ _ blocking
      · exact dispatchBlockingSend_historyAgrees state _ _ _ blocking
      · exact dispatchBlockingCancel_historyAgrees state _ blocking
  | drainDeferred subject =>
      rw [authoritativeGate_drainDeferred_state]
      split
      · exact drainDeferredCancellation_historyAgrees state subject blocking
      · exact ResourceHistoryAgrees.refl state
      · exact ResourceHistoryAgrees.refl state


/-! ## Caller-identity creation -/

/-- Caller-identity creation through the authoritative gate changes no
resource history except that the subject history may gain exactly the
caller's identity. -/
theorem authoritativeGate_createSubject_history (state : CompositeState) (subject : Nat) :
    (authoritativeGate state (.ordinary (.createSubject subject))).state.issuers =
        state.issuers ∧
      (authoritativeGate state (.ordinary (.createSubject subject))).state.frameBudgets =
        state.frameBudgets ∧
      (authoritativeGate state (.ordinary (.createSubject subject))).state.scrub = state.scrub ∧
      VirtualHistoryAgrees state.virtualMemory
        (authoritativeGate state (.ordinary (.createSubject subject))).state.virtualMemory ∧
      ((authoritativeGate state (.ordinary (.createSubject subject))).state.lifecycle.issuedSubjects =
          state.lifecycle.issuedSubjects ∨
        (state.lifecycle.issuedSubjects subject = false ∧
          (authoritativeGate state
              (.ordinary (.createSubject subject))).state.lifecycle.issuedSubjects =
            SubjectLifecycle.setBool state.lifecycle.issuedSubjects subject true)) := by
  rw [authoritativeGate_ordinary_state]
  rcases gate_stutters_or_applies state (.createSubject subject) with same | applied
  · rw [same]; exact ⟨rfl, rfl, rfl, VirtualHistoryAgrees.refl _, Or.inl rfl⟩
  · rw [applied]
    simp only [applyOperation]
    split
    · exact ⟨rfl, rfl, rfl, VirtualHistoryAgrees.refl _, Or.inl rfl⟩
    · next created =>
        obtain ⟨issuedMap, _⟩ :=
          BoundedLifecycle.subject_create_accepted_registry state.lifecycle subject created
        have fresh : state.lifecycle.issuedSubjects subject = false := by
          simp only [SubjectLifecycle.create] at created
          split at created
          · simp [SubjectLifecycle.reject] at created
          · split at created
            · simp [SubjectLifecycle.reject] at created
            · simp_all
        exact ⟨rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, Or.inr ⟨fresh, issuedMap⟩⟩


/-- A transition that keeps every other resource history and adds exactly one
subject identity below the subject counter keeps the resource invariant. -/
theorem resourceWellFormed_of_added_subject {before after : CompositeState} {subject : Nat}
    (issuers : after.issuers = before.issuers)
    (budgets : after.frameBudgets = before.frameBudgets)
    (scrub : after.scrub = before.scrub)
    (virtual : VirtualHistoryAgrees before.virtualMemory after.virtualMemory)
    (subjects : after.lifecycle.issuedSubjects =
      SubjectLifecycle.setBool before.lifecycle.issuedSubjects subject true)
    (bound : 0 < subject ∧ subject < before.issuers.subject.next)
    (holds : ResourceWellFormed before) :
    ResourceWellFormed after := by
  obtain ⟨issued, spaces, allocator, binding⟩ := virtual
  rw [resourceWellFormed_iff] at holds ⊢
  obtain ⟨issuersHold, agreementHold, budgetHold, scrubHold⟩ := holds
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [issuersInvariant, issuers] using issuersHold
  · simp only [issuerAgreementInvariant, CompositeState.lifecycleRuntime,
      BoundedLifecycle.issuedObject, issuers, issued, spaces, subjects] at agreementHold ⊢
    refine ⟨?_, agreementHold.2⟩
    intro candidate issuedNow
    by_cases same : candidate = subject
    · subst same; exact bound
    · simp only [SubjectLifecycle.setBool, same, ↓reduceIte] at issuedNow
      exact agreementHold.1 candidate issuedNow
  · simp only [budgetAgreementInvariant, budgets, allocator, subjects] at budgetHold ⊢
    intro frame owner committed
    obtain ⟨member, unreserved, issuedBefore⟩ := budgetHold frame owner committed
    refine ⟨member, unreserved, ?_⟩
    simp only [SubjectLifecycle.setBool]
    split <;> simp_all
  · simpa [scrubInvariant, CompositeState.scrubState, FrameScrub.ScrubInvariant, scrub,
      allocator, binding] using scrubHold

/-- **Caller-identity creation under the issuer bound.**  Composite
`createSubject k` keeps the resource invariant when `k` is a positive identity
below the subject counter: the issuer then already covers it, and the
creation itself rejects an identity that was ever issued. -/
theorem authoritativeGate_createSubject_preserves_resourceWellFormed (state : CompositeState)
    (subject : Nat) (bound : 0 < subject ∧ subject < state.issuers.subject.next)
    (holds : ResourceWellFormed state) :
    ResourceWellFormed (authoritativeGate state (.ordinary (.createSubject subject))).state := by
  obtain ⟨issuers, budgets, scrub, virtual, subjects⟩ :=
    authoritativeGate_createSubject_history state subject
  rcases subjects with same | ⟨_, added⟩
  · exact resourceWellFormed_of_historyAgrees
      (resourceHistoryAgrees_of issuers budgets scrub same virtual) holds
  · exact resourceWellFormed_of_added_subject issuers budgets scrub virtual added bound holds

/-- **The bound is necessary.**  If caller-identity creation adds its
identity to the history and the issuer agreement holds afterwards, then the
identity was positive and below the subject counter.  An accepted
`createSubject k` with `k` at or above the counter therefore breaks the
issuer agreement. -/
theorem authoritativeGate_createSubject_requires_bound (state : CompositeState) (subject : Nat)
    (created : (authoritativeGate state (.ordinary (.createSubject subject))).state.lifecycle.issuedSubjects
      subject = true)
    (agreement : issuerAgreementInvariant.holds
      (authoritativeGate state (.ordinary (.createSubject subject))).state) :
    0 < subject ∧ subject < state.issuers.subject.next := by
  have := agreement.1 subject created
  rwa [(authoritativeGate_createSubject_history state subject).1] at this


/-! ## Invalidation publication -/

/-- Every invalidation-publication entry point other than the active
current-unmap completion keeps every resource history: it writes only the
publication projection. -/
theorem InvalidationOperation.apply_historyAgrees (state : CompositeState)
    (operation : InvalidationOperation)
    (notCurrentUnmap : ∀ ack, operation ≠ .acknowledgeCurrentUnmap ack) :
    ResourceHistoryAgrees state (operation.apply state).state := by
  refine historyAgrees_of_frames (InvalidationOperation.apply_frames state operation) ?_
  intro projection member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  cases operation
  case acknowledgeCurrentUnmap ack => exact absurd rfl (notCurrentUnmap ack)
  all_goals
    rcases member with rfl | rfl | rfl | rfl | rfl <;>
      simp only [InvalidationOperation.footprint] <;> decide

/-- The pending unmap successor held by the publication protocol keeps the
composite's memory histories.  This is what the active current-unmap
completion needs, because it installs that successor's virtual memory. -/
def PendingHistoryAgrees (state : CompositeState) : Prop :=
  ∀ pending, state.invalidationPublication.pending = some pending →
    pending.kind = .unmap →
    VirtualHistoryAgrees state.virtualMemory pending.step.state.virtual

/-- **Active current-unmap completion.**  Under `PendingHistoryAgrees` the
acknowledgement keeps every resource history: a rejected acknowledgement
stutters, and an accepted one installs a successor whose memory histories
agree with the composite's. -/
theorem authoritativeAcknowledgeCurrentUnmap_historyAgrees (state : CompositeState) ack
    (pendingAgrees : PendingHistoryAgrees state) :
    ResourceHistoryAgrees state (authoritativeAcknowledgeCurrentUnmap state ack).state := by
  by_cases accepted : (authoritativeAcknowledgeUnmap state ack).accepted = true
  · obtain ⟨pending, hpending, hkind, _, _, hpublished, _⟩ :=
      authoritativeAcknowledgeUnmap_accepted_exact state ack accepted
    have virtual : (authoritativeAcknowledgeCurrentUnmap state ack).state.virtualMemory =
        pending.step.state.virtual := by
      rw [← hpublished]
      simp only [authoritativeAcknowledgeCurrentUnmap, accepted, ↓reduceIte]
      rfl
    have agrees := pendingAgrees pending hpending hkind
    rw [← virtual] at agrees
    refine resourceHistoryAgrees_of ?_ ?_ ?_ ?_ agrees <;>
      simp only [authoritativeAcknowledgeCurrentUnmap, accepted, ↓reduceIte] <;> rfl
  · have rejected : (authoritativeAcknowledgeCurrentUnmap state ack).accepted = false := by
      simp [authoritativeAcknowledgeCurrentUnmap, accepted]
    rw [(authoritativeAcknowledgeCurrentUnmap_rejected_inert state ack rejected).1]
    exact ResourceHistoryAgrees.refl state


/-- An unmap step of the publication protocol keeps the memory registry and
the issued address spaces. -/
theorem StaleTranslation.step_unmap_virtualHistory (state : TLB.State) actor addressSpace page :
    VirtualHistoryAgrees state.virtual
      (StaleTranslation.step state (.unmap actor addressSpace page)).state.virtual := by
  simp only [StaleTranslation.step]
  split
  · simp only [TLB.unmap]
    split
    · exact VirtualHistoryAgrees.refl _
    · exact VirtualHistoryAgrees.of_memory (VirtualMapping.unmap_registry ..).1
        (VirtualMapping.unmap_registry ..).2
  · exact VirtualHistoryAgrees.refl _

/-- Preparing the current-root unmap from a state whose publication
projection agrees with the composite records a pending successor whose memory
histories agree with the composite's. -/
theorem authoritativePrepareCurrentUnmap_pendingHistoryAgrees (state : CompositeState) page
    (coherent : state.Coherent) (projection : state.InvalidationProjectionCoherent)
    (prepared : (authoritativePrepareCurrentUnmap state page).accepted = true) :
    PendingHistoryAgrees (authoritativePrepareCurrentUnmap state page).state := by
  have publication : (authoritativePrepareCurrentUnmap state page).state.invalidationPublication =
      (InvalidationPublication.prepare state.invalidationPublication .unmap
        (.unmap state.execution.core.context.currentSubject
          state.execution.core.context.activeAddressSpace page)).state := rfl
  have accepted : (InvalidationPublication.prepare state.invalidationPublication .unmap
      (.unmap state.execution.core.context.currentSubject
        state.execution.core.context.activeAddressSpace page)).accepted = true := prepared
  have virtual : (authoritativePrepareCurrentUnmap state page).state.virtualMemory =
      state.virtualMemory := rfl
  intro pending hpending _
  rw [virtual]
  rw [publication] at hpending
  unfold InvalidationPublication.prepare at hpending accepted
  have published : state.invalidationPublication.published.virtual = state.virtualMemory := by
    rw [projection]; exact coherent.resumableVirtual
  cases hp : state.invalidationPublication.pending with
  | some _ => simp [hp] at accepted
  | none =>
      simp only [hp] at hpending accepted
      split at hpending
      · split at hpending
        · simp only [Option.some.injEq] at hpending
          subst pending
          have := StaleTranslation.step_unmap_virtualHistory
            state.invalidationPublication.published
            state.execution.core.context.currentSubject
            state.execution.core.context.activeAddressSpace page
          rwa [published] at this
        · simp_all
      · simp_all


/-! ## Combined invariant for every step -/

/-- Every invalidation-publication entry point other than the active
current-unmap completion keeps the authoritative runtime invariant. -/
theorem InvalidationOperation.apply_preserves_authoritativeRuntimeWellFormed
    (state : CompositeState) (operation : InvalidationOperation)
    (notCurrentUnmap : ∀ ack, operation ≠ .acknowledgeCurrentUnmap ack)
    (holds : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed (operation.apply state).state := by
  cases operation
  case acknowledgeCurrentUnmap ack => exact absurd rfl (notCurrentUnmap ack)
  all_goals simp only [InvalidationOperation.apply]
  all_goals first
    | exact authoritativePrepareUnmap_preserves_authoritativeRuntimeWellFormed _ _ _ _ holds
    | exact authoritativePrepareCurrentUnmap_preserves_authoritativeRuntimeWellFormed _ _ holds
    | exact authoritativePrepareProtect_preserves_authoritativeRuntimeWellFormed
        _ _ _ _ _ holds
    | exact authoritativePrepareRelease_preserves_authoritativeRuntimeWellFormed _ _ _ holds
    | exact authoritativePrepareDestroy_preserves_authoritativeRuntimeWellFormed _ _ _ holds
    | exact authoritativePrepareSwitch_preserves_authoritativeRuntimeWellFormed _ _ holds
    | exact authoritativeAcknowledgeUnmap_preserves_authoritativeRuntimeWellFormed _ _ holds
    | exact authoritativeAcknowledgeProtect_preserves_authoritativeRuntimeWellFormed _ _ holds
    | exact authoritativeAcknowledgeRelease_preserves_authoritativeRuntimeWellFormed _ _ holds
    | exact authoritativeAcknowledgeDestroy_preserves_authoritativeRuntimeWellFormed _ _ holds
    | exact authoritativeAcknowledgeSwitch_preserves_authoritativeRuntimeWellFormed _ _ holds
    | exact authoritativePublishReuse_preserves_authoritativeRuntimeWellFormed _ holds

/-- **Every authoritative step but caller-identity creation keeps the
combined invariant**, with no premise beyond the invariant itself.  This
covers interrupt cleanup, `syscall`, `resumePreempt`, `protect`, both
terminations, every scheduler step, the blocking operations, and the deferred
drain, together with the steps already covered by the frame rule. -/
theorem authoritativeGate_preserves_resourceRuntimeWellFormed (state : CompositeState)
    (operation : AuthoritativeOperation)
    (notCreate : ∀ subject, operation ≠ .ordinary (.createSubject subject))
    (holds : ResourceRuntimeWellFormed state) :
    ResourceRuntimeWellFormed (authoritativeGate state operation).state :=
  ⟨authoritativeGate_preserves_authoritativeRuntimeWellFormed state operation holds.1,
    resourceWellFormed_of_historyAgrees
      (authoritativeGate_historyAgrees state operation holds.1 notCreate) holds.2⟩

/-- Caller-identity creation keeps the combined invariant under the issuer
bound. -/
theorem authoritativeGate_createSubject_preserves_resourceRuntimeWellFormed
    (state : CompositeState) (subject : Nat)
    (bound : 0 < subject ∧ subject < state.issuers.subject.next)
    (holds : ResourceRuntimeWellFormed state) :
    ResourceRuntimeWellFormed
      (authoritativeGate state (.ordinary (.createSubject subject))).state :=
  ⟨authoritativeGate_preserves_authoritativeRuntimeWellFormed state _ holds.1,
    authoritativeGate_createSubject_preserves_resourceWellFormed state subject bound holds.2⟩

/-- Every invalidation-publication entry point other than the active
current-unmap completion keeps the combined invariant. -/
theorem InvalidationOperation.apply_preserves_resourceRuntimeWellFormed
    (state : CompositeState) (operation : InvalidationOperation)
    (notCurrentUnmap : ∀ ack, operation ≠ .acknowledgeCurrentUnmap ack)
    (holds : ResourceRuntimeWellFormed state) :
    ResourceRuntimeWellFormed (operation.apply state).state :=
  ⟨InvalidationOperation.apply_preserves_authoritativeRuntimeWellFormed state operation
      notCurrentUnmap holds.1,
    resourceWellFormed_of_historyAgrees
      (InvalidationOperation.apply_historyAgrees state operation notCurrentUnmap) holds.2⟩

/-- What the active current-unmap completion needs from the state it runs
in: its pending successor's memory histories agree with the composite's, and
the acknowledgement keeps the authoritative runtime invariant.  The second
conjunct is the existing conditional status of this entry point (see
`CompositeState.InvalidationProjectionCoherent`), not a resource premise. -/
def CurrentUnmapAdmissible (state : CompositeState)
    (ack : InvalidationPublication.Acknowledgement) : Prop :=
  PendingHistoryAgrees state ∧
    AuthoritativeRuntimeWellFormed (authoritativeAcknowledgeCurrentUnmap state ack).state

/-- The active current-unmap completion keeps the combined invariant when it
is admissible. -/
theorem authoritativeAcknowledgeCurrentUnmap_preserves_resourceRuntimeWellFormed
    (state : CompositeState) ack (admissible : CurrentUnmapAdmissible state ack)
    (holds : ResourceRuntimeWellFormed state) :
    ResourceRuntimeWellFormed (authoritativeAcknowledgeCurrentUnmap state ack).state :=
  ⟨admissible.2, resourceWellFormed_of_historyAgrees
    (authoritativeAcknowledgeCurrentUnmap_historyAgrees state ack admissible.1) holds.2⟩

/-- The established prepare-then-acknowledge path for the current root is
admissible: from an authoritative state whose publication projection agrees
with the composite, an accepted current-unmap preparation leaves a state in
which every acknowledgement is admissible. -/
theorem currentUnmapAdmissible_of_prepared (state : CompositeState) page ack
    (holds : AuthoritativeRuntimeWellFormed state)
    (projection : state.InvalidationProjectionCoherent)
    (running : state.execution.mode = .running)
    (prepared : (authoritativePrepareCurrentUnmap state page).accepted = true) :
    CurrentUnmapAdmissible (authoritativePrepareCurrentUnmap state page).state ack := by
  refine ⟨authoritativePrepareCurrentUnmap_pendingHistoryAgrees state page holds.left.1
    projection prepared, ?_⟩
  by_cases acknowledged :
      (authoritativeAcknowledgeCurrentUnmap
        (authoritativePrepareCurrentUnmap state page).state ack).accepted = true
  · exact (authoritativeCurrentUnmap_accepted_publication state page ack holds projection
      running prepared acknowledged).2.2.1
  · have rejected := authoritativeAcknowledgeCurrentUnmap_rejected_inert _ ack
      (by simpa using acknowledged)
    rw [rejected.1]
    exact authoritativePrepareCurrentUnmap_preserves_authoritativeRuntimeWellFormed
      state page holds


/-! ## Every composite step, and whole traces -/

/-- What a step needs from the state it runs in.  Two steps carry a premise:
caller-identity creation needs its identity positive and below the subject
counter, and the active current-unmap completion needs
`CurrentUnmapAdmissible`.  Every other step is admissible everywhere. -/
def CompositeStep.Admissible (state : CompositeState) (step : CompositeStep) : Prop :=
  (∀ subject, step = .authoritative (.ordinary (.createSubject subject)) →
    0 < subject ∧ subject < state.issuers.subject.next) ∧
  (∀ ack, step = .invalidation (.acknowledgeCurrentUnmap ack) →
    CurrentUnmapAdmissible state ack)

/-- The steps admissible in every state: everything except caller-identity
creation and the active current-unmap completion. -/
def CompositeStep.unconditional : CompositeStep → Bool
  | .authoritative (.ordinary (.createSubject _)) => false
  | .invalidation (.acknowledgeCurrentUnmap _) => false
  | _ => true

/-- An unconditional step is admissible in every state. -/
theorem CompositeStep.admissible_of_unconditional (state : CompositeState) (step : CompositeStep)
    (unconditional : step.unconditional = true) : step.Admissible state := by
  refine ⟨fun subject eq => ?_, fun ack eq => ?_⟩ <;> subst eq <;>
    simp [CompositeStep.unconditional] at unconditional

/-- **Every composite step keeps the combined invariant** from any state in
which it is admissible. -/
theorem CompositeStep.admissible_preserves (state : CompositeState) (step : CompositeStep)
    (holds : ResourceRuntimeWellFormed state) (admissible : step.Admissible state) :
    ResourceRuntimeWellFormed (step.apply state) := by
  cases step with
  | lifecycle operation =>
      exact lifecycleGate_preserves_resourceRuntimeWellFormed state operation holds
  | authoritative operation =>
      by_cases create : ∃ subject, operation = .ordinary (.createSubject subject)
      · obtain ⟨subject, rfl⟩ := create
        exact authoritativeGate_createSubject_preserves_resourceRuntimeWellFormed state subject
          (admissible.1 subject rfl) holds
      · exact authoritativeGate_preserves_resourceRuntimeWellFormed state operation
          (fun subject eq => create ⟨subject, eq⟩) holds
  | invalidation operation =>
      by_cases current : ∃ ack, operation = .acknowledgeCurrentUnmap ack
      · obtain ⟨ack, rfl⟩ := current
        exact authoritativeAcknowledgeCurrentUnmap_preserves_resourceRuntimeWellFormed state ack
          (admissible.2 ack rfl) holds
      · exact InvalidationOperation.apply_preserves_resourceRuntimeWellFormed state operation
          (fun ack eq => current ⟨ack, eq⟩) holds

/-- The memory histories and the frame commitment are kept, and the subject
history only grows. -/
def ResourceHistoryGrows (before after : CompositeState) : Prop :=
  after.frameBudgets = before.frameBudgets ∧ after.scrub = before.scrub ∧
    VirtualHistoryAgrees before.virtualMemory after.virtualMemory ∧
    ∀ subject, before.lifecycle.issuedSubjects subject = true →
      after.lifecycle.issuedSubjects subject = true

/-- Agreement is a special case of growth. -/
theorem ResourceHistoryAgrees.grows {before after : CompositeState}
    (agrees : ResourceHistoryAgrees before after) : ResourceHistoryGrows before after := by
  obtain ⟨_, budgets, scrub, subjects, issued, spaces, allocator, binding⟩ := agrees
  exact ⟨budgets, scrub, ⟨issued, spaces, allocator, binding⟩,
    fun subject issuedBefore => by rw [subjects]; exact issuedBefore⟩

/-- Growth composes along consecutive transitions. -/
theorem ResourceHistoryGrows.trans {first second third : CompositeState}
    (left : ResourceHistoryGrows first second) (right : ResourceHistoryGrows second third) :
    ResourceHistoryGrows first third := by
  obtain ⟨b1, s1, ⟨i1, a1, l1, n1⟩, g1⟩ := left
  obtain ⟨b2, s2, ⟨i2, a2, l2, n2⟩, g2⟩ := right
  exact ⟨b2.trans b1, s2.trans s1, ⟨i2.trans i1, a2.trans a1, l2.trans l1, n2.trans n1⟩,
    fun subject issued => g2 subject (g1 subject issued)⟩

/-- Caller-identity creation only grows the subject history. -/
theorem authoritativeGate_createSubject_grows (state : CompositeState) (subject : Nat) :
    ResourceHistoryGrows state
      (authoritativeGate state (.ordinary (.createSubject subject))).state := by
  obtain ⟨_, budgets, scrub, virtual, subjects⟩ :=
    authoritativeGate_createSubject_history state subject
  refine ⟨budgets, scrub, virtual, fun candidate issued => ?_⟩
  rcases subjects with same | ⟨_, added⟩
  · rw [same]; exact issued
  · rw [added]; simp only [SubjectLifecycle.setBool]; split <;> simp_all

/-- Issued creation only grows the subject history. -/
theorem lifecycleGate_grows (state : CompositeState) (operation : LifecycleOperation) :
    ResourceHistoryGrows state (lifecycleGate state operation).state := by
  cases operation
  have same : ResourceHistoryGrows state state :=
    (ResourceHistoryAgrees.refl state).grows
  cases hmode : state.execution.mode <;>
    simp only [lifecycleGate, hmode, LifecycleOperation.apply]
  all_goals try exact same
  cases result : (issueSubject state).result with
  | exhausted => rw [issueSubject_exhausted_unchanged state result]; exact same
  | rejected reason => rw [issueSubject_rejected_unchanged state reason result]; exact same
  | issued identity =>
      obtain ⟨_, _, _, eq⟩ := issueSubject_issued state identity result
      have created := authoritativeGate_createSubject_grows state identity
      rw [authoritativeGate_ordinary_state] at created
      simp only [gate, hmode] at created
      rw [eq]
      exact created

/-- Every admissible step keeps the memory histories and the frame
commitment, and only adds to the subject history. -/
theorem CompositeStep.admissible_grows (state : CompositeState) (step : CompositeStep)
    (holds : ResourceRuntimeWellFormed state) (admissible : step.Admissible state) :
    ResourceHistoryGrows state (step.apply state) := by
  cases step with
  | lifecycle operation => exact lifecycleGate_grows state operation
  | authoritative operation =>
      by_cases create : ∃ subject, operation = .ordinary (.createSubject subject)
      · obtain ⟨subject, rfl⟩ := create
        exact authoritativeGate_createSubject_grows state subject
      · exact (authoritativeGate_historyAgrees state operation holds.1
          (fun subject eq => create ⟨subject, eq⟩)).grows
  | invalidation operation =>
      by_cases current : ∃ ack, operation = .acknowledgeCurrentUnmap ack
      · obtain ⟨ack, rfl⟩ := current
        exact (authoritativeAcknowledgeCurrentUnmap_historyAgrees state ack
          (admissible.2 ack rfl).1).grows
      · exact (InvalidationOperation.apply_historyAgrees state operation
          (fun ack eq => current ⟨ack, eq⟩)).grows

/-- The subject identity a step adds to the issued history, by either
creation path: issued creation, or caller-identity creation. -/
def CompositeStep.created (state : CompositeState) : CompositeStep → Option Nat
  | .lifecycle operation => CompositeStep.issued state (.lifecycle operation)
  | .authoritative (.ordinary (.createSubject subject)) =>
      if state.lifecycle.issuedSubjects subject = false ∧
          (authoritativeGate state
            (.ordinary (.createSubject subject))).state.lifecycle.issuedSubjects subject = true
      then some subject else none
  | _ => none

/-- A created identity was not in the issued history before its step and is
in it afterwards. -/
theorem CompositeStep.created_fresh (state : CompositeState) (step : CompositeStep)
    (identity : Nat) (created : step.created state = some identity) :
    state.lifecycle.issuedSubjects identity = false ∧
      (step.apply state).lifecycle.issuedSubjects identity = true := by
  cases step with
  | lifecycle operation =>
      cases operation
      simp only [CompositeStep.created, CompositeStep.issued] at created
      cases hmode : state.execution.mode <;>
        simp only [lifecycleGate, hmode, LifecycleOperation.apply] at created
      all_goals try simp at created
      cases result : (issueSubject state).result with
      | exhausted => simp [result] at created
      | rejected reason => simp [result] at created
      | issued fresh =>
          simp only [result, Option.some.injEq] at created
          subst created
          obtain ⟨before, _, after, _⟩ := issueSubject_fresh state fresh result
          refine ⟨before, ?_⟩
          simp only [CompositeStep.apply, lifecycleGate, hmode, LifecycleOperation.apply]
          exact after
  | authoritative operation =>
      cases operation with
      | ordinary operation =>
          cases operation
          case createSubject subject =>
            simp only [CompositeStep.created] at created
            split at created
            · next condition =>
                simp only [Option.some.injEq] at created
                subst created
                exact condition
            · simp at created
          all_goals simp [CompositeStep.created] at created
      | blocking _ => simp [CompositeStep.created] at created
      | drainDeferred _ => simp [CompositeStep.created] at created
  | invalidation _ => simp [CompositeStep.created] at created

/-- Every identity created along a trace, by either creation path. -/
def createdAlong (state : CompositeState) : List CompositeStep → List Nat
  | [] => []
  | step :: rest => (step.created state).toList ++ createdAlong (step.apply state) rest

/-- Steps that are each admissible in the state they run in. -/
def AdmissibleAlong : CompositeState → List CompositeStep → Prop
  | _, [] => True
  | state, step :: rest => step.Admissible state ∧ AdmissibleAlong (step.apply state) rest

/-- A trace of unconditional steps is admissible from every state. -/
theorem admissibleAlong_of_unconditional (state : CompositeState) (steps : List CompositeStep)
    (unconditional : ∀ step, step ∈ steps → step.unconditional = true) :
    AdmissibleAlong state steps := by
  induction steps generalizing state with
  | nil => trivial
  | cons step rest ih =>
      exact ⟨step.admissible_of_unconditional state (unconditional step (by simp)),
        ih _ (fun later member => unconditional later (by simp [member]))⟩

/-- Along an admissible trace the combined invariant holds at the end and the
histories only grow. -/
theorem runSteps_admissible (state : CompositeState) (steps : List CompositeStep)
    (holds : ResourceRuntimeWellFormed state) (admissible : AdmissibleAlong state steps) :
    ResourceRuntimeWellFormed (runSteps state steps) ∧
      ResourceHistoryGrows state (runSteps state steps) := by
  induction steps generalizing state with
  | nil => exact ⟨holds, (ResourceHistoryAgrees.refl state).grows⟩
  | cons step rest ih =>
      obtain ⟨now, later⟩ := admissible
      obtain ⟨final, grows⟩ := ih (step.apply state) (step.admissible_preserves state holds now)
        later
      exact ⟨final, (step.admissible_grows state holds now).trans grows⟩

/-- Along an admissible trace no identity is created twice, and each created
identity was outside the starting history and is in the final one. -/
theorem createdAlong_fresh (state : CompositeState) (steps : List CompositeStep)
    (holds : ResourceRuntimeWellFormed state) (admissible : AdmissibleAlong state steps) :
    (createdAlong state steps).Nodup ∧
      ∀ identity, identity ∈ createdAlong state steps →
        state.lifecycle.issuedSubjects identity = false ∧
          (runSteps state steps).lifecycle.issuedSubjects identity = true := by
  induction steps generalizing state with
  | nil => simp [createdAlong]
  | cons step rest ih =>
      obtain ⟨now, later⟩ := admissible
      have next := step.admissible_preserves state holds now
      obtain ⟨nodup, fresh⟩ := ih (step.apply state) next later
      have grows := step.admissible_grows state holds now
      have tail := (runSteps_admissible (step.apply state) rest next later).2
      cases created : step.created state with
      | none =>
          simp only [createdAlong, created, Option.toList_none, List.nil_append, runSteps]
          refine ⟨nodup, fun identity member => ?_⟩
          obtain ⟨before, after⟩ := fresh identity member
          refine ⟨?_, after⟩
          cases h : state.lifecycle.issuedSubjects identity with
          | false => rfl
          | true => rw [grows.2.2.2 identity h] at before; contradiction
      | some identity =>
          obtain ⟨before, after⟩ := step.created_fresh state identity created
          simp only [createdAlong, created, Option.toList_some, List.singleton_append,
            List.nodup_cons, List.mem_cons, runSteps]
          refine ⟨⟨fun member => ?_, nodup⟩, ?_⟩
          · have := (fresh identity member).1
            rw [after] at this; contradiction
          · rintro candidate (rfl | member)
            · exact ⟨before, tail.2.2.2 candidate after⟩
            · obtain ⟨laterBefore, laterAfter⟩ := fresh candidate member
              refine ⟨?_, laterAfter⟩
              cases h : state.lifecycle.issuedSubjects candidate with
              | false => rfl
              | true => rw [grows.2.2.2 candidate h] at laterBefore; contradiction


/-! ## Budgets, termination, and whole traces -/

/-- A history-growing step keeps every subject's frame usage and limit. -/
theorem ResourceHistoryGrows.budget {before after : CompositeState}
    (grows : ResourceHistoryGrows before after) (subject : Capability.SubjectId) :
    after.budgetUsage subject = before.budgetUsage subject ∧
      after.budgetLimit subject = before.budgetLimit subject :=
  budget_eq_of_allocator grows.1 grows.2.2.1.2.2.1 subject

/-- **Exact budget accounting for every authoritative step.**  No
authoritative step, termination included, changes any subject's frame usage
or limit: none of them writes the frame commitment or the composite
allocator.  Caller-identity creation is included. -/
theorem authoritativeGate_budget_exact (state : CompositeState)
    (operation : AuthoritativeOperation) (holds : AuthoritativeRuntimeWellFormed state)
    (subject : Capability.SubjectId) :
    (authoritativeGate state operation).state.budgetUsage subject = state.budgetUsage subject ∧
      (authoritativeGate state operation).state.budgetLimit subject =
        state.budgetLimit subject := by
  by_cases create : ∃ identity, operation = .ordinary (.createSubject identity)
  · obtain ⟨identity, rfl⟩ := create
    exact (authoritativeGate_createSubject_grows state identity).budget subject
  · exact (authoritativeGate_historyAgrees state operation holds
      (fun identity eq => create ⟨identity, eq⟩)).grows.budget subject

/-- **Termination accounts for identities and budgets.**  Explicit
termination, termination of the current subject, and contained interrupt
cleanup keep both issuers and the whole subject history, so a terminated
identity stays issued and stays below the subject counter and can never be
issued again; and they keep every subject's frame usage and limit. -/
theorem authoritativeGate_termination_accounts (state : CompositeState)
    (operation : AuthoritativeOperation)
    (termination : (∃ subject, operation = .ordinary (.terminateSubject subject)) ∨
      operation = .ordinary .terminateCurrent ∨
      ∃ frame, operation = .ordinary (.interrupt frame))
    (holds : ResourceRuntimeWellFormed state) :
    (authoritativeGate state operation).state.issuers = state.issuers ∧
      (authoritativeGate state operation).state.lifecycle.issuedSubjects =
        state.lifecycle.issuedSubjects ∧
      (∀ subject, state.lifecycle.issuedSubjects subject = true →
        subject < (authoritativeGate state operation).state.issuers.subject.next) ∧
      ∀ subject,
        (authoritativeGate state operation).state.budgetUsage subject =
            state.budgetUsage subject ∧
          (authoritativeGate state operation).state.budgetLimit subject =
            state.budgetLimit subject := by
  have notCreate : ∀ subject, operation ≠ .ordinary (.createSubject subject) := by
    intro subject eq
    subst eq
    rcases termination with ⟨_, h⟩ | h | ⟨_, h⟩ <;> cases h
  have agrees := authoritativeGate_historyAgrees state operation holds.1 notCreate
  have agreement := ((resourceWellFormed_iff state).1 holds.2).2.1
  refine ⟨agrees.1, agrees.2.2.2.1, fun subject issued => ?_,
    fun subject => agrees.grows.budget subject⟩
  rw [agrees.1]
  exact ((agreement.1 subject issued).2 : subject < state.issuers.subject.next)

/-- **The resource invariants along every composite trace.**  Along every
trace of issued creations, authoritative operations, and invalidation entry
points, each admissible in the state it runs in, starting from a state that
satisfies the combined invariant:

- the combined invariant holds at the end;
- no subject identity is created twice, by either creation path, and none
  that was ever issued before the trace is created again;
- the identities drawn from the issuer strictly increase;
- the issued subject history only grows, so a terminated identity stays
  issued;
- every subject's frame usage and limit are exactly unchanged, and usage is
  within the limit at the end. -/
theorem composite_resource_trace (state : CompositeState) (steps : List CompositeStep)
    (holds : ResourceRuntimeWellFormed state) (admissible : AdmissibleAlong state steps) :
    ResourceRuntimeWellFormed (runSteps state steps) ∧
      (createdAlong state steps).Nodup ∧
      (∀ identity, identity ∈ createdAlong state steps →
        state.lifecycle.issuedSubjects identity = false) ∧
      (issuedAlong state steps).Pairwise (· < ·) ∧
      (∀ subject, state.lifecycle.issuedSubjects subject = true →
        (runSteps state steps).lifecycle.issuedSubjects subject = true) ∧
      (∀ subject,
        (runSteps state steps).budgetUsage subject = state.budgetUsage subject ∧
          (runSteps state steps).budgetLimit subject = state.budgetLimit subject) ∧
      ∀ subject,
        (runSteps state steps).budgetUsage subject ≤ (runSteps state steps).budgetLimit subject := by
  obtain ⟨final, grows⟩ := runSteps_admissible state steps holds admissible
  obtain ⟨nodup, fresh⟩ := createdAlong_fresh state steps holds admissible
  exact ⟨final, nodup, fun identity member => (fresh identity member).1,
    (issuedAlong_strictly_increasing state steps).1, grows.2.2.2,
    fun subject => grows.budget subject,
    fun subject => (budget_conservation (runSteps state steps)).1 subject⟩

/-- **A terminated identity is never created again.**  Along every admissible
trace, a subject identity that is already in the issued history (for example,
one that has been terminated) is neither drawn from the issuer nor created by
caller identity. -/
theorem issued_never_recreated (state : CompositeState) (steps : List CompositeStep)
    (holds : ResourceRuntimeWellFormed state) (admissible : AdmissibleAlong state steps)
    (subject : Nat) (issued : state.lifecycle.issuedSubjects subject = true) :
    subject ∉ createdAlong state steps ∧ subject ∉ issuedAlong state steps := by
  refine ⟨fun member => ?_, fun member => ?_⟩
  · have := (createdAlong_fresh state steps holds admissible).2 subject member
    rw [issued] at this; exact absurd this.1 (by decide)
  · have agreement := ((resourceWellFormed_iff state).1 holds.2).2.1
    have below : subject < state.issuers.subject.next := (agreement.1 subject issued).2
    have above : state.issuers.subject.next ≤ subject :=
      ((issuedAlong_strictly_increasing state steps).2 subject member).2.1
    omega

/-- Along a trace that never uses caller-identity creation or the active
current-unmap completion, every conclusion of `composite_resource_trace`
holds with no premise beyond the starting invariant. -/
theorem composite_resource_trace_unconditional (state : CompositeState)
    (steps : List CompositeStep) (holds : ResourceRuntimeWellFormed state)
    (unconditional : ∀ step, step ∈ steps → step.unconditional = true) :
    ResourceRuntimeWellFormed (runSteps state steps) ∧
      (createdAlong state steps).Nodup ∧
      ∀ subject,
        (runSteps state steps).budgetUsage subject = state.budgetUsage subject ∧
          (runSteps state steps).budgetLimit subject = state.budgetLimit subject := by
  obtain ⟨final, nodup, _, _, _, budget, _⟩ :=
    composite_resource_trace state steps holds
      (admissibleAlong_of_unconditional state steps unconditional)
  exact ⟨final, nodup, budget⟩

end LeanOS.FailStop
