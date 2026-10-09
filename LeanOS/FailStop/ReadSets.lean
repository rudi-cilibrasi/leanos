import LeanOS.FailStop.AuthoritativeGate

/-!
# Fail-stop composite: machine-checked read sets

The frame rule (`applyOperation_frames` and its gate forms) checks declared
*write* sets.  This module checks declared *read* sets: two composite states
that agree on an operation's declared reads produce the same reply and
post-states that agree on its declared writes (`applyOperation_reads`,
`operationReply_reads`, `gate_reads`, and the blocking, deferred-drain, and
authoritative forms).  With the frame rule, the declared footprint therefore
determines the whole post-state: written projections are a function of the
read projections, and every other projection is unchanged.

Each proof destructures both states and identifies every field covered by the
agreement hypothesis (`agree_subst`).  Every branch condition over agreed
projections is then syntactically shared, so one `split` decides it for both
states and each branch closes by unfolding.  A read missing from a declared
footprint makes some branch condition or written value mention a field that
the two states do not share, and the proof fails.

Three helpers are rewritten into forms over projections before splitting:
return-plan liveness (`returnPlanLiveOf`), the live return-authority
selection (`selectLiveExecution`), and the live-plan guard of user return
(`liveReturnExecution`).  Helpers whose result carries a whole composite state
(`dispatchIPC`, `restoreBlockingPeer`, `publishReleasedBlockingContext`) get
their own read lemmas.
-/
namespace LeanOS.FailStop

open LeanOS
open LeanOS.CompositeFootprint (Projection Footprint)

/-! ## Projection-level forms of state-wide helpers -/

/-- Return-plan liveness as a function of the two projections it reads. -/
def returnPlanLiveOf (execution : State) (virtualMemory : VirtualMapping.State) : Bool :=
  match execution.returnPlan,
      execution.returnAddressSpace execution.core.context.activeAddressSpace with
  | some plan, some view =>
      view.liveBound execution.core.context.activeAddressSpace plan virtualMemory
  | _, _ => false

theorem CompositeState.returnPlanLive_eq (state : CompositeState) :
    state.ReturnPlanLive = returnPlanLiveOf state.execution state.virtualMemory := rfl

/-- The execution projection selected by `selectLiveReturnAuthority`, as a
function of the two projections it reads. -/
def selectLiveExecution (execution : State) (virtualMemory : VirtualMapping.State)
    (purpose : Interrupt.ReturnPurpose) : State :=
  if returnPlanLiveOf execution virtualMemory then selectReturnAuthority execution purpose
  else { execution with returnAuthorityArmed := false }

/-- Live return-authority selection writes only the execution projection,
computed from the execution and virtual-memory projections. -/
theorem selectLiveReturnAuthority_eq_selectLiveExecution state purpose :
    selectLiveReturnAuthority state purpose =
      { state with execution :=
          selectLiveExecution state.execution state.virtualMemory purpose } := by
  unfold selectLiveReturnAuthority selectLiveExecution
  split <;> simp_all [CompositeState.returnPlanLive_eq]

/-- The execution projection that `completeUserReturn` consumes after the
live-plan guard. -/
def liveReturnExecution (execution : State) (virtualMemory : VirtualMapping.State) : State :=
  if returnPlanLiveOf execution virtualMemory then execution
  else { execution with returnAuthorityArmed := false }

theorem liveReturnExecution_fold (state : CompositeState) :
    (if state.ReturnPlanLive = true then state.execution
      else { state.execution with returnAuthorityArmed := false }) =
      liveReturnExecution state.execution state.virtualMemory := rfl

/-- Close a written-projection agreement goal whose two sides unfold to the
same value. -/
macro "agree_close" : tactic => `(tactic| (
  intro projection written
  cases projection <;> first | exact absurd written Bool.false_ne_true | rfl))

/-! ## Ordinary operations -/

/-- The data-only IPC dispatcher reads only the execution latch, the IPC
state, and the sealed-transfer store: two states that agree there produce the
same reply and agree on both written projections. -/
theorem dispatchIPC_reads (left right : CompositeState) (call : IPCSyscall.Call)
    (agree : CompositeState.AgreeOn
      (Footprint.ofLists [.execution] [.ipc, .transfers]).reads left right) :
    (dispatchIPC left call).reply = (dispatchIPC right call).reply ∧
      CompositeState.AgreeOn (Footprint.ofLists [.execution] [.ipc, .transfers]).writes
        (dispatchIPC left call).state (dispatchIPC right call).state := by
  cases left; cases right
  agree_subst agree
  clear agree
  cases call
  all_goals
    constructor
    · dsimp only [dispatchIPC, CompositeState.ipcContext]
      repeat' split
      all_goals rfl
    · intro projection written
      cases projection <;> (try exact absurd written Bool.false_ne_true)
      all_goals
        dsimp only [dispatchIPC, CompositeState.ipcContext, CompositeState.project]
        repeat' split
        all_goals rfl

/-- **Read independence.**  Two states that agree on an operation's declared
reads produce post-states that agree on its declared writes.  This checks every
`Operation.footprint` read set. -/
theorem applyOperation_reads (left right : CompositeState) (operation : Operation)
    (agree : CompositeState.AgreeOn operation.footprint.reads left right) :
    CompositeState.AgreeOn operation.footprint.writes
      (applyOperation left operation) (applyOperation right operation) := by
  cases operation
  case ipc call =>
    obtain ⟨reply, state⟩ := dispatchIPC_reads left right call agree
    intro projection written
    simp only [applyOperation]
    rw [reply]
    split
    all_goals first
      | exact state projection written
      | exact agree projection (Footprint.writesAreRead _ projection written)
  all_goals
    cases left; cases right
    agree_subst agree
    clear agree
    intro projection written
    cases projection <;> (try exact absurd written Bool.false_ne_true)
  all_goals
    simp only [applyOperation, ↓liveReturnExecution_fold,
      selectLiveReturnAuthority_eq_selectLiveExecution]
    dsimp only [CompositeState.syscallContext, schedulerAdmission, schedulerDispatch,
      schedulerYield, schedulerTick, CompositeState.returnPlanLive_eq, CompositeState.project]
    repeat' split
    all_goals rfl

/-- The typed reply of an operation depends only on its declared reads. -/
theorem operationReply_reads (left right : CompositeState) (operation : Operation)
    (agree : CompositeState.AgreeOn operation.footprint.reads left right) :
    operationReply left operation = operationReply right operation := by
  cases operation
  case ipc call =>
    simp only [operationReply, (dispatchIPC_reads left right call agree).1]
  all_goals
    cases left; cases right
    agree_subst agree
    clear agree
    simp only [operationReply, ↓liveReturnExecution_fold,
      selectLiveReturnAuthority_eq_selectLiveExecution]
    all_goals
      dsimp only [CompositeState.syscallContext, schedulerAdmission, schedulerDispatch,
        schedulerYield, schedulerTick, CompositeState.returnPlanLive_eq]
      repeat' split
      all_goals rfl

/-- **Gate read independence.**  The ordinary gate additionally reads the
execution mode of its latch.  States that agree on an operation's declared
reads and on that mode produce the same gate result and post-states that agree
on its declared writes, on accepted, busy, and halted outcomes alike. -/
theorem gate_reads (left right : CompositeState) (operation : Operation)
    (agree : CompositeState.AgreeOn operation.footprint.reads left right)
    (mode : left.execution.mode = right.execution.mode) :
    (gate left operation).result = (gate right operation).result ∧
      CompositeState.AgreeOn operation.footprint.writes
        (gate left operation).state (gate right operation).state := by
  have reply := operationReply_reads left right operation agree
  have apply := applyOperation_reads left right operation agree
  unfold gate
  rw [mode]
  repeat' split
  all_goals first
    | exact ⟨rfl, agree.writes_of_reads⟩
    | exact ⟨by rw [reply], apply⟩

/-! ## Blocking operations and the deferred drain -/

/-- The projections written by a blocking publication, as one value. -/
def blockingView (state : CompositeState) :=
  (state.execution, state.scheduler, state.preemption, state.lifecycle, state.resumable,
    state.blockingIPC, state.blockingContexts)

theorem agreeOn_blockingWrites_of_view {left right : CompositeState}
    (same : blockingView left = blockingView right) :
    CompositeState.AgreeOn (Footprint.ofLists [] blockingProjections).writes left right := by
  simp only [blockingView, Prod.mk.injEq] at same
  obtain ⟨_, _, _, _, _, _, _⟩ := same
  intro projection written
  cases projection <;> first
    | exact absurd written Bool.false_ne_true
    | (simp only [CompositeState.project]; assumption)

/-- Two fallible publications related by `blockingView`: they fail with the
same error or both succeed with states that agree on the blocking writes. -/
structure BlockingViewRelated (left right : β → Except ε CompositeState) : Prop where
  errorOk : ∀ input error next, left input = .error error → right input = .ok next → False
  okError : ∀ input next error, left input = .ok next → right input = .error error → False
  errorError : ∀ input error error', left input = .error error →
    right input = .error error' → error = error'
  okOk : ∀ input next next', left input = .ok next → right input = .ok next' →
    blockingView next = blockingView next'

theorem BlockingViewRelated.of_map {left right : β → Except ε CompositeState}
    (same : ∀ input, (left input).map blockingView = (right input).map blockingView) :
    BlockingViewRelated left right where
  errorOk input error next hleft hright := by
    have h := same input
    rw [hleft, hright] at h
    cases h
  okError input next error hleft hright := by
    have h := same input
    rw [hleft, hright] at h
    cases h
  errorError input error error' hleft hright := by
    have h := same input
    rw [hleft, hright] at h
    simp only [Except.map] at h
    injection h
  okOk input next next' hleft hright := by
    have h := same input
    rw [hleft, hright] at h
    simp only [Except.map] at h
    injection h

theorem restoreBlockingPeer_reads (left right : CompositeState) blocking
    (agree : CompositeState.AgreeOn (Footprint.ofLists [] blockingProjections).reads left right) :
    (restoreBlockingPeer left blocking).map blockingView =
      (restoreBlockingPeer right blocking).map blockingView := by
  cases left; cases right
  agree_subst agree
  clear agree
  unfold restoreBlockingPeer
  dsimp only [publishBlockingIPCContext]
  repeat' split
  all_goals rfl

theorem publishReleasedBlockingContext_reads (left right : CompositeState) blocking saved
    (agree : CompositeState.AgreeOn (Footprint.ofLists [] blockingProjections).reads left right) :
    (publishReleasedBlockingContext left blocking saved).map blockingView =
      (publishReleasedBlockingContext right blocking saved).map blockingView := by
  cases left; cases right
  agree_subst agree
  clear agree
  unfold publishReleasedBlockingContext
  dsimp only [publishBlockingIPCContext]
  repeat' split
  all_goals rfl

/-- Close one branch of a blocking dispatcher: equal stutters or
publications, or a pair of related fallible publications. -/
macro "blocking_close" related:term : tactic => `(tactic| first
  | (refine ⟨rfl, ?_⟩; agree_close)
  | exact absurd (($related).errorOk _ _ _ ‹_› ‹_›) id
  | exact absurd (($related).okError _ _ _ ‹_› ‹_›) id
  | exact ⟨rfl, agreeOn_blockingWrites_of_view (($related).okOk _ _ _ ‹_› ‹_›)⟩
  | (have same := ($related).errorError _ _ _ ‹_› ‹_›
     subst same
     refine ⟨rfl, ?_⟩
     agree_close))

theorem dispatchBlockingReceive_reads (left right : CompositeState) handleWord frame registers
    (agree : CompositeState.AgreeOn (Footprint.ofLists [] blockingProjections).reads left right) :
    (dispatchBlockingReceive left handleWord frame registers).reply =
        (dispatchBlockingReceive right handleWord frame registers).reply ∧
      CompositeState.AgreeOn (Footprint.ofLists [] blockingProjections).writes
        (dispatchBlockingReceive left handleWord frame registers).state
        (dispatchBlockingReceive right handleWord frame registers).state := by
  have related := BlockingViewRelated.of_map fun blocking =>
    restoreBlockingPeer_reads left right blocking agree
  unfold dispatchBlockingReceive
  generalize restoreBlockingPeer left = restoreLeft at related ⊢
  generalize restoreBlockingPeer right = restoreRight at related ⊢
  cases left; cases right
  agree_subst agree
  clear agree
  dsimp only [CompositeState.blockingIPCContext, CompositeState.blockingSavedContext]
  repeat' split
  all_goals blocking_close related

theorem dispatchBlockingSend_reads (left right : CompositeState) handleWord word0 word1
    (agree : CompositeState.AgreeOn (Footprint.ofLists [] blockingProjections).reads left right) :
    (dispatchBlockingSend left handleWord word0 word1).reply =
        (dispatchBlockingSend right handleWord word0 word1).reply ∧
      CompositeState.AgreeOn (Footprint.ofLists [] blockingProjections).writes
        (dispatchBlockingSend left handleWord word0 word1).state
        (dispatchBlockingSend right handleWord word0 word1).state := by
  have related := fun blocking => BlockingViewRelated.of_map fun saved =>
    publishReleasedBlockingContext_reads left right blocking saved agree
  unfold dispatchBlockingSend
  generalize publishReleasedBlockingContext left = releaseLeft at related ⊢
  generalize publishReleasedBlockingContext right = releaseRight at related ⊢
  cases left; cases right
  agree_subst agree
  clear agree
  dsimp only [CompositeState.blockingIPCContext]
  repeat' split
  all_goals blocking_close (related _)

theorem dispatchBlockingCancel_reads (left right : CompositeState) subject
    (agree : CompositeState.AgreeOn (Footprint.ofLists [] blockingProjections).reads left right) :
    (dispatchBlockingCancel left subject).reply = (dispatchBlockingCancel right subject).reply ∧
      CompositeState.AgreeOn (Footprint.ofLists [] blockingProjections).writes
        (dispatchBlockingCancel left subject).state (dispatchBlockingCancel right subject).state := by
  have related := fun blocking => BlockingViewRelated.of_map fun saved =>
    publishReleasedBlockingContext_reads left right blocking saved agree
  unfold dispatchBlockingCancel
  generalize publishReleasedBlockingContext left = releaseLeft at related ⊢
  generalize publishReleasedBlockingContext right = releaseRight at related ⊢
  cases left; cases right
  agree_subst agree
  clear agree
  dsimp only [CompositeState.blockingIPCContext]
  repeat' split
  all_goals blocking_close (related _)

/-- **Blocking read independence.**  Every blocking operation's reply and
written projections depend only on its declared reads. -/
theorem applyBlockingOperation_reads (left right : CompositeState)
    (operation : CompositeBlockingOperation)
    (agree : CompositeState.AgreeOn operation.footprint.reads left right) :
    blockingOperationReply left operation = blockingOperationReply right operation ∧
      CompositeState.AgreeOn operation.footprint.writes
        (applyBlockingOperation left operation) (applyBlockingOperation right operation) := by
  cases operation with
  | receive handleWord frame registers =>
      obtain ⟨reply, state⟩ :=
        dispatchBlockingReceive_reads left right handleWord frame registers agree
      exact ⟨by simp only [blockingOperationReply, reply], state⟩
  | send handleWord word0 word1 =>
      obtain ⟨reply, state⟩ := dispatchBlockingSend_reads left right handleWord word0 word1 agree
      exact ⟨by simp only [blockingOperationReply, reply], state⟩
  | cancel subject =>
      obtain ⟨reply, state⟩ := dispatchBlockingCancel_reads left right subject agree
      exact ⟨by simp only [blockingOperationReply, reply], state⟩

/-- The blocking gate reads the latch mode in addition to the declared
reads. -/
theorem blockingGate_reads (left right : CompositeState) (operation : CompositeBlockingOperation)
    (agree : CompositeState.AgreeOn operation.footprint.reads left right)
    (mode : left.execution.mode = right.execution.mode) :
    (blockingGate left operation).result = (blockingGate right operation).result ∧
      CompositeState.AgreeOn operation.footprint.writes
        (blockingGate left operation).state (blockingGate right operation).state := by
  obtain ⟨reply, apply⟩ := applyBlockingOperation_reads left right operation agree
  unfold blockingGate
  rw [mode]
  split
  all_goals first
    | exact ⟨rfl, agree.writes_of_reads⟩
    | exact ⟨by rw [reply], apply⟩

/-- The deferred-cancellation drain reads only its declared projections. -/
theorem drainDeferredCancellation_reads (left right : CompositeState) subject
    (agree : CompositeState.AgreeOn (Footprint.ofLists [] drainProjections).reads left right) :
    (drainDeferredCancellation left subject).result =
        (drainDeferredCancellation right subject).result ∧
      CompositeState.AgreeOn (Footprint.ofLists [] drainProjections).writes
        (drainDeferredCancellation left subject).state
        (drainDeferredCancellation right subject).state := by
  cases left; cases right
  agree_subst agree
  clear agree
  unfold drainDeferredCancellation
  dsimp only [CompositeState.blockingIPCContext, publishDeferredDrain,
    publishBlockingIPCContext]
  split
  all_goals
    refine ⟨rfl, ?_⟩
    agree_close

/-! ## The authoritative gate -/

/-- **Authoritative read independence.**  Every authoritative constructor's
reply and written projections depend only on its declared reads. -/
theorem applyAuthoritativeOperation_reads (left right : CompositeState)
    (operation : AuthoritativeOperation)
    (agree : CompositeState.AgreeOn operation.footprint.reads left right) :
    authoritativeOperationReply left operation = authoritativeOperationReply right operation ∧
      CompositeState.AgreeOn operation.footprint.writes
        (applyAuthoritativeOperation left operation)
        (applyAuthoritativeOperation right operation) := by
  cases operation with
  | ordinary operation =>
      exact ⟨by simp only [authoritativeOperationReply,
          operationReply_reads left right operation agree],
        applyOperation_reads left right operation agree⟩
  | blocking operation =>
      obtain ⟨reply, state⟩ := applyBlockingOperation_reads left right operation agree
      exact ⟨by simp only [authoritativeOperationReply, reply], state⟩
  | drainDeferred subject =>
      obtain ⟨result, state⟩ := drainDeferredCancellation_reads left right subject agree
      exact ⟨by simp only [authoritativeOperationReply, result], state⟩

/-- The authoritative gate reads the latch mode in addition to the declared
reads; its result and written projections depend on nothing else. -/
theorem authoritativeGate_reads (left right : CompositeState)
    (operation : AuthoritativeOperation)
    (agree : CompositeState.AgreeOn operation.footprint.reads left right)
    (mode : left.execution.mode = right.execution.mode) :
    (authoritativeGate left operation).result = (authoritativeGate right operation).result ∧
      CompositeState.AgreeOn operation.footprint.writes
        (authoritativeGate left operation).state (authoritativeGate right operation).state := by
  obtain ⟨reply, apply⟩ := applyAuthoritativeOperation_reads left right operation agree
  unfold authoritativeGate
  rw [mode]
  repeat' split
  all_goals first
    | exact ⟨rfl, agree.writes_of_reads⟩
    | exact ⟨by rw [reply], apply⟩
    | (simp only [authoritativeOperationReply, applyAuthoritativeOperation] at reply apply
       exact ⟨by rw [reply], apply⟩)

end LeanOS.FailStop
