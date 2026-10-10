import LeanOS.CompositeChannels

/-!
# Composite unwinding: channels that need another subject to run

The pairs of `LeanOS.CompositeChannels` are built from the observer's own
operations.  The channels below need subject 1 to act, so their pairs switch
to it and back with the authoritative timer switch (`resumePreempt`), exactly
as the hosted dispatcher traces do.  The traces are evaluated by the kernel on
the canonical sample boot plan (`BootPageTablePlan.sampleInput`), the plan
the hosted dispatcher replays from.

**The pair.**  Both runs start from the dispatcher seed.  Subject 2 (the
observer) copies its endpoint into its own slot 3 (identity 6).  Then:

* left: subject 2 delegates identity 6 to subject 1's slot 2 (identity 7);
  after the switch, subject 1 offers identity 7 on endpoint 10 (sealed
  identity 8, parent 7);
* right: after the switch, subject 1 copies its own endpoint root (identity 2)
  into its slot 2 (identity 7) and offers it the same way.

Both switch back to subject 2.  The observer sees the same row, the same
sealed transfer (identity 8, parent 7, sender 1) on its endpoint, and the same
counter.  Only the hidden derivation of identity 7 differs.

**Channels.**

* `revokeSubtree_own_step_inconsistent`: revoking the subtree of the
  observer's own slot 3 cancels the pending offer exactly when identity 7
  descends from identity 6.
* `revokeSubtree_other_step_inconsistent`: revoking the subtree of subject
  1's root (slot 1, identity 2) cancels it exactly when identity 7 descends
  from identity 2.
* `resumePreempt_output_inconsistent`: the reply of the observer's timer
  switch carries the restored context of the next subject, whose registers
  are outside the view.
-/
namespace LeanOS.CompositeSwitchedChannels

open LeanOS
open LeanOS.FailStop
open LeanOS.CompositeObservation
open LeanOS.CompositeUnwinding
open LeanOS.CompositeOwnSteps
open LeanOS.CompositeChannels
set_option linter.unusedSimpArgs false

/-- One authoritative timer switch away from the scheduled subject, saving the
given outgoing registers. -/
def switchOp (registers : ResumablePreemption.Registers) : AuthoritativeOperation :=
  .ordinary (.resumePreempt compositeDispatcherTimerFrame registers)

/-- Subject 1's handle words for its endpoint root (slot 1, generation 2) and
its slot-2 capability (generation 7). -/
def subjectOneEndpointWord : UInt64 := 131073
def subjectOneSlotTwoWord : UInt64 := 458754

def subjectOneOffer : AuthoritativeOperation :=
  .ordinary (.transferOffer subjectOneEndpointWord subjectOneSlotTwoWord .endpoint
    { word0 := 0, word1 := 0 } { send := true })

def leftTrace : List AuthoritativeOperation :=
  [.ordinary (.capabilityCopy 0 2 3 { send := true, grant := true }),
   .ordinary (.capabilityCopy 3 1 2 { send := true, grant := true }),
   switchOp compositeDispatcherBlockingRegisters,
   subjectOneOffer,
   switchOp compositeDispatcherTimerRegisters]

def rightTrace : List AuthoritativeOperation :=
  [.ordinary (.capabilityCopy 0 2 3 { send := true, grant := true }),
   switchOp compositeDispatcherBlockingRegisters,
   .ordinary (.capabilityCopy 1 1 2 { send := true, grant := true }),
   subjectOneOffer,
   switchOp compositeDispatcherTimerRegisters]

/-- Two runs that switch to subject 1 and back, saving different registers for
it. -/
def preemptLeftTrace : List AuthoritativeOperation :=
  [switchOp compositeDispatcherBlockingRegisters, switchOp compositeDispatcherTimerRegisters]

def preemptRightTrace : List AuthoritativeOperation :=
  [switchOp compositeDispatcherBlockingRegisters, switchOp compositeDispatcherBlockingRegisters]

/-- Subject 2 gives subject 1 a receive-only endpoint capability (slot 2,
generation 6); after the switch, subject 1 blocks on endpoint 10, saving the
given registers, and the kernel restores subject 2. -/
def blockedTrace (registers : ResumablePreemption.Registers) : List AuthoritativeOperation :=
  [.ordinary (.capabilityCopy 0 1 2 { receive := true }),
   switchOp compositeDispatcherTimerRegisters,
   .blocking (.receive 393218 compositeDispatcherBlockingFrame registers)]

def blockedLeftTrace : List AuthoritativeOperation :=
  blockedTrace compositeDispatcherBlockingRegisters

def blockedRightTrace : List AuthoritativeOperation :=
  blockedTrace compositeDispatcherTimerRegisters

/-- Subject 2's blocking send on endpoint 10, and its cancellation of subject
1's wait. -/
def blockingSend : AuthoritativeOperation := .blocking (.send endpointWord 5 6)
def blockingCancel : AuthoritativeOperation := .blocking (.cancel 1)

def runFrom (plan : BootPageTablePlan.Plan) (trace : List AuthoritativeOperation) :
    CompositeState :=
  runAuthoritativeOperations (seed plan) trace

def ownSubtree : Operation := .capabilityRevokeSubtree 0 2 3
def otherSubtree : Operation := .capabilityRevokeSubtree 0 1 1
def preempt : Operation := .resumePreempt compositeDispatcherTimerFrame
  compositeDispatcherTimerRegisters

/-- The decidable part of the observer's view: everything but the owned-space
predicate and mappings, which are functions. -/
def viewData (observer : Nat) (state : CompositeState) :
    Option Nat × Bool × Nat × List (Option Capability.Capability) ×
      List (Option ObjectView) × Option Nat × Option BlockingIPC.Completion :=
  let view := observe observer state
  (view.scheduled, view.live, view.capacity, view.row, view.named, view.waitingOn,
    view.completion)

/-- The premises of `OwnStepCounter` that are decided by evaluation. -/
def pairFacts (left right : CompositeState) : Bool :=
  left.lifecycle.current == some 2 && right.lifecycle.current == some 2 &&
    (match left.execution.mode, right.execution.mode with
      | .running, .running => true
      | _, _ => false) &&
    left.capabilities.nextIdentity == right.capabilities.nextIdentity &&
    viewData 2 left == viewData 2 right

/-- Every fact the channels below need, evaluated on one plan. -/
def facts (plan : BootPageTablePlan.Plan) : Bool :=
  let left := runFrom plan leftTrace
  let right := runFrom plan rightTrace
  let preemptLeft := runFrom plan preemptLeftTrace
  let preemptRight := runFrom plan preemptRightTrace
  pairFacts left right &&
    Names (step left ownSubtree) 2 10 &&
    (step left ownSubtree).transfers.pending 10 !=
      (step right ownSubtree).transfers.pending 10 &&
    Names (step left otherSubtree) 2 10 &&
    (step left otherSubtree).transfers.pending 10 !=
      (step right otherSubtree).transfers.pending 10 &&
    pairFacts preemptLeft preemptRight &&
    reply preemptLeft preempt != reply preemptRight preempt &&
    pairFacts (runFrom plan blockedLeftTrace) (runFrom plan blockedRightTrace) &&
    (authoritativeGate (runFrom plan blockedLeftTrace) blockingSend).result !=
      (authoritativeGate (runFrom plan blockedRightTrace) blockingSend).result &&
    (authoritativeGate (runFrom plan blockedLeftTrace) blockingCancel).result !=
      (authoritativeGate (runFrom plan blockedRightTrace) blockingCancel).result

set_option maxRecDepth 100000 in
/-- **Kernel evaluation on the canonical sample plan.** -/
theorem facts_sample :
    (match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
      | .ok plan => facts plan
      | .error _ => false) = true := by
  decide +kernel

theorem sample_plan_exists :
    ∃ plan, BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan := by
  have h := facts_sample
  cases hcompile : BootPageTablePlan.compile BootPageTablePlan.sampleInput with
  | ok plan => exact ⟨plan, rfl⟩
  | error reason =>
      rw [hcompile] at h
      cases h

theorem facts_of_compile {plan : BootPageTablePlan.Plan}
    (hplan : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan) :
    facts plan = true := by
  have h := facts_sample
  rw [hplan] at h
  exact h

/-! ## The structural half: owned spaces and mappings -/

/-- The operations of the traces above, which never change address-space
ownership or mappings. -/
def keepsSpaces : AuthoritativeOperation → Bool
  | .ordinary (.capabilityCopy _ _ _ _) => true
  | .ordinary (.transferOffer _ _ _ _ _) => true
  | .ordinary (.resumePreempt _ _) => true
  | .blocking (.receive _ _ _) => true
  | _ => false

theorem restoreBlockingPeer_virtualMemory (state : CompositeState)
    (blocking : BlockingIPCContext.State) (next : CompositeState)
    (hrestore : restoreBlockingPeer state blocking = .ok next) :
    next.virtualMemory = state.virtualMemory := by
  unfold restoreBlockingPeer at hrestore
  repeat' split at hrestore
  all_goals first
    | (cases hrestore; done)
    | (cases hrestore; rfl)

theorem dispatchBlockingReceive_virtualMemory (state : CompositeState) (handleWord : UInt64)
    (frame : Interrupt.HardwareFrame) (registers : ResumableContext.Registers) :
    (dispatchBlockingReceive state handleWord frame registers).state.virtualMemory =
      state.virtualMemory := by
  unfold dispatchBlockingReceive
  dsimp only
  split
  · rfl
  · generalize BlockingIPCContext.receiveOrBlock _ _ _ _ = outcome
    rcases outcome with ⟨next, result⟩
    cases result with
    | contextRejected reason => rfl
    | completed result =>
        cases result with
        | delivered envelope => rfl
        | rejected reason => rfl
        | blocked =>
            dsimp only
            split
            · split
              · rfl
              · rename_i published hpublished
                exact restoreBlockingPeer_virtualMemory _ _ _ hpublished
            · rfl

theorem switch_translations_virtual (resumable : ResumablePreemption.State)
    (interruptState : Interrupt.State) (frame : Interrupt.HardwareFrame)
    (registers : ResumablePreemption.Registers) :
    (ResumablePreemption.switch resumable interruptState frame
      registers).state.translations.virtual = resumable.translations.virtual := by
  unfold ResumablePreemption.switch
  generalize Scheduler.tick resumable.scheduler = scheduled
  rcases scheduled with ⟨next, (_ | selected) | reason⟩
  all_goals
    simp only
    repeat' split
  all_goals simp [ResumablePreemption.reject, ResumablePreemption.halt, TLB.switch]

theorem keepsSpaces_step (state : CompositeState) (hstate : AuthoritativeRuntimeWellFormed state)
    (operation : AuthoritativeOperation) (hkeeps : keepsSpaces operation = true) :
    (authoritativeGate state operation).state.virtualMemory.owner =
        state.virtualMemory.owner ∧
      (authoritativeGate state operation).state.virtualMemory.mappings =
        state.virtualMemory.mappings := by
  have hvirtual := translations_eq (coherent_of hstate)
  cases operation with
  | ordinary operation =>
      rw [authoritativeGate_ordinary_state]
      rcases gate_state_cases state operation with hsame | happly
      · rw [hsame]
        exact ⟨rfl, rfl⟩
      rw [happly]
      cases operation with
      | capabilityCopy source destination destinationSlot rights =>
          simp only [applyOperation]
          split <;> exact ⟨rfl, rfl⟩
      | transferOffer endpointWord sourceWord sourceKind payload rights =>
          rw [applyOperation_transferOffer]
          split <;> exact ⟨rfl, rfl⟩
      | resumePreempt frame registers =>
          have htranslations := switch_translations_virtual state.resumable
            state.execution.core frame registers
          simp only [applyOperation]
          split
          · split
            · simp [installResumable, htranslations, hvirtual]
            · exact ⟨rfl, rfl⟩
          · exact ⟨rfl, rfl⟩
          · simp [installResumable, htranslations, hvirtual]
      | _ => simp [keepsSpaces] at hkeeps
  | blocking operation =>
      cases operation with
      | receive handleWord frame registers =>
          rw [authoritativeGate_blocking_state]
          cases hmode : state.execution.mode with
          | running =>
              rw [blockingGate_running_exact state _ hmode]
              simp [applyBlockingOperation, dispatchBlockingReceive_virtualMemory]
          | handling active => simp [blockingGate, hmode]
          | halted record => simp [blockingGate, hmode]
      | send handleWord word0 word1 => simp [keepsSpaces] at hkeeps
      | cancel subject => simp [keepsSpaces] at hkeeps
  | drainDeferred subject => simp [keepsSpaces] at hkeeps

theorem keepsSpaces_run (state : CompositeState) (hstate : AuthoritativeRuntimeWellFormed state)
    (operations : List AuthoritativeOperation)
    (hkeeps : ∀ operation, operation ∈ operations → keepsSpaces operation = true) :
    (runAuthoritativeOperations state operations).virtualMemory.owner =
        state.virtualMemory.owner ∧
      (runAuthoritativeOperations state operations).virtualMemory.mappings =
        state.virtualMemory.mappings := by
  induction operations generalizing state with
  | nil => exact ⟨rfl, rfl⟩
  | cons operation rest ih =>
      have hhead := keepsSpaces_step state hstate operation (hkeeps operation (by simp))
      have htail := ih (authoritativeGate state operation).state
        (authoritativeGate_preserves_authoritativeRuntimeWellFormed state operation hstate)
        (fun candidate hmem => hkeeps candidate (by simp [hmem]))
      exact ⟨htail.1.trans hhead.1, htail.2.trans hhead.2⟩

/-- Low equivalence from agreement on the decidable part of the view, the
owner map, and the mappings. -/
theorem lowEquiv_of_viewData {observer : Nat} {left right : CompositeState}
    (hdata : viewData observer left = viewData observer right)
    (howner : left.virtualMemory.owner = right.virtualMemory.owner)
    (hmappings : left.virtualMemory.mappings = right.virtualMemory.mappings) :
    LowEquiv observer left right := by
  simp only [viewData, Prod.mk.injEq] at hdata
  obtain ⟨hscheduled, hlive, hcapacity, hrow, hnamed, hwaiting, hcompletion⟩ := hdata
  unfold LowEquiv
  have howns : (observe observer left).owns = (observe observer right).owns := by
    funext space
    simp only [observe, howner]
  have hmaps : (observe observer left).mappings = (observe observer right).mappings := by
    funext space page
    simp only [observe, howner, hmappings]
  cases hleft : observe observer left
  cases hright : observe observer right
  rw [hleft, hright] at hscheduled hlive hcapacity hrow hnamed hwaiting hcompletion howns hmaps
  simp only at hscheduled hlive hcapacity hrow hnamed hwaiting hcompletion howns hmaps
  subst hscheduled hlive hcapacity hrow hnamed hwaiting hcompletion howns hmaps
  rfl

theorem runFrom_wellFormed (plan : BootPageTablePlan.Plan)
    (trace : List AuthoritativeOperation) :
    AuthoritativeRuntimeWellFormed (runFrom plan trace) :=
  runAuthoritativeOperations_preserves_authoritativeRuntimeWellFormed (seed plan) trace
    (seed_wellFormed plan)

/-- `pairFacts` and space preservation give every `OwnStepCounter` premise. -/
theorem ownStepCounter_of_pairFacts (plan : BootPageTablePlan.Plan)
    (leftOps rightOps : List AuthoritativeOperation)
    (hleftKeeps : ∀ operation, operation ∈ leftOps → keepsSpaces operation = true)
    (hrightKeeps : ∀ operation, operation ∈ rightOps → keepsSpaces operation = true)
    (hfacts : pairFacts (runFrom plan leftOps) (runFrom plan rightOps) = true) :
    OwnStepCounter 2 (runFrom plan leftOps) (runFrom plan rightOps) := by
  unfold pairFacts at hfacts
  simp only [Bool.and_eq_true, beq_iff_eq] at hfacts
  obtain ⟨⟨⟨⟨hleftCurrent, _⟩, hmode⟩, hcounter⟩, hdata⟩ := hfacts
  have hleft := keepsSpaces_run (seed plan) (seed_wellFormed plan) leftOps hleftKeeps
  have hright := keepsSpaces_run (seed plan) (seed_wellFormed plan) rightOps hrightKeeps
  refine
    { low := lowEquiv_of_viewData hdata (hleft.1.trans hright.1.symm)
        (hleft.2.trans hright.2.symm)
      leftWF := (runFrom_wellFormed plan leftOps).left
      rightWF := (runFrom_wellFormed plan rightOps).left
      current := hleftCurrent
      mode := ?_
      counter := hcounter }
  split at hmode
  · rename_i hl hr
    rw [hl, hr]
  · cases hmode

theorem leftTrace_keeps : ∀ operation, operation ∈ leftTrace → keepsSpaces operation = true := by
  decide

theorem rightTrace_keeps : ∀ operation, operation ∈ rightTrace → keepsSpaces operation = true := by
  decide

theorem preemptLeftTrace_keeps :
    ∀ operation, operation ∈ preemptLeftTrace → keepsSpaces operation = true := by
  decide

theorem preemptRightTrace_keeps :
    ∀ operation, operation ∈ preemptRightTrace → keepsSpaces operation = true := by
  decide

/-! ## The channels -/

theorem blockedTrace_keeps (registers : ResumablePreemption.Registers) :
    ∀ operation, operation ∈ blockedTrace registers → keepsSpaces operation = true := by
  intro operation hmem
  simp only [blockedTrace, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl <;> rfl

/-- Every fact of `facts`, named. -/
structure Facts (plan : BootPageTablePlan.Plan) : Prop where
  derivationPair : pairFacts (runFrom plan leftTrace) (runFrom plan rightTrace) = true
  ownNames : Names (step (runFrom plan leftTrace) ownSubtree) 2 10 = true
  ownPending : (step (runFrom plan leftTrace) ownSubtree).transfers.pending 10 ≠
    (step (runFrom plan rightTrace) ownSubtree).transfers.pending 10
  otherNames : Names (step (runFrom plan leftTrace) otherSubtree) 2 10 = true
  otherPending : (step (runFrom plan leftTrace) otherSubtree).transfers.pending 10 ≠
    (step (runFrom plan rightTrace) otherSubtree).transfers.pending 10
  preemptPair : pairFacts (runFrom plan preemptLeftTrace) (runFrom plan preemptRightTrace) = true
  preemptReply : reply (runFrom plan preemptLeftTrace) preempt ≠
    reply (runFrom plan preemptRightTrace) preempt
  blockedPair : pairFacts (runFrom plan blockedLeftTrace) (runFrom plan blockedRightTrace) = true
  sendReply : (authoritativeGate (runFrom plan blockedLeftTrace) blockingSend).result ≠
    (authoritativeGate (runFrom plan blockedRightTrace) blockingSend).result
  cancelReply : (authoritativeGate (runFrom plan blockedLeftTrace) blockingCancel).result ≠
    (authoritativeGate (runFrom plan blockedRightTrace) blockingCancel).result

theorem facts_parts {plan : BootPageTablePlan.Plan}
    (hplan : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan) :
    Facts plan := by
  have hfacts := facts_of_compile hplan
  simp only [facts, Bool.and_eq_true, bne_iff_ne, ne_eq] at hfacts
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hpair, hownNames⟩, hownPending⟩, hotherNames⟩, hotherPending⟩,
    hpreemptPair⟩, hpreempt⟩, hblockedPair⟩, hsend⟩, hcancel⟩ := hfacts
  exact ⟨hpair, hownNames, hownPending, hotherNames, hotherPending, hpreemptPair, hpreempt,
    hblockedPair, hsend, hcancel⟩

theorem derivation_pair (plan : BootPageTablePlan.Plan)
    (hplan : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan) :
    OwnStepCounter 2 (runFrom plan leftTrace) (runFrom plan rightTrace) :=
  ownStepCounter_of_pairFacts plan _ _ leftTrace_keeps rightTrace_keeps
    (facts_parts hplan).derivationPair

theorem blocked_pair (plan : BootPageTablePlan.Plan)
    (hplan : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan) :
    OwnStepCounter 2 (runFrom plan blockedLeftTrace) (runFrom plan blockedRightTrace) :=
  ownStepCounter_of_pairFacts plan _ _ (blockedTrace_keeps _) (blockedTrace_keeps _)
    (facts_parts hplan).blockedPair

theorem not_lowEquiv_of_pending {left right : CompositeState}
    (hnames : Names left 2 10 = true)
    (hpending : left.transfers.pending 10 ≠ right.transfers.pending 10) :
    ¬ LowEquiv 2 left right := by
  intro hlow
  exact hpending (congrArg ObjectView.sealed (hlow.namedView 10 hnames))

/-- **Subtree revocation of the observer's own capability is step
inconsistent**: whether it cancels the sealed transfer pending on the
observer's endpoint depends on a derivation the observer cannot see. -/
theorem revokeSubtree_own_step_inconsistent (plan : BootPageTablePlan.Plan)
    (hplan : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan) :
    OwnStepCounter 2 (runFrom plan leftTrace) (runFrom plan rightTrace) ∧
      ¬ LowEquiv 2 (step (runFrom plan leftTrace) ownSubtree)
        (step (runFrom plan rightTrace) ownSubtree) :=
  ⟨derivation_pair plan hplan,
    not_lowEquiv_of_pending (facts_parts hplan).ownNames (facts_parts hplan).ownPending⟩

/-- **Subtree revocation of another subject's capability is step
inconsistent**: it cancels the observer's pending transfer exactly when that
transfer descends from the revoked root through a hidden derivation. -/
theorem revokeSubtree_other_step_inconsistent (plan : BootPageTablePlan.Plan)
    (hplan : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan) :
    OwnStepCounter 2 (runFrom plan leftTrace) (runFrom plan rightTrace) ∧
      ¬ LowEquiv 2 (step (runFrom plan leftTrace) otherSubtree)
        (step (runFrom plan rightTrace) otherSubtree) :=
  ⟨derivation_pair plan hplan,
    not_lowEquiv_of_pending (facts_parts hplan).otherNames (facts_parts hplan).otherPending⟩

/-- **The observer's timer switch is output inconsistent**: its reply carries
the restored context of the next subject, including registers outside the
observer's view. -/
theorem resumePreempt_output_inconsistent (plan : BootPageTablePlan.Plan)
    (hplan : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan) :
    OwnStepCounter 2 (runFrom plan preemptLeftTrace) (runFrom plan preemptRightTrace) ∧
      reply (runFrom plan preemptLeftTrace) preempt ≠
        reply (runFrom plan preemptRightTrace) preempt :=
  ⟨ownStepCounter_of_pairFacts plan _ _ preemptLeftTrace_keeps preemptRightTrace_keeps
    (facts_parts hplan).preemptPair, (facts_parts hplan).preemptReply⟩

/-- **The observer's blocking send is output inconsistent**: a send that wakes
a waiter replies with the waiter's saved context, whose registers are outside
the observer's view. -/
theorem blockingSend_output_inconsistent (plan : BootPageTablePlan.Plan)
    (hplan : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan) :
    OwnStepCounter 2 (runFrom plan blockedLeftTrace) (runFrom plan blockedRightTrace) ∧
      (authoritativeGate (runFrom plan blockedLeftTrace) blockingSend).result ≠
        (authoritativeGate (runFrom plan blockedRightTrace) blockingSend).result :=
  ⟨blocked_pair plan hplan, (facts_parts hplan).sendReply⟩

/-- **The observer's wait cancellation is output inconsistent**: it replies
with the cancelled subject's saved context. -/
theorem blockingCancel_output_inconsistent (plan : BootPageTablePlan.Plan)
    (hplan : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan) :
    OwnStepCounter 2 (runFrom plan blockedLeftTrace) (runFrom plan blockedRightTrace) ∧
      (authoritativeGate (runFrom plan blockedLeftTrace) blockingCancel).result ≠
        (authoritativeGate (runFrom plan blockedRightTrace) blockingCancel).result :=
  ⟨blocked_pair plan hplan, (facts_parts hplan).cancelReply⟩

end LeanOS.CompositeSwitchedChannels
