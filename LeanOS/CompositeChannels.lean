import LeanOS.CompositeOwnSteps

/-!
# Composite unwinding: channels of the observer's excluded operations

`LeanOS.CompositeOwnSteps` proves step and output consistency for the
observer's own operations wherever they hold.  Every family it excludes reads
or writes state outside the observer's view, and this module proves each such
exclusion with a concrete counterexample: two states that satisfy every
premise of the consistency theorems, including agreement on the public
identity counter (`OwnStepCounter`), yet give the observer different replies
(output channel) or distinguishable views (step channel).

All pairs are built from the canonical runtime-well-formed dispatcher seed
`FailStop.compositeDispatcherInitial` by `authoritativeGate` steps of the
scheduled observer, subject 2.  The two states of each pair differ only by
steps that leave its view unchanged:

* `created`: subject 2 creates subject 3.  Liveness and issuance of another
  subject are outside the view.
* `toSlotTwo` and `toSlotThree`: subject 2 delegates its endpoint into subject
  1's slot 2 or slot 3.  Another subject's slot occupancy is outside the view;
  both consume one identity, so the counters agree.
* `offered` and `offeredCreated`: subject 2 offers its memory capability on
  its endpoint, then (in the second) creates subject 3.

Channels:

* `create_output_inconsistent`, `terminate_output_inconsistent`,
  `scheduleAdd_output_inconsistent`: the replies reveal another subject's
  liveness, issuance, and runnability.
* `terminate_step_inconsistent`: terminating another subject cancels every
  pending sealed offer, including one on the observer's endpoint, exactly when
  the termination is accepted.
* `copy_destination_output_inconsistent_counter`,
  `revoke_other_output_inconsistent`,
  `revokeSubtree_other_output_inconsistent`: the replies reveal another
  subject's slot occupancy, now with the counters equal.
* `offer_counter_step_inconsistent`: without the public counter, the
  observer's own transfer offer is step inconsistent, as its delegation is
  (`CompositeUnwinding.Channels.identity_counter_step_inconsistent`).
-/
namespace LeanOS.CompositeChannels

open LeanOS
open LeanOS.FailStop
open LeanOS.CompositeObservation
open LeanOS.CompositeUnwinding
open LeanOS.CompositeOwnSteps
set_option linter.unusedSimpArgs false

abbrev seed (plan : BootPageTablePlan.Plan) : CompositeState := Channels.seed plan

def step (state : CompositeState) (operation : Operation) : CompositeState :=
  (authoritativeGate state (.ordinary operation)).state

def reply (state : CompositeState) (operation : Operation) : AuthoritativeGateResult :=
  (authoritativeGate state (.ordinary operation)).result

theorem step_wellFormed {state : CompositeState} (hstate : AuthoritativeRuntimeWellFormed state)
    (operation : Operation) : AuthoritativeRuntimeWellFormed (step state operation) :=
  authoritativeGate_preserves_authoritativeRuntimeWellFormed state _ hstate

/-- A gate step whose applied effect leaves the observer's view unchanged
leaves it unchanged on the gate too. -/
theorem observe_step_of_apply (observer : Nat) (state : CompositeState)
    (operation : Operation)
    (happly : observe observer (applyOperation state operation) = observe observer state) :
    observe observer (step state operation) = observe observer state := by
  unfold step
  rw [authoritativeGate_ordinary_state]
  rcases gate_state_cases state operation with hsame | happly'
  · rw [hsame]
  · rw [happly', happly]

/-! ## The paired states -/

/-- Subject 2 creates subject 3. -/
def createThree : Operation := .createSubject 3

def created (plan : BootPageTablePlan.Plan) : CompositeState := step (seed plan) createThree

/-- Subject 2 delegates a send-only endpoint capability into subject 1's slot 2
or slot 3. -/
def toSlotTwo (plan : BootPageTablePlan.Plan) : CompositeState :=
  step (seed plan) (.capabilityCopy 0 1 2 { send := true })

def toSlotThree (plan : BootPageTablePlan.Plan) : CompositeState :=
  step (seed plan) (.capabilityCopy 0 1 3 { send := true })

/-- Handle words for subject 2's endpoint (slot 0, generation 3) and memory
(slot 2, generation 5). -/
def endpointWord : UInt64 := 196608
def memoryWord : UInt64 := 327682

/-- Subject 2 offers a read-only descendant of its memory capability on its
own endpoint. -/
def offerMemory : Operation := .transferOffer endpointWord memoryWord .memory
  { word0 := 1, word1 := 2 } { read := true }

def offered (plan : BootPageTablePlan.Plan) : CompositeState := step (seed plan) offerMemory

def offeredCreated (plan : BootPageTablePlan.Plan) : CompositeState :=
  step (offered plan) createThree

theorem seed_wellFormed (plan : BootPageTablePlan.Plan) :
    AuthoritativeRuntimeWellFormed (seed plan) :=
  compositeDispatcherInitial_authoritativeRuntimeWellFormed plan

theorem seed_current (plan : BootPageTablePlan.Plan) :
    (seed plan).lifecycle.current = some 2 := rfl

theorem observe_created (state : CompositeState)
    (hstate : AuthoritativeRuntimeWellFormed state) :
    observe 2 (step state createThree) = observe 2 state :=
  observe_step_of_apply 2 state _
    (observe_apply_create_other 2 state 3 (by decide) hstate.left.1)

theorem observe_toSlot (plan : BootPageTablePlan.Plan) (slot : Nat) :
    observe 2 (step (seed plan) (.capabilityCopy 0 1 slot { send := true })) =
      observe 2 (seed plan) :=
  observe_step_of_apply 2 _ _
    (observe_apply_copy_other 2 (seed plan) 0 1 slot { send := true } (by decide))

/-- The premises of every consistency theorem, with the public counter. -/
theorem ownStepCounter_of {left right : CompositeState}
    (hleft : AuthoritativeRuntimeWellFormed left) (hright : AuthoritativeRuntimeWellFormed right)
    (hlow : LowEquiv 2 left right) (hcurrent : left.lifecycle.current = some 2)
    (hmode : left.execution.mode = right.execution.mode)
    (hcounter : left.capabilities.nextIdentity = right.capabilities.nextIdentity) :
    OwnStepCounter 2 left right :=
  { low := hlow
    leftWF := hleft.left
    rightWF := hright.left
    current := hcurrent
    mode := hmode
    counter := hcounter }

theorem seed_created (plan : BootPageTablePlan.Plan) :
    OwnStepCounter 2 (seed plan) (created plan) :=
  ownStepCounter_of (seed_wellFormed plan) (step_wellFormed (seed_wellFormed plan) _)
    (observe_created (seed plan) (seed_wellFormed plan)).symm rfl rfl rfl

theorem slotThree_slotTwo (plan : BootPageTablePlan.Plan) :
    OwnStepCounter 2 (toSlotThree plan) (toSlotTwo plan) :=
  ownStepCounter_of (step_wellFormed (seed_wellFormed plan) _)
    (step_wellFormed (seed_wellFormed plan) _)
    ((observe_toSlot plan 3).trans (observe_toSlot plan 2).symm) rfl rfl rfl

theorem offered_offeredCreated (plan : BootPageTablePlan.Plan) :
    OwnStepCounter 2 (offered plan) (offeredCreated plan) :=
  ownStepCounter_of (step_wellFormed (seed_wellFormed plan) _)
    (step_wellFormed (step_wellFormed (seed_wellFormed plan) _) _)
    (observe_created (offered plan) (step_wellFormed (seed_wellFormed plan) _)).symm
    rfl rfl rfl

/-! ## Liveness and issuance of another subject -/

/-- **Creating another subject is output inconsistent**: the reply reveals
whether that subject is already live. -/
theorem create_output_inconsistent (plan : BootPageTablePlan.Plan) :
    OwnStepCounter 2 (seed plan) (created plan) ∧
      reply (seed plan) createThree ≠ reply (created plan) createThree := by
  refine ⟨seed_created plan, ?_⟩
  have hleft : reply (seed plan) createThree =
      .completed (.ordinary (.createSubject .accepted)) := rfl
  have hright : reply (created plan) createThree =
      .completed (.ordinary (.createSubject (.rejected .alreadyLive))) := rfl
  rw [hleft, hright]
  simp

/-- **Terminating another subject is output inconsistent**: the reply reveals
whether that subject was ever issued. -/
theorem terminate_output_inconsistent (plan : BootPageTablePlan.Plan) :
    OwnStepCounter 2 (seed plan) (created plan) ∧
      reply (seed plan) (.terminateSubject 3) ≠ reply (created plan) (.terminateSubject 3) := by
  refine ⟨seed_created plan, ?_⟩
  have hleft : reply (seed plan) (.terminateSubject 3) =
      .completed (.ordinary (.terminateSubject (.rejected .neverIssued))) := rfl
  have hright : reply (created plan) (.terminateSubject 3) =
      .completed (.ordinary (.terminateSubject .accepted)) := rfl
  rw [hleft, hright]
  simp

/-- **Queue admission of another subject is output inconsistent**: the reply
reveals whether that subject is live. -/
theorem scheduleAdd_output_inconsistent (plan : BootPageTablePlan.Plan) :
    OwnStepCounter 2 (seed plan) (created plan) ∧
      reply (seed plan) (.scheduleAdd 3) ≠ reply (created plan) (.scheduleAdd 3) := by
  refine ⟨seed_created plan, ?_⟩
  have hleft : reply (seed plan) (.scheduleAdd 3) =
      .completed (.ordinary (.scheduler (.rejected .notLive))) := rfl
  have hright : reply (created plan) (.scheduleAdd 3) =
      .completed (.ordinary (.scheduler (.rejected .notRunnable))) := rfl
  rw [hleft, hright]
  simp

/-- The sealed transfers pending on the endpoints in subject 2's row. -/
def sealedView (state : CompositeState) : List (Option (Option CapabilityTransfer.Sealed)) :=
  (observe 2 state).named.map (Option.map (·.sealed))

/-- **Terminating another subject is step inconsistent**: an accepted
termination cancels every pending sealed offer, including the observer's own
offer on its own endpoint, while a rejected one changes nothing. -/
theorem terminate_step_inconsistent (plan : BootPageTablePlan.Plan) :
    OwnStepCounter 2 (offered plan) (offeredCreated plan) ∧
      ¬ LowEquiv 2 (step (offered plan) (.terminateSubject 3))
        (step (offeredCreated plan) (.terminateSubject 3)) := by
  refine ⟨offered_offeredCreated plan, fun hlow => ?_⟩
  have hnames : Names (step (offered plan) (.terminateSubject 3)) 2 10 = true := rfl
  have hleft : (step (offered plan) (.terminateSubject 3)).transfers.pending 10 =
      some ⟨6, 5, 2, 20, .memory, { read := true }⟩ := rfl
  have hright : (step (offeredCreated plan) (.terminateSubject 3)).transfers.pending 10 =
      none := rfl
  have hsealed := congrArg ObjectView.sealed (hlow.namedView 10 hnames)
  simp only [CompositeObservation.objectView, hleft, hright] at hsealed
  cases hsealed

/-! ## Another subject's slot occupancy, with the counters equal -/

/-- **Delegation to another subject is output inconsistent** even with the
counter public. -/
theorem copy_destination_output_inconsistent_counter (plan : BootPageTablePlan.Plan) :
    OwnStepCounter 2 (toSlotThree plan) (toSlotTwo plan) ∧
      reply (toSlotThree plan) Channels.delegateToOther ≠
        reply (toSlotTwo plan) Channels.delegateToOther := by
  refine ⟨slotThree_slotTwo plan, ?_⟩
  have hleft : reply (toSlotThree plan) Channels.delegateToOther =
      .completed (.ordinary (.capability .accepted)) := rfl
  have hright : reply (toSlotTwo plan) Channels.delegateToOther =
      .completed (.ordinary (.capability (.rejected .occupiedSlot))) := rfl
  rw [hleft, hright]
  simp

/-- **Revoking another subject's slot is output inconsistent**: the reply
reveals whether that slot is occupied. -/
theorem revoke_other_output_inconsistent (plan : BootPageTablePlan.Plan) :
    OwnStepCounter 2 (toSlotThree plan) (toSlotTwo plan) ∧
      reply (toSlotThree plan) (.capabilityRevoke 0 1 2) ≠
        reply (toSlotTwo plan) (.capabilityRevoke 0 1 2) := by
  refine ⟨slotThree_slotTwo plan, ?_⟩
  have hleft : reply (toSlotThree plan) (.capabilityRevoke 0 1 2) =
      .completed (.ordinary (.capability (.rejected .staleSlot))) := rfl
  have hright : reply (toSlotTwo plan) (.capabilityRevoke 0 1 2) =
      .completed (.ordinary (.capability .accepted)) := rfl
  rw [hleft, hright]
  simp

/-- **Subtree revocation of another subject's slot is output inconsistent**,
for the same reason. -/
theorem revokeSubtree_other_output_inconsistent (plan : BootPageTablePlan.Plan) :
    OwnStepCounter 2 (toSlotThree plan) (toSlotTwo plan) ∧
      reply (toSlotThree plan) (.capabilityRevokeSubtree 0 1 2) ≠
        reply (toSlotTwo plan) (.capabilityRevokeSubtree 0 1 2) := by
  refine ⟨slotThree_slotTwo plan, ?_⟩
  have hleft : reply (toSlotThree plan) (.capabilityRevokeSubtree 0 1 2) =
      .completed (.ordinary (.capability (.rejected .staleSlot))) := rfl
  have hright : reply (toSlotTwo plan) (.capabilityRevokeSubtree 0 1 2) =
      .completed (.ordinary (.capability .accepted)) := rfl
  rw [hleft, hright]
  simp

/-! ## The identity counter and transfer offers -/

/-- **Without the public counter, the observer's transfer offer is step
inconsistent**: the sealed transfer pending on its own endpoint carries the
identity drawn from the global counter. -/
theorem offer_counter_step_inconsistent (plan : BootPageTablePlan.Plan) :
    OwnStep 2 (seed plan) (Channels.shifted plan) ∧
      (seed plan).capabilities.nextIdentity ≠ (Channels.shifted plan).capabilities.nextIdentity ∧
      ¬ LowEquiv 2 (step (seed plan) offerMemory) (step (Channels.shifted plan) offerMemory) := by
  refine ⟨Channels.seed_ownStep_shifted plan, fun hcounter => ?_, fun hlow => ?_⟩
  · have hvalues : (6 : Nat) = 7 := hcounter
    exact absurd hvalues (by decide)
  have hnames : Names (step (seed plan) offerMemory) 2 10 = true := rfl
  have hleft : (step (seed plan) offerMemory).transfers.pending 10 =
      some ⟨6, 5, 2, 20, .memory, { read := true }⟩ := rfl
  have hright : (step (Channels.shifted plan) offerMemory).transfers.pending 10 =
      some ⟨7, 5, 2, 20, .memory, { read := true }⟩ := rfl
  have hsealed := congrArg ObjectView.sealed (hlow.namedView 10 hnames)
  simp only [CompositeObservation.objectView, hleft, hright] at hsealed
  simp at hsealed

end LeanOS.CompositeChannels
