import LeanOS.CompositeRegisterChannels
import LeanOS.CompositeLocalRespect

/-!
# Composite unwinding over the subject-facing gate

`FailStop.subjectGate` is what a scheduled subject can ask the kernel for: it
refuses, with one fixed result and no effect, every request that names a
subject other than the scheduled one (`FailStop.CompositeState.refusesCrossSubject`),
and is otherwise `FailStop.authoritativeGate`.  This module states the
observer unwinding over it.

**Local respect** (`subjectGate_silent_observe`).  Another subject's refused
request leaves the state unchanged, so it is silent too
(`isSilentSubject`).  The trace theorem is `finite_trace_lowEquiv_subject`.

**The channels of `LeanOS.CompositeChannels` are closed.**  When the scheduled
observer names another subject, the gate refuses on both sides of an
`OwnStep` pair (or, with the latch busy or halted, rejects on both sides as
`authoritativeGate` does): `own_step_cross` and `own_output_cross`.  This
covers delegation to, direct and subtree revocation of, and creation,
termination, queue admission, wait cancellation and deferred drain of another
subject.  The channel theorems of `LeanOS.CompositeChannels` and the
other-subject half of `LeanOS.CompositeSwitchedChannels` stay as the
adversarial record of the raw transitions: `authoritativeGate` remains the
kernel's engine, and exposed to a subject it leaked.
`cross_subject_channels_closed` re-evaluates the same pairs through the
subject gate.

**Every other operation is unchanged.**  For an operation that names no
subject or names the observer, the subject gate is `authoritativeGate` on both
sides (`subjectGate_own`), so every consistency theorem proved for the
authoritative gate carries over (`own_step_consistent_subject`,
`own_output_consistent_subject`).
-/
namespace LeanOS.CompositeSubjectGate

open LeanOS
open LeanOS.FailStop
open LeanOS.CompositeObservation
open LeanOS.CompositeUnwinding
open LeanOS.CompositeOwnSteps
open LeanOS.CompositeLocalRespect
set_option linter.unusedSimpArgs false

/-! ## Local respect and the trace theorem -/

/-- Another subject's refused request, or a request already silent for the
authoritative gate. -/
def isSilentSubject (observer : Nat) (state : CompositeState)
    (operation : AuthoritativeOperation) : Bool :=
  state.refusesCrossSubject operation || isSilentExtended observer state operation

/-- **Local respect over the subject gate.** -/
theorem subjectGate_silent_observe (observer : Nat) (state : CompositeState)
    (operation : AuthoritativeOperation) (hstate : AuthoritativeRuntimeWellFormed state)
    (hsilent : isSilentSubject observer state operation = true) :
    LowEquiv observer (subjectGate state operation).state state := by
  cases hrefused : state.refusesCrossSubject operation
  · simp only [isSilentSubject, hrefused, Bool.false_or] at hsilent
    rw [subjectGate_of_not_refused hrefused]
    exact authoritativeGate_silentExtended_observe observer state operation hstate hsilent
  · rw [subjectGate_refused hrefused]
    rfl

/-- One observer event over the subject gate. -/
structure Event where
  view : View
  reply : Option SubjectGateResult

def execute (observer : Nat) (state : CompositeState) (operation : AuthoritativeOperation) :
    CompositeState × Option Event :=
  let outcome := subjectGate state operation
  (outcome.state,
    if isSilentSubject observer state operation then none
    else some
      { view := observe observer outcome.state
        reply := if actor state = observer then some outcome.result else none })

def system (observer : Nat) :
    ReplayUnwinding.System CompositeState AuthoritativeOperation Event View where
  observe := observe observer
  execute := execute observer
  applyEvent _ event := event.view

def run (observer : Nat) (state : CompositeState) (operations : List AuthoritativeOperation) :
    CompositeState × List Event :=
  ReplayUnwinding.run (system observer) state operations

def projection (observer : Nat) (state : CompositeState)
    (operations : List AuthoritativeOperation) : List Event :=
  ReplayUnwinding.projection (system observer) state operations

/-- The run's state component is exactly the subject-gate trace. -/
theorem run_state (observer : Nat) (state : CompositeState)
    (operations : List AuthoritativeOperation) :
    (run observer state operations).1 = runSubjectOperations state operations := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation rest ih =>
      simp only [run, ReplayUnwinding.run, runSubjectOperations] at ih ⊢
      exact ih _

theorem system_replaysOn (observer : Nat) :
    ReplayUnwinding.ReplaysOn (system observer) AuthoritativeRuntimeWellFormed := by
  apply ReplayUnwinding.replaysOn_of_unwinding
  · intro state operation hstate hnone
    simp only [system, execute] at hnone ⊢
    split at hnone
    · rename_i hsilent
      exact subjectGate_silent_observe observer state operation hstate hsilent
    · simp at hnone
  · intro state operation event _ hsome
    simp only [system, execute] at hsome ⊢
    split at hsome
    · simp at hsome
    · simp only [Option.some.injEq] at hsome
      rw [← hsome]

/-- **Finite-trace noninterference over the subject gate.** -/
theorem finite_trace_lowEquiv_subject (observer : Nat) (left right : CompositeState)
    (leftOperations rightOperations : List AuthoritativeOperation)
    (hleft : AuthoritativeRuntimeWellFormed left)
    (hright : AuthoritativeRuntimeWellFormed right)
    (hlow : LowEquiv observer left right)
    (hevents : projection observer left leftOperations =
      projection observer right rightOperations) :
    LowEquiv observer (run observer left leftOperations).1
      (run observer right rightOperations).1 :=
  ReplayUnwinding.finite_trace_lowEquiv_on (system observer) (system_replaysOn observer)
    (fun state operation hstate =>
      subjectGate_preserves_authoritativeRuntimeWellFormed state operation hstate)
    left right leftOperations rightOperations hleft hright hlow hevents

/-! ## The observer's requests that name another subject -/

/-- The request names a subject other than the observer. -/
def crossTarget (observer : Nat) (operation : AuthoritativeOperation) : Bool :=
  match operation.target with
  | some target => target != observer
  | none => false

theorem not_nmi_of_target {operation : AuthoritativeOperation} {target : Nat}
    (htarget : operation.target = some target) :
    ∀ raw context, operation ≠ .ordinary (.nmi raw context) := by
  intro raw context heq
  subst heq
  simp [AuthoritativeOperation.target] at htarget

/-- With the latch busy or halted, every operation but an NMI stutters and
answers from the latch alone. -/
theorem authoritativeGate_not_running (state : CompositeState) (operation : AuthoritativeOperation)
    (hnmi : ∀ raw context, operation ≠ .ordinary (.nmi raw context))
    (hmode : state.execution.mode ≠ .running) :
    (authoritativeGate state operation).state = state ∧
      (authoritativeGate state operation).result =
        match state.execution.mode with
        | .halted record => .rejectedHalted record
        | _ => .rejectedBusy := by
  cases operation with
  | ordinary operation =>
      cases operation <;> cases hm : state.execution.mode <;> simp_all [authoritativeGate]
  | blocking operation =>
      cases hm : state.execution.mode <;> simp_all [authoritativeGate]
  | drainDeferred subject =>
      cases hm : state.execution.mode <;> simp_all [authoritativeGate]

/-- **A request that names another subject is answered without reading it.**
On both sides of an `OwnStep` pair the subject gate refuses (latch running)
or rejects from the latch (busy or halted), changing nothing. -/
theorem own_cross_stutter {observer : Nat} {left right : CompositeState}
    (h : OwnStep observer left right) (operation : AuthoritativeOperation)
    (hcross : crossTarget observer operation = true) :
    (subjectGate left operation).state = left ∧
      (subjectGate right operation).state = right ∧
      (subjectGate left operation).result = (subjectGate right operation).result := by
  cases htarget : operation.target with
  | none => simp [crossTarget, htarget] at hcross
  | some target =>
      simp only [crossTarget, htarget, bne_iff_ne, ne_eq] at hcross
      by_cases hmode : left.execution.mode = .running
      · have hrefused : ∀ state : CompositeState, state.execution.mode = .running →
            state.lifecycle.current = some observer →
            state.refusesCrossSubject operation = true := by
          intro state hrun hcurrent
          simp [CompositeState.refusesCrossSubject, hrun, hcurrent, htarget, hcross]
        rw [subjectGate_refused (hrefused left hmode h.current),
          subjectGate_refused (hrefused right (h.mode ▸ hmode) h.rightCurrent)]
        exact ⟨rfl, rfl, rfl⟩
      · have hnot : ∀ state : CompositeState, state.execution.mode ≠ .running →
            state.refusesCrossSubject operation = false := by
          intro state hrun
          unfold CompositeState.refusesCrossSubject
          split <;> simp_all
        have hrightMode : right.execution.mode ≠ .running := h.mode ▸ hmode
        rw [subjectGate_of_not_refused (hnot left hmode),
          subjectGate_of_not_refused (hnot right hrightMode)]
        obtain ⟨hl, hlr⟩ := authoritativeGate_not_running left operation
          (not_nmi_of_target htarget) hmode
        obtain ⟨hr, hrr⟩ := authoritativeGate_not_running right operation
          (not_nmi_of_target htarget) hrightMode
        refine ⟨hl, hr, ?_⟩
        simp only [SubjectGateResult.gate.injEq]
        rw [hlr, hrr, h.mode]

/-- **Step consistency of the observer's cross-subject requests.** -/
theorem own_step_cross {observer : Nat} {left right : CompositeState}
    (h : OwnStep observer left right) (operation : AuthoritativeOperation)
    (hcross : crossTarget observer operation = true) :
    LowEquiv observer (subjectGate left operation).state (subjectGate right operation).state := by
  obtain ⟨hl, hr, _⟩ := own_cross_stutter h operation hcross
  rw [hl, hr]
  exact h.low

/-- **Output consistency of the observer's cross-subject requests.** -/
theorem own_output_cross {observer : Nat} {left right : CompositeState}
    (h : OwnStep observer left right) (operation : AuthoritativeOperation)
    (hcross : crossTarget observer operation = true) :
    (subjectGate left operation).result = (subjectGate right operation).result :=
  (own_cross_stutter h operation hcross).2.2

/-! ## Every other request is the authoritative gate -/

/-- A request of the scheduled observer that names no other subject is never
refused. -/
theorem refuses_own {observer : Nat} {state : CompositeState}
    (hcurrent : state.lifecycle.current = some observer) (operation : AuthoritativeOperation)
    (hcross : crossTarget observer operation = false) :
    state.refusesCrossSubject operation = false := by
  apply refusesCrossSubject_eq_false_of_target
  intro target htarget
  simp only [crossTarget, htarget, bne_eq_false_iff_eq] at hcross
  rw [hcross]
  exact hcurrent

theorem subjectGate_own {observer : Nat} {state : CompositeState}
    (hcurrent : state.lifecycle.current = some observer) (operation : AuthoritativeOperation)
    (hcross : crossTarget observer operation = false) :
    subjectGate state operation =
      { state := (authoritativeGate state operation).state
        result := .gate (authoritativeGate state operation).result } :=
  subjectGate_of_not_refused (refuses_own hcurrent operation hcross)

/-- The observer's requests that are step consistent once the identity
counter is public: every request naming another subject, every ordinary
operation of `ownStepConsistentCounter`, and every drain. -/
def ownStepSubject (observer : Nat) (operation : AuthoritativeOperation) : Bool :=
  crossTarget observer operation ||
    match operation with
    | .ordinary operation => ownStepConsistentCounter observer operation
    | .drainDeferred _ => true
    | .blocking _ => false

/-- **Step consistency for the observer's requests, identity counter
public.** -/
theorem own_step_consistent_subject {observer : Nat} {left right : CompositeState}
    (h : OwnStepCounter observer left right)
    (hleft : AuthoritativeRuntimeWellFormed left) (hright : AuthoritativeRuntimeWellFormed right)
    (operation : AuthoritativeOperation) (hfamily : ownStepSubject observer operation = true) :
    LowEquiv observer (subjectGate left operation).state (subjectGate right operation).state := by
  cases hcross : crossTarget observer operation
  · rw [subjectGate_own h.current operation hcross,
      subjectGate_own h.toOwnStep.rightCurrent operation hcross]
    simp only [ownStepSubject, hcross, Bool.false_or] at hfamily
    cases operation with
    | ordinary operation => exact own_step_consistent_counter h operation hfamily
    | drainDeferred subject => exact own_step_drain h.toOwnStep hleft hright subject
    | blocking operation => simp at hfamily
  · exact own_step_cross h.toOwnStep operation hcross

/-- The observer's requests that are output consistent once the identity
counter is public. -/
def ownOutputSubject (observer : Nat) (operation : AuthoritativeOperation) : Bool :=
  crossTarget observer operation ||
    match operation with
    | .ordinary operation => ownOutputConsistentCounter observer operation
    | .drainDeferred subject => subject == observer
    | .blocking _ => false

/-- **Output consistency for the observer's requests, identity counter
public.** -/
theorem own_output_consistent_subject {observer : Nat} {left right : CompositeState}
    (h : OwnStepCounter observer left right)
    (hleft : AuthoritativeRuntimeWellFormed left) (hright : AuthoritativeRuntimeWellFormed right)
    (operation : AuthoritativeOperation) (hfamily : ownOutputSubject observer operation = true) :
    (subjectGate left operation).result = (subjectGate right operation).result := by
  cases hcross : crossTarget observer operation
  · rw [subjectGate_own h.current operation hcross,
      subjectGate_own h.toOwnStep.rightCurrent operation hcross]
    simp only [ownOutputSubject, hcross, Bool.false_or] at hfamily
    simp only [SubjectGateResult.gate.injEq]
    cases operation with
    | ordinary operation => exact own_output_consistent_counter h operation hfamily
    | drainDeferred subject =>
        simp only [beq_iff_eq] at hfamily
        subst hfamily
        exact own_output_drain_self h.toOwnStep hleft hright
    | blocking operation => simp at hfamily
  · exact own_output_cross h.toOwnStep operation hcross

/-! ## The `#542` channels, re-evaluated through the subject gate -/

/-- The subject gate's reply on a request. -/
def subjectReply (state : CompositeState) (operation : Operation) : SubjectGateResult :=
  (subjectGate state (.ordinary operation)).result

def subjectStep (state : CompositeState) (operation : Operation) : CompositeState :=
  (subjectGate state (.ordinary operation)).state

/-- **The cross-subject channels of `#542` are closed.**  On the very pairs on
which `LeanOS.CompositeChannels` and `LeanOS.CompositeSwitchedChannels` proved
the raw transitions leaky (and which satisfy every `OwnStepCounter`
premise), the subject gate gives the observer equal replies to creation,
termination and queue admission of another subject and to delegation into,
direct revocation of and subtree revocation of another subject's slot, and
low-equivalent states after terminating another subject and after revoking
the subtree of another subject's capability. -/
theorem cross_subject_channels_closed (plan : BootPageTablePlan.Plan) :
    subjectReply (CompositeChannels.seed plan) CompositeChannels.createThree =
        subjectReply (CompositeChannels.created plan) CompositeChannels.createThree ∧
      subjectReply (CompositeChannels.seed plan) (.terminateSubject 3) =
        subjectReply (CompositeChannels.created plan) (.terminateSubject 3) ∧
      subjectReply (CompositeChannels.seed plan) (.scheduleAdd 3) =
        subjectReply (CompositeChannels.created plan) (.scheduleAdd 3) ∧
      LowEquiv 2 (subjectStep (CompositeChannels.offered plan) (.terminateSubject 3))
        (subjectStep (CompositeChannels.offeredCreated plan) (.terminateSubject 3)) ∧
      subjectReply (CompositeChannels.toSlotThree plan) CompositeUnwinding.Channels.delegateToOther =
        subjectReply (CompositeChannels.toSlotTwo plan)
          CompositeUnwinding.Channels.delegateToOther ∧
      subjectReply (CompositeChannels.toSlotThree plan) (.capabilityRevoke 0 1 2) =
        subjectReply (CompositeChannels.toSlotTwo plan) (.capabilityRevoke 0 1 2) ∧
      subjectReply (CompositeChannels.toSlotThree plan) (.capabilityRevokeSubtree 0 1 2) =
        subjectReply (CompositeChannels.toSlotTwo plan) (.capabilityRevokeSubtree 0 1 2) := by
  have created := (CompositeChannels.seed_created plan).toOwnStep
  have slots := (CompositeChannels.slotThree_slotTwo plan).toOwnStep
  have offered := (CompositeChannels.offered_offeredCreated plan).toOwnStep
  exact ⟨own_output_cross created _ rfl, own_output_cross created _ rfl,
    own_output_cross created _ rfl, own_step_cross offered _ rfl,
    own_output_cross slots _ rfl, own_output_cross slots _ rfl,
    own_output_cross slots _ rfl⟩

/-- **Subtree revocation of another subject's capability is closed.**  On the
pair of `CompositeSwitchedChannels.revokeSubtree_other_step_inconsistent`,
whose hidden derivation decided whether the observer's pending transfer was
cancelled, the subject gate refuses on both sides. -/
theorem revokeSubtree_other_closed (plan : BootPageTablePlan.Plan)
    (hplan : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan) :
    LowEquiv 2
      (subjectStep (CompositeSwitchedChannels.runFrom plan CompositeSwitchedChannels.leftTrace)
        CompositeSwitchedChannels.otherSubtree)
      (subjectStep (CompositeSwitchedChannels.runFrom plan CompositeSwitchedChannels.rightTrace)
        CompositeSwitchedChannels.otherSubtree) :=
  own_step_cross (CompositeSwitchedChannels.derivation_pair plan hplan).toOwnStep _ rfl

end LeanOS.CompositeSubjectGate
