import LeanOS.CompositeFullIsolation

/-!
# Finite traces on the full view

Local respect and the finite-trace theorem for the full view
(`LeanOS.CompositeFullView`) over the subject gate.

**Silence** (`isSilentFull`).  A request is silent for the observer when the
subject gate refuses it (no effect), or when it is silent for the view
(`CompositeLocalRespect.isSilentExtended`) and it touches no object the
observer is offered (`quietFull`): another subject's kernel entries, memory
operations, scheduler operations, delegation and direct revocation of another
subject's capability, and data IPC on an endpoint the observer neither names
nor is offered.  Every other request is visible: its event carries the
observer's full view afterwards.
-/
namespace LeanOS.CompositeFullTrace

open LeanOS
open LeanOS.FailStop
open LeanOS.CompositeObservation
open LeanOS.CompositeUnwinding
open LeanOS.CompositeOwnSteps
open LeanOS.CompositeLocalRespect
open LeanOS.CompositeSubjectGate
open LeanOS.CompositeFullView
open LeanOS.CompositeFullSteps
set_option linter.unusedSimpArgs false

/-- The authority is unchanged by a step that extends the derivation history,
keeps the row and every pending transfer, and keeps the view of every object
the observer is offered. -/
theorem extra_eq_of_carried {observer : Nat} {before after : CompositeState}
    (hissued : Issued before)
    (hextends : ∀ index, index < before.capabilities.nextIdentity →
      after.capabilities.derivations index = before.capabilities.derivations index)
    (hrow : row after observer = row before observer)
    (hpending : after.transfers.pending = before.transfers.pending)
    (hcarried : ∀ object, Carried before observer object = true →
      objectView after object = objectView before object) :
    extra observer after = extra observer before := by
  unfold extra
  rw [hrow]
  apply List.map_congr_left
  intro slot hmem
  cases slot with
  | none => rfl
  | some cap =>
      simp only [Option.map_some, Option.some.injEq, slotExtra, SlotExtra.mk.injEq, hpending]
      refine ⟨lineage_of_extends _ _ hissued.precede hextends _ (hissued.row hmem), ?_⟩
      cases hcase : before.transfers.pending cap.object with
      | none => rfl
      | some transfer =>
          simp only [Option.map_some, Option.some.injEq, carriedView, CarriedView.mk.injEq,
            hpending]
          refine ⟨lineage_of_extends _ _ hissued.precede hextends _
            (hissued.pending _ _ hcase), hcarried _ (carried_of_mem hmem hcase), ?_⟩
          cases hnested : before.transfers.pending transfer.object with
          | none => rfl
          | some nested =>
              simp only [Option.map_some, Option.some.injEq]
              exact lineage_of_extends _ _ hissued.precede hextends _
                (hissued.pending _ _ hnested)

theorem extra_eq_of_unchanged {observer : Nat} {before after : CompositeState}
    (hissued : Issued before) (hunchanged : Unchanged before after) :
    extra observer after = extra observer before :=
  extra_eq_of_carried hissued (fun index _ => by rw [hunchanged.capabilities])
    (hunchanged.row observer) hunchanged.pending fun object _ => hunchanged.objects object

/-- Requests that touch no object the observer is offered. -/
def quietFull (observer : Nat) (state : CompositeState) : AuthoritativeOperation → Bool
  | .ordinary operation =>
      match operation with
      | .ipc call =>
          match ipcTarget state call with
          | none => true
          | some object => !Carried state observer object
      | .capabilityCopy _ _ _ _ | .capabilityRevoke _ _ _ | .interrupt _ => true
      | operation => unchangedFamily operation
  | _ => false

/-- Silence on the full view. -/
def isSilentFull (observer : Nat) (state : CompositeState)
    (operation : AuthoritativeOperation) : Bool :=
  (state.refusal operation).isSome ||
    (isSilentExtended observer state operation && quietFull observer state operation)

/-- The capability store after an accepted delegation extends the history. -/
theorem copy_extends (a : Capability.State) actor source destination destinationSlot
    (rights : Capability.Rights) :
    ∀ index, index < a.nextIdentity →
      (Capability.copy a actor source destination destinationSlot rights).state.derivations
        index = a.derivations index := by
  intro index hindex
  have hne : index ≠ a.nextIdentity := Nat.ne_of_lt hindex
  simp only [Capability.copy]
  repeat' split
  all_goals simp_all [Capability.reject, Capability.install]

/-- Local respect for the authority: an ordinary request silent on the full
view leaves `extra` unchanged. -/
theorem extra_apply_silent (observer : Nat) (state : CompositeState)
    (hstate : AuthoritativeRuntimeWellFormed state) (operation : Operation)
    (hsilent : isSilentExtendedOrdinary observer state operation = true)
    (hquiet : quietFull observer state (.ordinary operation) = true) :
    extra observer (applyOperation state operation) = extra observer state := by
  have hcoherent := coherent_of hstate
  have hissued := issued_of_runtime hstate.left
  cases operation with
  | interrupt frame =>
      simp only [isSilentExtendedOrdinary, Bool.and_eq_true] at hsilent
      exact extra_eq_of_unchanged hissued (unchanged_apply_interrupt state hcoherent frame hsilent.2)
  | ipc call =>
      have hframe := frame_apply_ipc state hcoherent call
      apply extra_eq_of_carried hissued hframe.1.extends_
        (by simp only [CompositeObservation.row, hframe.2]) hframe.1.pending
      intro object hcarried
      simp only [applyOperation]
      have hinstall : ∀ ipc : IPCSyscall.State,
          (∀ object, ipcTarget state call ≠ some object →
            ipc.endpoints.mailbox object = state.ipc.endpoints.mailbox object) →
          objectView (installIPC state ipc) object = objectView state object := by
        intro ipc hmailbox
        rw [objectView_installIPC, hmailbox object]
        · rfl
        · intro htarget
          simp only [quietFull, htarget, Bool.not_eq_true'] at hquiet
          rw [hquiet] at hcarried
          cases hcarried
      have hdispatch := hinstall _ fun object hne => ipcDispatch_mailbox_other state call object hne
      cases call with
      | send handleWord word0 word1 =>
          simp only [dispatchIPC]
          split <;> first | rfl | exact hdispatch
      | receive handleWord =>
          split
          all_goals first | rfl | skip
          all_goals
            simp only [dispatchIPC]
            repeat' split
            all_goals first | rfl | exact hdispatch | skip
  | capabilityCopy source destination destinationSlot rights =>
      simp only [isSilentExtendedOrdinary, isSilentCoherentOrdinary, isSilentOrdinary,
        Bool.and_eq_true, bne_iff_ne, ne_eq] at hsilent
      obtain ⟨hsubjects, hcapacity, hslots, hobjects, hkinds⟩ :=
        copy_frame state.capabilities state.execution.core.context.currentSubject source
          destination destinationSlot rights observer hsilent.2
      simp only [applyOperation]
      split
      · rfl
      · apply extra_eq_of_carried hissued
          (copy_extends state.capabilities _ source destination destinationSlot rights)
        · simp only [CompositeObservation.row, Capability.capabilitySpace, installCopiedCapabilities,
            hcapacity, hslots]
        · rfl
        · intro object _
          rw [objectView_installCopiedCapabilities, hobjects, hkinds]; rfl
  | capabilityRevoke authoritySlot victim victimSlot =>
      simp only [isSilentExtendedOrdinary, isSilentCoherentOrdinary, isSilentOrdinary,
        Bool.and_eq_true, bne_iff_ne, ne_eq] at hsilent
      obtain ⟨hsubjects, hcapacity, hslots, hobjects, hkinds⟩ :=
        revokeRuntimeSafe_frame state.capabilities state.execution.core.context.currentSubject
          authoritySlot victim victimSlot observer hsilent.2
      obtain ⟨hderivations, _⟩ := revokeRuntimeSafe_store state.capabilities
        state.execution.core.context.currentSubject authoritySlot victim victimSlot
      simp only [applyOperation]
      split
      · rfl
      · apply extra_eq_of_carried hissued
          (fun index _ => by simp only [installCopiedCapabilities, hderivations])
        · simp only [CompositeObservation.row, Capability.capabilitySpace, installCopiedCapabilities,
            hcapacity, hslots]
        · rfl
        · intro object _
          rw [objectView_installCopiedCapabilities, hobjects, hkinds]; rfl
  | _ =>
      first
        | exact extra_eq_of_unchanged hissued (unchanged_apply state hcoherent _ hquiet)
        | simp [quietFull, unchangedFamily] at hquiet

/-- **Local respect on the full view over the subject gate.** -/
theorem subjectGate_silent_full (observer : Nat) (state : CompositeState)
    (operation : AuthoritativeOperation) (hstate : AuthoritativeRuntimeWellFormed state)
    (hsilent : isSilentFull observer state operation = true) :
    FullLowEquiv observer (subjectGate state operation).state state := by
  rcases subjectGate_cases state operation with ⟨_, _, hsame, _⟩ | ⟨hnone, hgate, _⟩
  · rw [hsame]; rfl
  · simp only [isSilentFull, hnone, Option.isSome_none, Bool.false_or, Bool.and_eq_true]
      at hsilent
    obtain ⟨hextended, hquiet⟩ := hsilent
    rw [hgate]
    have hlow := authoritativeGate_silentExtended_observe observer state operation hstate
      hextended
    apply fullLowEquiv_of hlow
    cases operation with
    | ordinary operation =>
        rw [authoritativeGate_ordinary_state]
        rcases gate_state_cases state operation with hsame | happly
        · rw [hsame]
        · rw [happly]
          exact extra_apply_silent observer state hstate operation hextended hquiet
    | blocking operation => simp [quietFull] at hquiet
    | drainDeferred subject => simp [quietFull] at hquiet

/-! ## The trace theorem -/

/-- One observer event on the full view. -/
structure Event where
  view : FullView
  reply : Option SubjectGateResult

def execute (observer : Nat) (state : CompositeState) (operation : AuthoritativeOperation) :
    CompositeState × Option Event :=
  let outcome := subjectGate state operation
  (outcome.state,
    if isSilentFull observer state operation then none
    else some
      { view := observeFull observer outcome.state
        reply := if actor state = observer then some outcome.result else none })

def system (observer : Nat) :
    ReplayUnwinding.System CompositeState AuthoritativeOperation Event FullView where
  observe := observeFull observer
  execute := execute observer
  applyEvent _ event := event.view

def run (observer : Nat) (state : CompositeState) (operations : List AuthoritativeOperation) :
    CompositeState × List Event :=
  ReplayUnwinding.run (system observer) state operations

def projection (observer : Nat) (state : CompositeState)
    (operations : List AuthoritativeOperation) : List Event :=
  ReplayUnwinding.projection (system observer) state operations

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
      exact subjectGate_silent_full observer state operation hstate hsilent
    · simp at hnone
  · intro state operation event _ hsome
    simp only [system, execute] at hsome ⊢
    split at hsome
    · simp at hsome
    · simp only [Option.some.injEq] at hsome
      rw [← hsome]

/-- **Finite-trace noninterference on the full view over the subject gate.** -/
theorem finite_trace_full (observer : Nat) (left right : CompositeState)
    (leftOperations rightOperations : List AuthoritativeOperation)
    (hleft : AuthoritativeRuntimeWellFormed left)
    (hright : AuthoritativeRuntimeWellFormed right)
    (hlow : FullLowEquiv observer left right)
    (hevents : projection observer left leftOperations =
      projection observer right rightOperations) :
    FullLowEquiv observer (run observer left leftOperations).1
      (run observer right rightOperations).1 :=
  ReplayUnwinding.finite_trace_lowEquiv_on (system observer) (system_replaysOn observer)
    (fun state operation hstate =>
      subjectGate_preserves_authoritativeRuntimeWellFormed state operation hstate)
    left right leftOperations rightOperations hleft hright hlow hevents

end LeanOS.CompositeFullTrace
