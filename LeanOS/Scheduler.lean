import LeanOS.SubjectLifecycle
import LeanOS.Syscall

/-!
# Bounded round-robin scheduler

An executable, single-core scheduler.  `ready` contains runnable subjects other
than `current`; dispatch removes its head and appends a yielded current subject
at the tail.  The queue is bounded by `capacity` and subject identity and
address-space ownership come from `SubjectLifecycle.State`.
-/
namespace LeanOS.Scheduler

open LeanOS
set_option linter.unusedSimpArgs false

abbrev SubjectId := SubjectLifecycle.SubjectId
abbrev AddressSpaceId := SubjectLifecycle.AddressSpaceId

structure State where
  lifecycle : SubjectLifecycle.State
  ready : List SubjectId
  capacity : Nat

def ownsAddressSpace (state : State) (subject : SubjectId) : Option AddressSpaceId :=
  if state.lifecycle.addressOwner subject = some subject then some subject else none

/-- Scheduler invariants composed with the lifecycle model. -/
def WellFormed (state : State) : Prop :=
  SubjectLifecycle.WellFormed state.lifecycle ∧
  state.ready.Nodup ∧ state.ready.length ≤ state.capacity ∧
  (∀ subject, subject ∈ state.ready →
    state.lifecycle.capabilities.subjects subject = true ∧
    state.lifecycle.runnable subject = true ∧ ownsAddressSpace state subject ≠ none) ∧
  (∀ subject, state.lifecycle.current = some subject →
    state.lifecycle.capabilities.subjects subject = true ∧
    state.lifecycle.runnable subject = true ∧ ownsAddressSpace state subject ≠ none ∧
    subject ∉ state.ready)

structure TrustedContext where
  currentSubject : SubjectId
  activeAddressSpace : AddressSpaceId
  deriving DecidableEq, Repr

inductive Error where
  | notLive | notRunnable | noAddressSpace | duplicate | queueFull
  | notQueued | noCurrent | lifecycle (reason : SubjectLifecycle.TerminateError)
  deriving DecidableEq, Repr

inductive Result where
  | accepted (context : Option TrustedContext := none)
  | rejected (reason : Error)
  deriving DecidableEq, Repr

structure Outcome where
  state : State
  result : Result

def reject (state : State) (reason : Error) : Outcome :=
  { state, result := .rejected reason }

def add (state : State) (subject : SubjectId) : Outcome :=
  if !state.lifecycle.capabilities.subjects subject then reject state .notLive
  else if !state.lifecycle.runnable subject then reject state .notRunnable
  else match ownsAddressSpace state subject with
    | none => reject state .noAddressSpace
    | some _ =>
      if state.lifecycle.current = some subject || subject ∈ state.ready then
        reject state .duplicate
      else if state.ready.length = state.capacity then reject state .queueFull
      else { state := { state with ready := state.ready ++ [subject] }, result := .accepted }

def remove (state : State) (subject : SubjectId) : Outcome :=
  if state.lifecycle.current = some subject || subject ∈ state.ready then
    { state := { state with
        ready := state.ready.filter (· ≠ subject)
        lifecycle := { state.lifecycle with
          runnable := SubjectLifecycle.setBool state.lifecycle.runnable subject false
          current := if state.lifecycle.current = some subject then none
            else state.lifecycle.current } },
      result := .accepted }
  else reject state .notQueued

/-- Select the head. Empty selection is deterministic and successful. -/
def selectNext (state : State) : Outcome :=
  match state.lifecycle.current, state.ready with
  | some _, _ => reject state .duplicate
  | none, [] => { state, result := .accepted none }
  | none, subject :: rest =>
    match ownsAddressSpace state subject with
    | none => reject state .noAddressSpace
    | some space =>
      { state := { state with
          ready := rest
          lifecycle := { state.lifecycle with current := some subject } },
        result := .accepted (some ⟨subject, space⟩) }

def yield (state : State) : Outcome :=
  match state.lifecycle.current with
  | none => reject state .noCurrent
  | some subject =>
    if state.ready.length = state.capacity then reject state .queueFull
    else
      match selectNext { state with
          ready := state.ready ++ [subject]
          lifecycle := { state.lifecycle with current := none } } with
      | { result := .rejected reason, .. } => reject state reason
      | outcome => outcome

/-- A timer tick is exactly one deterministic round-robin yield. -/
def tick (state : State) : Outcome := yield state

def terminateCurrent (state : State) : Outcome :=
  match state.lifecycle.current with
  | none => reject state .noCurrent
  | some subject =>
    match SubjectLifecycle.terminate state.lifecycle subject with
    | { result := .rejected reason, .. } => reject state (.lifecycle reason)
    | { state := lifecycle, result := .accepted } =>
      { state := { state with
          lifecycle := lifecycle
          ready := state.ready.filter (· ≠ subject) }, result := .accepted }

theorem add_rejected_unchanged state subject reason
    (h : (add state subject).result = .rejected reason) :
    (add state subject).state = state := by
  simp only [add] at h ⊢
  split <;> simp_all [reject]
  split <;> simp_all [reject]
  split <;> simp_all [reject]
  next space =>
    split <;> simp_all [reject]
    split <;> simp_all [reject]

theorem remove_rejected_unchanged state subject reason
    (h : (remove state subject).result = .rejected reason) :
    (remove state subject).state = state := by
  simp only [remove] at h ⊢
  split <;> simp_all [reject]

theorem select_rejected_unchanged state reason
    (h : (selectNext state).result = .rejected reason) :
    (selectNext state).state = state := by
  simp only [selectNext] at h ⊢
  split <;> simp_all [reject]
  next => split <;> simp_all [reject]

theorem yield_rejected_unchanged state reason
    (h : (yield state).result = .rejected reason) :
    (yield state).state = state := by
  unfold yield at h ⊢
  split
  · simp_all [reject]
  next =>
    rename_i subject heq
    split
    · simp_all [reject]
    generalize hs : selectNext { state with
      ready := state.ready ++ [subject]
      lifecycle := { state.lifecycle with current := none } } = outcome
    cases outcome with
    | mk next result =>
      cases result <;> simp_all [reject]

theorem tick_rejected_unchanged state reason
    (h : (tick state).result = .rejected reason) :
    (tick state).state = state :=
  yield_rejected_unchanged state reason h

theorem terminateCurrent_rejected_unchanged state reason
    (h : (terminateCurrent state).result = .rejected reason) :
    (terminateCurrent state).state = state := by
  unfold terminateCurrent at h ⊢
  split
  · simp_all [reject]
  next subject hcurrent =>
    generalize ht : SubjectLifecycle.terminate state.lifecycle subject = outcome at h ⊢
    cases outcome with
    | mk next result =>
      cases result with
      | accepted => simp_all [reject]
      | rejected lifecycleReason =>
        have unchanged := SubjectLifecycle.terminate_rejected_unchanged
          state.lifecycle subject lifecycleReason (by simp [ht])
        simp_all [reject]

theorem add_preserves_wellFormed state subject (hwf : WellFormed state) :
    WellFormed (add state subject).state := by
  simp only [add]
  split <;> simp_all [reject]
  split <;> simp_all [reject]
  split
  · simp_all [reject]
  next space hspace =>
    split <;> simp_all [reject]
    split <;> simp_all [reject]
    simp_all [WellFormed, ownsAddressSpace]
    grind

theorem remove_preserves_wellFormed state subject (hwf : WellFormed state) :
    WellFormed (remove state subject).state := by
  simp only [remove]
  split <;> simp_all [reject]
  simp_all [WellFormed, SubjectLifecycle.WellFormed,
    SubjectLifecycle.setBool, ownsAddressSpace]
  grind

theorem selectNext_preserves_wellFormed state (hwf : WellFormed state) :
    WellFormed (selectNext state).state := by
  simp only [selectNext]
  split <;> simp_all [reject]
  split <;> simp_all [reject]
  all_goals grind [WellFormed, SubjectLifecycle.WellFormed, ownsAddressSpace]

theorem yield_preserves_wellFormed state (hwf : WellFormed state) :
    WellFormed (yield state).state := by
  simp only [yield]
  split <;> simp_all [reject]
  next hcurrent subject =>
    split
    · simp_all [reject]
    next hcapacity =>
      have rotated : WellFormed { state with
        ready := state.ready ++ [hcurrent]
        lifecycle := { state.lifecycle with current := none } } := by
        simp_all [WellFormed, SubjectLifecycle.WellFormed, ownsAddressSpace]
        grind
      generalize hs : selectNext { state with
        ready := state.ready ++ [hcurrent]
        lifecycle := { state.lifecycle with current := none } } = outcome
      cases outcome with
      | mk next result =>
        have preserved := selectNext_preserves_wellFormed _ rotated
        rw [hs] at preserved
        cases result <;> simp_all [reject]

theorem tick_preserves_wellFormed state (hwf : WellFormed state) :
    WellFormed (tick state).state :=
  yield_preserves_wellFormed state hwf

theorem terminateCurrent_preserves_wellFormed state (hwf : WellFormed state) :
    WellFormed (terminateCurrent state).state := by
  simp only [terminateCurrent]
  split <;> simp_all [reject]
  next subject hcurrent =>
    generalize ht : SubjectLifecycle.terminate state.lifecycle subject = outcome
    cases outcome with
    | mk lifecycle result =>
      cases result with
      | rejected reason => simp_all [reject]
      | accepted =>
        have heq : lifecycle = SubjectLifecycle.terminateState state.lifecycle subject := by
          grind [SubjectLifecycle.terminate, SubjectLifecycle.reject]
        subst lifecycle
        have hlifecycle := SubjectLifecycle.terminateState_preserves_wellFormed
          state.lifecycle subject hwf.1
        simp_all [WellFormed, SubjectLifecycle.terminateState,
          SubjectLifecycle.terminatedCapabilities, SubjectLifecycle.setBool,
          ownsAddressSpace]
        grind

/-- A returned dispatch context is exactly the selected current subject and an
address space owned by that subject; neither value is a transition argument. -/
theorem dispatch_context_safe state next context
    (h : (selectNext state).result = .accepted (some context))
    (hnext : (selectNext state).state = next) :
    next.lifecycle.current = some context.currentSubject ∧
      state.lifecycle.addressOwner context.activeAddressSpace =
        some context.currentSubject := by
  grind [selectNext, ownsAddressSpace, reject]

/-- Well-formed queue membership makes the selected subject live and runnable. -/
theorem dispatch_selects_live_runnable state context
    (hwf : WellFormed state)
    (h : (selectNext state).result = .accepted (some context)) :
    state.lifecycle.capabilities.subjects context.currentSubject = true ∧
      state.lifecycle.runnable context.currentSubject = true := by
  grind [selectNext, WellFormed, reject]

theorem termination_cleanup (state : State) (subject : SubjectId) :
    subject ∉ state.ready.filter (· ≠ subject) ∧
      (SubjectLifecycle.terminateState state.lifecycle subject).current ≠ some subject := by
  simp [SubjectLifecycle.terminateState]

/-- Execute a finite sequence of scheduler transitions.  This is scheduler-step
progress only: callers must assume ticks continue, the runnable set stays fixed,
and no subject blocks during the execution. -/
def runTransitions : Nat → State → State
  | 0, state => state
  | steps + 1, state =>
      let outcome := if state.lifecycle.current.isSome then tick state else selectNext state
      runTransitions steps outcome.state

/-- Queue membership gives a finite round-robin position strictly below the
documented capacity.  Under a fixed runnable set and repeated select/yield
steps, one head is consumed per step, so this is the scheduler-step bound. -/
theorem bounded_progress_position (state : State) (subject : SubjectId)
    (hwf : WellFormed state) (member : subject ∈ state.ready) :
    ∃ before after, state.ready = before ++ subject :: after ∧
      before.length < state.capacity := by
  rw [List.mem_iff_append] at member
  obtain ⟨before, after, hs⟩ := member
  refine ⟨before, after, hs, ?_⟩
  have hlen := hwf.2.2.1
  rw [hs] at hlen
  simp at hlen
  omega

/-- The executable dispatch order contains every continuously runnable queued
subject at an index below the fixed capacity.  With a fixed queue and one
round-robin scheduling step per index, this is the finite selection bound. -/
theorem bounded_round_robin_selection (state : State) (subject : SubjectId)
    (hwf : WellFormed state) (member : subject ∈ state.ready) :
    ∃ steps, steps < state.capacity ∧ state.ready[steps]? = some subject := by
  obtain ⟨before, after, hs, hbound⟩ :=
    bounded_progress_position state subject hwf member
  refine ⟨before.length, hbound, ?_⟩
  simp [hs]

private def live : SubjectLifecycle.State :=
  { capabilities := {
      subjects := fun s => s < 3
      objects := fun _ => false
      kinds := fun _ => none
      slots := fun _ _ => none }
    issuedSubjects := fun s => s < 3
    ownedMemory := fun _ => none
    addressOwner := fun a => if a < 3 then some a else none
    mapping := fun _ _ => none
    endpointOwner := fun _ => none
    mailbox := fun _ => none
    frameOwner := fun _ => none
    freeFrame := fun _ => true
    runnable := fun s => s < 3
    current := none }

private def empty : State := { lifecycle := live, ready := [], capacity := 3 }
private def single : State := { lifecycle := live, ready := [1], capacity := 3 }
private def many : State := { lifecycle := live, ready := [0, 1, 2], capacity := 3 }

example : (selectNext empty).result = .accepted none := by native_decide
example : (selectNext single).result = .accepted (some ⟨1, 1⟩) := by native_decide
example : ((selectNext many).state.lifecycle.current) = some 0 := by native_decide
example : (yield (selectNext many).state).state.lifecycle.current = some 1 := by native_decide
example : (tick (yield (selectNext many).state).state).state.lifecycle.current = some 2 := by
  native_decide
/-- An executable repeated-transition witness: with a fixed three-subject queue
and continuing scheduler steps, every subject is dispatched within one round. -/
theorem many_selected_within_one_round :
    (runTransitions 1 many).lifecycle.current = some 0 ∧
    (runTransitions 2 many).lifecycle.current = some 1 ∧
    (runTransitions 3 many).lifecycle.current = some 2 := by
  native_decide
example : (add many 1).result = .rejected .duplicate := by native_decide
example : (add empty 9).result = .rejected .notLive := by native_decide
example : (terminateCurrent (selectNext many).state).state.ready = [1, 2] := by native_decide
example : (yield { many with lifecycle := { live with current := some 2 }, ready := [0, 1] }).state.ready =
    [1, 2] := by native_decide

end LeanOS.Scheduler
