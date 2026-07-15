import LeanOS.Observation
import LeanOS.Scheduler

/-!
# Observer isolation for finite scheduled traces

This module composes the scheduler's authoritative current subject/address
space with the observation model.  Actor requests carry claimed context only
so stale adapters can be rejected; accepted execution uses the context derived
from `Scheduler.State`.
-/
namespace LeanOS.ScheduledObservation

open LeanOS
set_option linter.unusedSimpArgs false

abbrev SubjectId := Scheduler.SubjectId
abbrev AddressSpaceId := Scheduler.AddressSpaceId

structure State where
  scheduler : Scheduler.State
  observation : Observation.State

/-- There is one authoritative current subject: the scheduler.  The legacy
observation field is maintained only as a proved projection adapter. -/
def AdapterAgrees (state : State) : Prop :=
  state.observation.schedulerCurrent = state.scheduler.lifecycle.current ∧
    state.observation.live = state.scheduler.lifecycle.capabilities.subjects

def observe (observer : SubjectId) (state : State) : Observation.View :=
  { Observation.observe observer state.observation with
    live := state.scheduler.lifecycle.capabilities.subjects observer
    schedulerCurrent := state.scheduler.lifecycle.current }

def LowEquiv (observer : SubjectId) (left right : State) : Prop :=
  observe observer left = observe observer right

inductive SchedulerOp where
  | select | tick | terminate
  deriving Repr

inductive Step where
  | actor (claimedSubject : SubjectId) (claimedSpace : AddressSpaceId)
      (operation : Observation.Step)
  | scheduler (operation : SchedulerOp)
  deriving Repr

inductive Reject where
  | noCurrent | staleSubject | staleAddressSpace | nonActorOperation
  deriving DecidableEq, Repr

inductive Event where
  | rejected (reason : Reject)
  | visible (view : Observation.View)

structure Outcome where
  state : State
  event : Option Event

def actorOf : Observation.Step → Option SubjectId
  | .privateWrite actor _ _ | .sharedWrite actor _ _ | .map actor _ _ |
      .unmap actor _ | .access actor _ | .boundedCopy actor _ _ |
      .delegate actor _ _ _ | .revoke actor _ _ | .reject actor _ |
      .send actor _ _ _ _ | .receive actor | .allocate actor => some actor
  | .schedule _ => none

def isSilent (observer : SubjectId) : Observation.Step → Bool
  | .privateWrite actor _ _ | .map actor _ _ | .unmap actor _ |
      .access actor _ | .boundedCopy actor _ _ | .reject actor _ |
      .receive actor => observer != actor
  | .delegate _ recipient _ _ => observer != recipient
  | .revoke _ victim _ => observer != victim
  | .send actor recipient _ _ _ => observer != actor && observer != recipient
  | .sharedWrite _ _ _ | .allocate _ | .schedule _ => false

theorem isSilent_iff observer operation :
    isSilent observer operation = true ↔ Observation.SilentFor observer operation := by
  cases operation <;> simp [isSilent, Observation.SilentFor]

def sync (scheduler : Scheduler.State) (observation : Observation.State) : State :=
  { scheduler
    observation := { observation with
      live := scheduler.lifecycle.capabilities.subjects
      schedulerCurrent := scheduler.lifecycle.current } }

def schedulerStep (state : State) : SchedulerOp → State
  | .select => sync (Scheduler.selectNext state.scheduler).state state.observation
  | .tick => sync (Scheduler.tick state.scheduler).state state.observation
  | .terminate => sync (Scheduler.terminateCurrent state.scheduler).state state.observation

def actorResult (state : State) (claimedSubject : SubjectId)
    (claimedSpace : AddressSpaceId) (operation : Observation.Step) :
    Except Reject State :=
  match actorOf operation with
  | none => .error .nonActorOperation
  | some actor =>
    match state.scheduler.lifecycle.current with
    | none => .error .noCurrent
    | some current =>
      if actor != claimedSubject || claimedSubject != current then
        .error .staleSubject
      else if Scheduler.ownsAddressSpace state.scheduler current != some claimedSpace then
        .error .staleAddressSpace
      else .ok (sync state.scheduler (Observation.transition state.observation operation))

/-- Execute one request and classify exactly the declared low event.  An
unrelated private actor operation is silent; scheduling, rejection, IPC,
sharing, capability, and resource effects are retained. -/
def executeOne (observer : SubjectId) (state : State) : Step → Outcome
  | .scheduler operation =>
      let next := schedulerStep state operation
      { state := next, event := some (.visible (observe observer next)) }
  | .actor subject space operation =>
      match actorResult state subject space operation with
      | .error reason => { state, event := some (.rejected reason) }
      | .ok next =>
        if isSilent observer operation then { state := next, event := none }
        else { state := next, event := some (.visible (observe observer next)) }

def run (observer : SubjectId) : State → List Step → State × List Event
  | state, [] => (state, [])
  | state, step :: rest =>
      let outcome := executeOne observer state step
      let tail := run observer outcome.state rest
      (tail.1, outcome.event.toList ++ tail.2)

def applyEvent (prior : Observation.View) : Event → Observation.View
  | .rejected _ => prior
  | .visible view => view

def replay (initial : Observation.View) (events : List Event) : Observation.View :=
  events.foldl applyEvent initial

theorem sync_agrees scheduler observation : AdapterAgrees (sync scheduler observation) := by
  simp [AdapterAgrees, sync]

/-- An accepted actor request names exactly the selected subject and that
subject's scheduler-derived owned address space. -/
theorem accepted_actor_uses_current_owned_space state subject space operation next
    (h : actorResult state subject space operation = .ok next) :
    state.scheduler.lifecycle.current = some subject ∧
      Scheduler.ownsAddressSpace state.scheduler subject = some space := by
  simp only [actorResult] at h
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all

theorem noncurrent_actor_rejected state subject space operation current
    (hc : state.scheduler.lifecycle.current = some current) (hne : subject ≠ current) :
    ∃ reason, actorResult state subject space operation = .error reason := by
  simp [actorResult, hc, hne]
  cases hactor : actorOf operation <;> simp [hactor, hc, hne]

theorem silent_actor_observe_unchanged observer state subject space operation next
    (hr : actorResult state subject space operation = .ok next)
    (hs : Observation.SilentFor observer operation) :
    observe observer next = observe observer state := by
  have hn : next = sync state.scheduler
      (Observation.transition state.observation operation) := by
    grind [actorResult]
  subst next
  have hv := Observation.silent_observe_unchanged observer state.observation operation hs
  apply Observation.View.ext
  · simp [observe, sync, Observation.observe]
  · simpa [observe, sync, Observation.observe] using congrArg Observation.View.held hv
  · simpa [observe, sync, Observation.observe] using
      congrArg Observation.View.authorizedBytes hv
  · simpa [observe, sync, Observation.observe] using
      congrArg Observation.View.sharedBytes hv
  · simpa [observe, sync, Observation.observe] using
      congrArg Observation.View.ownedMappings hv
  · simpa [observe, sync, Observation.observe] using congrArg Observation.View.reply hv
  · simpa [observe, sync, Observation.observe] using
      congrArg Observation.View.deliveries hv
  · simp [observe, sync]

theorem executeOne_replays observer state step :
    observe observer (executeOne observer state step).state =
      replay (observe observer state) (executeOne observer state step).event.toList := by
  cases step with
  | scheduler operation => simp [executeOne, replay, applyEvent]
  | actor subject space operation =>
    simp only [executeOne]
    split
    · simp [replay, applyEvent]
    next next hr =>
      split
      · rename_i hs
        have silent := (isSilent_iff observer operation).1 hs
        simpa [replay] using
          silent_actor_observe_unchanged observer state subject space operation next hr silent
      · simp [replay, applyEvent]

theorem run_replays observer state steps :
    observe observer (run observer state steps).1 =
      replay (observe observer state) (run observer state steps).2 := by
  induction steps generalizing state with
  | nil => simp [run, replay]
  | cons step rest ih =>
    simp only [run]
    generalize ho : executeOne observer state step = outcome
    cases outcome with
    | mk next event =>
      rw [ih next]
      have hone := executeOne_replays observer state step
      rw [ho] at hone
      cases event <;> simp [replay, applyEvent] at hone ⊢
      · rw [hone]
      · rw [hone]

def projection (observer : SubjectId) (state : State) (steps : List Step) : List Event :=
  (run observer state steps).2

/-- Termination-insensitive finite-prefix isolation.  Runs may contain
different numbers and choices of silent steps.  Equal declared event
projections (which retain public schedules, replies, deliveries, sharing,
capability and resource outcomes) imply equal final observer views. -/
theorem finite_trace_lowEquiv observer left right leftSteps rightSteps
    (_hlow : LowEquiv observer left right)
    (hevents : projection observer left leftSteps =
      projection observer right rightSteps) :
    LowEquiv observer (run observer left leftSteps).1 (run observer right rightSteps).1 := by
  unfold LowEquiv at *
  rw [run_replays observer left leftSteps, run_replays observer right rightSteps]
  simp only [projection] at hevents
  rw [_hlow, hevents]

private def lifecycle (current : Option SubjectId) : SubjectLifecycle.State :=
  { capabilities := {
      subjects := fun subject => subject < 2
      objects := fun _ => false
      kinds := fun _ => none
      slots := fun _ _ => none }
    issuedSubjects := fun subject => subject < 2
    ownedMemory := fun _ => none
    addressOwner := fun space => if space < 2 then some space else none
    mapping := fun _ _ => none
    endpointOwner := fun _ => none
    mailbox := fun _ => none
    frameOwner := fun _ => none
    freeFrame := fun _ => true
    runnable := fun subject => subject < 2
    current }

private def scheduler : Scheduler.State :=
  { lifecycle := lifecycle (some 1), ready := [0], capacity := 2 }

private def localState (secret : Nat) (resources : Nat := 1) : Observation.State :=
  { live := fun subject => subject < 2
    held := fun _ _ => none
    authorizedBytes := fun _ _ => 0
    sharedBytes := fun _ => 0
    ownedMappings := fun _ _ => none
    reply := fun _ => .none
    deliveries := fun _ => []
    privateSecret := fun subject => if subject = 1 then secret else 0
    resourcesRemaining := resources
    schedulerCurrent := some 1 }

private def pairedLeft : State := { scheduler, observation := localState 7 }
private def pairedRight : State := { scheduler, observation := localState 99 }

private def leftTrace : List Step :=
  [.actor 1 1 (.privateWrite 1 4 0xaa),
   .actor 1 1 (.map 1 8 { read := true }),
   .actor 1 1 (.boundedCopy 1 12 [1, 2]),
   .actor 1 1 (.reject 1 9),
   .actor 1 1 (.send 1 1 2 0x41 0x42),
   .scheduler .tick,
   .scheduler .tick]

private def rightTrace : List Step :=
  [.actor 1 1 (.privateWrite 1 4 0xbb),
   .actor 1 1 (.unmap 1 9),
   .scheduler .tick,
   .scheduler .tick]

/-- Executable paired traces include private writes, mappings, copies,
unrelated IPC, multiple dispatches, and two extra silent steps on the left. -/
example : projection 0 pairedLeft leftTrace = projection 0 pairedRight rightTrace := by
  rfl

example : LowEquiv 0 (run 0 pairedLeft leftTrace).1 (run 0 pairedRight rightTrace).1 := by
  apply finite_trace_lowEquiv 0 pairedLeft pairedRight leftTrace rightTrace
  · rfl
  · rfl

/-- Stale subject and address-space adapters are executable negative
regressions: neither can reach the accepted transition. -/
example : actorResult pairedLeft 0 1 (.privateWrite 0 0 1) = .error .staleSubject := by
  rfl
example : actorResult pairedLeft 1 0 (.privateWrite 1 0 1) = .error .staleAddressSpace := by
  rfl

/-- Public schedules, shared writes, observer-directed capabilities and IPC,
resource results, and observed termination remain in the projection. -/
example : projection 0 pairedLeft [] ≠ projection 0 pairedLeft [.scheduler .tick] := by
  simp [projection, run, executeOne]
example : (executeOne 0 pairedLeft
    (.actor 1 1 (.sharedWrite 1 4 1))).state.observation.sharedBytes 4 = 1 := by rfl
example : (executeOne 0 pairedLeft (.actor 1 1
    (.delegate 1 0 3 { read := true }))).state.observation.held 0 3 =
      some { read := true } := by rfl
private def delegated : State :=
  { pairedLeft with observation :=
      { pairedLeft.observation with
        held := Observation.set2 pairedLeft.observation.held 0 3
          (some { read := true }) } }
example : (executeOne 0 delegated
    (.actor 1 1 (.revoke 1 0 3))).state.observation.held 0 3 = none := by rfl
example : (executeOne 0 pairedLeft
    (.actor 1 1 (.send 1 0 2 1 2))).state.observation.deliveries 0 =
      [{ handle := 2, sender := 1, word0 := 1, word1 := 2 }] := by rfl
example : (executeOne 0
    { pairedLeft with observation := localState 7 0 }
    (.actor 1 1 (.allocate 1))).state.observation.reply 1 = .exhausted := by rfl

private def fullMailbox : State :=
  { pairedLeft with observation :=
      { pairedLeft.observation with
        deliveries := Observation.set1 pairedLeft.observation.deliveries 0
          [{ handle := 2, sender := 1, word0 := 8, word1 := 9 }] } }

example : (executeOne 0 fullMailbox
    (.actor 1 1 (.send 1 0 2 1 2))).state.observation.reply 1 = .ipcFull := by rfl
example : (executeOne 1 pairedLeft
    (.scheduler .terminate)).state.observation.live 1 = false := by rfl

end LeanOS.ScheduledObservation
