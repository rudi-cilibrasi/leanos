/-!
# Replay unwinding for finite observer traces

This is the unwinding structure of `LeanOS.ScheduledObservation`, stated once
over an arbitrary deterministic system so that the scheduler-observation model
and the authoritative composite model share it instead of each re-proving it.

A `System` executes one step and emits at most one observer event.  The
unwinding obligation `Replays` has two halves, which correspond to the
classical conditions:

* **local respect** (`silent_unchanged`): a step that emits no event leaves the
  observer's view unchanged;
* **output-determined step consistency** (`visible_replays`): a step that does
  emit an event leaves the observer in exactly the view that the event names,
  so two runs that emit equal events end in equal views.

The conclusion `finite_trace_lowEquiv` is termination-insensitive finite-trace
noninterference: from low-equivalent initial states, runs whose observer event
projections are equal end in low-equivalent states, even when the runs contain
different numbers and choices of silent steps.

`ReplaysOn` relativizes the obligation to an invariant that every step
preserves (`Preserves`).  `finite_trace_lowEquiv_on` then needs the invariant
only of the two initial states; the unconditional `Replays` is the special
case of the trivial invariant (`replaysOn_true`).
-/
namespace LeanOS.ReplayUnwinding

structure System (State Step Event View : Type) where
  observe : State → View
  execute : State → Step → State × Option Event
  applyEvent : View → Event → View

variable {State Step Event View : Type} (system : System State Step Event View)

/-- Execute a finite list of steps, collecting the observer events in order. -/
def run : State → List Step → State × List Event
  | state, [] => (state, [])
  | state, step :: rest =>
      let outcome := system.execute state step
      let tail := run outcome.1 rest
      (tail.1, outcome.2.toList ++ tail.2)

/-- The observer-visible event projection of a finite run. -/
def projection (state : State) (steps : List Step) : List Event :=
  (run system state steps).2

def replay (initial : View) (events : List Event) : View :=
  events.foldl system.applyEvent initial

/-- Observer low equivalence is equality of the complete declared view. -/
def LowEquiv (left right : State) : Prop :=
  system.observe left = system.observe right

/-- The one-step unwinding obligation. -/
def Replays : Prop :=
  ∀ state step, system.observe (system.execute state step).1 =
    replay system (system.observe state) (system.execute state step).2.toList

/-- Local respect and output-determined step consistency together discharge
the one-step unwinding obligation. -/
theorem replays_of_unwinding
    (silent_unchanged : ∀ state step, (system.execute state step).2 = none →
      system.observe (system.execute state step).1 = system.observe state)
    (visible_replays : ∀ state step event, (system.execute state step).2 = some event →
      system.observe (system.execute state step).1 =
        system.applyEvent (system.observe state) event) :
    Replays system := by
  intro state step
  cases hevent : (system.execute state step).2 with
  | none => simpa [replay, hevent] using silent_unchanged state step hevent
  | some event => simpa [replay, hevent] using visible_replays state step event hevent

theorem run_replays (hreplays : Replays system) (state : State) (steps : List Step) :
    system.observe (run system state steps).1 =
      replay system (system.observe state) (run system state steps).2 := by
  induction steps generalizing state with
  | nil => simp [run, replay]
  | cons step rest ih =>
    simp only [run]
    rw [ih (system.execute state step).1, hreplays state step]
    simp [replay, List.foldl_append]

/-- **Finite-trace noninterference by unwinding.**  Low-equivalent initial
states and equal observer event projections give low-equivalent final states.
The runs may differ in the number and choice of silent steps, and nothing is
claimed about runs that do not terminate. -/
theorem finite_trace_lowEquiv (hreplays : Replays system) (left right : State)
    (leftSteps rightSteps : List Step) (hlow : LowEquiv system left right)
    (hevents : projection system left leftSteps = projection system right rightSteps) :
    LowEquiv system (run system left leftSteps).1 (run system right rightSteps).1 := by
  unfold LowEquiv at *
  rw [run_replays system hreplays left leftSteps, run_replays system hreplays right rightSteps]
  simp only [projection] at hevents
  rw [hlow, hevents]

/-! ## Unwinding relative to a trace invariant -/

/-- Every step preserves `invariant`. -/
def Preserves (invariant : State → Prop) : Prop :=
  ∀ state step, invariant state → invariant (system.execute state step).1

/-- The one-step unwinding obligation, required only of states satisfying
`invariant`. -/
def ReplaysOn (invariant : State → Prop) : Prop :=
  ∀ state step, invariant state → system.observe (system.execute state step).1 =
    replay system (system.observe state) (system.execute state step).2.toList

theorem replaysOn_true (hreplays : Replays system) :
    ReplaysOn system fun _ => True :=
  fun state step _ => hreplays state step

/-- Invariant-relative local respect and output-determined step consistency
discharge `ReplaysOn`. -/
theorem replaysOn_of_unwinding (invariant : State → Prop)
    (silent_unchanged : ∀ state step, invariant state →
      (system.execute state step).2 = none →
      system.observe (system.execute state step).1 = system.observe state)
    (visible_replays : ∀ state step event, invariant state →
      (system.execute state step).2 = some event →
      system.observe (system.execute state step).1 =
        system.applyEvent (system.observe state) event) :
    ReplaysOn system invariant := by
  intro state step hinvariant
  cases hevent : (system.execute state step).2 with
  | none => simpa [replay, hevent] using silent_unchanged state step hinvariant hevent
  | some event =>
      simpa [replay, hevent] using visible_replays state step event hinvariant hevent

theorem run_preserves {invariant : State → Prop} (hpreserves : Preserves system invariant)
    (state : State) (steps : List Step) (hstate : invariant state) :
    invariant (run system state steps).1 := by
  induction steps generalizing state with
  | nil => exact hstate
  | cons step rest ih => exact ih _ (hpreserves state step hstate)

theorem run_replays_on {invariant : State → Prop} (hreplays : ReplaysOn system invariant)
    (hpreserves : Preserves system invariant) (state : State) (steps : List Step)
    (hstate : invariant state) :
    system.observe (run system state steps).1 =
      replay system (system.observe state) (run system state steps).2 := by
  induction steps generalizing state with
  | nil => simp [run, replay]
  | cons step rest ih =>
    simp only [run]
    rw [ih (system.execute state step).1 (hpreserves state step hstate),
      hreplays state step hstate]
    simp [replay, List.foldl_append]

/-- **Finite-trace noninterference relative to a trace invariant.**  As
`finite_trace_lowEquiv`, but the unwinding obligation is needed only on states
satisfying an invariant that every step preserves, and the invariant is
assumed only of the two initial states. -/
theorem finite_trace_lowEquiv_on {invariant : State → Prop}
    (hreplays : ReplaysOn system invariant) (hpreserves : Preserves system invariant)
    (left right : State) (leftSteps rightSteps : List Step)
    (hleft : invariant left) (hright : invariant right)
    (hlow : LowEquiv system left right)
    (hevents : projection system left leftSteps = projection system right rightSteps) :
    LowEquiv system (run system left leftSteps).1 (run system right rightSteps).1 := by
  unfold LowEquiv at *
  rw [run_replays_on system hreplays hpreserves left leftSteps hleft,
    run_replays_on system hreplays hpreserves right rightSteps hright]
  simp only [projection] at hevents
  rw [hlow, hevents]

end LeanOS.ReplayUnwinding
