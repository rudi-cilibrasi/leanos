import LeanOS.FailStop
import LeanOS.CompositeDispatcher

/-!
# The composite dispatcher under the resource invariant

`CompositeDispatcher` replays one canonical trace of `FailStop.authoritativeGate`
steps from `initialState`, which is `bootRuntime plan`.  Its first command,
`createSubjectOne`, is caller-identity creation `Operation.createSubject 1`.
`CompositeStep.Admissible` admits that step only when `0 < 1` and `1` is below
the subject counter (`authoritativeGate_createSubject_requires_bound`), but
`bootRuntime` carries the default subject issuer `{ next := 1 }`.  So the
dispatcher's first step ran outside the premise of `composite_resource_trace`
(the gap recorded in ADR 0010's 2026-10-10 gate row for #499).

This module closes that gap without changing the dispatcher.

**The resource view.**  `resourceView state` is `state` with the subject
counter set to `2`, the first identity above the one the dispatcher creates.
No authoritative operation reads or writes the issuers
(`AuthoritativeOperation.footprint_unread_resources`), so the gate commutes
with the view (`authoritativeGate_resourceView`): the same result, and a
post-state that differs from the dispatcher's only in the subject counter.
Every state the dispatcher materializes is therefore, up to that counter, the
state reached by running the canonical command path from the view of the boot
runtime (`materialize_resourceView`).

**What follows.**  The view of the boot runtime satisfies the combined
invariant (`resourceSeed_resourceRuntimeWellFormed`); every edge of the
dispatcher's token graph is admissible in the view of its pre-state, and in
particular `createSubjectOne` meets the caller-identity bound
(`dispatcher_createSubject_admissible`, `dispatcher_edge_admissible`); and
`composite_resource_trace` applies to the whole canonical path
(`dispatcher_resource_trace`): the combined invariant holds at every
reachable token, no identity is created twice, and every subject's frame
usage and limit are exactly the boot values.

`initialState`, the dispatcher, and its generated C are unchanged: this is a
hosted proof module, not a boot module.
-/
namespace LeanOS.CompositeDispatcherResources

open LeanOS
open LeanOS.FailStop
open LeanOS.CompositeDispatcher
open LeanOS.CompositeFootprint (Projection)
set_option linter.unusedSimpArgs false

/-! ## The resource view -/

/-- The subject issuer the view installs: its next identity is `2`, above the
caller identity `1` that `createSubjectOne` creates. -/
def viewIssuer : LifetimeIssuer.Issuer .subject := { next := 2 }

/-- Replace only the issuers of a composite state. -/
def withIssuers (state : CompositeState) (issuers : LifecycleIssuers) : CompositeState :=
  { state with issuers }

/-- The resource view of a dispatcher state: the subject counter covers the
caller identity the dispatcher creates. -/
def resourceView (state : CompositeState) : CompositeState :=
  withIssuers state { state.issuers with subject := viewIssuer }

theorem withIssuers_project (state : CompositeState) (issuers : LifecycleIssuers)
    (projection : Projection) (ne : projection ≠ .issuers) :
    (withIssuers state issuers).project projection = state.project projection := by
  cases projection <;> first | rfl | exact absurd rfl ne

theorem issuers_unread (operation : AuthoritativeOperation) (projection : Projection)
    (read : operation.footprint.reads projection = true) : projection ≠ .issuers := by
  intro same
  subst same
  rw [(AuthoritativeOperation.footprint_unread_resources operation).1] at read
  cases read

/-- **The gate commutes with replacing the issuers.**  No authoritative step
observes the issuers, so running it on a state with other issuers gives the
same result and the same post-state with those issuers. -/
theorem authoritativeGate_withIssuers (state : CompositeState) (issuers : LifecycleIssuers)
    (operation : AuthoritativeOperation) :
    (authoritativeGate (withIssuers state issuers) operation).result =
        (authoritativeGate state operation).result ∧
      (authoritativeGate (withIssuers state issuers) operation).state =
        withIssuers (authoritativeGate state operation).state issuers := by
  have agree : CompositeState.AgreeOn operation.footprint.reads
      (withIssuers state issuers) state := fun projection read =>
    withIssuers_project state issuers projection (issuers_unread operation projection read)
  obtain ⟨result, written⟩ := authoritativeGate_reads _ state operation agree rfl
  refine ⟨result, CompositeState.eq_of_agreeOn_all fun projection _ => ?_⟩
  cases writes : operation.footprint.writes projection with
  | true =>
      have ne := issuers_unread operation projection (operation.footprint.writesAreRead _ writes)
      rw [written projection writes, withIssuers_project _ _ _ ne]
  | false =>
      rw [authoritativeGate_frames _ operation projection writes]
      by_cases same : projection = .issuers
      · subst same; rfl
      · rw [withIssuers_project _ _ _ same, withIssuers_project _ _ _ same,
          authoritativeGate_frames state operation projection writes]

/-- Every authoritative step keeps the issuers literally. -/
theorem authoritativeGate_issuers (state : CompositeState) (operation : AuthoritativeOperation) :
    (authoritativeGate state operation).state.issuers = state.issuers :=
  (authoritativeGate_resources state operation).1

/-- **The view commutes with the gate.** -/
theorem authoritativeGate_resourceView (state : CompositeState)
    (operation : AuthoritativeOperation) :
    (authoritativeGate (resourceView state) operation).result =
        (authoritativeGate state operation).result ∧
      resourceView (authoritativeGate state operation).state =
        (authoritativeGate (resourceView state) operation).state := by
  obtain ⟨result, eq⟩ := authoritativeGate_withIssuers state
    { state.issuers with subject := viewIssuer } operation
  refine ⟨result, ?_⟩
  unfold resourceView
  rw [eq, authoritativeGate_issuers]

theorem resourceView_gate (state : CompositeState) (operation : AuthoritativeOperation) :
    resourceView (authoritativeGate state operation).state =
      (authoritativeGate (resourceView state) operation).state :=
  (authoritativeGate_resourceView state operation).2

/-- The view differs from the dispatcher's state only in the subject counter. -/
theorem resourceView_project (state : CompositeState) (projection : Projection)
    (ne : projection ≠ .issuers) :
    (resourceView state).project projection = state.project projection :=
  withIssuers_project _ _ projection ne

/-! ## The seed -/

theorem two_le_identityReserved : 2 ≤ LifetimeIssuer.identityReserved := by
  unfold LifetimeIssuer.identityReserved LifetimeIssuer.identityRadix
  decide

/-- **The view of the boot runtime satisfies the combined invariant.**
Nothing is issued at boot, so a subject counter of `2` bounds the empty
history. -/
theorem resourceSeed_resourceRuntimeWellFormed input plan
    (compiled : BootPageTablePlan.compile input = .ok plan) :
    ResourceRuntimeWellFormed (resourceView (bootRuntime plan)) := by
  obtain ⟨authoritative, resource⟩ := bootRuntime_resourceRuntimeWellFormed input plan compiled
  refine ⟨authoritative.withIssuers _, ?_⟩
  rw [resourceWellFormed_iff] at resource ⊢
  obtain ⟨issuersHold, agreementHold, budgetHold, scrubHold⟩ := resource
  refine ⟨⟨two_le_identityReserved, issuersHold.2⟩, ?_, budgetHold, scrubHold⟩
  refine ⟨fun subject issued => ?_, fun object issued => ?_⟩
  · simp [bootRuntime, bootLifecycle, resourceView, withIssuers] at issued
  · exact agreementHold.2 object issued

/-! ## The dispatcher's canonical path -/

/-- The commands that lead from `initial` to each state token. -/
def path : StateId → List CommandId
  | .initial => []
  | .subjectCreated => [.createSubjectOne]
  | .unknownSyscallRejected => [.createSubjectOne, .rejectUnknownSyscall]
  | .malformedMapRejected => [.createSubjectOne, .rejectUnknownSyscall, .rejectMalformedMap]
  | .schedulerObserved =>
      [.createSubjectOne, .rejectUnknownSyscall, .rejectMalformedMap, .observeScheduler]
  | .subjectTerminated =>
      [.createSubjectOne, .rejectUnknownSyscall, .rejectMalformedMap, .observeScheduler,
        .terminateSubjectOne]
  | .fatalEntered =>
      [.createSubjectOne, .rejectUnknownSyscall, .rejectMalformedMap, .observeScheduler,
        .terminateSubjectOne, .enterFatalKernelFault]
  | .postFatalRejected =>
      [.createSubjectOne, .rejectUnknownSyscall, .rejectMalformedMap, .observeScheduler,
        .terminateSubjectOne, .enterFatalKernelFault, .attemptPostFatalSchedule]

/-- A command list as composite steps. -/
def steps (commands : List CommandId) : List CompositeStep :=
  commands.map fun command => .authoritative (commandOperation command)

theorem runSteps_append_single (state : CompositeState) (front : List CompositeStep)
    (step : CompositeStep) :
    runSteps state (front ++ [step]) = step.apply (runSteps state front) := by
  induction front generalizing state with
  | nil => rfl
  | cons head rest ih => exact ih _

/-- Each non-initial token is its predecessor's state after one gate step. -/
theorem materialize_pred (state : StateId) (notInitial : state ≠ .initial) :
    ∃ previous command, path state = path previous ++ [command] ∧
      (path previous).length < (path state).length ∧
      materialize state = (do
        let pre ← materialize previous
        pure (authoritativeGate pre (commandOperation command)).state) := by
  cases state with
  | initial => exact absurd rfl notInitial
  | subjectCreated => exact ⟨.initial, .createSubjectOne, rfl, by decide, rfl⟩
  | unknownSyscallRejected =>
      exact ⟨.subjectCreated, .rejectUnknownSyscall, rfl, by decide, rfl⟩
  | malformedMapRejected =>
      exact ⟨.unknownSyscallRejected, .rejectMalformedMap, rfl, by decide, rfl⟩
  | schedulerObserved =>
      exact ⟨.malformedMapRejected, .observeScheduler, rfl, by decide, rfl⟩
  | subjectTerminated =>
      exact ⟨.schedulerObserved, .terminateSubjectOne, rfl, by decide, rfl⟩
  | fatalEntered => exact ⟨.subjectTerminated, .enterFatalKernelFault, rfl, by decide, rfl⟩
  | postFatalRejected =>
      exact ⟨.fatalEntered, .attemptPostFatalSchedule, rfl, by decide, rfl⟩

theorem bind_pure_ok {ε α : Type} {m : Except ε α} {f : α → α} {x : α}
    (h : (do let s ← m; pure (f s)) = Except.ok x) : ∃ s, m = .ok s ∧ x = f s := by
  cases m with
  | error e => cases h
  | ok s => cases h; exact ⟨s, rfl, rfl⟩

/-- **Every materialized state is the view of a canonical replay.**  Up to the
subject counter, the state behind each token is the composite trace of its
canonical command path run from the view of the boot runtime. -/
theorem materialize_resourceView (state : StateId) (materialized : CompositeState)
    (ok : materialize state = .ok materialized) :
    ∃ plan, BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan ∧
      resourceView materialized =
        runSteps (resourceView (bootRuntime plan)) (steps (path state)) := by
  suffices ∀ length state materialized, (path state).length = length →
      materialize state = .ok materialized →
      ∃ plan, BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan ∧
        resourceView materialized =
          runSteps (resourceView (bootRuntime plan)) (steps (path state)) from
    this _ state materialized rfl ok
  intro length
  induction length using Nat.strongRecOn with
  | ind length ih =>
  intro state materialized lengthEq ok
  by_cases initial : state = .initial
  · subst initial
    change initialState = .ok materialized at ok
    unfold initialState at ok
    split at ok
    · next plan compiled =>
        cases ok
        exact ⟨plan, compiled, rfl⟩
    · cases ok
  · obtain ⟨previous, command, pathEq, shorter, eq⟩ := materialize_pred state initial
    rw [eq] at ok
    obtain ⟨pre, preOk, rfl⟩ := bind_pure_ok ok
    obtain ⟨plan, compiled, view⟩ :=
      ih _ (lengthEq ▸ shorter) previous pre rfl preOk
    refine ⟨plan, compiled, ?_⟩
    rw [pathEq, steps, List.map_append, List.map_cons, List.map_nil, runSteps_append_single,
      ← steps, ← view]
    exact resourceView_gate pre (commandOperation command)

/-- The view's subject counter is always `2`. -/
@[simp] theorem resourceView_subject_next (state : CompositeState) :
    (resourceView state).issuers.subject.next = 2 := rfl

/-- Every authoritative step keeps the view's subject counter at `2`. -/
theorem runSteps_subject_next (state : CompositeState) (commands : List CommandId)
    (two : state.issuers.subject.next = 2) :
    (runSteps state (steps commands)).issuers.subject.next = 2 := by
  induction commands generalizing state with
  | nil => exact two
  | cons command rest ih =>
      apply ih
      simp only [CompositeStep.apply, authoritativeGate_issuers, two]

/-- One dispatcher command is admissible in every state whose subject counter
is `2`: the only creation is `createSubject 1`, and `0 < 1 < 2`. -/
theorem command_admissible (state : CompositeState) (command : CompositeDispatcher.CommandId)
    (two : state.issuers.subject.next = 2) :
    (CompositeStep.authoritative (commandOperation command)).Admissible state := by
  refine ⟨fun subject eq => ?_, fun ack eq => by cases eq⟩
  rw [two]
  cases command <;> simp [commandOperation] at eq
  subst eq
  decide

theorem steps_admissible (state : CompositeState) (commands : List CommandId)
    (two : state.issuers.subject.next = 2) :
    AdmissibleAlong state (steps commands) := by
  induction commands generalizing state with
  | nil => trivial
  | cons command rest ih =>
      refine ⟨command_admissible state command two, ih _ ?_⟩
      simp only [CompositeStep.apply, authoritativeGate_issuers, two]

/-- **Caller-identity creation is admissible wherever the dispatcher runs it.**
On every materialized token from which `createSubjectOne` is an edge of the
token graph, the identity `1` is positive and below the view's subject
counter. -/
theorem dispatcher_createSubject_admissible (state next : StateId)
    (materialized : CompositeState) (ok : materialize state = .ok materialized)
    (edge : nextState state .createSubjectOne = some next) :
    state = .initial ∧
      (CompositeStep.authoritative (commandOperation .createSubjectOne)).Admissible
        (resourceView materialized) ∧
      0 < 1 ∧ 1 < (resourceView materialized).issuers.subject.next := by
  have initial : state = .initial := by cases state <;> simp_all [nextState]
  exact ⟨initial, command_admissible _ _ rfl, by decide, by simp⟩

/-- **Every edge of the token graph is admissible** in the view of its
pre-state. -/
theorem dispatcher_edge_admissible (state next : StateId) (command : CommandId)
    (materialized : CompositeState) (_ok : materialize state = .ok materialized)
    (_edge : nextState state command = some next) :
    (CompositeStep.authoritative (commandOperation command)).Admissible
      (resourceView materialized) :=
  command_admissible _ command rfl

/-- **The dispatcher's whole path under the resource invariant.**  For every
token the dispatcher materializes, the view of its state satisfies the
combined invariant, and along the canonical path from boot: no subject
identity is created twice, none was issued before, and every subject's frame
usage and limit are exactly the boot values. -/
theorem dispatcher_resource_trace (state : StateId) (materialized : CompositeState)
    (ok : materialize state = .ok materialized) :
    ∃ plan, BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan ∧
      ResourceRuntimeWellFormed (resourceView materialized) ∧
      (createdAlong (resourceView (bootRuntime plan)) (steps (path state))).Nodup ∧
      (∀ identity, identity ∈ createdAlong (resourceView (bootRuntime plan)) (steps (path state)) →
        (bootRuntime plan).lifecycle.issuedSubjects identity = false) ∧
      ∀ subject,
        (resourceView materialized).budgetUsage subject =
            (resourceView (bootRuntime plan)).budgetUsage subject ∧
          (resourceView materialized).budgetLimit subject =
            (resourceView (bootRuntime plan)).budgetLimit subject := by
  obtain ⟨plan, compiled, view⟩ := materialize_resourceView state materialized ok
  have seed := resourceSeed_resourceRuntimeWellFormed _ plan compiled
  obtain ⟨final, nodup, fresh, _, _, budget, _⟩ :=
    composite_resource_trace _ (steps (path state)) seed
      (steps_admissible _ (path state) rfl)
  refine ⟨plan, compiled, by rw [view]; exact final, nodup, fun identity member => ?_,
    fun subject => by rw [view]; exact budget subject⟩
  exact fresh identity member

/-- The view and the dispatcher's own state have the same budgets: the view
changes only the subject counter. -/
theorem resourceView_budget (state : CompositeState) (subject : Capability.SubjectId) :
    (resourceView state).budgetUsage subject = state.budgetUsage subject ∧
      (resourceView state).budgetLimit subject = state.budgetLimit subject :=
  ⟨rfl, rfl⟩

end LeanOS.CompositeDispatcherResources
