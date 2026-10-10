import LeanOS.FailStop.SpawnAuthority

/-!
# Fail-stop composite: whole traces with spawn

`composite_resource_trace` (in `ResourceSteps`) covers traces of issued
creations, authoritative operations, and invalidation entry points.
`SpawnTraceStep` adds the spawn family to those steps, and
`spawn_resource_trace` proves the same conclusions for every mixed trace:

- the combined invariant `ResourceRuntimeWellFormed` holds at the end;
- no subject identity is created twice, by issued creation, caller-identity
  creation, or spawn, and none that was ever issued before the trace is
  created again;
- the issued subject history only grows;
- every subject's frame usage and limit are exactly unchanged, and usage is
  within the limit at the end.

Spawn steps change the object histories (they issue the child's address
space), so the relation carried along the trace is `ResourceBudgetGrows`:
frame commitment, frame contents, allocator, and bindings exact, subject
history growing.
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

/-- One step of a trace that may also spawn. -/
inductive SpawnTraceStep where
  | composite (step : CompositeStep)
  | spawn (operation : SpawnOperation)

def SpawnTraceStep.apply (state : CompositeState) : SpawnTraceStep → CompositeState
  | .composite step => step.apply state
  | .spawn operation => (spawnGate state operation).state

/-- Spawn steps need no premise; composite steps keep theirs. -/
def SpawnTraceStep.Admissible (state : CompositeState) : SpawnTraceStep → Prop
  | .composite step => step.Admissible state
  | .spawn _ => True

/-- The subject identity a step adds to the issued history, by any creation
path. -/
def SpawnTraceStep.created (state : CompositeState) : SpawnTraceStep → Option Nat
  | .composite step => step.created state
  | .spawn operation =>
      match (spawnGate state operation).result with
      | .completed (.spawn (.spawned child _)) => some child
      | _ => none

def runSpawnSteps (state : CompositeState) : List SpawnTraceStep → CompositeState
  | [] => state
  | step :: rest => runSpawnSteps (step.apply state) rest

def createdAlongSpawn (state : CompositeState) : List SpawnTraceStep → List Nat
  | [] => []
  | step :: rest => (step.created state).toList ++ createdAlongSpawn (step.apply state) rest

def AdmissibleAlongSpawn : CompositeState → List SpawnTraceStep → Prop
  | _, [] => True
  | state, step :: rest => step.Admissible state ∧ AdmissibleAlongSpawn (step.apply state) rest

/-- Frame commitment, frame contents, allocator, and bindings are kept, and
the subject history only grows. -/
def ResourceBudgetGrows (before after : CompositeState) : Prop :=
  after.frameBudgets = before.frameBudgets ∧ after.scrub = before.scrub ∧
    after.virtualMemory.memory.allocator = before.virtualMemory.memory.allocator ∧
    after.virtualMemory.memory.binding = before.virtualMemory.memory.binding ∧
    ∀ subject, before.lifecycle.issuedSubjects subject = true →
      after.lifecycle.issuedSubjects subject = true

theorem ResourceBudgetGrows.refl (state : CompositeState) : ResourceBudgetGrows state state :=
  ⟨rfl, rfl, rfl, rfl, fun _ h => h⟩

theorem ResourceBudgetGrows.trans {first second third : CompositeState}
    (left : ResourceBudgetGrows first second) (right : ResourceBudgetGrows second third) :
    ResourceBudgetGrows first third :=
  ⟨right.1.trans left.1, right.2.1.trans left.2.1, right.2.2.1.trans left.2.2.1,
    right.2.2.2.1.trans left.2.2.2.1, fun subject h => right.2.2.2.2 subject (left.2.2.2.2 subject h)⟩

theorem ResourceHistoryGrows.budgetGrows {before after : CompositeState}
    (grows : ResourceHistoryGrows before after) : ResourceBudgetGrows before after :=
  ⟨grows.1, grows.2.1, grows.2.2.1.2.2.1, grows.2.2.1.2.2.2, grows.2.2.2⟩

theorem ResourceBudgetGrows.budget {before after : CompositeState}
    (grows : ResourceBudgetGrows before after) (subject : Capability.SubjectId) :
    after.budgetUsage subject = before.budgetUsage subject ∧
      after.budgetLimit subject = before.budgetLimit subject :=
  budget_eq_of_allocator grows.1 grows.2.2.1 subject

/-- Every spawn-family step keeps the budget histories and only grows the
subject history. -/
theorem spawnGate_grows (state : CompositeState) (operation : SpawnOperation) :
    ResourceBudgetGrows state (spawnGate state operation).state := by
  cases hmode : state.execution.mode <;> simp only [spawnGate, hmode]
  case running =>
    cases operation with
    | spawn request =>
        simp only [SpawnOperation.apply]
        cases result : (spawn state request).result with
        | rejected reason =>
            rw [spawn_rejected_unchanged state request reason result]
            exact ResourceBudgetGrows.refl state
        | spawned child addressSpace =>
            obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, budgets, scrub, allocator, binding,
              subjects⟩ := spawn_keeps state request child addressSpace result
            refine ⟨budgets, scrub, allocator, binding, fun subject issued => ?_⟩
            rw [subjects]; simp only [SubjectLifecycle.setBool]; split <;> simp_all
    | grantAuthority subject =>
        simp only [SpawnOperation.apply, grantSpawnAuthority]
        split <;> exact ResourceBudgetGrows.refl state
    | revokeAuthority subject => exact ResourceBudgetGrows.refl state
  all_goals exact ResourceBudgetGrows.refl state

theorem SpawnTraceStep.admissible_preserves (state : CompositeState) (step : SpawnTraceStep)
    (holds : ResourceRuntimeWellFormed state) (admissible : step.Admissible state) :
    ResourceRuntimeWellFormed (step.apply state) := by
  cases step with
  | composite step => exact step.admissible_preserves state holds admissible
  | spawn operation => exact spawnGate_preserves_resourceRuntimeWellFormed state operation holds

theorem SpawnTraceStep.admissible_grows (state : CompositeState) (step : SpawnTraceStep)
    (holds : ResourceRuntimeWellFormed state) (admissible : step.Admissible state) :
    ResourceBudgetGrows state (step.apply state) := by
  cases step with
  | composite step => exact (step.admissible_grows state holds admissible).budgetGrows
  | spawn operation => exact spawnGate_grows state operation

/-- A created identity was not in the issued history before its step and is
in it afterwards. -/
theorem SpawnTraceStep.created_fresh (state : CompositeState) (step : SpawnTraceStep)
    (identity : Nat) (created : step.created state = some identity) :
    state.lifecycle.issuedSubjects identity = false ∧
      (step.apply state).lifecycle.issuedSubjects identity = true := by
  cases step with
  | composite step => exact step.created_fresh state identity created
  | spawn operation =>
      simp only [SpawnTraceStep.created] at created
      split at created
      · next result =>
        simp only [Option.some.injEq] at created
        subst created
        cases hmode : state.execution.mode <;> simp only [spawnGate, hmode] at result
        case handling => simp at result
        case halted => simp at result
        cases operation with
        | spawn request =>
            simp only [SpawnOperation.apply, SpawnOperationResult.spawn.injEq,
              SpawnGateResult.completed.injEq] at result
            obtain ⟨_, issued, _⟩ := spawn_spawned_stages state request _ _ result
            refine ⟨(issueSubject_fresh state _ issued).1, ?_⟩
            have subjects := (spawn_keeps state request _ _ result).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
            simp only [SpawnTraceStep.apply, spawnGate, hmode, SpawnOperation.apply, subjects,
              SubjectLifecycle.setBool, ↓reduceIte]
        | grantAuthority subject =>
            simp only [SpawnOperation.apply, grantSpawnAuthority] at result
            split at result <;> simp at result
        | revokeAuthority subject => simp [SpawnOperation.apply] at result
      · contradiction

/-- Along an admissible mixed trace the combined invariant holds at the end
and the budget histories are kept. -/
theorem runSpawnSteps_admissible (state : CompositeState) (steps : List SpawnTraceStep)
    (holds : ResourceRuntimeWellFormed state) (admissible : AdmissibleAlongSpawn state steps) :
    ResourceRuntimeWellFormed (runSpawnSteps state steps) ∧
      ResourceBudgetGrows state (runSpawnSteps state steps) := by
  induction steps generalizing state with
  | nil => exact ⟨holds, ResourceBudgetGrows.refl state⟩
  | cons step rest ih =>
      obtain ⟨now, later⟩ := admissible
      obtain ⟨final, grows⟩ := ih (step.apply state) (step.admissible_preserves state holds now)
        later
      exact ⟨final, (step.admissible_grows state holds now).trans grows⟩

theorem createdAlongSpawn_fresh (state : CompositeState) (steps : List SpawnTraceStep)
    (holds : ResourceRuntimeWellFormed state) (admissible : AdmissibleAlongSpawn state steps) :
    (createdAlongSpawn state steps).Nodup ∧
      ∀ identity, identity ∈ createdAlongSpawn state steps →
        state.lifecycle.issuedSubjects identity = false ∧
          (runSpawnSteps state steps).lifecycle.issuedSubjects identity = true := by
  induction steps generalizing state with
  | nil => simp [createdAlongSpawn]
  | cons step rest ih =>
      obtain ⟨now, later⟩ := admissible
      have next := step.admissible_preserves state holds now
      obtain ⟨nodup, fresh⟩ := ih (step.apply state) next later
      have grows := step.admissible_grows state holds now
      have tail := (runSpawnSteps_admissible (step.apply state) rest next later).2
      cases created : step.created state with
      | none =>
          simp only [createdAlongSpawn, created, Option.toList_none, List.nil_append,
            runSpawnSteps]
          refine ⟨nodup, fun identity member => ?_⟩
          obtain ⟨before, after⟩ := fresh identity member
          refine ⟨?_, after⟩
          cases h : state.lifecycle.issuedSubjects identity with
          | false => rfl
          | true => rw [grows.2.2.2.2 identity h] at before; contradiction
      | some identity =>
          obtain ⟨before, after⟩ := step.created_fresh state identity created
          simp only [createdAlongSpawn, created, Option.toList_some, List.singleton_append,
            List.nodup_cons, runSpawnSteps]
          refine ⟨⟨fun member => ?_, nodup⟩, ?_⟩
          · have := (fresh identity member).1
            rw [after] at this; contradiction
          · intro candidate member
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · exact ⟨before, tail.2.2.2.2 candidate after⟩
            · obtain ⟨laterBefore, laterAfter⟩ := fresh candidate member
              refine ⟨?_, laterAfter⟩
              cases h : state.lifecycle.issuedSubjects candidate with
              | false => rfl
              | true => rw [grows.2.2.2.2 candidate h] at laterBefore; contradiction

/-- **The resource invariants along every trace that may spawn.**  Along
every trace of issued creations, authoritative operations, invalidation
entry points, and spawn-family steps, each admissible in the state it runs
in, starting from a state that satisfies the combined invariant:

- the combined invariant holds at the end;
- no subject identity is created twice, by any creation path including
  spawn, and none that was ever issued before the trace is created again;
- the issued subject history only grows;
- every subject's frame usage and limit are exactly unchanged, and usage is
  within the limit at the end.  In particular every spawned child keeps a
  zero frame budget along the trace. -/
theorem spawn_resource_trace (state : CompositeState) (steps : List SpawnTraceStep)
    (holds : ResourceRuntimeWellFormed state) (admissible : AdmissibleAlongSpawn state steps) :
    ResourceRuntimeWellFormed (runSpawnSteps state steps) ∧
      (createdAlongSpawn state steps).Nodup ∧
      (∀ identity, identity ∈ createdAlongSpawn state steps →
        state.lifecycle.issuedSubjects identity = false) ∧
      (∀ subject, state.lifecycle.issuedSubjects subject = true →
        (runSpawnSteps state steps).lifecycle.issuedSubjects subject = true) ∧
      (∀ subject,
        (runSpawnSteps state steps).budgetUsage subject = state.budgetUsage subject ∧
          (runSpawnSteps state steps).budgetLimit subject = state.budgetLimit subject) ∧
      ∀ subject,
        (runSpawnSteps state steps).budgetUsage subject ≤
          (runSpawnSteps state steps).budgetLimit subject := by
  obtain ⟨final, grows⟩ := runSpawnSteps_admissible state steps holds admissible
  obtain ⟨nodup, fresh⟩ := createdAlongSpawn_fresh state steps holds admissible
  exact ⟨final, nodup, fun identity member => (fresh identity member).1, grows.2.2.2.2,
    fun subject => grows.budget subject,
    fun subject => (budget_conservation (runSpawnSteps state steps)).1 subject⟩

/-- Composite traces embed into mixed traces unchanged. -/
theorem runSpawnSteps_composite (state : CompositeState) (steps : List CompositeStep) :
    runSpawnSteps state (steps.map .composite) = runSteps state steps := by
  induction steps generalizing state with
  | nil => rfl
  | cons step rest ih => exact ih _

end LeanOS.FailStop
