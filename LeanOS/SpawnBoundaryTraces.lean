import LeanOS.SpawnBoundary
import LeanOS.CompositeDispatcherResources

/-!
# The spawn family's dispatcher path under the whole-trace theorem

`LeanOS.SpawnBoundary` proves each edge of the generated spawn table is one
gate step.  This module proves that the states the table's tokens name are
the states of an admissible trace of `child_resource_trace`, so every
conclusion of that theorem holds at every token: the authoritative, resource,
child-accounting, and spawn-tree invariants; no subject identity created
twice and none reused; frame usage within limit; no frame newly committed;
every parent's children within its subject budget; and every retired control
word retired forever.

The four seeds (`SpawnBoundary.seedState`) differ from the dispatcher's seed
`compositeDispatcherInitial` only in the issuers, the frame commitment, and
the spawn registry.  No authoritative conjunct reads those projections, so the
seed's authoritative invariant is the dispatcher seed's
(`compositeDispatcherInitial_authoritativeRuntimeWellFormed`); the resource
conjuncts are checked directly (`familySeed_resourceRuntimeWellFormed`).
-/
namespace LeanOS.SpawnBoundary

open LeanOS
open LeanOS.FailStop
open LeanOS.CompositeFootprint (Projection)

/-! ## Seeds satisfy the combined invariant -/

/-- A seed of the family: the dispatcher seed with issuers, the single frame
commitment of frame 4 to subject 2, and an empty spawn registry with some
generation counters. -/
def familySeed (plan : BootPageTablePlan.Plan) (subjectNext objectNext : Nat)
    (registry : SpawnRegistry) : CompositeState :=
  { compositeDispatcherInitial plan with
    issuers := { subject := { next := subjectNext }, object := { next := objectNext } }
    frameBudgets := { commitment := fun frame => if frame = 4 then some 2 else none }
    spawn := registry }

theorem authoritative_issuers_frameBudgets_unsupported :
    authoritativeInvariants.all
      (fun invariant => !invariant.support.contains .issuers &&
        !invariant.support.contains .frameBudgets) = true := by
  decide

theorem familySeed_authoritativeRuntimeWellFormed (plan : BootPageTablePlan.Plan)
    (subjectNext objectNext : Nat) (registry : SpawnRegistry) :
    AuthoritativeRuntimeWellFormed (familySeed plan subjectNext objectNext registry) := by
  have holds := compositeDispatcherInitial_authoritativeRuntimeWellFormed plan
  rw [authoritativeRuntimeWellFormed_iff_all] at holds ⊢
  intro invariant member
  apply invariant.dependsOn (compositeDispatcherInitial plan) _ _ (holds invariant member)
  intro projection supported
  have unsupported := List.all_eq_true.1 authoritative_issuers_frameBudgets_unsupported
    invariant member
  have spawnFree := List.all_eq_true.1 spawn_unsupported invariant
    (List.mem_append_left _ member)
  simp only [decide_eq_true_eq] at supported
  cases projection <;> try rfl
  all_goals simp_all

theorem dispatcherSeed_issuedSubjects (plan : BootPageTablePlan.Plan) (subject : Nat) :
    (compositeDispatcherInitial plan).lifecycle.issuedSubjects subject =
      (decide (subject = 1) || decide (subject = 2)) := rfl

theorem dispatcherSeed_issuedObject (plan : BootPageTablePlan.Plan) (object : Nat) :
    (compositeDispatcherInitial plan).virtualMemory.memory.issued object =
        (decide (object = 1) || decide (object = 2) || decide (object = 10) ||
          decide (object = 20)) ∧
      (compositeDispatcherInitial plan).virtualMemory.issuedAddressSpace object =
        (decide (object = 1) || decide (object = 2)) := ⟨rfl, rfl⟩

/-- **Every family seed satisfies the combined invariant** when its counters
bound the seed's histories and stay in the identity domain. -/
theorem familySeed_resourceRuntimeWellFormed (plan : BootPageTablePlan.Plan)
    (subjectNext objectNext : Nat) (registry : SpawnRegistry)
    (subjectBound : 3 ≤ subjectNext) (subjectDomain : subjectNext ≤ LifetimeIssuer.identityReserved)
    (objectBound : 21 ≤ objectNext) (objectDomain : objectNext ≤ LifetimeIssuer.identityReserved) :
    ResourceRuntimeWellFormed (familySeed plan subjectNext objectNext registry) := by
  refine ⟨familySeed_authoritativeRuntimeWellFormed plan subjectNext objectNext registry, ?_⟩
  rw [resourceWellFormed_iff]
  refine ⟨⟨subjectDomain, objectDomain⟩, ⟨fun subject issued => ?_, fun object issued => ?_⟩,
    fun frame subject committed => ?_, fun object frame bound unwritten => ?_⟩
  · change (compositeDispatcherInitial plan).lifecycle.issuedSubjects subject = true at issued
    rw [dispatcherSeed_issuedSubjects] at issued
    show 0 < subject ∧ subject < subjectNext
    simp only [Bool.or_eq_true, decide_eq_true_eq] at issued
    rcases issued with rfl | rfl <;> exact ⟨by decide, Nat.lt_of_lt_of_le (by decide) subjectBound⟩
  · change ((compositeDispatcherInitial plan).virtualMemory.memory.issued object ||
      (compositeDispatcherInitial plan).virtualMemory.issuedAddressSpace object) = true at issued
    rw [(dispatcherSeed_issuedObject plan object).1,
      (dispatcherSeed_issuedObject plan object).2] at issued
    show 0 < object ∧ object < objectNext
    simp only [Bool.or_eq_true, decide_eq_true_eq] at issued
    rcases issued with (((rfl | rfl) | rfl) | rfl) | (rfl | rfl) <;>
      exact ⟨by decide, Nat.lt_of_lt_of_le (by decide) objectBound⟩
  · change (if frame = 4 then some 2 else none) = some subject at committed
    by_cases four : frame = 4
    · subst four
      simp only [↓reduceIte, Option.some.injEq] at committed
      subst committed
      refine ⟨List.mem_singleton.2 rfl, fun reserved => ?_, rfl⟩
      cases reserved
    · simp [four] at committed
  · change (if object = 20 then some 4 else none) = some frame at bound
    by_cases twenty : object = 20
    · subst twenty
      simp only [↓reduceIte, Option.some.injEq] at bound
      subst bound
      exact ⟨rfl, fun _ _ => rfl⟩
    · simp [twenty] at bound

theorem familySeed_childAccounting (plan : BootPageTablePlan.Plan) (subjectNext objectNext : Nat)
    (registry : SpawnRegistry) (empty : ∀ parent slot, registry.children parent slot = none) :
    ChildAccountingWellFormed (familySeed plan subjectNext objectNext registry) :=
  childAccounting_of_empty _ empty

theorem familySeed_spawnTree (plan : BootPageTablePlan.Plan) (subjectNext objectNext : Nat)
    (registry : SpawnRegistry) (empty : ∀ parent slot, registry.children parent slot = none)
    (noAuthority : ∀ subject, registry.authority subject = none)
    (noParents : ∀ child, registry.parent child = none) :
    SpawnTreeWellFormed (familySeed plan subjectNext objectNext registry) :=
  spawnTree_of_empty _ empty noAuthority noParents

/-- Each of the four seeds is a family seed. -/
theorem seedState_familySeed (plan : BootPageTablePlan.Plan) (seed : Seed) :
    ∃ subjectNext objectNext registry,
      seedState plan seed = familySeed plan subjectNext objectNext registry ∧
      3 ≤ subjectNext ∧ subjectNext ≤ LifetimeIssuer.identityReserved ∧
      21 ≤ objectNext ∧ objectNext ≤ LifetimeIssuer.identityReserved ∧
      (∀ parent slot, registry.children parent slot = none) ∧
      (∀ subject, registry.authority subject = none) ∧
      (∀ child, registry.parent child = none) := by
  have reserved : 21 ≤ LifetimeIssuer.identityReserved := by
    unfold LifetimeIssuer.identityReserved LifetimeIssuer.identityRadix
    decide
  cases seed with
  | main =>
      exact ⟨3, 21, {}, rfl, by omega, by omega, by omega, reserved,
        fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩
  | subjectsExhausted =>
      exact ⟨LifetimeIssuer.identityReserved, 21, {}, rfl, by omega, Nat.le_refl _, by omega,
        reserved, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩
  | objectsExhausted =>
      exact ⟨3, LifetimeIssuer.identityReserved, {}, rfl, by omega, by omega, reserved,
        Nat.le_refl _, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩
  | controlsExhausted =>
      exact ⟨3, 21, { nextChildGeneration := CapabilityHandle.generationReserved }, rfl,
        by omega, by omega, by omega, reserved, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-! ## The dispatcher path is an admissible child trace -/

theorem runFamily_runChildSteps (state : CompositeState) (commands : List FamilyCommand) :
    runFamily state commands = runChildSteps state (commands.map FamilyCommand.toStep) := by
  induction commands generalizing state with
  | nil => rfl
  | cons command rest ih =>
      simp only [runFamily, List.map_cons, runChildSteps]
      rw [familyStep_state]
      exact ih _

/-- Every family command is admissible in every state: child and memory steps
need no premise, and the switch and the copy are unconditional composite
steps. -/
theorem toStep_admissible (state : CompositeState) (command : FamilyCommand) :
    command.toStep.Admissible state := by
  cases command with
  | child operation => trivial
  | memory operation => trivial
  | switch => exact CompositeStep.admissible_of_unconditional _ _ rfl
  | copy => exact CompositeStep.admissible_of_unconditional _ _ rfl

theorem admissibleAlong_family (state : CompositeState) (commands : List FamilyCommand) :
    AdmissibleAlongChild state (commands.map FamilyCommand.toStep) := by
  induction commands generalizing state with
  | nil => trivial
  | cons command rest ih => exact ⟨toStep_admissible state command, ih _⟩

/-- **The whole-trace theorem at every token.**  Every state the spawn
family's tokens name satisfies the authoritative, resource, child-accounting,
and spawn-tree invariants; frame usage is within limit; every parent's live
children are within its subject budget, and its usage plus its children's
limits within its entitlement; no frame outside the seed's commitment is
committed; and no subject identity was created twice or reused along the
replayed path. -/
theorem spawn_boundary_trace (plan : BootPageTablePlan.Plan) (id : StateId) :
    let state := stateOf plan id
    let seed := seedState plan (origin id).1
    let steps := (origin id).2.map FamilyCommand.toStep
    ResourceRuntimeWellFormed state ∧ ChildAccountingWellFormed state ∧
      SpawnTreeWellFormed state ∧
      (createdAlongChild seed steps).Nodup ∧
      (∀ identity, identity ∈ createdAlongChild seed steps →
        seed.lifecycle.issuedSubjects identity = false) ∧
      (∀ subject, state.budgetUsage subject ≤ state.budgetLimit subject) ∧
      (∀ frame, (state.frameBudgets.commitment frame).isSome = true →
        (seed.frameBudgets.commitment frame).isSome = true) ∧
      (∀ parent capability, state.spawn.authority parent = some capability →
        childCount state parent ≤ capability.subjectBudget) ∧
      (∀ parent, state.budgetUsage parent + childLimits state parent ≤
        entitlement state parent) := by
  intro state seed steps
  obtain ⟨subjectNext, objectNext, registry, seedEq, subjectBound, subjectDomain, objectBound,
    objectDomain, empty, noAuthority, noParents⟩ := seedState_familySeed plan (origin id).1
  have holds : ResourceRuntimeWellFormed seed := by
    simp only [seed, seedEq]
    exact familySeed_resourceRuntimeWellFormed plan subjectNext objectNext registry subjectBound
      subjectDomain objectBound objectDomain
  have accounting : ChildAccountingWellFormed seed := by
    simp only [seed, seedEq]
    exact familySeed_childAccounting plan subjectNext objectNext registry empty
  have tree : SpawnTreeWellFormed seed := by
    simp only [seed, seedEq]
    exact familySeed_spawnTree plan subjectNext objectNext registry empty noAuthority noParents
  obtain ⟨final, finalAccounting, finalTree, nodup, fresh, _, _, usage, _, committed, budget,
    entitled, _, _⟩ :=
    child_resource_trace seed steps holds accounting tree (admissibleAlong_family _ _)
  have stateEq : state = runChildSteps seed steps := runFamily_runChildSteps _ _
  rw [stateEq]
  exact ⟨final, finalAccounting, finalTree, nodup, fresh, usage, committed, budget, entitled⟩

end LeanOS.SpawnBoundary
