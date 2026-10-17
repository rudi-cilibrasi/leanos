import LeanOS.SpawnAllocatorSimulation
import LeanOS.SpawnBoundaryTraces

/-!
# The family seeds are family states (#575)

Every family seed (`SpawnBoundary.familySeed`: the dispatcher seed with
issuers, frame 4 committed to subject 2, and an empty spawn registry) is a
`Family` state (`familySeed_family`), and so are the four seeds of the spawn
table (`seedState_family`).  With `familyTrace_simulates`, every command
trace the allocator decides from a seed's record runs through the composite
gates to the allocator's replies and records (`seed_trace_simulates`).
-/
namespace LeanOS.SpawnAllocator

open LeanOS
open LeanOS.FailStop
open LeanOS.SpawnBoundary

set_option linter.unusedSimpArgs false

section Seed

variable (plan : BootPageTablePlan.Plan) (subjectNext objectNext : Nat) (registry : SpawnRegistry)

/-! ## Readings of the seed -/

theorem seed_subjects (subject : Nat) :
    (familySeed plan subjectNext objectNext registry).capabilities.subjects subject =
      (decide (subject = 1) || decide (subject = 2)) := rfl

theorem seed_objects (object : Nat) :
    (familySeed plan subjectNext objectNext registry).capabilities.objects object =
      (decide (object = 1) || decide (object = 2) || decide (object = 10) ||
        decide (object = 20)) := rfl

theorem seed_ownedMemory (object : Nat) :
    (familySeed plan subjectNext objectNext registry).lifecycle.ownedMemory object =
      if object = 20 then some (2, 4) else none := rfl

theorem seed_endpointOwner (object : Nat) :
    (familySeed plan subjectNext objectNext registry).lifecycle.endpointOwner object =
      if object = 10 then some 1 else none := rfl

theorem seed_commitment (frame : Nat) :
    (familySeed plan subjectNext objectNext registry).frameBudgets.commitment frame =
      if frame = 4 then some 2 else none := rfl

theorem seed_status_four :
    (familySeed plan subjectNext objectNext registry).virtualMemory.memory.allocator.status 4 =
      .owned 20 := rfl

theorem seed_memory_slot :
    (familySeed plan subjectNext objectNext registry).capabilities.slots parent 2 =
      some { object := 20, kind := .memory, rights := Capability.allRights, identity := 5 } := rfl

theorem seed_abstraction_memory :
    (abstraction (familySeed plan subjectNext objectNext registry)).memory = [some 5, none] := rfl

theorem seed_budgetLimit :
    (familySeed plan subjectNext objectNext registry).budgetLimit parent = 1 := rfl

theorem seed_budgetUsage :
    (familySeed plan subjectNext objectNext registry).budgetUsage parent = 1 := rfl

/-- **Every family seed is a family state** when its counters bound the
seed's histories, its spawn registry is empty, and its generation counters
are representable. -/
theorem familySeed_family
    (subjectBound : 3 ≤ subjectNext) (subjectDomain : subjectNext ≤ LifetimeIssuer.identityReserved)
    (objectBound : 21 ≤ objectNext) (objectDomain : objectNext ≤ LifetimeIssuer.identityReserved)
    (empty : ∀ parent slot, registry.children parent slot = none)
    (noAuthority : ∀ subject, registry.authority subject = none)
    (noParents : ∀ child, registry.parent child = none)
    (control : registry.nextChildGeneration ≤ CapabilityHandle.generationReserved)
    (generation : 0 < registry.nextGeneration ∧ registry.nextGeneration < wordBound) :
    Family (familySeed plan subjectNext objectNext registry) := by
  have children : (abstraction (familySeed plan subjectNext objectNext registry)).children =
      (List.range childCapacity).map fun _ => none := by
    simp only [abstraction]
    apply List.map_congr_left
    intro slot _
    change (registry.children parent slot).map _ = none
    rw [empty]; rfl
  refine ⟨familySeed_resourceRuntimeWellFormed plan subjectNext objectNext registry subjectBound
      subjectDomain objectBound objectDomain,
    familySeed_childAccounting plan subjectNext objectNext registry empty,
    familySeed_spawnTree plan subjectNext objectNext registry empty noAuthority noParents,
    rfl, rfl, rfl, fun _ => rfl, rfl, noParents parent, ⟨10, rfl, rfl, rfl, rfl⟩,
    ⟨_, rfl, rfl, rfl, rfl⟩, ?_, ?_, fun _ _ => empty _ _, ?_, fun subject _ => noAuthority subject,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, control, generation, ?_⟩
  · intro slot which
    rcases which with rfl | rfl
    · right
      exact ⟨_, 4, seed_memory_slot plan subjectNext objectNext registry, rfl, rfl, by decide,
        rfl, rfl, rfl, rfl⟩
    · left; rfl
  · intro first second _ held3
    cases held3
  · intro capability held
    change registry.authority parent = some capability at held
    rw [noAuthority] at held
    cases held
  · intro slot entry found
    change registry.children parent slot = some entry at found
    rw [empty] at found
    cases found
  · intro subject live
    rw [seed_subjects] at live
    simp only [Bool.or_eq_true, decide_eq_true_eq] at live
    rcases live with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · intro frame subject committed
    rw [seed_commitment] at committed
    split at committed
    · cases committed; exact Or.inl rfl
    · cases committed
  · show List.Nodup [4]
    decide
  · intro slot capability subject _ _
    exact noParents subject
  · intro object high
    change objectNext ≤ object at high
    have ne20 : object ≠ 20 := by omega
    have ne10 : object ≠ 10 := by omega
    refine ⟨?_, ?_, ?_⟩
    · rw [seed_objects]
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
      exact ⟨⟨⟨by omega, by omega⟩, ne10⟩, ne20⟩
    · rw [seed_ownedMemory]; simp [ne20]
    · rw [seed_endpointOwner]; simp [ne10]
  · intro frame committed free
    rw [seed_commitment] at committed
    split at committed
    · next four =>
      subst four
      rw [seed_status_four] at free
      cases free
    · cases committed
  · rw [seed_budgetUsage, State.memoryUsed, seed_abstraction_memory]; rfl
  · show 6 ≤ CapabilityHandle.generationReserved + 1
    unfold CapabilityHandle.generationReserved CapabilityHandle.generationRadix
    decide
  · rw [seed_budgetLimit, State.chargeSum, children]
    unfold childCapacity frameBound
    decide

end Seed

/-- **The four seeds of the spawn table are family states.** -/
theorem seedState_family (plan : BootPageTablePlan.Plan) (seed : Seed) :
    Family (seedState plan seed) := by
  have reserved : 21 ≤ LifetimeIssuer.identityReserved := by
    unfold LifetimeIssuer.identityReserved LifetimeIssuer.identityRadix
    decide
  have generation : 0 < (({} : SpawnRegistry)).nextGeneration ∧
      ({} : SpawnRegistry).nextGeneration < wordBound := by
    unfold wordBound; decide
  have control : ({} : SpawnRegistry).nextChildGeneration ≤ CapabilityHandle.generationReserved := by
    unfold CapabilityHandle.generationReserved CapabilityHandle.generationRadix
    decide
  cases seed with
  | main =>
      exact familySeed_family plan 3 21 {} (by omega) (by omega) (by omega) reserved
        (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) control generation
  | subjectsExhausted =>
      exact familySeed_family plan LifetimeIssuer.identityReserved 21 {} (by omega) (Nat.le_refl _)
        (by omega) reserved (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) control generation
  | objectsExhausted =>
      exact familySeed_family plan 3 LifetimeIssuer.identityReserved {} (by omega) (by omega)
        reserved (Nat.le_refl _) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) control generation
  | controlsExhausted =>
      exact familySeed_family plan 3 21 { nextChildGeneration := CapabilityHandle.generationReserved }
        (by omega) (by omega) (by omega) reserved (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (Nat.le_refl _) generation

/-- **Every allocator-decided trace from a seed is a composite trace.**  The
composite family, run from a seed over commands the allocator decides from
the seed's record, returns the allocator's replies and ends in a family
state whose record is the allocator's. -/
theorem seed_trace_simulates (plan : BootPageTablePlan.Plan) (seed : Seed)
    (commands : List FamilyCommand) (allocatorCommands : List Command)
    (translated : commands.map toCommand = allocatorCommands.map some)
    (record : State) (replies : List (UInt64 × UInt64))
    (decided : runSteps (abstraction (seedState plan seed)) allocatorCommands =
      some (record, replies)) :
    familyReplies (seedState plan seed) commands = replies ∧
      abstraction (runFamily (seedState plan seed) commands) = record ∧
      Family (runFamily (seedState plan seed) commands) :=
  familyTrace_simulates _ (seedState_family plan seed) commands allocatorCommands translated
    record replies decided

/-! ## The table's record tokens, for every boot plan -/

/-- The allocator record of each seed; no seed reads the boot plan. -/
def seedRecord : Seed → State
  | .main => ⟨3, 21, 6, 1, 1, none, 0, [none, none, none, none], [some 5, none], 1⟩
  | .subjectsExhausted =>
      ⟨LifetimeIssuer.identityReserved, 21, 6, 1, 1, none, 0, [none, none, none, none],
        [some 5, none], 1⟩
  | .objectsExhausted =>
      ⟨3, LifetimeIssuer.identityReserved, 6, 1, 1, none, 0, [none, none, none, none],
        [some 5, none], 1⟩
  | .controlsExhausted =>
      ⟨3, 21, 6, CapabilityHandle.generationReserved, 1, none, 0, [none, none, none, none],
        [some 5, none], 1⟩

theorem abstraction_seedState (plan : BootPageTablePlan.Plan) (seed : Seed) :
    abstraction (seedState plan seed) = seedRecord seed := by
  cases seed <;> rfl

/-- The allocator run of a token's replay. -/
def tokenRun (id : StateId) : Option (State × List (UInt64 × UInt64)) :=
  runSteps (seedRecord (origin id).1) ((origin id).2.filterMap toCommand)

/-- Every record token is replayed by allocator commands alone, all decided. -/
def tokenDecided (id : StateId) : Bool :=
  (origin id).2.all (fun command => (toCommand command).isSome) && (tokenRun id).isSome

theorem recordTokens_decided : recordTokens.all tokenDecided = true := by
  decide

theorem map_toCommand_filterMap (commands : List FamilyCommand)
    (all : commands.all (fun command => (toCommand command).isSome) = true) :
    commands.map toCommand = (commands.filterMap toCommand).map some := by
  induction commands with
  | nil => rfl
  | cons command rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at all
      obtain ⟨head, tail⟩ := all
      cases translated : toCommand command with
      | none => rw [translated] at head; cases head
      | some allocatorCommand =>
          simp only [List.map_cons, List.filterMap_cons, translated, ih tail]

/-- **Every record token of the spawn table is a family state, for every
boot plan**, and its record is the allocator's run of the token's replay
from its seed's record. -/
theorem recordToken_family (plan : BootPageTablePlan.Plan) (id : StateId)
    (member : id ∈ recordTokens) :
    ∃ record replies, tokenRun id = some (record, replies) ∧
      abstraction (stateOf plan id) = record ∧ Family (stateOf plan id) ∧
      familyReplies (seedState plan (origin id).1) (origin id).2 = replies := by
  have decided := List.all_eq_true.1 recordTokens_decided id member
  simp only [tokenDecided, Bool.and_eq_true] at decided
  obtain ⟨translatable, some⟩ := decided
  cases run : tokenRun id with
  | none => rw [run] at some; cases some
  | some result =>
      obtain ⟨record, replies⟩ := result
      have simulated := seed_trace_simulates plan (origin id).1 (origin id).2
        ((origin id).2.filterMap toCommand) (map_toCommand_filterMap _ translatable) record replies
        (by rw [abstraction_seedState]; exact run)
      exact ⟨record, replies, rfl, simulated.2.1, simulated.2.2, simulated.1⟩

/-- **Every allocator edge of the spawn table is a composite step, for every
boot plan.**  From a record token, every allocator command the allocator
decides — not only the table's edges — runs through the composite gate to
the allocator's status, value and successor record. -/
theorem recordToken_simulates (plan : BootPageTablePlan.Plan) (id : StateId)
    (member : id ∈ recordTokens) (command : FamilyCommand) (allocatorCommand : Command)
    (result : Step) (translated : toCommand command = some allocatorCommand)
    (decided : step (abstraction (stateOf plan id)) allocatorCommand = some result) :
    Simulates (stateOf plan id) command result := by
  obtain ⟨_, _, _, _, family, _⟩ := recordToken_family plan id member
  exact familyStep_simulates _ family command allocatorCommand result translated decided

end LeanOS.SpawnAllocator
