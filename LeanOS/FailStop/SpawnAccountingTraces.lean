import LeanOS.FailStop.SpawnTree

/-!
# Fail-stop composite: whole traces of the public spawn family

`ChildTraceStep` is one step of a trace that may run every composite step
(`CompositeStep`: issued creation, authoritative operations, invalidation
entry points), every operation of the public spawn family (`ChildOperation`,
through `childGate`), and every operation of the composite memory family
(`MemoryOperation`, through `memoryGate`: budget-charged allocation and
release).  `child_resource_trace` is the whole-trace resource theorem with
charged spawn, frame slices, child termination, and memory allocation and
release.  Along every admissible trace from a state satisfying the combined
invariant, the accounting invariant, and the spawn-tree invariant:

- all three invariants hold at the end;
- no subject identity is created twice, by any creation path, and none that
  was issued before the trace;
- the subject history only grows;
- **no frame is created**: the allocator's frame list is exactly the
  starting one, and every frame committed at the end was committed at the
  start;
- **subject budgets**: every parent holding a spawn capability has at most
  its subject budget of children;
- **frame budgets**: every parent's own usage plus its children's frame
  limits is within its entitlement, and a subject that was issued and not a
  charged child at the start (a root parent) never gains entitlement, so its
  children's budgets plus its own usage never exceed what it started with;
- **stale control words stay stale**: a retired control word is retired at
  the end, whatever spawns reused its slot.
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

/-- One step of a trace that may use the public spawn family and the memory
family. -/
inductive ChildTraceStep where
  | composite (step : CompositeStep)
  | child (operation : ChildOperation)
  | memory (operation : MemoryOperation)

def ChildTraceStep.apply (state : CompositeState) : ChildTraceStep → CompositeState
  | .composite step => step.apply state
  | .child operation => (childGate state operation).state
  | .memory operation => (memoryGate state operation).state

/-- Spawn-family and memory steps need no premise; composite steps keep
theirs. -/
def ChildTraceStep.Admissible (state : CompositeState) : ChildTraceStep → Prop
  | .composite step => step.Admissible state
  | .child _ => True
  | .memory _ => True

/-- The subject identity a step adds to the issued history, by any creation
path. -/
def ChildTraceStep.created (state : CompositeState) : ChildTraceStep → Option Nat
  | .composite step => step.created state
  | .child operation =>
      match (childGate state operation).result with
      | .completed (.spawned spawnedChild _ _) => some spawnedChild
      | _ => none
  | .memory _ => none

def runChildSteps (state : CompositeState) : List ChildTraceStep → CompositeState
  | [] => state
  | step :: rest => runChildSteps (step.apply state) rest

def createdAlongChild (state : CompositeState) : List ChildTraceStep → List Nat
  | [] => []
  | step :: rest => (step.created state).toList ++ createdAlongChild (step.apply state) rest

def AdmissibleAlongChild : CompositeState → List ChildTraceStep → Prop
  | _, [] => True
  | state, step :: rest => step.Admissible state ∧ AdmissibleAlongChild (step.apply state) rest

/-- What every step keeps: the allocator's frame list, the committed frames
(which only shrink), the subject history (which only grows), fresh control
generations, and uncharged issued subjects (which stay uncharged and never
gain entitlement). -/
structure ChildStepKeeps (before after : CompositeState) : Prop where
  frames : after.virtualMemory.memory.allocator.frames =
    before.virtualMemory.memory.allocator.frames
  committed : ∀ frame, (after.frameBudgets.commitment frame).isSome = true →
    (before.frameBudgets.commitment frame).isSome = true
  issued : ∀ subject, before.lifecycle.issuedSubjects subject = true →
    after.lifecycle.issuedSubjects subject = true
  advances : TableAdvances before after
  roots : ∀ subject, before.lifecycle.issuedSubjects subject = true →
    ¬ChargedChild before subject →
      ¬ChargedChild after subject ∧ entitlement after subject ≤ entitlement before subject

theorem ChildStepKeeps.trans {first second third : CompositeState}
    (left : ChildStepKeeps first second) (right : ChildStepKeeps second third) :
    ChildStepKeeps first third := by
  refine ⟨right.frames.trans left.frames,
    fun frame committed => left.committed frame (right.committed frame committed),
    fun subject issued => right.issued subject (left.issued subject issued),
    ⟨Nat.le_trans left.advances.1 right.advances.1, fun parent slot entry found => ?_⟩,
    fun subject issued uncharged => ?_⟩
  · rcases right.advances.2 parent slot entry found with ⟨middle, middleFound, same⟩ | fresh
    · rcases left.advances.2 parent slot middle middleFound with ⟨old, oldFound, same'⟩ | fresh'
      · exact Or.inl ⟨old, oldFound, same'.trans same⟩
      · exact Or.inr (same ▸ fresh')
    · exact Or.inr (Nat.le_trans left.advances.1 fresh)
  · obtain ⟨middleUncharged, middleLe⟩ := left.roots subject issued uncharged
    obtain ⟨finalUncharged, finalLe⟩ :=
      right.roots subject (left.issued subject issued) middleUncharged
    exact ⟨finalUncharged, Nat.le_trans finalLe middleLe⟩

theorem ChildStepKeeps.refl (state : CompositeState) : ChildStepKeeps state state :=
  ⟨rfl, fun _ committed => committed, fun _ issued => issued, TableAdvances.refl state,
    fun _ _ uncharged => ⟨uncharged, Nat.le_refl _⟩⟩

/-- A step that changes only spawn authority keeps everything. -/
theorem ChildStepKeeps.of_children (state : CompositeState) (registry : SpawnRegistry)
    (children : registry.children = state.spawn.children)
    (next : registry.nextChildGeneration = state.spawn.nextChildGeneration) :
    ChildStepKeeps state { state with spawn := registry } := by
  have same : ∀ subject, entitlement { state with spawn := registry } subject =
      entitlement state subject := by
    intro subject
    simp only [entitlement,
      (childTable_congr (after := { state with spawn := registry }) children subject).1]
    rfl
  refine ⟨rfl, fun _ committed => committed, fun _ issued => issued,
    ⟨by simp only [next]; exact Nat.le_refl _, fun parent slot entry found => ?_⟩,
    fun subject _ uncharged => ⟨fun charged => ?_, by rw [same]; exact Nat.le_refl _⟩⟩
  · simp only [children] at found
    exact Or.inl ⟨entry, found, rfl⟩
  · obtain ⟨parent, slot, entry, found, eq⟩ := charged
    simp only [children] at found
    exact uncharged ⟨parent, slot, entry, found, eq⟩

/-! ## Each step keeps them -/

theorem CompositeStep.keeps (state : CompositeState) (step : CompositeStep)
    (holds : ResourceRuntimeWellFormed state) (admissible : step.Admissible state)
    (accounting : ChildAccountingWellFormed state) :
    ChildStepKeeps state (step.apply state) := by
  have grows := step.admissible_grows state holds admissible
  have spawnSame := step.apply_spawn state
  have entitlements := (step.childAccounting state holds admissible accounting).2
  refine ⟨by rw [grows.2.2.1.2.2.1], fun frame committed => by
      rw [grows.1] at committed; exact committed,
    grows.2.2.2, step.advances state, fun subject _ uncharged => ⟨?_, ?_⟩⟩
  · intro charged
    apply uncharged
    obtain ⟨parent, slot, entry, found, same⟩ := charged
    rw [spawnSame] at found
    exact ⟨parent, slot, entry, found, same⟩
  · rw [entitlements]; exact Nat.le_refl _

/-- Every entry after a charged spawn is an old entry or names the new child,
which was never issued before. -/
theorem spawnCharged_charged (state : CompositeState) (request : SpawnRequest)
    (holds : ResourceRuntimeWellFormed state) (subject : Nat)
    (charged : ChargedChild (spawnCharged state request).state subject) :
    ChargedChild state subject ∨ state.lifecycle.issuedSubjects subject = false := by
  rcases spawnCharged_shape state request with ⟨same, _⟩ | ⟨child, addressSpace, control, result⟩
  · rw [same] at charged; exact Or.inl charged
  · obtain ⟨slot, _, _, _, _, spawned, _, stateEq⟩ :=
      spawnCharged_spawned state request child addressSpace control result
    obtain ⟨childrenEq, _, _⟩ := spawn_childTable state request child addressSpace spawned
    have unissued := (spawn_fresh_identity state request child addressSpace holds spawned).2.1
    obtain ⟨parent, candidateSlot, entry, found, same⟩ := charged
    rw [stateEq] at found
    simp only [installChild, childrenEq] at found
    split at found
    · simp only [Option.some.injEq] at found
      subst found
      right; rw [← same]; exact unissued
    · exact Or.inl ⟨parent, candidateSlot, entry, found, same⟩

theorem ChildOperation.apply_keeps (state : CompositeState) (operation : ChildOperation)
    (running : state.execution.mode = .running) (holds : ResourceRuntimeWellFormed state)
    (accounting : ChildAccountingWellFormed state) :
    ChildStepKeeps state (operation.apply state).state := by
  have entitlements := (childGate_preserves state operation holds accounting).2.2
  simp only [childGate, running] at entitlements
  have advances := ChildOperation.apply_advances state operation
  have rootsOf : (∀ subject, ChargedChild (operation.apply state).state subject →
      ChargedChild state subject ∨ state.lifecycle.issuedSubjects subject = false) →
      ∀ subject, state.lifecycle.issuedSubjects subject = true → ¬ChargedChild state subject →
        ¬ChargedChild (operation.apply state).state subject ∧
          entitlement (operation.apply state).state subject ≤ entitlement state subject := by
    intro back subject issued uncharged
    refine ⟨fun charged => ?_, ?_⟩
    · rcases back subject charged with old | fresh
      · exact uncharged old
      · rw [issued] at fresh; cases fresh
    · rcases entitlements subject with le | charged
      · exact le
      · exact absurd charged uncharged
  cases operation with
  | spawn request =>
      simp only [ChildOperation.apply] at advances rootsOf ⊢
      rcases spawnCharged_shape state request with ⟨same, _⟩ |
        ⟨child, addressSpace, control, result⟩
      · rw [same]; exact ChildStepKeeps.refl state
      · obtain ⟨slot, _, _, _, _, spawned, _, stateEq⟩ :=
          spawnCharged_spawned state request child addressSpace control result
        have keeps := spawn_keeps state request child addressSpace spawned
        have budgetsEq := keeps.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have issuedEq := keeps.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        refine ⟨?_, fun frame committed => ?_, fun subject issued => ?_, advances,
          rootsOf (spawnCharged_charged state request holds)⟩
        · rw [stateEq]
          show (FailStop.spawn state request).state.virtualMemory.memory.allocator.frames = _
          rw [keeps.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
        · rw [stateEq] at committed
          have budgets : (installChild (FailStop.spawn state request).state (spawnParent state)
              slot child).frameBudgets = state.frameBudgets := budgetsEq
          rw [budgets] at committed; exact committed
        · rw [stateEq]
          show (FailStop.spawn state request).state.lifecycle.issuedSubjects subject = true
          rw [issuedEq]
          simp only [SubjectLifecycle.setBool]; split <;> simp_all
  | grantFrames control frames =>
      simp only [ChildOperation.apply] at advances rootsOf ⊢
      rcases grantFrames_shape state control frames with ⟨same, _⟩ | ⟨child, moved, result⟩
      · rw [same]; exact ChildStepKeeps.refl state
      · obtain ⟨slot, entry, resolved, childEq, _, _, _, stateEq⟩ :=
          grantFrames_granted state control frames child moved result
        obtain ⟨_, _, found⟩ := resolveControl_ok resolved
        refine ⟨by rw [stateEq]; rfl, fun frame committed => ?_,
          fun subject issued => by rw [stateEq]; exact issued, advances, rootsOf ?_⟩
        · rw [stateEq] at committed
          simp only [moveFrames] at committed
          split at committed
          · next contained =>
            have member : frame ∈ availableFrames state (spawnParent state) :=
              List.mem_of_mem_take (by simpa [grantedFrames] using contained)
            rw [(mem_availableFrames member).2.1]; rfl
          · exact committed
        · intro subject charged
          left
          obtain ⟨parent, candidateSlot, entry', found', same⟩ := charged
          rw [stateEq] at found'
          simp only [setChildEntry] at found'
          split at found'
          · next h =>
            obtain ⟨rfl, rfl⟩ := h
            simp only [Option.some.injEq] at found'
            subst found'
            exact ⟨_, _, entry, found, by rw [← same]; rfl⟩
          · exact ⟨parent, candidateSlot, entry', found', same⟩
  | terminateChild control =>
      simp only [ChildOperation.apply] at advances rootsOf ⊢
      rcases terminateChild_shape state control with ⟨same, _⟩ | ⟨child, returned, result⟩
      · rw [same]; exact ChildStepKeeps.refl state
      · obtain ⟨slot, entry, _, _, _, stateEq⟩ :=
          terminateChild_terminated state control child returned result
        obtain ⟨_, agreesT, spawnT⟩ := terminatedChild_facts state child holds
        obtain ⟨_, budgetsT, _, issuedT, _, _, allocatorT, _⟩ := agreesT
        refine ⟨by
            rw [stateEq]
            show (terminatedChild state child).virtualMemory.memory.allocator.frames = _
            rw [allocatorT], fun frame committed => ?_,
          fun subject issued => by
            rw [stateEq]
            show (terminatedChild state child).lifecycle.issuedSubjects subject = true
            rw [issuedT]; exact issued,
          advances, rootsOf ?_⟩
        · rw [stateEq] at committed
          simp only [releaseChild, reclaimChildFrames, returnFrames, budgetsT] at committed
          split at committed
          · next fromChild => rw [fromChild]; rfl
          · exact committed
        · intro subject charged
          left
          obtain ⟨parent, candidateSlot, entry', found', same⟩ := charged
          rw [stateEq] at found'
          simp only [releaseChild, reclaimChildFrames, spawnT] at found'
          split at found'
          · cases found'
          · exact ⟨parent, candidateSlot, entry', found', same⟩
  | grantAuthority subject budget =>
      simp only [ChildOperation.apply]
      unfold grantBudgetedAuthority
      split
      · exact ChildStepKeeps.of_children state _ rfl rfl
      · exact ChildStepKeeps.refl state
  | revokeAuthority subject =>
      simp only [ChildOperation.apply]
      exact ChildStepKeeps.of_children state _ rfl rfl

theorem childGate_keeps (state : CompositeState) (operation : ChildOperation)
    (holds : ResourceRuntimeWellFormed state) (accounting : ChildAccountingWellFormed state) :
    ChildStepKeeps state (childGate state operation).state := by
  cases hmode : state.execution.mode <;> simp only [childGate, hmode]
  · exact ChildOperation.apply_keeps state operation hmode holds accounting
  all_goals exact ChildStepKeeps.refl state

/-- A memory step keeps every entitlement: the frame commitment, the frame
list, and the child tables are unchanged. -/
theorem memoryGate_entitlement (state : CompositeState) (operation : MemoryOperation)
    (subject : Nat) :
    entitlement (memoryGate state operation).state subject = entitlement state subject := by
  have keeps := memoryGate_keeps state operation
  have children : (memoryGate state operation).state.spawn.children = state.spawn.children := by
    rw [keeps.spawn]
  simp only [entitlement, budgetLimit_of_frames _ _ subject keeps.frameBudgets keeps.frames,
    (childTable_congr children subject).1]

/-- **Memory steps keep the accounting.** -/
theorem memoryGate_childAccounting (state : CompositeState) (operation : MemoryOperation)
    (accounting : ChildAccountingWellFormed state) :
    ChildAccountingWellFormed (memoryGate state operation).state := by
  have keeps := memoryGate_keeps state operation
  have children : (memoryGate state operation).state.spawn.children = state.spawn.children := by
    rw [keeps.spawn]
  refine ⟨fun parent slot entry found => ?_,
    fun parent slot entry parent' slot' entry' f1 f2 eq => ?_,
    fun subject slot unissued => ?_, fun parent capability found => ?_⟩
  · rw [children] at found
    obtain ⟨inRange, generation, ne, issued, bound⟩ := accounting.entries parent slot entry found
    refine ⟨inRange, by rw [keeps.spawn]; exact generation, ne,
      by rw [keeps.issuedSubjects]; exact issued, ?_⟩
    rw [memoryGate_entitlement]; exact bound
  · rw [children] at f1 f2
    exact accounting.unique parent slot entry parent' slot' entry' f1 f2 eq
  · rw [children]
    rw [keeps.issuedSubjects] at unissued
    exact accounting.fresh subject slot unissued
  · rw [keeps.spawn] at found
    rw [(childTable_congr children parent).2]
    exact accounting.budget parent capability found

theorem memoryGate_childKeeps (state : CompositeState) (operation : MemoryOperation) :
    ChildStepKeeps state (memoryGate state operation).state := by
  have keeps := memoryGate_keeps state operation
  refine ⟨keeps.frames, fun frame committed => by rw [keeps.frameBudgets] at committed; exact committed,
    fun subject issued => by rw [keeps.issuedSubjects]; exact issued,
    TableAdvances.of_spawn_eq keeps.spawn, fun subject _ uncharged => ⟨?_, ?_⟩⟩
  · intro charged
    apply uncharged
    obtain ⟨parent, slot, entry, found, same⟩ := charged
    rw [keeps.spawn] at found
    exact ⟨parent, slot, entry, found, same⟩
  · rw [memoryGate_entitlement]; exact Nat.le_refl _

/-! ## Steps -/

theorem ChildTraceStep.admissible_preserves (state : CompositeState) (step : ChildTraceStep)
    (holds : ResourceRuntimeWellFormed state) (accounting : ChildAccountingWellFormed state)
    (tree : SpawnTreeWellFormed state) (admissible : step.Admissible state) :
    ResourceRuntimeWellFormed (step.apply state) ∧ ChildAccountingWellFormed (step.apply state) ∧
      SpawnTreeWellFormed (step.apply state) ∧ ChildStepKeeps state (step.apply state) := by
  cases step with
  | composite step =>
      exact ⟨step.admissible_preserves state holds admissible,
        (step.childAccounting state holds admissible accounting).1,
        step.spawnTree state holds admissible tree,
        step.keeps state holds admissible accounting⟩
  | child operation =>
      obtain ⟨h1, h2, _⟩ := childGate_preserves state operation holds accounting
      exact ⟨h1, h2, childGate_spawnTree state operation holds accounting tree,
        childGate_keeps state operation holds accounting⟩
  | memory operation =>
      exact ⟨memoryGate_preserves state operation holds,
        memoryGate_childAccounting state operation accounting,
        memoryGate_spawnTree state operation tree, memoryGate_childKeeps state operation⟩

/-- A created identity was not in the issued history before its step and is
in it afterwards. -/
theorem ChildTraceStep.created_fresh (state : CompositeState) (step : ChildTraceStep)
    (identity : Nat) (created : step.created state = some identity) :
    state.lifecycle.issuedSubjects identity = false ∧
      (step.apply state).lifecycle.issuedSubjects identity = true := by
  cases step with
  | composite step => exact step.created_fresh state identity created
  | child operation =>
      simp only [ChildTraceStep.created] at created
      split at created
      · next result =>
        simp only [Option.some.injEq] at created
        subst created
        cases hmode : state.execution.mode <;> simp only [childGate, hmode] at result
        case handling => cases result
        case halted => cases result
        simp only [ChildGateResult.completed.injEq] at result
        cases operation with
        | spawn request =>
            simp only [ChildOperation.apply] at result
            obtain ⟨slot, _, _, _, _, spawned, _, stateEq⟩ :=
              spawnCharged_spawned state request _ _ _ result
            obtain ⟨_, issued, _⟩ := spawn_spawned_stages state request _ _ spawned
            refine ⟨(issueSubject_fresh state _ issued).1, ?_⟩
            have subjects :=
              (spawn_keeps state request _ _ spawned).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
            simp only [ChildTraceStep.apply, childGate, hmode, ChildOperation.apply, stateEq]
            show (spawn state request).state.lifecycle.issuedSubjects _ = true
            rw [subjects]
            simp [SubjectLifecycle.setBool]
        | grantFrames control frames =>
            simp only [ChildOperation.apply] at result
            rcases grantFrames_shape state control frames with ⟨_, reason, rejected⟩ |
              ⟨_, _, granted⟩
            · rw [rejected] at result; cases result
            · rw [granted] at result; cases result
        | terminateChild control =>
            simp only [ChildOperation.apply] at result
            rcases terminateChild_shape state control with ⟨_, reason, rejected⟩ |
              ⟨_, _, terminated⟩
            · rw [rejected] at result; cases result
            · rw [terminated] at result; cases result
        | grantAuthority subject budget =>
            simp only [ChildOperation.apply, grantBudgetedAuthority] at result
            split at result <;> cases result
        | revokeAuthority subject => cases result
      · cases created
  | memory operation => cases created

/-! ## Whole traces -/

theorem runChildSteps_admissible (state : CompositeState) (steps : List ChildTraceStep)
    (holds : ResourceRuntimeWellFormed state) (accounting : ChildAccountingWellFormed state)
    (tree : SpawnTreeWellFormed state) (admissible : AdmissibleAlongChild state steps) :
    ResourceRuntimeWellFormed (runChildSteps state steps) ∧
      ChildAccountingWellFormed (runChildSteps state steps) ∧
      SpawnTreeWellFormed (runChildSteps state steps) ∧
      ChildStepKeeps state (runChildSteps state steps) := by
  induction steps generalizing state with
  | nil => exact ⟨holds, accounting, tree, ChildStepKeeps.refl state⟩
  | cons step rest ih =>
      obtain ⟨now, later⟩ := admissible
      obtain ⟨nextHolds, nextAccounting, nextTree, keeps⟩ :=
        step.admissible_preserves state holds accounting tree now
      obtain ⟨final, finalAccounting, finalTree, finalKeeps⟩ := ih (step.apply state) nextHolds
        nextAccounting nextTree later
      exact ⟨final, finalAccounting, finalTree, keeps.trans finalKeeps⟩

theorem createdAlongChild_fresh (state : CompositeState) (steps : List ChildTraceStep)
    (holds : ResourceRuntimeWellFormed state) (accounting : ChildAccountingWellFormed state)
    (tree : SpawnTreeWellFormed state) (admissible : AdmissibleAlongChild state steps) :
    (createdAlongChild state steps).Nodup ∧
      ∀ identity, identity ∈ createdAlongChild state steps →
        state.lifecycle.issuedSubjects identity = false ∧
          (runChildSteps state steps).lifecycle.issuedSubjects identity = true := by
  induction steps generalizing state with
  | nil => simp [createdAlongChild]
  | cons step rest ih =>
      obtain ⟨now, later⟩ := admissible
      obtain ⟨nextHolds, nextAccounting, nextTree, keeps⟩ :=
        step.admissible_preserves state holds accounting tree now
      obtain ⟨nodup, fresh⟩ := ih (step.apply state) nextHolds nextAccounting nextTree later
      have tail := (runChildSteps_admissible (step.apply state) rest nextHolds nextAccounting
        nextTree later).2.2.2
      cases created : step.created state with
      | none =>
          simp only [createdAlongChild, created, Option.toList_none, List.nil_append,
            runChildSteps]
          refine ⟨nodup, fun identity member => ?_⟩
          obtain ⟨before, after⟩ := fresh identity member
          refine ⟨?_, after⟩
          cases h : state.lifecycle.issuedSubjects identity with
          | false => rfl
          | true => rw [keeps.issued identity h] at before; cases before
      | some identity =>
          obtain ⟨before, after⟩ := step.created_fresh state identity created
          simp only [createdAlongChild, created, Option.toList_some, List.singleton_append,
            List.nodup_cons, runChildSteps]
          refine ⟨⟨fun member => ?_, nodup⟩, ?_⟩
          · have := (fresh identity member).1
            rw [after] at this; cases this
          · intro candidate member
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · exact ⟨before, tail.issued candidate after⟩
            · obtain ⟨laterBefore, laterAfter⟩ := fresh candidate member
              refine ⟨?_, laterAfter⟩
              cases h : state.lifecycle.issuedSubjects candidate with
              | false => rfl
              | true => rw [keeps.issued candidate h] at laterBefore; cases laterBefore

/-- **The whole-trace resource theorem with charged spawn and memory**
(#490, #491, ADR 0010 gate items 1 and 4).  Along every admissible trace of
composite steps, public spawn-family steps, and memory steps (budget-charged
allocation and release), from a state satisfying the combined invariant, the
accounting invariant, and the spawn-tree invariant:

- all three invariants hold at the end;
- no subject identity is created twice, and none issued before the trace is
  created again;
- the subject history only grows;
- the allocator's frame list is exactly the starting one and every frame
  committed at the end was committed at the start: no frame is ever
  created;
- every subject's usage is within its limit;
- no child in any child table has children of its own;
- every parent holding a spawn capability has at most its subject budget of
  children;
- every parent's own usage plus its children's frame limits is within its
  entitlement;
- every subject issued and not a charged child at the start never gains
  entitlement, so its children's budgets plus its own usage stay within what
  it started with;
- every retired control word is still retired at the end. -/
theorem child_resource_trace (state : CompositeState) (steps : List ChildTraceStep)
    (holds : ResourceRuntimeWellFormed state) (accounting : ChildAccountingWellFormed state)
    (tree : SpawnTreeWellFormed state) (admissible : AdmissibleAlongChild state steps) :
    ResourceRuntimeWellFormed (runChildSteps state steps) ∧
      ChildAccountingWellFormed (runChildSteps state steps) ∧
      SpawnTreeWellFormed (runChildSteps state steps) ∧
      (createdAlongChild state steps).Nodup ∧
      (∀ identity, identity ∈ createdAlongChild state steps →
        state.lifecycle.issuedSubjects identity = false) ∧
      (∀ subject, state.lifecycle.issuedSubjects subject = true →
        (runChildSteps state steps).lifecycle.issuedSubjects subject = true) ∧
      (runChildSteps state steps).virtualMemory.memory.allocator.frames =
        state.virtualMemory.memory.allocator.frames ∧
      (∀ subject, (runChildSteps state steps).budgetUsage subject ≤
        (runChildSteps state steps).budgetLimit subject) ∧
      (∀ parent slot entry, (runChildSteps state steps).spawn.children parent slot = some entry →
        ∀ childSlot, (runChildSteps state steps).spawn.children entry.child childSlot = none) ∧
      (∀ frame, ((runChildSteps state steps).frameBudgets.commitment frame).isSome = true →
        (state.frameBudgets.commitment frame).isSome = true) ∧
      (∀ parent capability, (runChildSteps state steps).spawn.authority parent = some capability →
        childCount (runChildSteps state steps) parent ≤ capability.subjectBudget) ∧
      (∀ parent, (runChildSteps state steps).budgetUsage parent +
        childLimits (runChildSteps state steps) parent ≤
          entitlement (runChildSteps state steps) parent) ∧
      (∀ subject, state.lifecycle.issuedSubjects subject = true → ¬ChargedChild state subject →
        (runChildSteps state steps).budgetUsage subject +
          childLimits (runChildSteps state steps) subject ≤ entitlement state subject) ∧
      ∀ parent word, ControlRetired state parent word →
        ControlRetired (runChildSteps state steps) parent word := by
  obtain ⟨final, finalAccounting, finalTree, keeps⟩ :=
    runChildSteps_admissible state steps holds accounting tree admissible
  obtain ⟨nodup, fresh⟩ := createdAlongChild_fresh state steps holds accounting tree admissible
  refine ⟨final, finalAccounting, finalTree, nodup, fun identity member => (fresh identity member).1,
    keeps.issued, keeps.frames, fun subject => (budget_conservation _).1 subject,
    fun parent slot entry found => (charged_child_childless finalTree found).2,
    keeps.committed, finalAccounting.budget,
    usage_add_childLimits_le _ finalAccounting, fun subject issued uncharged => ?_,
    fun parent word retired => keeps.advances.retired retired⟩
  exact Nat.le_trans (usage_add_childLimits_le _ finalAccounting subject)
    (keeps.roots subject issued uncharged).2

/-- **The boot runtime satisfies all three invariants**: the combined
invariant (`bootRuntime_resourceRuntimeWellFormed`) and, since the spawn
registry is empty, the accounting and spawn-tree invariants.  So
`child_resource_trace` applies to every admissible trace from boot. -/
theorem bootRuntime_childAccounting input plan
    (compiled : BootPageTablePlan.compile input = .ok plan) :
    ResourceRuntimeWellFormed (bootRuntime plan) ∧
      ChildAccountingWellFormed (bootRuntime plan) ∧ SpawnTreeWellFormed (bootRuntime plan) :=
  ⟨bootRuntime_resourceRuntimeWellFormed input plan compiled,
    childAccounting_of_empty _ (fun _ _ => rfl),
    spawnTree_of_empty _ (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)⟩

/-- Composite traces embed into child traces unchanged. -/
theorem runChildSteps_composite (state : CompositeState) (steps : List CompositeStep) :
    runChildSteps state (steps.map .composite) = runSteps state steps := by
  induction steps generalizing state with
  | nil => rfl
  | cons step rest ih => exact ih _

/-- **The issue #491 scenario.**  Spawn a child, terminate it, spawn again
(possibly into the same child-table slot): the first control word is
rejected by both control operations with the state unchanged. -/
theorem stale_control_after_respawn (state : CompositeState) (word : UInt64)
    (child returned : Nat) (accounting : ChildAccountingWellFormed state)
    (terminated : (terminateChild state word).result = .terminated child returned)
    (request : SpawnRequest) (frames : Nat) :
    let respawned := (childGate (terminateChild state word).state (.spawn request)).state
    spawnParent respawned = spawnParent state →
    (∃ reason, (grantFrames respawned word frames).result = .framesRejected (.control reason)) ∧
      (grantFrames respawned word frames).state = respawned ∧
      (∃ reason, (terminateChild respawned word).result = .terminateRejected reason) ∧
      (terminateChild respawned word).state = respawned := by
  intro respawned sameParent
  have retired := terminateChild_retires state word child returned accounting terminated
  have advanced := childGate_advances (terminateChild state word).state (.spawn request)
  have stillRetired := advanced.retired retired
  rw [← sameParent] at stillRetired
  exact retired_rejected_unchanged respawned word frames stillRetired

end LeanOS.FailStop
