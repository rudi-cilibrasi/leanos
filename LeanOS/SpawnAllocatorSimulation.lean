import LeanOS.SpawnAllocatorMemoryStep

/-!
# The composite spawn family simulates the bounded allocator (#575)

`Family` names the composite states the spawn family runs on: the parent is
the current subject of a running latch and holds the family's endpoint and
address-space root in slots 0 and 1 and memory or nothing in slots 2 and 3,
its children sit in the first `childCapacity` slots of its table, and the
identity, generation and frame counters stay in the representable range.
`abstraction` reads such a state as an allocator record.

**`familyStep_simulates`**: on every `Family` state, every family command
the allocator decides (`step (abstraction state) command = some result`)
runs through the composite gate to the allocator's status and value, its
post-state reads as the allocator's successor, and the post-state is again a
`Family` state.  `step` answers `none` only for a kernel authority grant the
record cannot hold (a budget past `childCapacity`, an exhausted generation,
or an accepted grant to the bystander).

So the allocator is not a table of reachable states: every theorem of
`SpawnAllocatorTheorems` about `step`, over every bounded record, is a theorem
about the composite family on the corresponding `Family` states
(`familyTrace_simulates` lifts the step to whole command traces).
-/
namespace LeanOS.SpawnAllocator

open LeanOS
open LeanOS.FailStop
open LeanOS.SpawnFamily

set_option linter.unusedSimpArgs false

/-- The composite command `command` on `state` simulates the allocator step
`result`: the same status and value, the allocator's successor as the
abstraction of its post-state, and a `Family` post-state. -/
def Simulates (state : CompositeState) (command : FamilyCommand) (result : Step) : Prop :=
  (familyStep state command).status = result.status ∧
    (familyStep state command).value = result.value ∧
    abstraction (familyStep state command).state = result.next ∧
    Family (familyStep state command).state

/-! ## The gates run the operation on a family state -/

theorem familyStep_child (state : CompositeState) (family : Family state)
    (operation : ChildOperation) :
    familyStep state (.child operation) =
      { state := (operation.apply state).state
        status := (childStatus (operation.apply state).result).1
        value := (childStatus (operation.apply state).result).2 } := by
  simp [familyStep, childGate, family.running, childGateStatus]

theorem familyStep_memory (state : CompositeState) (family : Family state)
    (operation : MemoryOperation) :
    familyStep state (.memory operation) =
      { state := (operation.apply state).state
        status := memoryStatus (operation.apply state).result
        value := 0 } := by
  simp [familyStep, memoryGate, family.running, memoryGateStatus]

/-- A child operation simulates an allocator step when its status and value
are the allocator's and an accepted step keeps the abstraction and the
family; rejections keep the pre-state on both sides. -/
theorem child_simulates (state : CompositeState) (family : Family state)
    (operation : ChildOperation) (result : Step)
    (status : childStatus (operation.apply state).result = (result.status, result.value))
    (rejectedNext : result.status ≠ 0x01 → result.next = abstraction state)
    (acceptedNext : result.status = 0x01 → abstraction (operation.apply state).state = result.next)
    (acceptedFamily : result.status = 0x01 → Family (operation.apply state).state) :
    Simulates state (.child operation) result := by
  unfold Simulates
  rw [familyStep_child state family operation]
  simp only [status]
  refine ⟨trivial, trivial, ?_⟩
  by_cases accepted : result.status = 0x01
  · exact ⟨acceptedNext accepted, acceptedFamily accepted⟩
  · have rejected : (operation.apply state).result.rejected = true := by
      rcases childStatus_accepted_or_rejected (operation.apply state).result with ok | rejected
      · rw [status] at ok; exact absurd ok accepted
      · exact rejected
    rw [ChildOperation.apply_rejected_unchanged state operation rejected, rejectedNext accepted]
    exact ⟨rfl, family⟩

theorem memory_simulates (state : CompositeState) (family : Family state)
    (operation : MemoryOperation) (result : Step)
    (status : memoryStatus (operation.apply state).result = result.status)
    (value : result.value = 0)
    (rejectedNext : result.status ≠ 0x01 → result.next = abstraction state)
    (acceptedNext : result.status = 0x01 → abstraction (operation.apply state).state = result.next)
    (acceptedFamily : result.status = 0x01 → Family (operation.apply state).state) :
    Simulates state (.memory operation) result := by
  unfold Simulates
  rw [familyStep_memory state family operation]
  simp only [status, value]
  refine ⟨trivial, trivial, ?_⟩
  by_cases accepted : result.status = 0x01
  · exact ⟨acceptedNext accepted, acceptedFamily accepted⟩
  · obtain ⟨reason, rejected⟩ :
        ∃ reason, (operation.apply state).result = .rejected reason := by
      rcases memoryStatus_accepted_or_rejected (operation.apply state).result with ok | rejected
      · rw [status] at ok; exact absurd ok accepted
      · exact rejected
    rw [MemoryOperation.apply_rejected_unchanged state operation reason rejected,
      rejectedNext accepted]
    exact ⟨rfl, family⟩

/-! ## The kernel authority commands -/

/-- The composite after replacing the spawn-authority map and the next
authority generation. -/
def withAuthority (state : CompositeState) (authority : Nat → Option SpawnCapability)
    (nextGeneration : Nat) : CompositeState :=
  { state with spawn := { state.spawn with authority, nextGeneration } }

/-- Changing only spawn authority keeps the family when the parent's
authority stays bounded, no other subject gains authority, and the
generation counter stays representable. -/
theorem family_withAuthority (state : CompositeState) (family : Family state)
    (authority : Nat → Option SpawnCapability) (nextGeneration : Nat)
    (resources : ResourceRuntimeWellFormed (withAuthority state authority nextGeneration))
    (accounting : ChildAccountingWellFormed (withAuthority state authority nextGeneration))
    (tree : SpawnTreeWellFormed (withAuthority state authority nextGeneration))
    (parentAuthority : ∀ capability, authority parent = some capability →
      capability.subjectBudget ≤ childCapacity ∧ 0 < capability.generation ∧
        capability.generation < nextGeneration)
    (others : ∀ subject, subject ≠ parent → authority subject = none)
    (bound : 0 < nextGeneration ∧ nextGeneration < wordBound) :
    Family (withAuthority state authority nextGeneration) :=
  ⟨resources, accounting, tree, family.running, family.current, family.lifecycleCurrent,
    family.capacity, family.parentLive, family.parentRoot, family.endpoint, family.space,
    family.memory, family.memoryDistinct, family.childSlots, parentAuthority, others,
    family.childLive, family.live, family.committed, family.framesNodup, family.parentNames,
    family.fresh, family.parentFree, family.usage, family.capabilityBound, family.controlBound,
    bound, family.frameBound⟩

/-- The abstraction after an authority change. -/
theorem abstraction_withAuthority (state : CompositeState) (authority : Nat → Option SpawnCapability)
    (nextGeneration : Nat) :
    abstraction (withAuthority state authority nextGeneration) =
      { abstraction state with
        authorityNext := nextGeneration
        authority := (authority parent).map SpawnCapability.generation
        budget := match authority parent with
          | some capability => capability.subjectBudget
          | none => 0 } := rfl

/-- The authority-grant map. -/
def grantedAuthority (state : CompositeState) (subject budget : Nat) :
    Nat → Option SpawnCapability :=
  fun candidate => if candidate = subject then
    some { generation := state.spawn.nextGeneration, subjectBudget := budget }
    else state.spawn.authority candidate

theorem grantBudgetedAuthority_eq (state : CompositeState) (subject budget : Nat) :
    grantBudgetedAuthority state subject budget =
      if state.capabilities.subjects subject = true ∧ budget ≤ childSlots ∧
          childCount state subject ≤ budget ∧ state.spawn.parent subject = none then
        { state := withAuthority state (grantedAuthority state subject budget)
            (state.spawn.nextGeneration + 1)
          result := .authorityGranted state.spawn.nextGeneration }
      else { state, result := .authorityRejected } := rfl

/-- A child of the parent is recorded as its child, so the kernel never
grants it authority. -/
theorem family_child_recorded (state : CompositeState) (family : Family state) (subject : Nat)
    (live : state.capabilities.subjects subject = true) (notParent : subject ≠ parent)
    (notBystander : subject ≠ bystander) :
    state.spawn.parent subject = some parent := by
  rcases family.live subject live with same | same | ⟨slot, entry, found, child⟩
  · exact absurd same notBystander
  · exact absurd same notParent
  · rw [← child]; exact family.tree.recorded parent slot entry found

theorem grantAuthority_simulates (state : CompositeState) (family : Family state)
    (subject budget : Nat) (result : Step)
    (decided : grantAuthorityStep (abstraction state) subject budget = some result) :
    Simulates state (.child (.grantAuthority subject budget)) result := by
  have rejectedCase : grantAuthorityStep (abstraction state) subject budget =
      some (authorityRejected (abstraction state)) →
      (grantBudgetedAuthority state subject budget).result = .authorityRejected →
      Simulates state (.child (.grantAuthority subject budget)) result := by
    intro allocatorRejected compositeRejected
    rw [allocatorRejected] at decided
    cases decided
    apply child_simulates state family _ _
    · simp only [ChildOperation.apply, compositeRejected, childStatus, authorityRejected]
    · intro _; rfl
    · intro accepted; simp [authorityRejected] at accepted
    · intro accepted; simp [authorityRejected] at accepted
  have rejectedResult : ¬(state.capabilities.subjects subject = true ∧ budget ≤ childSlots ∧
      childCount state subject ≤ budget ∧ state.spawn.parent subject = none) →
      (grantBudgetedAuthority state subject budget).result = .authorityRejected := by
    intro notGranted
    rw [grantBudgetedAuthority_eq]; simp only [notGranted, ↓reduceIte]
  by_cases isParent : subject = parent
  · subst isParent
    have count := childCount_family state family
    by_cases within : budget ≤ childSlots ∧ (abstraction state).childCount ≤ budget
    · have stepEq := decided
      unfold grantAuthorityStep at stepEq
      simp only [within, and_self, ↓reduceIte] at stepEq
      split at stepEq
      · cases stepEq
      next representable =>
      cases stepEq
      have granted : state.capabilities.subjects parent = true ∧ budget ≤ childSlots ∧
          childCount state parent ≤ budget ∧ state.spawn.parent parent = none :=
        ⟨family.parentLive, within.1, by rw [count]; exact within.2, family.parentRoot⟩
      have applied : (grantBudgetedAuthority state parent budget) =
          { state := withAuthority state (grantedAuthority state parent budget)
              (state.spawn.nextGeneration + 1)
            result := .authorityGranted state.spawn.nextGeneration } := by
        rw [grantBudgetedAuthority_eq]; simp only [granted, and_self, ↓reduceIte]
      have notOver : budget ≤ childCapacity ∧
          state.spawn.nextGeneration + 1 < wordBound := by
        simp only [not_or, Nat.not_lt, Nat.not_le] at representable
        exact representable
      apply child_simulates state family _ _
      · simp only [ChildOperation.apply, applied, childStatus, acceptWith]
        rfl
      · intro rejected; simp [acceptWith] at rejected
      · intro _
        simp only [ChildOperation.apply, applied, acceptWith]
        rw [abstraction_withAuthority]
        simp [grantedAuthority]
        rfl
      · intro _
        simp only [ChildOperation.apply, applied]
        have invariants := family_childGate_invariants state family (.grantAuthority parent budget)
        simp only [ChildOperation.apply, applied] at invariants
        obtain ⟨resources, accounting, tree⟩ := invariants
        refine family_withAuthority state family _ _ resources accounting tree ?_ ?_ ?_
        · intro capability held
          simp only [grantedAuthority, ↓reduceIte, Option.some.injEq] at held
          subst held
          exact ⟨notOver.1, family.generationBound.1, Nat.lt_succ_self _⟩
        · intro other ne
          simp only [grantedAuthority, ne, ↓reduceIte]
          exact family.others other ne
        · exact ⟨Nat.succ_pos _, notOver.2⟩
    · have stepEq := decided
      unfold grantAuthorityStep at stepEq
      simp only [within, ↓reduceIte] at stepEq
      apply rejectedCase (by unfold grantAuthorityStep; simp only [within, ↓reduceIte])
      apply rejectedResult
      rintro ⟨_, small, counted, _⟩
      exact within ⟨small, by rw [← count]; exact counted⟩
  · by_cases isBystander : subject = bystander
    · subst isBystander
      have over : ¬budget ≤ childSlots := by
        intro small
        unfold grantAuthorityStep at decided
        simp [isParent, small] at decided
      apply rejectedCase (by unfold grantAuthorityStep; simp [isParent, over])
      apply rejectedResult
      rintro ⟨_, small, _⟩
      exact over small
    · apply rejectedCase (by unfold grantAuthorityStep; simp [isParent, isBystander])
      apply rejectedResult
      rintro ⟨live, _, _, root⟩
      rw [family_child_recorded state family subject live isParent isBystander] at root
      cases root

/-- The revocation map. -/
def revokedAuthority (state : CompositeState) (subject : Nat) : Nat → Option SpawnCapability :=
  fun candidate => if candidate = subject then none else state.spawn.authority candidate

theorem revokeSpawnAuthority_eq (state : CompositeState) (subject : Nat) :
    revokeSpawnAuthority state subject =
      withAuthority state (revokedAuthority state subject) state.spawn.nextGeneration := rfl

theorem revokeAuthority_simulates (state : CompositeState) (family : Family state)
    (subject : Nat) :
    Simulates state (.child (.revokeAuthority subject)) (revokeAuthorityStep (abstraction state) subject) := by
  have invariants := family_childGate_invariants state family (.revokeAuthority subject)
  simp only [ChildOperation.apply, revokeSpawnAuthority_eq] at invariants
  obtain ⟨resources, accounting, tree⟩ := invariants
  apply child_simulates state family _ _
  · simp only [ChildOperation.apply, childStatus, revokeAuthorityStep]
    split <;> rfl
  · intro rejected; unfold revokeAuthorityStep at rejected; split at rejected <;> simp [acceptWith] at rejected
  · intro _
    simp only [ChildOperation.apply, revokeSpawnAuthority_eq, abstraction_withAuthority,
      revokeAuthorityStep]
    by_cases isParent : subject = parent
    · subst isParent
      simp [revokedAuthority, acceptWith]
      rfl
    · simp only [isParent, ↓reduceIte, acceptWith, revokedAuthority, Ne.symm isParent]
      rfl
  · intro _
    simp only [ChildOperation.apply, revokeSpawnAuthority_eq]
    refine family_withAuthority state family _ _ resources accounting tree ?_ ?_
      family.generationBound
    · intro capability held
      by_cases isParent : subject = parent
      · subst isParent; simp [revokedAuthority] at held
      · simp only [revokedAuthority, Ne.symm isParent, ↓reduceIte] at held
        exact family.authority capability held
    · intro other ne
      simp only [revokedAuthority]
      split
      · rfl
      · exact family.others other ne

/-! ## Every decided command -/

theorem allocateStep_value (record : State) (slot : Nat) : (allocateStep record slot).value = 0 := by
  by_cases accepted : (allocateStep record slot).status = 0x01
  · obtain ⟨_, _, _, _, _, _, stepEq⟩ := allocateStep_accepted record slot accepted
    rw [stepEq]; rfl
  · exact step_rejected_value record (.memory (.allocate slot)) _ rfl accepted

theorem releaseStep_value (record : State) (slot : Nat) : (releaseStep record slot).value = 0 := by
  by_cases accepted : (releaseStep record slot).status = 0x01
  · obtain ⟨_, _, _, _, stepEq⟩ := releaseStep_accepted record slot accepted
    rw [stepEq]; rfl
  · exact step_rejected_value record (.memory (.release slot)) _ rfl accepted

/-- **The composite spawn family simulates the bounded allocator.**  On every
`Family` state, every command the allocator decides runs through the
composite gate to the allocator's status and value, its post-state reads as
the allocator's successor, and the post-state is again a `Family` state. -/
theorem familyStep_simulates (state : CompositeState) (family : Family state)
    (command : FamilyCommand) (allocatorCommand : Command) (result : Step)
    (translated : toCommand command = some allocatorCommand)
    (decided : step (abstraction state) allocatorCommand = some result) :
    Simulates state command result := by
  cases command with
  | switch => cases translated
  | copy => cases translated
  | child operation =>
      cases translated
      cases operation with
      | spawn request =>
          cases decided
          apply child_simulates state family (.spawn request) (spawnStep (abstraction state) request)
            ((spawnCharged_family state family request).1)
          · exact step_rejected_unchanged _ (.child (.spawn request)) _ rfl
          · exact spawnCharged_abstraction state family request
          · exact spawnCharged_family_preserved state family request
      | grantFrames control frames =>
          cases decided
          apply child_simulates state family (.grantFrames control frames)
            (grantStep (abstraction state) control frames)
            (grantFrames_status_family state family control frames)
          · exact step_rejected_unchanged _ (.child (.grantFrames control frames)) _ rfl
          · exact grantFrames_abstraction state family control frames
          · exact grantFrames_family_preserved state family control frames
      | terminateChild control =>
          cases decided
          apply child_simulates state family (.terminateChild control)
            (terminateStep (abstraction state) control)
            (terminateChild_status_family state family control)
          · exact step_rejected_unchanged _ (.child (.terminateChild control)) _ rfl
          · exact terminateChild_abstraction state family control
          · exact terminateChild_family_preserved state family control
      | grantAuthority subject budget =>
          exact grantAuthority_simulates state family subject budget result decided
      | revokeAuthority subject =>
          cases decided
          exact revokeAuthority_simulates state family subject
  | memory operation =>
      cases translated
      cases operation with
      | allocate slot =>
          cases decided
          apply memory_simulates state family (.allocate slot) (allocateStep (abstraction state) slot)
            (allocateMemory_status_family state family slot)
            (allocateStep_value _ slot)
          · exact step_rejected_unchanged _ (.memory (.allocate slot)) _ rfl
          · exact allocateMemory_abstraction state family slot
          · exact allocateMemory_family_preserved state family slot
      | release slot =>
          cases decided
          apply memory_simulates state family (.release slot) (releaseStep (abstraction state) slot)
            (releaseMemory_status_family state family slot)
            (releaseStep_value _ slot)
          · exact step_rejected_unchanged _ (.memory (.release slot)) _ rfl
          · exact releaseMemory_abstraction state family slot
          · exact releaseMemory_family_preserved state family slot

/-- The only commands `step` leaves undecided are kernel authority grants. -/
theorem step_undecided (record : State) (command : Command) (undecided : step record command = none) :
    ∃ subject budget, command = .child (.grantAuthority subject budget) := by
  cases command with
  | child operation =>
      cases operation with
      | grantAuthority subject budget => exact ⟨subject, budget, rfl⟩
      | _ => cases undecided
  | memory operation => cases operation <;> cases undecided

/-! ## Whole traces -/

/-- Run the allocator over a list of commands, stopping at the first
undecided one. -/
def runSteps (record : State) : List Command → Option (State × List (UInt64 × UInt64))
  | [] => some (record, [])
  | command :: rest =>
      match step record command with
      | none => none
      | some result => (runSteps result.next rest).map fun run =>
          (run.1, (result.status, result.value) :: run.2)

/-- The replies of the composite family over a list of commands
(`SpawnFamily.runFamily` is its final state). -/
def familyReplies (state : CompositeState) : List FamilyCommand → List (UInt64 × UInt64)
  | [] => []
  | command :: rest =>
      ((familyStep state command).status, (familyStep state command).value) ::
        familyReplies (familyStep state command).state rest

/-- **Whole traces simulate.**  From a `Family` state, a list of family
commands the allocator decides end to end produces the allocator's replies,
ends in a `Family` state, and its final state reads as the allocator's final
record. -/
theorem familyTrace_simulates (state : CompositeState) (family : Family state)
    (commands : List FamilyCommand) (allocatorCommands : List Command)
    (translated : commands.map toCommand = allocatorCommands.map some)
    (record : State) (replies : List (UInt64 × UInt64))
    (decided : runSteps (abstraction state) allocatorCommands = some (record, replies)) :
    familyReplies state commands = replies ∧ abstraction (runFamily state commands) = record ∧
      Family (runFamily state commands) := by
  induction commands generalizing state allocatorCommands record replies with
  | nil =>
      cases allocatorCommands with
      | nil =>
          simp only [runSteps, Option.some.injEq, Prod.mk.injEq] at decided
          obtain ⟨recordEq, repliesEq⟩ := decided
          subst recordEq repliesEq
          exact ⟨rfl, rfl, family⟩
      | cons => cases translated
  | cons command rest ih =>
      cases allocatorCommands with
      | nil => cases translated
      | cons allocatorCommand allocatorRest =>
          simp only [List.map_cons, List.cons.injEq] at translated
          obtain ⟨head, tail⟩ := translated
          simp only [runSteps] at decided
          cases stepped : step (abstraction state) allocatorCommand with
          | none => rw [stepped] at decided; cases decided
          | some result =>
              rw [stepped] at decided
              dsimp only at decided
              obtain ⟨status, value, next, nextFamily⟩ :=
                familyStep_simulates state family command allocatorCommand result head stepped
              cases restRun : runSteps result.next allocatorRest with
              | none => rw [restRun] at decided; cases decided
              | some run =>
                  rw [restRun] at decided
                  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at decided
                  obtain ⟨recordEq, repliesEq⟩ := decided
                  rw [← next] at restRun
                  obtain ⟨restReplies, restRecord, restFamily⟩ :=
                    ih (familyStep state command).state nextFamily allocatorRest tail run.1 run.2
                      restRun
                  simp only [familyReplies, runFamily]
                  refine ⟨?_, ?_, restFamily⟩
                  · rw [restReplies, status, value, ← repliesEq]
                  · rw [restRecord, recordEq]

end LeanOS.SpawnAllocator
