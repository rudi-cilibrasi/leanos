import LeanOS.FailStop.SpawnAccountingInvariants

/-!
# Fail-stop composite: stale child authority and cleanup on termination

Issue #491 and gate item 4 of ADR 0010.

## Control handles stay stale

A parent names a child by the control word an accepted spawn returned: the
child-table slot and the entry's generation (`controlWord`).  After
`terminateChild` the slot is empty (`terminateChild_retires`).  A later spawn
may reuse the slot, but its entry takes the next generation from the
never-reused counter, so the old word still names no entry.

`ControlRetired state parent word` says the word decodes, its generation was
already issued, and the parent's slot holds no entry of that generation.
Every step of the public spawn family and every composite step keeps it
(`childGate_retired`, `CompositeStep.retired`, through `TableAdvances`), and
a retired word is rejected by both control operations with the pre-state
(`retired_rejected_unchanged`).

## Capabilities naming the child

Child termination runs the composite termination transition.  Every
capability held by the child, and every capability any subject holds over an
object the child owned (an endpoint, an address space, or memory), is removed
(`terminateChild_revokes`).  So a handle word that named such a capability,
for example a parent's endpoint to the child, no longer resolves
(`terminateChild_stale_word`), and it still does not resolve after a new child
is spawned (`stale_word_after_respawn`): spawn changes no slot of an
existing subject.

## Cleanup

`terminateChild_releases` collects what termination gives back: the child is
not live and holds nothing, is not runnable, owns no address space, its
frames are committed to the parent again, and its child-table entry and
spawn records are gone.
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

/-! ## Retired control words -/

/-- A control word whose generation was issued and whose slot no longer holds
an entry of that generation. -/
def ControlRetired (state : CompositeState) (parent : Nat) (word : UInt64) : Prop :=
  ∃ handle, CapabilityHandle.decode word = .ok handle ∧
    handle.identity < state.spawn.nextChildGeneration ∧
    ∀ entry, state.spawn.children parent handle.slot = some entry →
      entry.generation ≠ handle.identity

/-- The child table only gains entries with fresh generations: the counter
never decreases, and every entry after the step either was there before with
the same generation or has a generation at least the old counter. -/
def TableAdvances (before after : CompositeState) : Prop :=
  before.spawn.nextChildGeneration ≤ after.spawn.nextChildGeneration ∧
    ∀ parent slot entry, after.spawn.children parent slot = some entry →
      (∃ old, before.spawn.children parent slot = some old ∧
        old.generation = entry.generation) ∨
        before.spawn.nextChildGeneration ≤ entry.generation

theorem TableAdvances.refl (state : CompositeState) : TableAdvances state state :=
  ⟨Nat.le_refl _, fun _ _ entry found => Or.inl ⟨entry, found, rfl⟩⟩

theorem TableAdvances.retired {before after : CompositeState}
    (advances : TableAdvances before after) {parent : Nat} {word : UInt64}
    (retired : ControlRetired before parent word) : ControlRetired after parent word := by
  obtain ⟨handle, decoded, issued, stale⟩ := retired
  refine ⟨handle, decoded, Nat.lt_of_lt_of_le issued advances.1, fun entry found same => ?_⟩
  rcases advances.2 parent handle.slot entry found with ⟨old, oldFound, generation⟩ | fresh
  · exact stale old oldFound (generation.trans same)
  · omega

theorem TableAdvances.of_spawn_eq {before after : CompositeState}
    (same : after.spawn = before.spawn) : TableAdvances before after := by
  rw [TableAdvances, same]; exact TableAdvances.refl before

/-- **A retired control word is rejected with the pre-state** by both control
operations. -/
theorem retired_rejected_unchanged (state : CompositeState) (word : UInt64) (frames : Nat)
    (retired : ControlRetired state (spawnParent state) word) :
    (∃ reason, (grantFrames state word frames).result = .framesRejected (.control reason)) ∧
      (grantFrames state word frames).state = state ∧
      (∃ reason, (terminateChild state word).result = .terminateRejected reason) ∧
      (terminateChild state word).state = state := by
  obtain ⟨handle, decoded, _, stale⟩ := retired
  obtain ⟨reason, denied⟩ := resolveControl_stale state word handle decoded stale
  refine ⟨⟨reason, by simp [grantFrames, denied]⟩, by simp [grantFrames, denied],
    ⟨reason, by simp [terminateChild, denied]⟩, by simp [terminateChild, denied]⟩

/-- Every step of the public spawn family advances the child table. -/
theorem ChildOperation.apply_advances (state : CompositeState) (operation : ChildOperation) :
    TableAdvances state (operation.apply state).state := by
  cases operation with
  | spawn request =>
      simp only [ChildOperation.apply]
      rcases spawnCharged_result state request with ⟨child, addressSpace, control, result⟩ |
        ⟨reason, result⟩
      · obtain ⟨slot, _, _, _, _, spawned, _, stateEq⟩ :=
          spawnCharged_spawned state request child addressSpace control result
        obtain ⟨childrenEq, nextEq, _⟩ := spawn_childTable state request child addressSpace spawned
        rw [stateEq]
        refine ⟨by simp only [installChild, nextEq]; omega, fun parent candidateSlot entry found => ?_⟩
        simp only [installChild, childrenEq, nextEq] at found
        split at found
        · simp only [Option.some.injEq] at found
          subst found
          exact Or.inr (Nat.le_refl _)
        · exact Or.inl ⟨entry, found, rfl⟩
      · rw [spawnCharged_rejected_unchanged state request reason result]
        exact TableAdvances.refl state
  | grantFrames control frames =>
      simp only [ChildOperation.apply]
      rcases grantFrames_result state control frames with ⟨child, moved, result⟩ |
        ⟨reason, result⟩
      · obtain ⟨slot, entry, resolved, _, _, _, _, stateEq⟩ :=
          grantFrames_granted state control frames child moved result
        obtain ⟨_, _, found⟩ := resolveControl_ok resolved
        rw [stateEq]
        refine ⟨Nat.le_refl _, fun parent candidateSlot entry' found' => ?_⟩
        simp only [setChildEntry] at found'
        split at found'
        · next h =>
          obtain ⟨rfl, rfl⟩ := h
          simp only [Option.some.injEq] at found'
          subst found'
          exact Or.inl ⟨entry, found, rfl⟩
        · exact Or.inl ⟨entry', found', rfl⟩
      · rw [grantFrames_rejected_unchanged state control frames reason result]
        exact TableAdvances.refl state
  | terminateChild control =>
      simp only [ChildOperation.apply]
      rcases terminateChild_result state control with ⟨child, returned, result⟩ |
        ⟨reason, result⟩
      · obtain ⟨slot, entry, _, _, _, stateEq⟩ :=
          terminateChild_terminated state control child returned result
        have spawnT : (terminatedChild state child).spawn = state.spawn :=
          authoritativeGate_frames state _ .spawn
            ((AuthoritativeOperation.ordinary (.terminateSubject child)).footprint.unread_is_untouched
              .spawn (footprints_unread_spawn.2.1 _))
        rw [stateEq]
        refine ⟨by simp only [releaseChild, spawnT]; exact Nat.le_refl _,
          fun parent candidateSlot entry' found' => ?_⟩
        simp only [releaseChild, spawnT] at found'
        split at found'
        · cases found'
        · exact Or.inl ⟨entry', found', rfl⟩
      · rw [terminateChild_rejected_unchanged state control reason result]
        exact TableAdvances.refl state
  | grantAuthority subject budget =>
      simp only [ChildOperation.apply, grantBudgetedAuthority]
      split
      · exact ⟨Nat.le_refl _, fun _ _ entry found => Or.inl ⟨entry, found, rfl⟩⟩
      · exact TableAdvances.refl state
  | revokeAuthority subject =>
      exact ⟨Nat.le_refl _, fun _ _ entry found => Or.inl ⟨entry, found, rfl⟩⟩

theorem childGate_advances (state : CompositeState) (operation : ChildOperation) :
    TableAdvances state (childGate state operation).state := by
  cases hmode : state.execution.mode <;> simp only [childGate, hmode]
  · exact ChildOperation.apply_advances state operation
  all_goals exact TableAdvances.refl state

theorem CompositeStep.advances (state : CompositeState) (step : CompositeStep) :
    TableAdvances state (step.apply state) :=
  TableAdvances.of_spawn_eq (step.apply_spawn state)

/-- **A terminated child's control word is retired.** -/
theorem terminateChild_retires (state : CompositeState) (word : UInt64) (child returned : Nat)
    (accounting : ChildAccountingWellFormed state)
    (terminated : (terminateChild state word).result = .terminated child returned) :
    ControlRetired (terminateChild state word).state (spawnParent state) word := by
  obtain ⟨slot, entry, resolved, _, _, stateEq⟩ :=
    terminateChild_terminated state word child returned terminated
  obtain ⟨_, decoded, found⟩ := resolveControl_ok resolved
  have generation := (accounting.entries _ _ _ found).2.1
  have spawnT : (terminatedChild state child).spawn = state.spawn :=
    authoritativeGate_frames state _ .spawn
      ((AuthoritativeOperation.ordinary (.terminateSubject child)).footprint.unread_is_untouched
        .spawn (footprints_unread_spawn.2.1 _))
  refine ⟨controlHandle slot entry.generation, decoded, ?_, fun entry' found' => ?_⟩
  · rw [stateEq]; simp only [releaseChild, spawnT, controlHandle]; exact generation
  · rw [stateEq] at found'
    simp [releaseChild, spawnT, controlHandle] at found'

/-! ## Capabilities naming the child -/

/-- An object owned by `subject` in the lifecycle: an endpoint, an address
space, or memory. -/
def OwnedBy (lifecycle : SubjectLifecycle.State) (subject object : Nat) : Prop :=
  lifecycle.endpointOwner object = some subject ∨ lifecycle.addressOwner object = some subject ∨
    (lifecycle.ownedMemory object).any (fun owner => owner.1 = subject) = true

/-- **Terminating a child revokes every capability naming it.**  Every slot
the child held, and every slot any subject held over an object the child
owned, is empty after the termination. -/
theorem terminateChild_revokes (state : CompositeState) (word : UInt64) (child returned : Nat)
    (running : state.execution.mode = .running) (holds : ResourceRuntimeWellFormed state)
    (terminated : (terminateChild state word).result = .terminated child returned)
    (holder slot : Nat) (capability : Capability.Capability)
    (held : state.capabilities.slots holder slot = some capability)
    (names : holder = child ∨ OwnedBy state.lifecycle child capability.object) :
    (terminateChild state word).state.capabilities.slots holder slot = none := by
  obtain ⟨childSlot, entry, _, _, _, stateEq⟩ :=
    terminateChild_terminated state word child returned terminated
  rw [stateEq]
  show (terminatedChild state child).capabilities.slots holder slot = none
  have runtime := holds.1.left
  have coherent := runtime.1
  have lifecycleWf := runtime.2.2.1
  have capsEq : state.capabilities = state.lifecycle.capabilities := coherent.2.2.2.1
  have resumableLifecycle : state.resumable.scheduler.lifecycle = state.lifecycle := by
    rw [coherent.2.2.2.2.2.2.2.1, coherent.2.1]
  simp only [terminatedChild, authoritativeGate_ordinary_state]
  cases accepted : (SubjectLifecycle.terminate state.lifecycle child).result with
  | accepted =>
      simp only [gate, running, applyOperation, accepted]
      simp only [installTerminatedSubject, installTerminatedResumable,
        ResumablePreemption.cleanupSubject, ResumablePreemption.retireOwnedAddressSpaces,
        SubjectLifecycle.terminateState, SubjectLifecycle.terminatedCapabilities,
        resumableLifecycle]
      rw [capsEq] at held
      simp only [held]
      simp only [OwnedBy] at names
      rcases names with same | endpoint | address | memory
      · simp [same]
      · simp [endpoint]
      · split
        · rfl
        · rename_i kept found
          split at found
          · cases found
          · simp only [Option.some.injEq] at found
            subst found
            simp [address]
      · simp [memory]
  | rejected reason =>
      exfalso
      have live : state.lifecycle.capabilities.subjects child = true := by
        rcases names with same | endpoint | address | memory
        · subst same
          rw [← capsEq]
          exact (runtime.2.2.2.1.1 _ _ _ held).1
        · exact lifecycleWf.2.2.2.1 _ _ endpoint
        · exact lifecycleWf.2.2.1 _ _ address
        · cases owned : state.lifecycle.ownedMemory capability.object with
          | none => simp [owned] at memory
          | some owner =>
              simp only [owned, Option.any_some, decide_eq_true_eq] at memory
              obtain ⟨subject, frame⟩ := owner
              simp only at memory
              subst memory
              exact (lifecycleWf.2.1 _ _ _ owned).1
      have issued := lifecycleWf.1 child live
      simp [SubjectLifecycle.terminate, issued, live] at accepted

/-- **A handle word naming a terminated child's object is stale.**  If a
subject's word resolved, before the termination, to a capability over an
object the child owned (for example the parent's endpoint to the child), the
same word does not resolve afterwards. -/
theorem terminateChild_stale_word (state : CompositeState) (word : UInt64) (child returned : Nat)
    (running : state.execution.mode = .running) (holds : ResourceRuntimeWellFormed state)
    (terminated : (terminateChild state word).result = .terminated child returned)
    (holder : Nat) (handleWord : UInt64) (kind : Capability.ObjectKind)
    (resolution : CapabilityHandle.Resolution)
    (resolved : CapabilityHandle.resolveCurrent state.capabilities { caller := holder } handleWord
      kind = .ok resolution)
    (names : holder = child ∨ OwnedBy state.lifecycle child resolution.capability.object) :
    ∃ reason, CapabilityHandle.resolveCurrent (terminateChild state word).state.capabilities
      { caller := holder } handleWord kind = .error reason := by
  obtain ⟨decoded, _, _, held, _⟩ := CapabilityHandle.resolveCurrent_sound _ _ _ _ _ resolved
  have cleared := terminateChild_revokes state word child returned running holds terminated
    holder _ _ held names
  cases after : CapabilityHandle.resolveCurrent (terminateChild state word).state.capabilities
      { caller := holder } handleWord kind with
  | error reason => exact ⟨reason, rfl⟩
  | ok later =>
      obtain ⟨decodedLater, _, _, heldLater, _⟩ :=
        CapabilityHandle.resolveCurrent_sound _ _ _ _ _ after
      rw [decoded] at decodedLater
      simp only [Except.ok.injEq] at decodedLater
      rw [← decodedLater, cleared] at heldLater
      cases heldLater

/-- **Still stale after a new child takes the slot.**  A charged spawn
changes no slot of an existing subject, so a capability slot emptied by the
termination stays empty, and the stale word keeps failing. -/
theorem stale_slot_after_respawn (state : CompositeState) (request : SpawnRequest)
    (holds : ResourceRuntimeWellFormed state) (holder slot : Nat)
    (issued : state.lifecycle.issuedSubjects holder = true)
    (cleared : state.capabilities.slots holder slot = none) :
    (spawnCharged state request).state.capabilities.slots holder slot = none := by
  rcases spawnCharged_result state request with ⟨child, addressSpace, control, result⟩ |
    ⟨reason, result⟩
  · obtain ⟨_, _, _, _, _, spawned, _, stateEq⟩ :=
      spawnCharged_spawned state request child addressSpace control result
    rw [stateEq]
    show (spawn state request).state.capabilities.slots holder slot = none
    have unissued := (spawn_fresh_identity state request child addressSpace holds spawned).2.1
    have ne : holder ≠ child := by
      intro same; rw [same, unissued] at issued; cases issued
    rw [spawn_other_slots_unchanged state request child addressSpace holds.1.left spawned holder ne]
    exact cleared
  · rw [spawnCharged_rejected_unchanged state request reason result]
    exact cleared

/-- **Stale after reuse.**  A word that resolved to a capability over a
terminated child's object stays unresolvable after a new child is spawned. -/
theorem stale_word_after_respawn (state : CompositeState) (word : UInt64) (child returned : Nat)
    (running : state.execution.mode = .running) (holds : ResourceRuntimeWellFormed state)
    (accounting : ChildAccountingWellFormed state)
    (terminated : (terminateChild state word).result = .terminated child returned)
    (request : SpawnRequest)
    (holder : Nat) (handleWord : UInt64) (kind : Capability.ObjectKind)
    (resolution : CapabilityHandle.Resolution)
    (resolved : CapabilityHandle.resolveCurrent state.capabilities { caller := holder } handleWord
      kind = .ok resolution)
    (names : holder = child ∨ OwnedBy state.lifecycle child resolution.capability.object) :
    ∃ reason, CapabilityHandle.resolveCurrent
      (spawnCharged (terminateChild state word).state request).state.capabilities
      { caller := holder } handleWord kind = .error reason := by
  obtain ⟨decoded, live, _, held, _⟩ := CapabilityHandle.resolveCurrent_sound _ _ _ _ _ resolved
  have cleared := terminateChild_revokes state word child returned running holds terminated
    holder _ _ held names
  obtain ⟨holdsPost, _, _⟩ := terminateChild_preserves state word holds accounting
  have issued : (terminateChild state word).state.lifecycle.issuedSubjects holder = true := by
    obtain ⟨_, _, _, _, _, stateEq⟩ :=
      terminateChild_terminated state word child returned terminated
    have agrees := (terminatedChild_facts state child holds).2.1
    rw [stateEq]
    show (terminatedChild state child).lifecycle.issuedSubjects holder = true
    rw [agrees.2.2.2.1]
    exact live_issued holds.1.left live
  have stillCleared := stale_slot_after_respawn _ request holdsPost holder _ issued cleared
  cases after : CapabilityHandle.resolveCurrent
      (spawnCharged (terminateChild state word).state request).state.capabilities
      { caller := holder } handleWord kind with
  | error reason => exact ⟨reason, rfl⟩
  | ok later =>
      obtain ⟨decodedLater, _, _, heldLater, _⟩ :=
        CapabilityHandle.resolveCurrent_sound _ _ _ _ _ after
      rw [decoded] at decodedLater
      simp only [Except.ok.injEq] at decodedLater
      rw [← decodedLater, stillCleared] at heldLater
      cases heldLater

/-! ## Cleanup on termination -/

/-- **Terminating a child releases everything it was given** (gate item 4).
After an accepted `terminateChild`: the child is not live and holds no
capability (so neither the granted endpoint nor its address-space root), is
not runnable, owns no address space; every frame committed to it is
committed to the parent again, so the parent's limit grows by the child's
and the child's is zero; and the parent's child-table entry and the child's
spawn records are removed, so the parent's child count drops by one. -/
theorem terminateChild_releases (state : CompositeState) (word : UInt64) (child returned : Nat)
    (running : state.execution.mode = .running) (holds : ResourceRuntimeWellFormed state)
    (accounting : ChildAccountingWellFormed state)
    (terminated : (terminateChild state word).result = .terminated child returned) :
    (terminateChild state word).state.capabilities.subjects child = false ∧
      (∀ slot, (terminateChild state word).state.capabilities.slots child slot = none) ∧
      (terminateChild state word).state.lifecycle.runnable child = false ∧
      (∀ addressSpace, state.lifecycle.addressOwner addressSpace = some child →
        (terminateChild state word).state.lifecycle.addressOwner addressSpace = none) ∧
      returned = state.budgetLimit child ∧
      (terminateChild state word).state.budgetLimit child = 0 ∧
      (terminateChild state word).state.budgetLimit (spawnParent state) =
        state.budgetLimit (spawnParent state) + state.budgetLimit child ∧
      (terminateChild state word).state.spawn.parent child = none ∧
      (terminateChild state word).state.spawn.addressSpace child = none ∧
      childCount (terminateChild state word).state (spawnParent state) + 1 =
        childCount state (spawnParent state) := by
  obtain ⟨slot, entry, resolved, childEq, returnedEq, stateEq⟩ :=
    terminateChild_terminated state word child returned terminated
  obtain ⟨_, _, found⟩ := resolveControl_ok resolved
  obtain ⟨inRange, _, entryNe, entryIssued, _⟩ :=
    accounting.entries (spawnParent state) slot entry found
  rw [childEq] at entryNe entryIssued
  obtain ⟨holdsPost, _, _⟩ := terminateChild_preserves state word holds accounting
  obtain ⟨holdsT, agreesT, spawnT⟩ := terminatedChild_facts state child holds
  obtain ⟨_, budgetsT, _, _, _, _, allocatorT, _⟩ := agreesT
  have runtimeT := holdsT.1.left
  have runtime := holds.1.left
  -- the child is dead after the composite termination
  have deadT : (terminatedChild state child).lifecycle.capabilities.subjects child = false := by
    simp only [terminatedChild, authoritativeGate_ordinary_state]
    cases accepted : SubjectLifecycle.terminate state.lifecycle child with
    | mk lifecycle result =>
      cases result with
      | accepted =>
          exact (terminateSubject_accepted_cleans_runtime_references state child lifecycle
            runtime running accepted).2.1
      | rejected reason =>
          have rejected : (SubjectLifecycle.terminate state.lifecycle child).result =
              .rejected reason := by rw [accepted]
          simp only [gate, running, applyOperation, rejected]
          have issuedLifecycle : state.lifecycle.issuedSubjects child = true := entryIssued
          cases live : state.lifecycle.capabilities.subjects child with
          | false => rfl
          | true => simp [SubjectLifecycle.terminate, issuedLifecycle, live] at rejected
  have capsT : (terminatedChild state child).capabilities =
      (terminatedChild state child).lifecycle.capabilities := runtimeT.1.2.2.2.1
  have dead : (terminateChild state word).state.capabilities.subjects child = false := by
    rw [stateEq]; show (terminatedChild state child).capabilities.subjects child = false
    rw [capsT]; exact deadT
  have runtimePost := holdsPost.1.left
  refine ⟨dead, fun candidateSlot => ?_, ?_, fun addressSpace owned => ?_, returnedEq, ?_, ?_, ?_,
    ?_, ?_⟩
  · cases held : (terminateChild state word).state.capabilities.slots child candidateSlot with
    | none => rfl
    | some capability =>
        have := (runtimePost.2.2.2.1.1 _ _ _ held).1
        rw [dead] at this; cases this
  · cases runnable : (terminateChild state word).state.lifecycle.runnable child with
    | false => rfl
    | true =>
        have live := runtimePost.2.2.1.2.2.2.2.1 child runnable
        rw [← runtimePost.1.2.2.2.1, dead] at live; cases live
  · rw [stateEq]
    show (terminatedChild state child).lifecycle.addressOwner addressSpace = none
    simp only [terminatedChild, authoritativeGate_ordinary_state]
    cases accepted : SubjectLifecycle.terminate state.lifecycle child with
    | mk lifecycle result =>
      cases result with
      | accepted =>
          exact terminateSubject_accepted_removes_owned_address_spaces state child lifecycle
            runtime running accepted addressSpace owned
      | rejected reason =>
          exfalso
          have rejected : (SubjectLifecycle.terminate state.lifecycle child).result =
              .rejected reason := by rw [accepted]
          have live := runtime.2.2.1.2.2.1 _ _ owned
          have issuedLifecycle : state.lifecycle.issuedSubjects child = true := entryIssued
          simp [SubjectLifecycle.terminate, issuedLifecycle, live] at rejected
  · rw [stateEq]
    exact (releaseChild_limits _ _ slot child entryNe).2.1
  · rw [stateEq]
    have := (releaseChild_limits (terminatedChild state child) (spawnParent state) slot child
      entryNe).1
    rw [this, (budget_eq_of_allocator budgetsT allocatorT _).2,
      (budget_eq_of_allocator budgetsT allocatorT _).2]
  · rw [stateEq]; simp [releaseChild]
  · rw [stateEq]; simp [releaseChild]
  · have update := childTable_update state (terminateChild state word).state (spawnParent state)
      slot inRange (fun candidate candidateSlot ne' => by
        rw [stateEq]; simp only [releaseChild, spawnT]; simp [ne'])
    have cleared : (terminateChild state word).state.spawn.children (spawnParent state) slot =
        none := by
      rw [stateEq]; simp [releaseChild]
    rw [cleared, found] at update
    simp only [entryCount, Option.isSome_some, Option.isSome_none, ↓reduceIte,
      Bool.false_eq_true] at update
    omega

end LeanOS.FailStop
