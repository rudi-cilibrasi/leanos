import LeanOS.SpawnAllocatorSpawnStep

/-!
# A frame grant on a family state is the allocator's grant (#575)

On every composite state satisfying `Family`, `FailStop.grantFrames` returns
the allocator's status and value (`grantFrames_status_family`); an accepted
grant's post-state has the allocator's successor as its abstraction
(`grantFrames_abstraction`) and satisfies `Family` again
(`grantFrames_family_preserved`).
-/
namespace LeanOS.SpawnAllocator

open LeanOS
open LeanOS.FailStop

set_option linter.unusedSimpArgs false

/-! ## Counting moved frames -/

/-- Counting the members of a duplicate-free sublist inside a duplicate-free
list counts the sublist. -/
theorem countP_contains_nodup (values moved : List Nat) (valuesNodup : values.Nodup)
    (movedNodup : moved.Nodup) (inside : ∀ item, item ∈ moved → item ∈ values) :
    values.countP (fun item => moved.contains item) = moved.length := by
  induction values generalizing moved with
  | nil =>
      cases moved with
      | nil => rfl
      | cons head tail => exact absurd (inside head List.mem_cons_self) (by simp)
  | cons head tail ih =>
      rw [List.nodup_cons] at valuesNodup
      obtain ⟨headFresh, tailNodup⟩ := valuesNodup
      by_cases member : head ∈ moved
      · have erasedNodup : (moved.erase head).Nodup := movedNodup.erase head
        have erasedInside : ∀ item, item ∈ moved.erase head → item ∈ tail := by
          intro item erased
          have ne : item ≠ head := by
            intro same; subst same
            exact (List.Nodup.not_mem_erase movedNodup) erased
          rcases List.mem_cons.1 (inside item (List.mem_of_mem_erase erased)) with same | rest
          · exact absurd same ne
          · exact rest
        have tailCount := ih (moved.erase head) tailNodup erasedNodup erasedInside
        have same : tail.countP (fun item => moved.contains item) =
            tail.countP (fun item => (moved.erase head).contains item) := by
          apply List.countP_congr
          intro item inTail
          have ne : item ≠ head := fun same => headFresh (same ▸ inTail)
          simp [List.mem_erase_of_ne ne]
        rw [List.countP_cons, same, tailCount, List.length_erase_of_mem member]
        have : 0 < moved.length := List.length_pos_of_mem member
        simp [member]
        omega
      · have tailInside : ∀ item, item ∈ moved → item ∈ tail := by
          intro item inMoved
          rcases List.mem_cons.1 (inside item inMoved) with same | rest
          · exact absurd (same ▸ inMoved) member
          · exact rest
        rw [List.countP_cons, ih moved tailNodup movedNodup tailInside]
        simp [member]

theorem grantedFrames_facts (state : CompositeState) (family : Family state) (frames : Nat) :
    (grantedFrames state parent frames).Nodup ∧
      (∀ frame, frame ∈ grantedFrames state parent frames →
        frame ∈ availableFrames state parent) ∧
      (grantedFrames state parent frames).length = min frames (abstraction state).available := by
  have availableNodup : (availableFrames state parent).Nodup :=
    List.Nodup.sublist (List.filter_sublist) family.framesNodup
  refine ⟨List.Nodup.sublist (List.take_sublist _ _) availableNodup,
    fun frame member => List.mem_of_mem_take member, ?_⟩
  unfold grantedFrames
  rw [List.length_take, availableFrames_length state family]

theorem movedCount_family (state : CompositeState) (family : Family state) (frames : Nat) :
    movedCount state (grantedFrames state parent frames) = min frames (abstraction state).available := by
  obtain ⟨nodup, available, length⟩ := grantedFrames_facts state family frames
  unfold movedCount
  rw [countP_contains_nodup _ _ family.framesNodup nodup
    (fun frame member => (mem_availableFrames (available frame member)).1), length]

/-! ## The status of a grant -/

/-- The child-table entry a resolved control word names is in the parent's
table, live, with exactly its charge in frames. -/
theorem resolved_entry (state : CompositeState) (family : Family state) (word : UInt64)
    (slot : Nat) (entry : ChildEntry) (resolved : FailStop.resolveControl state word = .ok (slot, entry)) :
    state.spawn.children parent slot = some entry ∧ state.capabilities.subjects entry.child = true ∧
      0 < entry.generation ∧ state.budgetLimit entry.child = entry.charge := by
  obtain ⟨_, _, found⟩ := FailStop.resolveControl_ok resolved
  rw [family_spawnParent state family] at found
  exact ⟨found, family.childLive slot entry found⟩

/-- **A frame grant on a family state returns the allocator's status and
value.** -/
theorem grantFrames_status_family (state : CompositeState) (family : Family state)
    (control : UInt64) (frames : Nat) :
    SpawnBoundary.childStatus (FailStop.grantFrames state control frames).result =
      ((grantStep (abstraction state) control frames).status,
        (grantStep (abstraction state) control frames).value) := by
  unfold FailStop.grantFrames grantStep
  cases allocatorResolved : (abstraction state).resolveControl control with
  | error denial =>
      rw [resolveControl_family_error state family control denial allocatorResolved]
      simp [rejectWith, SpawnBoundary.childStatus, SpawnAccountingOracle.frameGrantErrorCode]
  | ok found =>
      obtain ⟨slot, record⟩ := found
      obtain ⟨entry, resolved, recordEq⟩ :=
        resolveControl_family_ok state family control slot record allocatorResolved
      rw [resolved]
      obtain ⟨_, live, _, _⟩ := resolved_entry state family control slot entry resolved
      simp only [live, Bool.true_eq_false, ↓reduceIte]
      rw [family_spawnParent state family]
      obtain ⟨_, _, length⟩ := grantedFrames_facts state family frames
      rw [length]
      by_cases short : (abstraction state).available < frames
      · have : min frames (abstraction state).available < frames := by omega
        simp [this, short, rejectWith, SpawnBoundary.childStatus,
          SpawnAccountingOracle.frameGrantErrorCode]
      · have : ¬min frames (abstraction state).available < frames := by omega
        simp only [this, short, ↓reduceIte, acceptWith, SpawnBoundary.childStatus]
        rw [movedCount_family state family frames]
        have : min frames (abstraction state).available = frames := by omega
        rw [this]

/-! ## The post-state of an accepted grant -/

/-- An accepted grant on a family state, unfolded. -/
theorem grantFrames_accepted (state : CompositeState) (family : Family state)
    (control : UInt64) (frames : Nat)
    (accepted : (grantStep (abstraction state) control frames).status = 0x01) :
    ∃ slot entry, FailStop.resolveControl state control = .ok (slot, entry) ∧
      frames ≤ (abstraction state).available ∧
      (FailStop.grantFrames state control frames).state =
        { setChildEntry state parent slot (some (chargeEntry entry frames)) with
          frameBudgets := moveFrames state.frameBudgets (grantedFrames state parent frames)
            entry.child } := by
  have status := grantFrames_status_family state family control frames
  rw [accepted] at status
  rcases FailStop.grantFrames_result state control frames with ⟨child, moved, result⟩ |
    ⟨reason, result⟩
  · obtain ⟨slot, entry, resolved, childEq, _, _, movedEq, stateEq⟩ :=
      FailStop.grantFrames_granted state control frames child moved result
    obtain ⟨_, _, _, enough, _⟩ := grantStep_accepted (abstraction state) control frames accepted
    rw [family_spawnParent state family] at movedEq stateEq
    rw [movedCount_family state family frames] at movedEq
    have movedFrames : moved = frames := by rw [movedEq]; omega
    subst movedFrames childEq
    exact ⟨slot, entry, resolved, enough, stateEq⟩
  · rw [result] at status
    simp only [SpawnBoundary.childStatus, Prod.mk.injEq] at status
    exact absurd status.1 (reject_status_ne (frameGrantErrorCode_lt reason))

theorem setChildEntry_children (state : CompositeState) (p slot : Nat) (entry : Option ChildEntry) :
    (setChildEntry state p slot entry).spawn.children = fun candidate candidateSlot =>
      if candidate = p ∧ candidateSlot = slot then entry
      else state.spawn.children candidate candidateSlot := rfl

/-- **The abstraction of an accepted grant's post-state is the allocator's
successor.** -/
theorem grantFrames_abstraction (state : CompositeState) (family : Family state)
    (control : UInt64) (frames : Nat)
    (accepted : (grantStep (abstraction state) control frames).status = 0x01) :
    abstraction (FailStop.grantFrames state control frames).state =
      (grantStep (abstraction state) control frames).next := by
  obtain ⟨slot, record, allocatorResolved, enough, stepEq⟩ :=
    grantStep_accepted (abstraction state) control frames accepted
  obtain ⟨slot', entry, resolved, _, stateEq⟩ :=
    grantFrames_accepted state family control frames accepted
  obtain ⟨entry', resolved', recordEq⟩ :=
    resolveControl_family_ok state family control slot record allocatorResolved
  rw [resolved] at resolved'
  simp only [Except.ok.injEq, Prod.mk.injEq] at resolved'
  obtain ⟨slotEq, entryEq⟩ := resolved'
  have slotEq' := slotEq.symm
  subst slotEq' entryEq recordEq
  obtain ⟨found, live, _, _⟩ := resolved_entry state family control slot entry resolved
  obtain ⟨inRange, _, childNe, _, _⟩ := family.accounting.entries parent slot entry found
  have slotSmall : slot < childCapacity := by
    by_cases small : slot < childCapacity
    · exact small
    · rw [family.childSlots slot (by omega)] at found; cases found
  obtain ⟨_, available, _⟩ := grantedFrames_facts state family frames
  have fromParent : ∀ frame, frame ∈ grantedFrames state parent frames →
      frame ∈ availableFrames state parent := available
  obtain ⟨limitParent, _, _⟩ := grantFrames_limits state parent entry.child
    (grantedFrames state parent frames) childNe fromParent
  rw [movedCount_family state family frames] at limitParent
  have minEq : min frames (abstraction state).available = frames := by omega
  rw [minEq] at limitParent
  rw [stepEq, stateEq]
  simp only [acceptWith, granted, abstraction, State.mk.injEq]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, ?_⟩
  · apply map_range_set childCapacity slot slotSmall
    intro index
    rw [setChildEntry_children]
    by_cases same : index = slot
    · subst same; simp [found, recordOf, chargeEntry]
    · simp [same]
  · have limitEq : ({ setChildEntry state parent slot (some (chargeEntry entry frames)) with
        frameBudgets := moveFrames state.frameBudgets (grantedFrames state parent frames)
          entry.child } : CompositeState).budgetLimit parent + frames = state.budgetLimit parent :=
      limitParent
    simp only [budgetLimit_countP] at limitEq ⊢
    omega

/-! ## The family invariant after a grant -/

/-- Moving free frames away from the parent leaves its usage unchanged. -/
theorem usage_moveFree (state : CompositeState) (moved : List Nat) (child : Nat) (_ne : child ≠ parent)
    (free : ∀ frame, moved.contains frame = true →
      state.virtualMemory.memory.allocator.status frame = .free) :
    ({ state with frameBudgets := moveFrames state.frameBudgets moved child } :
      CompositeState).budgetUsage parent = state.budgetUsage parent := by
  rw [budgetUsage_committed, budgetUsage_committed]
  unfold committedFrames
  rw [List.countP_filter, List.countP_filter]
  apply List.countP_congr
  intro frame _
  simp only [moveFrames]
  by_cases contained : moved.contains frame = true
  · have freeFrame := free frame contained
    simp [contained, isOwned, freeFrame]
  · have notMem : frame ∉ moved := by simpa using contained
    simp [notMem, isOwned]

/-- The composite state with moved frames, as `grantFrames_limits` states it. -/
def withMoved (state : CompositeState) (moved : List Nat) (child : Nat) : CompositeState :=
  { state with frameBudgets := moveFrames state.frameBudgets moved child }

/-- **An accepted grant keeps the family invariant.** -/
theorem grantFrames_family_preserved (state : CompositeState) (family : Family state)
    (control : UInt64) (frames : Nat)
    (accepted : (grantStep (abstraction state) control frames).status = 0x01) :
    Family (FailStop.grantFrames state control frames).state := by
  have abstractionEq := grantFrames_abstraction state family control frames accepted
  obtain ⟨allocatorSlot, allocatorRecord, allocatorResolved, _, stepEq⟩ :=
    grantStep_accepted (abstraction state) control frames accepted
  rw [stepEq] at abstractionEq
  simp only [acceptWith] at abstractionEq
  obtain ⟨slot, entry, resolved, enough, stateEq⟩ :=
    grantFrames_accepted state family control frames accepted
  obtain ⟨found, live, positive, limit⟩ := resolved_entry state family control slot entry resolved
  obtain ⟨_, _, childNe, _, _⟩ := family.accounting.entries parent slot entry found
  have slotSmall : slot < childCapacity := by
    by_cases small : slot < childCapacity
    · exact small
    · rw [family.childSlots slot (by omega)] at found; cases found
  obtain ⟨_, available, _⟩ := grantedFrames_facts state family frames
  obtain ⟨limitParent, limitChild, limitOther⟩ := grantFrames_limits state parent entry.child
    (grantedFrames state parent frames) childNe available
  rw [movedCount_family state family frames] at limitParent limitChild
  have minEq : min frames (abstraction state).available = frames := by omega
  rw [minEq] at limitParent limitChild
  have limitChild' : (withMoved state (grantedFrames state parent frames) entry.child).budgetLimit
      entry.child = state.budgetLimit entry.child + frames := limitChild
  have limitOther' : ∀ other, other ≠ parent → other ≠ entry.child →
      (withMoved state (grantedFrames state parent frames) entry.child).budgetLimit other =
        state.budgetLimit other := limitOther
  have limitParent' : (withMoved state (grantedFrames state parent frames) entry.child).budgetLimit
      parent + frames = state.budgetLimit parent := limitParent
  have movedFree : ∀ frame, (grantedFrames state parent frames).contains frame = true →
      state.virtualMemory.memory.allocator.status frame = .free ∧
        state.frameBudgets.commitment frame = some parent := by
    intro frame contained
    obtain ⟨_, committed, free⟩ := mem_availableFrames (available frame (by simpa using contained))
    exact ⟨free, committed⟩
  have invariants := family_childGate_invariants state family (.grantFrames control frames)
  simp only [ChildOperation.apply] at invariants
  obtain ⟨resources, accounting, tree⟩ := invariants
  rw [stateEq] at resources accounting tree abstractionEq ⊢
  generalize hpost : ({ setChildEntry state parent slot (some (chargeEntry entry frames)) with
      frameBudgets := moveFrames state.frameBudgets (grantedFrames state parent frames)
        entry.child } : CompositeState) = post at resources accounting tree abstractionEq ⊢
  have postChildren : ∀ candidateSlot, post.spawn.children parent candidateSlot =
      if candidateSlot = slot then some (chargeEntry entry frames)
      else state.spawn.children parent candidateSlot := by
    intro candidateSlot; rw [← hpost]; simp [setChildEntry_children]
  have postCommitment : ∀ frame, post.frameBudgets.commitment frame =
      if (grantedFrames state parent frames).contains frame = true then some entry.child
      else state.frameBudgets.commitment frame := by
    intro frame; rw [← hpost]; rfl
  have postLimit : ∀ subject, post.budgetLimit subject =
      (withMoved state (grantedFrames state parent frames) entry.child).budgetLimit subject := by
    intro subject; rw [← hpost]; rfl
  have postUsage : post.budgetUsage parent = state.budgetUsage parent := by
    rw [← usage_moveFree state (grantedFrames state parent frames) entry.child childNe
      (fun frame contained => (movedFree frame contained).1), ← hpost]; rfl
  have sameExecution : post.execution = state.execution := by rw [← hpost]; rfl
  have sameCapabilities : post.capabilities = state.capabilities := by rw [← hpost]; rfl
  have sameLifecycle : post.lifecycle = state.lifecycle := by rw [← hpost]; rfl
  have sameVirtual : post.virtualMemory = state.virtualMemory := by rw [← hpost]; rfl
  have sameIssuers : post.issuers = state.issuers := by rw [← hpost]; rfl
  have sameAuthority : post.spawn.authority = state.spawn.authority := by rw [← hpost]; rfl
  have sameGeneration : post.spawn.nextGeneration = state.spawn.nextGeneration := by
    rw [← hpost]; rfl
  have sameControl : post.spawn.nextChildGeneration = state.spawn.nextChildGeneration := by
    rw [← hpost]; rfl
  have sameParentRecord : post.spawn.parent = state.spawn.parent := by rw [← hpost]; rfl
  have oldSlot : ∀ candidateSlot other, state.spawn.children parent candidateSlot = some other →
      candidateSlot ≠ slot → post.spawn.children parent candidateSlot = some other := by
    intro candidateSlot other found ne; rw [postChildren]; simp [ne, found]
  have atSlot : ∀ other, state.spawn.children parent slot = some other → other = entry := by
    intro other found'; rw [found] at found'; exact (Option.some.inj found').symm
  clear hpost
  refine ⟨resources, accounting, tree, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sameExecution]; exact family.running
  · rw [sameExecution]; exact family.current
  · rw [sameLifecycle]; exact family.lifecycleCurrent
  · rw [sameCapabilities]; exact family.capacity
  · rw [sameCapabilities]; exact family.parentLive
  · rw [sameParentRecord]; exact family.parentRoot
  · rw [sameCapabilities, sameLifecycle]; exact family.endpoint
  · rw [sameCapabilities, sameLifecycle]; exact family.space
  · intro memorySlot which
    rcases family.memory memorySlot which with empty | ⟨capability, frame, held, kind, revoke,
      identity, bound, status, owned, committed⟩
    · left; rw [sameCapabilities]; exact empty
    · right
      refine ⟨capability, frame, by rw [sameCapabilities]; exact held, kind, revoke, identity,
        by rw [sameVirtual]; exact bound, by rw [sameVirtual]; exact status,
        by rw [sameLifecycle]; exact owned, ?_⟩
      rw [postCommitment]
      have notMoved : (grantedFrames state parent frames).contains frame = false := by
        cases contained : (grantedFrames state parent frames).contains frame with
        | false => rfl
        | true => rw [(movedFree frame contained).1] at status; cases status
      rw [notMoved]; simpa using committed
  · rw [sameCapabilities]; exact family.memoryDistinct
  · intro candidateSlot high
    rw [postChildren]
    have : candidateSlot ≠ slot := by omega
    simp [this, family.childSlots candidateSlot high]
  · intro capability held
    rw [sameAuthority] at held
    rw [sameGeneration]; exact family.authority capability held
  · intro subject other
    rw [sameAuthority]; exact family.others subject other
  · intro candidateSlot other found'
    rw [postChildren] at found'
    by_cases same : candidateSlot = slot
    · simp only [same, ↓reduceIte, Option.some.injEq] at found'
      subst found'
      refine ⟨by rw [sameCapabilities]; exact live, positive, ?_⟩
      rw [postLimit]
      show (withMoved state (grantedFrames state parent frames) entry.child).budgetLimit
        entry.child = entry.charge + frames
      rw [limitChild', limit]
    · simp only [same, ↓reduceIte] at found'
      obtain ⟨otherLive, otherPositive, otherLimit⟩ := family.childLive candidateSlot other found'
      obtain ⟨_, _, otherNe, _, _⟩ := family.accounting.entries parent candidateSlot other found'
      have distinct : other.child ≠ entry.child := by
        intro sameChild
        exact same (family.accounting.unique parent candidateSlot other parent slot entry found'
          found sameChild).2
      refine ⟨by rw [sameCapabilities]; exact otherLive, otherPositive, ?_⟩
      rw [postLimit, limitOther' other.child otherNe distinct, otherLimit]
  · intro subject liveNow
    rw [sameCapabilities] at liveNow
    rcases family.live subject liveNow with bystanderIs | parentIs |
      ⟨candidateSlot, other, found', childIs⟩
    · exact Or.inl bystanderIs
    · exact Or.inr (Or.inl parentIs)
    · right; right
      by_cases same : candidateSlot = slot
      · subst same
        have := atSlot other found'
        subst this
        exact ⟨candidateSlot, chargeEntry other frames, by rw [postChildren]; simp, childIs⟩
      · exact ⟨candidateSlot, other, oldSlot candidateSlot other found' same, childIs⟩
  · intro frame subject committedNow
    rw [postCommitment] at committedNow
    by_cases contained : (grantedFrames state parent frames).contains frame = true
    · simp only [contained, ↓reduceIte, Option.some.injEq] at committedNow
      subst committedNow
      obtain ⟨freeFrame, toParent⟩ := movedFree frame contained
      right
      refine ⟨by rw [sameVirtual]; exact freeFrame, ?_, slot, chargeEntry entry frames,
        by rw [postChildren]; simp, rfl⟩
      rw [sameLifecycle]; exact family.parentFree frame toParent freeFrame
    · simp only [Bool.not_eq_true] at contained
      simp only [contained, Bool.false_eq_true, ↓reduceIte] at committedNow
      rcases family.committed frame subject committedNow with parentIs |
        ⟨freeFrame, unowned, candidateSlot, other, found', childIs⟩
      · exact Or.inl parentIs
      · right
        refine ⟨by rw [sameVirtual]; exact freeFrame, by rw [sameLifecycle]; exact unowned, ?_⟩
        by_cases same : candidateSlot = slot
        · subst same
          have := atSlot other found'
          subst this
          exact ⟨candidateSlot, chargeEntry other frames, by rw [postChildren]; simp, childIs⟩
        · exact ⟨candidateSlot, other, oldSlot candidateSlot other found' same, childIs⟩
  · rw [sameVirtual]; exact family.framesNodup
  · rw [sameCapabilities, sameLifecycle, sameParentRecord]; exact family.parentNames
  · intro object high
    rw [sameIssuers] at high
    rw [sameCapabilities, sameLifecycle]; exact family.fresh object high
  · intro frame committedNow freeNow
    rw [postCommitment] at committedNow
    by_cases contained : (grantedFrames state parent frames).contains frame = true
    · simp only [contained, ↓reduceIte, Option.some.injEq] at committedNow
      exact absurd committedNow childNe
    · simp only [Bool.not_eq_true] at contained
      simp only [contained, Bool.false_eq_true, ↓reduceIte] at committedNow
      rw [sameVirtual] at freeNow
      rw [sameLifecycle]; exact family.parentFree frame committedNow freeNow
  · rw [abstractionEq, granted_memoryUsed, postUsage]; exact family.usage
  · rw [sameCapabilities]; exact family.capabilityBound
  · rw [sameControl]; exact family.controlBound
  · rw [sameGeneration]; exact family.generationBound
  · rw [abstractionEq, granted_chargeSum _ allocatorSlot allocatorRecord frames
      (SpawnAllocator.resolveControl_ok allocatorResolved).2]
    have frameBound := family.frameBound
    have parentFrames : (abstraction state).parentFrames = state.budgetLimit parent := rfl
    rw [postLimit]
    omega

end LeanOS.SpawnAllocator
