import LeanOS.SpawnAllocatorTerminateStep

/-!
# Memory allocation and release on a family state are the allocator's (#575)

On every composite state satisfying `Family`, `allocateMemory` and
`releaseMemory` by the parent return the allocator's status
(`allocateMemory_status_family`, `releaseMemory_status_family`); an accepted
step's post-state has the allocator's successor as its abstraction and
satisfies `Family` again.
-/
namespace LeanOS.SpawnAllocator

open LeanOS
open LeanOS.FailStop

set_option linter.unusedSimpArgs false

theorem family_memoryActor (state : CompositeState) (family : Family state) :
    memoryActor state = parent := family.current

/-- The parent's slots 0 and 1 are occupied. -/
theorem family_low_slots (state : CompositeState) (family : Family state) (slot : Nat)
    (low : slot < memoryBase) : (state.capabilities.slots parent slot).isSome = true := by
  unfold memoryBase at low
  obtain ⟨object, endpoint, _⟩ := family.endpoint
  obtain ⟨capability, held, _⟩ := family.space
  rcases slot with _ | _ | slot
  · rw [endpoint]; rfl
  · rw [held]; rfl
  · omega

/-- A parent memory slot holds something exactly when the allocator records
memory there. -/
theorem family_memory_slot (state : CompositeState) (family : Family state) (slot : Nat)
    (which : slot = 2 ∨ slot = 3) :
    (state.capabilities.slots parent slot).isSome = ((abstraction state).memoryAt slot).isSome := by
  have memoryAt : (abstraction state).memoryAt slot = memoryIn state slot := by
    rw [abstraction_memoryAt]; rcases which with rfl | rfl <;> simp
  rw [memoryAt]
  unfold memoryIn
  rcases family.memory slot which with empty | ⟨capability, _, held, kind, _⟩
  · rw [empty]; rfl
  · rw [held]; simp [kind]

/-! ## The status of an allocation -/

/-- **An allocation by the parent on a family state returns the allocator's
status.** -/
theorem allocateMemory_status_family (state : CompositeState) (family : Family state) (slot : Nat) :
    SpawnBoundary.memoryStatus (allocateMemory state slot).result =
      (allocateStep (abstraction state) slot).status := by
  rw [allocateMemory_result]
  unfold allocateDecision allocateStep
  rw [family_memoryActor state family]
  simp only [family.parentLive, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    Capability.slotInRange, family.capacity parent]
  by_cases range : CapabilityHandle.slotReserved ≤ slot ∨ parentSlots ≤ slot
  · have range' : CapabilityHandle.slotReserved ≤ slot ∨ !decide (slot < parentSlots) = true := by
      rcases range with high | high
      · exact Or.inl high
      · right; simp; omega
    simp [range, range', rejectWith, SpawnBoundary.memoryStatus, memoryCode,
      SpawnBoundary.memoryErrorCode]
  have range' : ¬(CapabilityHandle.slotReserved ≤ slot ∨ !decide (slot < parentSlots) = true) := by
    simp only [not_or] at range ⊢; simp; omega
  simp only [range, range', ↓reduceIte]
  have capabilitiesEq : (abstraction state).capabilityNext = state.capabilities.nextIdentity := rfl
  rw [capabilitiesEq]
  by_cases capabilities : capabilityExhausted state.capabilities.nextIdentity = true
  · have exhausted : state.capabilities.nextIdentity = 0 ∨
        CapabilityHandle.generationReserved ≤ state.capabilities.nextIdentity := by
      simpa [capabilityExhausted] using capabilities
    simp [range, exhausted, capabilities, rejectWith, SpawnBoundary.memoryStatus, memoryCode,
      SpawnBoundary.memoryErrorCode]
  have live : ¬(state.capabilities.nextIdentity = 0 ∨
      CapabilityHandle.generationReserved ≤ state.capabilities.nextIdentity) := by
    simpa [capabilityExhausted] using capabilities
  simp only [live, capabilities, ↓reduceIte, Bool.false_eq_true]
  have occupied : (state.capabilities.slots parent slot).isSome =
      (decide (slot < memoryBase) || ((abstraction state).memoryAt slot).isSome) := by
    by_cases low : slot < memoryBase
    · simp [low, family_low_slots state family slot low]
    · have which : slot = 2 ∨ slot = 3 := by
        unfold memoryBase parentSlots at *; simp only [not_or] at range; omega
      simp [low, family_memory_slot state family slot which]
  rw [occupied]
  by_cases full : slot < memoryBase ∨ ((abstraction state).memoryAt slot).isSome = true
  · rcases full with low | some
    · simp [range, live, low, rejectWith, SpawnBoundary.memoryStatus, memoryCode,
        SpawnBoundary.memoryErrorCode]
    · simp [range, live, some, rejectWith, SpawnBoundary.memoryStatus, memoryCode,
        SpawnBoundary.memoryErrorCode]
  simp only [not_or, Bool.not_eq_true] at full
  simp only [full, decide_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte, Nat.not_lt.2 (by
    have := full.1; omega : memoryBase ≤ slot)]
  have objectsEq : (abstraction state).objectNext = state.issuers.object.next := rfl
  rw [objectsEq]
  by_cases objects : identityExhausted state.issuers.object.next = true
  · simp [range, live, full, LifetimeIssuer.issue, identityExhausted_issuer, objects, rejectWith,
      SpawnBoundary.memoryStatus, memoryCode, SpawnBoundary.memoryErrorCode]
  have objectsLive : identityExhausted state.issuers.object.next = false := by simpa using objects
  obtain ⟨unissuedSpace, unissued, dead, _, endpointFree⟩ := family_next_object state family
  have available : objectAvailable state state.issuers.object.next = true := by
    simp [objectAvailable, unissuedSpace, unissued, dead, endpointFree]
  simp only [LifetimeIssuer.issue, identityExhausted_issuer, objectsLive, Bool.false_eq_true,
    ↓reduceIte, available]
  have firstIs := firstAvailable_family state family
  cases first : FrameBudget.firstAvailable state.budgetState parent with
  | none =>
      rw [first] at firstIs
      have zero : (abstraction state).available = 0 := by simpa using firstIs.symm
      simp [range, live, full, objectsLive, zero, rejectWith, SpawnBoundary.memoryStatus, memoryCode,
        SpawnBoundary.memoryErrorCode]
  | some frame =>
      rw [first] at firstIs
      have positive : (abstraction state).available ≠ 0 := by
        have : 0 < (abstraction state).available := by simpa using firstIs.symm
        omega
      obtain ⟨_, committed, free⟩ := firstAvailable_some first
      have unowned := family.parentFree frame committed free
      simp [range, live, full, objectsLive, positive, unowned, acceptWith,
        SpawnBoundary.memoryStatus]

/-! ## The status of a release -/

/-- **A release by the parent on a family state returns the allocator's
status.** -/
theorem releaseMemory_status_family (state : CompositeState) (family : Family state) (slot : Nat) :
    SpawnBoundary.memoryStatus (releaseMemory state slot).result =
      (releaseStep (abstraction state) slot).status := by
  rw [releaseMemory_result]
  unfold releaseDecision releaseStep Capability.lookup
  rw [family_memoryActor state family]
  simp only [family.parentLive, ↓reduceIte, Capability.slotInRange, family.capacity parent]
  by_cases range : parentSlots ≤ slot
  · have : ¬slot < parentSlots := by omega
    simp [range, this, rejectWith, SpawnBoundary.memoryStatus, memoryCode,
      SpawnBoundary.memoryErrorCode]
  have inRange : slot < parentSlots := by omega
  simp only [range, inRange, decide_true, ↓reduceIte]
  by_cases low : slot < memoryBase
  · have occupied := family_low_slots state family slot low
    cases held : state.capabilities.slots parent slot with
    | none => rw [held] at occupied; cases occupied
    | some capability =>
        have kindNe : capability.kind ≠ .memory := by
          obtain ⟨object, endpoint, _⟩ := family.endpoint
          obtain ⟨space, spaceHeld, spaceKind, _⟩ := family.space
          unfold memoryBase at low
          rcases slot with _ | _ | slot
          · rw [endpoint] at held; cases held; simp
          · rw [spaceHeld] at held; cases held; rw [spaceKind]; simp
          · omega
        have kindBne : (capability.kind != .memory) = true := by simpa using kindNe
        simp [low, kindBne, rejectWith, SpawnBoundary.memoryStatus, memoryCode,
          SpawnBoundary.memoryErrorCode]
  have which : slot = 2 ∨ slot = 3 := by unfold memoryBase parentSlots at *; omega
  have memoryAt : (abstraction state).memoryAt slot = memoryIn state slot := by
    rw [abstraction_memoryAt]; rcases which with rfl | rfl <;> simp
  simp only [low, ↓reduceIte, memoryAt]
  unfold memoryIn
  rcases family.memory slot which with empty | ⟨capability, frame, held, kind, revoke, _, bound,
    status, owned, _⟩
  · rw [empty]
    simp [rejectWith, SpawnBoundary.memoryStatus, memoryCode, SpawnBoundary.memoryErrorCode]
  · rw [held]
    simp [kind, revoke, bound, status, owned, acceptWith, SpawnBoundary.memoryStatus]

/-! ## The post-state of an accepted allocation -/

theorem countP_flip {α : Type} [DecidableEq α] (values : List α) (nodup : values.Nodup)
    (item : α) (member : item ∈ values) (before after : α → Bool) (wasFalse : before item = false)
    (isTrue : after item = true) (others : ∀ other, other ∈ values → other ≠ item →
      after other = before other) :
    values.countP after = values.countP before + 1 := by
  induction values with
  | nil => cases member
  | cons head tail ih =>
      rw [List.nodup_cons] at nodup
      obtain ⟨headFresh, tailNodup⟩ := nodup
      by_cases same : head = item
      · subst same
        have tailSame : tail.countP after = tail.countP before := by
          apply List.countP_congr
          intro other inTail
          have ne : other ≠ head := fun eq => headFresh (eq ▸ inTail)
          rw [others other (List.mem_cons_of_mem _ inTail) ne]
        simp [List.countP_cons, wasFalse, isTrue, tailSame]
      · have inTail : item ∈ tail := by
          rcases List.mem_cons.1 member with eq | rest
          · exact absurd eq.symm same
          · exact rest
        have headSame := others head List.mem_cons_self same
        have step := ih tailNodup inTail (fun other inRest ne =>
          others other (List.mem_cons_of_mem _ inRest) ne)
        simp only [List.countP_cons, headSame, step]
        omega

/-- An accepted allocation on a family state, unfolded. -/
theorem allocateMemory_accepted (state : CompositeState) (family : Family state) (slot : Nat)
    (accepted : (allocateStep (abstraction state) slot).status = 0x01) :
    ∃ frame, FrameBudget.firstAvailable state.budgetState parent = some frame ∧
      (allocateMemory state slot).state =
        allocatedState state state.issuers.object.next parent slot frame := by
  have status := allocateMemory_status_family state family slot
  rw [accepted] at status
  rw [allocateMemory_result] at status
  cases decision : allocateDecision state slot with
  | allocated object frame =>
      have result : (allocateMemory state slot).result = .allocated object frame := by
        rw [allocateMemory_result, decision]
      obtain ⟨objectEq, _, _, first, _, _, stateEq⟩ :=
        allocateMemory_allocated state slot object frame result
      rw [family_memoryActor state family] at first stateEq
      subst objectEq
      exact ⟨frame, first, stateEq⟩
  | released object frame => exact absurd decision (allocateDecision_not_released _ _ _ _)
  | rejected reason =>
      rw [decision] at status
      simp only [SpawnBoundary.memoryStatus] at status
      exact absurd status (reject_status_ne (memoryCode_lt reason) ∘ (by
        intro h; rw [show memoryCode reason = SpawnBoundary.memoryErrorCode reason by
          cases reason <;> rfl]; exact h))

theorem allocatedState_fields (state : CompositeState) (object slot frame : Nat) :
    let post := allocatedState state object parent slot frame
    post.capabilities = allocatedCapabilities state.capabilities object parent slot ∧
      post.lifecycle.ownedMemory = (fun candidate =>
        if candidate = object then some (parent, frame) else state.lifecycle.ownedMemory candidate) ∧
      post.lifecycle.frameOwner = (fun candidate =>
        if candidate = frame then some parent else state.lifecycle.frameOwner candidate) ∧
      post.lifecycle.endpointOwner = state.lifecycle.endpointOwner ∧
      post.lifecycle.addressOwner = state.lifecycle.addressOwner ∧
      post.lifecycle.current = state.lifecycle.current ∧
      post.virtualMemory.memory.allocator.frames = state.virtualMemory.memory.allocator.frames ∧
      post.virtualMemory.memory.allocator.status = (fun candidate =>
        if candidate = frame then .owned object
        else state.virtualMemory.memory.allocator.status candidate) ∧
      post.virtualMemory.memory.binding = (fun candidate =>
        if candidate = object then some frame else state.virtualMemory.memory.binding candidate) ∧
      post.execution.mode = state.execution.mode ∧
      post.execution.core.context = state.execution.core.context ∧
      post.issuers.object.next = object + 1 ∧
      post.issuers.subject = state.issuers.subject ∧
      post.frameBudgets = state.frameBudgets ∧ post.spawn = state.spawn := by
  intro post
  simp only [post, allocatedState, installAllocatedMemory, allocatedLifecycle, allocatedMemory,
    FrameAllocator.setStatus, MemoryLifecycle.setBinding]
  simp
  rfl

/-- The memory list of the abstraction after a slot update. -/
theorem memory_list_update (state post : CompositeState) (slot : Nat) (value : Option Nat)
    (which : slot = 2 ∨ slot = 3)
    (updated : ∀ other, other = 2 ∨ other = 3 →
      memoryIn post other = if other = slot then value else memoryIn state other) :
    [memoryIn post 2, memoryIn post 3] = (abstraction state).memory.set (slot - memoryBase) value := by
  have memoryEq : (abstraction state).memory = [memoryIn state 2, memoryIn state 3] := rfl
  rw [memoryEq, updated 2 (Or.inl rfl), updated 3 (Or.inr rfl)]
  unfold memoryBase
  rcases which with rfl | rfl <;> simp

/-- **The abstraction of an accepted allocation's post-state is the
allocator's successor.** -/
theorem allocateMemory_abstraction (state : CompositeState) (family : Family state) (slot : Nat)
    (accepted : (allocateStep (abstraction state) slot).status = 0x01) :
    abstraction (allocateMemory state slot).state = (allocateStep (abstraction state) slot).next := by
  obtain ⟨range, low, _, _, _, _, stepEq⟩ := allocateStep_accepted (abstraction state) slot accepted
  obtain ⟨frame, first, stateEq⟩ := allocateMemory_accepted state family slot accepted
  obtain ⟨capabilities, _, _, _, _, _, frames, _, _, _, _, objectNext, subjectIssuer, budgets,
    spawnSame⟩ := allocatedState_fields state state.issuers.object.next slot frame
  have which : slot = 2 ∨ slot = 3 := by unfold memoryBase parentSlots at *; omega
  rw [stepEq, stateEq]
  simp only [acceptWith, allocated, abstraction, State.mk.injEq]
  refine ⟨by rw [subjectIssuer], objectNext, by rw [capabilities]; rfl, by rw [spawnSame],
    by rw [spawnSame], by rw [spawnSame], by simp only [subjectBudget, spawnSame], by rw [spawnSame],
    ?_, ?_⟩
  · apply memory_list_update state _ slot _ which
    intro other otherWhich
    unfold memoryIn
    rw [capabilities, allocatedCapabilities_slots]
    by_cases same : other = slot
    · subst same; simp [memoryRoot]
    · simp [same, Ne.symm same]
  · rw [budgetLimit_countP, budgetLimit_countP, frames, budgets]

/-! ## The family invariant after a memory step -/

theorem family_memoryGate_invariants (state : CompositeState) (family : Family state)
    (operation : MemoryOperation) :
    ResourceRuntimeWellFormed (operation.apply state).state ∧
      ChildAccountingWellFormed (operation.apply state).state ∧
      SpawnTreeWellFormed (operation.apply state).state := by
  have gateEq : (memoryGate state operation).state = (operation.apply state).state := by
    simp [memoryGate, family.running]
  have resources := memoryGate_preserves state operation family.resources
  have accounting := memoryGate_childAccounting state operation family.accounting
  have tree := memoryGate_spawnTree state operation family.tree
  rw [gateEq] at resources accounting tree
  exact ⟨resources, accounting, tree⟩

/-- **An accepted allocation keeps the family invariant.** -/
theorem allocateMemory_family_preserved (state : CompositeState) (family : Family state)
    (slot : Nat) (accepted : (allocateStep (abstraction state) slot).status = 0x01) :
    Family (allocateMemory state slot).state := by
  have abstractionEq := allocateMemory_abstraction state family slot accepted
  obtain ⟨range, low, empty, capabilitiesLive, _, _, stepEq⟩ :=
    allocateStep_accepted (abstraction state) slot accepted
  rw [stepEq] at abstractionEq
  simp only [acceptWith] at abstractionEq
  obtain ⟨frame, first, stateEq⟩ := allocateMemory_accepted state family slot accepted
  obtain ⟨member, committed, free⟩ := firstAvailable_some first
  simp only [CompositeState.budgetState] at member committed free
  have unowned := family.parentFree frame committed free
  obtain ⟨_, _, dead, ownedNone, endpointNone⟩ := family_next_object state family
  obtain ⟨capabilityPositive, capabilityBounded⟩ := capabilityExhausted_false capabilitiesLive
  have which : slot = 2 ∨ slot = 3 := by unfold memoryBase parentSlots at *; omega
  have invariants := family_memoryGate_invariants state family (.allocate slot)
  simp only [MemoryOperation.apply] at invariants
  obtain ⟨resources, accounting, tree⟩ := invariants
  obtain ⟨capabilities, ownedMemory, frameOwner, endpointOwner, addressOwner, current, frames,
    status, binding, mode, context, objectNext, subjectIssuer, budgets, spawnSame⟩ :=
    allocatedState_fields state state.issuers.object.next slot frame
  rw [stateEq] at resources accounting tree abstractionEq ⊢
  generalize hpost : allocatedState state state.issuers.object.next parent slot frame = post at *
  clear hpost
  have slotEmpty : state.capabilities.slots parent slot = none := by
    have memoryAt : (abstraction state).memoryAt slot = memoryIn state slot := by
      rw [abstraction_memoryAt]; rcases which with rfl | rfl <;> simp
    rw [memoryAt] at empty
    rcases family.memory slot which with none | ⟨capability, _, held, kind, _⟩
    · exact none
    · unfold memoryIn at empty; rw [held] at empty; simp [kind] at empty
  have postSlots : ∀ namedSlot, post.capabilities.slots parent namedSlot =
      if namedSlot = slot then some (memoryRoot state.capabilities state.issuers.object.next)
      else state.capabilities.slots parent namedSlot := by
    intro namedSlot
    rw [capabilities, allocatedCapabilities_slots]
    by_cases same : namedSlot = slot <;> simp [same]
  have otherSlots : ∀ subject namedSlot, subject ≠ parent →
      post.capabilities.slots subject namedSlot = state.capabilities.slots subject namedSlot := by
    intro subject namedSlot ne
    rw [capabilities, allocatedCapabilities_slots]; simp [ne]
  have postObjects : ∀ object, post.capabilities.objects object =
      if object = state.issuers.object.next then true else state.capabilities.objects object := by
    intro object; rw [capabilities, allocatedCapabilities_objects]
  have postKinds : ∀ object, post.capabilities.kinds object =
      if object = state.issuers.object.next then some .memory else state.capabilities.kinds object := by
    intro object; rw [capabilities, allocatedCapabilities_kinds]
  have liveNe : ∀ object, state.capabilities.objects object = true →
      object ≠ state.issuers.object.next := fun object live =>
    family_live_object_ne state family object live
  have slotsLive : ∀ namedSlot capability, state.capabilities.slots parent namedSlot = some capability →
      state.capabilities.objects capability.object = true := fun namedSlot capability held =>
    ((family_runtime state family).2.2.2.1.1 parent namedSlot capability held).2.1
  have frameNotChild : ∀ subject, subject ≠ parent →
      state.frameBudgets.commitment frame ≠ some subject := by
    intro subject ne same; rw [committed] at same; exact ne (Option.some.inj same).symm
  refine ⟨resources, accounting, tree, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mode]; exact family.running
  · rw [context]; exact family.current
  · rw [current]; exact family.lifecycleCurrent
  · intro subject; rw [capabilities]; exact family.capacity subject
  · rw [capabilities]; exact family.parentLive
  · rw [spawnSame]; exact family.parentRoot
  · obtain ⟨object, endpointSlot, objectLive, objectKind, owner⟩ := family.endpoint
    have ne := liveNe object objectLive
    have slotNe : (0 : Nat) ≠ slot := by unfold memoryBase at low; omega
    refine ⟨object, by rw [postSlots]; simp only [slotNe, ↓reduceIte]; exact endpointSlot,
      by rw [postObjects]; simp [ne, objectLive],
      by rw [postKinds]; simp [ne, objectKind], by rw [endpointOwner]; exact owner⟩
  · obtain ⟨capability, held, kind, identity, owner⟩ := family.space
    have slotNe : (1 : Nat) ≠ slot := by unfold memoryBase at low; omega
    exact ⟨capability, by rw [postSlots]; simp only [slotNe, ↓reduceIte]; exact held, kind, identity,
      by rw [addressOwner]; exact owner⟩
  · intro memorySlot memoryWhich
    by_cases same : memorySlot = slot
    · subst same
      right
      refine ⟨memoryRoot state.capabilities state.issuers.object.next, frame, by rw [postSlots]; simp,
        rfl, rfl, capabilityPositive, ?_, ?_, ?_, ?_⟩
      · rw [binding]; simp [memoryRoot]
      · rw [status]; simp [memoryRoot]
      · rw [ownedMemory]; simp [memoryRoot]
      · rw [budgets]; exact committed
    · rcases family.memory memorySlot memoryWhich with none | ⟨capability, otherFrame, held, kind,
        revoke, identity, bound, otherStatus, owned, otherCommitted⟩
      · left; rw [postSlots]; simp [same, none]
      · right
        have objectNe := liveNe _ (slotsLive _ _ held)
        have frameNe : otherFrame ≠ frame := by
          intro sameFrame; rw [sameFrame, free] at otherStatus; cases otherStatus
        refine ⟨capability, otherFrame, by rw [postSlots]; simp [same, held], kind, revoke, identity,
          ?_, ?_, ?_, by rw [budgets]; exact otherCommitted⟩
        · rw [binding]; simp [objectNe, bound]
        · rw [status]; simp [frameNe, otherStatus]
        · rw [ownedMemory]; simp [objectNe, owned]
  · intro first second held2 held3
    rw [postSlots] at held2 held3
    by_cases two : slot = 2
    · subst two
      simp only [↓reduceIte, Option.some.injEq] at held2
      simp only [show (3 : Nat) ≠ 2 from by decide, ↓reduceIte] at held3
      subst held2
      exact fun sameObject => liveNe _ (slotsLive _ _ held3) sameObject.symm
    · have three : slot = 3 := by omega
      subst three
      simp only [show (2 : Nat) ≠ 3 from by decide, ↓reduceIte] at held2
      simp only [↓reduceIte, Option.some.injEq] at held3
      subst held3
      exact fun sameObject => liveNe _ (slotsLive _ _ held2) sameObject
  · intro candidateSlot high; rw [spawnSame]; exact family.childSlots candidateSlot high
  · intro capability held
    rw [spawnSame] at held ⊢; exact family.authority capability held
  · intro subject other; rw [spawnSame]; exact family.others subject other
  · intro candidateSlot entry found
    rw [spawnSame] at found
    obtain ⟨live, positive, limit⟩ := family.childLive candidateSlot entry found
    refine ⟨by rw [capabilities]; exact live, positive, ?_⟩
    rw [budgetLimit_countP, frames, budgets, ← budgetLimit_countP]; exact limit
  · intro subject liveNow
    rw [capabilities] at liveNow
    rw [spawnSame]; exact family.live subject liveNow
  · intro otherFrame subject committedNow
    rw [budgets] at committedNow
    rcases family.committed otherFrame subject committedNow with parentIs |
      ⟨freeFrame, unownedFrame, candidateSlot, entry, found, childIs⟩
    · exact Or.inl parentIs
    · right
      have ne : otherFrame ≠ frame := by
        intro same; subst same
        have := frameNotChild subject (by
          intro isParent; rw [isParent] at committedNow
          obtain ⟨_, _, notParent, _, _⟩ := family.accounting.entries parent candidateSlot entry found
          exact notParent (childIs.trans isParent)) committedNow
        exact this
      refine ⟨by rw [status]; simp [ne, freeFrame], by rw [frameOwner]; simp [ne, unownedFrame],
        candidateSlot, entry, by rw [spawnSame]; exact found, childIs⟩
  · rw [frames]; exact family.framesNodup
  · intro namedSlot capability subject held owned
    rw [postSlots] at held
    rw [spawnSame]
    by_cases same : namedSlot = slot
    · simp only [same, ↓reduceIte, Option.some.injEq] at held
      subst held
      unfold OwnedBy at owned
      rw [endpointOwner, addressOwner, ownedMemory] at owned
      simp only [memoryRoot, ↓reduceIte, Option.any_some, decide_eq_true_eq] at owned
      rcases owned with endpoint | address | isParent
      · rw [endpointNone] at endpoint; cases endpoint
      · rw [addressOwner_none_of_unissued (family_runtime state family)
          (family_next_object state family).1] at address
        cases address
      · rw [← isParent]; exact family.parentRoot
    · simp only [same, ↓reduceIte] at held
      have objectNe := liveNe _ (slotsLive _ _ held)
      apply family.parentNames namedSlot capability subject held
      unfold OwnedBy at owned ⊢
      rw [endpointOwner, addressOwner, ownedMemory] at owned
      simpa [objectNe] using owned
  · intro object high
    rw [objectNext] at high
    have ne : object ≠ state.issuers.object.next := by omega
    obtain ⟨objectDead, objectOwned, objectEndpoint⟩ := family.fresh object (by omega)
    refine ⟨by rw [postObjects]; simp [ne, objectDead], by rw [ownedMemory]; simp [ne, objectOwned],
      by rw [endpointOwner]; exact objectEndpoint⟩
  · intro otherFrame committedNow freeNow
    rw [budgets] at committedNow
    rw [status] at freeNow
    by_cases same : otherFrame = frame
    · subst same; simp at freeNow
    · simp only [same, ↓reduceIte] at freeNow
      rw [frameOwner]; simp [same, family.parentFree otherFrame committedNow freeNow]
  · rw [abstractionEq]
    have usedAfter : (allocated (abstraction state) slot).memoryUsed =
        (abstraction state).memoryUsed + 1 := by
      have inRange : slot - memoryBase < (abstraction state).memory.length := by
        have : (abstraction state).memory.length = 2 := rfl
        unfold memoryBase parentSlots at *; omega
      have used := memoryUsed_set (next := allocated (abstraction state) slot) rfl inRange
      have emptyAt : (abstraction state).memory[slot - memoryBase] = none := by
        unfold State.memoryAt at empty
        simp only [Nat.not_lt.2 low, ↓reduceIte] at empty
        rw [List.getElem?_eq_getElem inRange] at empty
        simpa using empty
      simp only [emptyAt, Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte]
        at used
      omega
    rw [usedAfter, ← family.usage]
    rw [budgetUsage_committed, budgetUsage_committed]
    have committedSame : committedFrames post parent = committedFrames state parent := by
      unfold committedFrames; rw [frames, budgets]
    rw [committedSame]
    have committedNodup : (committedFrames state parent).Nodup :=
      List.Nodup.sublist List.filter_sublist family.framesNodup
    apply countP_flip _ committedNodup frame
    · unfold committedFrames; simp [member, committed]
    · simp [isOwned, free]
    · simp [isOwned, status]
    · intro other _ ne
      simp [isOwned, status, ne]
  · rw [capabilities, allocatedCapabilities_nextIdentity]
    have same : (abstraction state).capabilityNext = state.capabilities.nextIdentity := rfl
    rw [same] at capabilityBounded
    omega
  · rw [spawnSame]; exact family.controlBound
  · rw [spawnSame]; exact family.generationBound
  · rw [abstractionEq, allocated_chargeSum]
    rw [budgetLimit_countP, frames, budgets, ← budgetLimit_countP]
    exact family.frameBound

/-! ## The post-state of an accepted release -/

/-- Committed frames are allocator frames (`budgetAgreementInvariant`). -/
theorem family_frame_member (state : CompositeState) (family : Family state) (frame subject : Nat)
    (committed : state.frameBudgets.commitment frame = some subject) :
    frame ∈ state.virtualMemory.memory.allocator.frames := by
  have agreement := ((resourceWellFormed_iff state).1 family.resources.2).2.2.1
  exact (agreement frame subject committed).1

/-- Two parent capabilities of different kinds name different objects. -/
theorem family_kind_object_ne (state : CompositeState) (family : Family state)
    {first second : Nat} {firstCapability secondCapability : Capability.Capability}
    (firstHeld : state.capabilities.slots parent first = some firstCapability)
    (secondHeld : state.capabilities.slots parent second = some secondCapability)
    (kinds : firstCapability.kind ≠ secondCapability.kind) :
    firstCapability.object ≠ secondCapability.object := by
  intro same
  have firstKind := ((family_runtime state family).2.2.2.1.1 parent first firstCapability
    firstHeld).2.2.1
  have secondKind := ((family_runtime state family).2.2.2.1.1 parent second secondCapability
    secondHeld).2.2.1
  rw [same, secondKind] at firstKind
  exact kinds (Option.some.inj firstKind).symm

/-- An accepted release on a family state, unfolded. -/
theorem releaseMemory_accepted (state : CompositeState) (family : Family state) (slot : Nat)
    (accepted : (releaseStep (abstraction state) slot).status = 0x01) :
    ∃ capability frame, state.capabilities.slots parent slot = some capability ∧
      capability.kind = .memory ∧
      state.virtualMemory.memory.binding capability.object = some frame ∧
      state.virtualMemory.memory.allocator.status frame = .owned capability.object ∧
      state.lifecycle.ownedMemory capability.object = some (parent, frame) ∧
      state.frameBudgets.commitment frame = some parent ∧
      (releaseMemory state slot).state = releasedState state capability.object frame := by
  obtain ⟨_, range, low, _, _⟩ := releaseStep_accepted (abstraction state) slot accepted
  have which : slot = 2 ∨ slot = 3 := by unfold memoryBase parentSlots at *; omega
  have status := releaseMemory_status_family state family slot
  rw [accepted, releaseMemory_result] at status
  cases decision : releaseDecision state slot with
  | released object frame =>
      have result : (releaseMemory state slot).result = .released object frame := by
        rw [releaseMemory_result, decision]
      obtain ⟨capability, found, objectEq, kind, _, bound, owned, ownedMemory, stateEq⟩ :=
        releaseMemory_released state slot object frame result
      rw [family_memoryActor state family] at found ownedMemory
      have held : state.capabilities.slots parent slot = some capability := by
        unfold Capability.lookup at found
        split at found
        · split at found
          · split at found
            · next _ heldSlot => cases found; exact heldSlot
            · cases found
          · cases found
        · cases found
      subst objectEq
      rcases family.memory slot which with none | ⟨other, otherFrame, otherHeld, _, _, _, otherBound,
        _, _, otherCommitted⟩
      · rw [none] at held; cases held
      · rw [held] at otherHeld
        cases otherHeld
        rw [bound] at otherBound
        cases otherBound
        exact ⟨capability, frame, held, kind, bound, owned, ownedMemory, otherCommitted, stateEq⟩
  | allocated object frame => exact absurd decision (releaseDecision_not_allocated _ _ _ _)
  | rejected reason =>
      rw [decision] at status
      simp only [SpawnBoundary.memoryStatus] at status
      exact absurd status (reject_status_ne (memoryCode_lt reason) ∘ (by
        intro h; rw [show memoryCode reason = SpawnBoundary.memoryErrorCode reason by
          cases reason <;> rfl]; exact h))

theorem releasedState_fields (state : CompositeState) (object frame : Nat) :
    let post := releasedState state object frame
    post.capabilities = MemoryLifecycle.retireCapabilities state.capabilities object ∧
      post.lifecycle.ownedMemory = releasedOwnership state.lifecycle.ownedMemory object frame ∧
      post.lifecycle.frameOwner = (fun candidate =>
        if candidate = frame then none else state.lifecycle.frameOwner candidate) ∧
      post.lifecycle.endpointOwner = state.lifecycle.endpointOwner ∧
      post.lifecycle.addressOwner = state.lifecycle.addressOwner ∧
      post.lifecycle.current = state.lifecycle.current ∧
      post.virtualMemory.memory.allocator.frames = state.virtualMemory.memory.allocator.frames ∧
      post.virtualMemory.memory.allocator.status = (fun candidate =>
        if candidate = frame then .free
        else state.virtualMemory.memory.allocator.status candidate) ∧
      post.virtualMemory.memory.binding = (fun candidate =>
        if candidate = object then none else state.virtualMemory.memory.binding candidate) ∧
      post.execution.mode = state.execution.mode ∧
      post.execution.core.context = state.execution.core.context ∧
      post.issuers = state.issuers ∧
      post.frameBudgets = state.frameBudgets ∧ post.spawn = state.spawn := by
  intro post
  simp only [post, releasedState, installReleasedMemory, releasedLifecycle, releasedMemory,
    FrameAllocator.setStatus, MemoryLifecycle.setBinding]
  simp
  rfl

/-- `releasedOwnership` only removes records. -/
theorem releasedOwnership_sub {owned : Capability.ObjectId → Option (Capability.SubjectId × Nat)}
    {object frame candidate : Nat} {record : Capability.SubjectId × Nat}
    (held : releasedOwnership owned object frame candidate = some record) :
    owned candidate = some record := by
  unfold releasedOwnership at held
  split at held
  · split at held
    · cases held
    · next found _ => rw [found]; exact held
  · cases held

/-- `releasedOwnership` keeps the records of other objects on other frames. -/
theorem releasedOwnership_keep {owned : Capability.ObjectId → Option (Capability.SubjectId × Nat)}
    {object frame candidate : Nat} {record : Capability.SubjectId × Nat}
    (held : owned candidate = some record) (objectNe : candidate ≠ object) (frameNe : record.2 ≠ frame) :
    releasedOwnership owned object frame candidate = some record := by
  unfold releasedOwnership
  rw [held]
  simp [objectNe, frameNe]

/-- **The abstraction of an accepted release's post-state is the allocator's
successor.** -/
theorem releaseMemory_abstraction (state : CompositeState) (family : Family state) (slot : Nat)
    (accepted : (releaseStep (abstraction state) slot).status = 0x01) :
    abstraction (releaseMemory state slot).state = (releaseStep (abstraction state) slot).next := by
  obtain ⟨_, range, low, _, stepEq⟩ := releaseStep_accepted (abstraction state) slot accepted
  obtain ⟨capability, frame, held, kind, _, _, _, _, stateEq⟩ :=
    releaseMemory_accepted state family slot accepted
  obtain ⟨capabilities, _, _, _, _, _, frames, _, _, _, _, issuers, budgets, spawnSame⟩ :=
    releasedState_fields state capability.object frame
  have which : slot = 2 ∨ slot = 3 := by unfold memoryBase parentSlots at *; omega
  rw [stepEq, stateEq]
  simp only [acceptWith, released, abstraction, State.mk.injEq]
  refine ⟨by rw [issuers], by rw [issuers], by rw [capabilities]; rfl, by rw [spawnSame],
    by rw [spawnSame], by rw [spawnSame], by simp only [subjectBudget, spawnSame], by rw [spawnSame],
    ?_, ?_⟩
  · apply memory_list_update state _ slot _ which
    intro other otherWhich
    unfold memoryIn
    rw [capabilities]
    by_cases same : other = slot
    · subst same
      simp [MemoryLifecycle.retireCapabilities, held]
    · simp only [same, ↓reduceIte]
      cases otherHeld : state.capabilities.slots parent other with
      | none => simp [MemoryLifecycle.retireCapabilities, otherHeld]
      | some otherCapability =>
          have objectNe : otherCapability.object ≠ capability.object := by
            rcases which with rfl | rfl <;> rcases otherWhich with rfl | rfl
            · exact absurd rfl same
            · exact (family.memoryDistinct _ _ held otherHeld).symm
            · exact family.memoryDistinct _ _ otherHeld held
            · exact absurd rfl same
          simp [MemoryLifecycle.retireCapabilities, otherHeld, objectNe]
  · rw [budgetLimit_countP, budgetLimit_countP, frames, budgets]

/-- **An accepted release keeps the family invariant.** -/
theorem releaseMemory_family_preserved (state : CompositeState) (family : Family state)
    (slot : Nat) (accepted : (releaseStep (abstraction state) slot).status = 0x01) :
    Family (releaseMemory state slot).state := by
  have abstractionEq := releaseMemory_abstraction state family slot accepted
  obtain ⟨identity, range, low, heldIdentity, stepEq⟩ :=
    releaseStep_accepted (abstraction state) slot accepted
  rw [stepEq] at abstractionEq
  simp only [acceptWith] at abstractionEq
  obtain ⟨capability, frame, held, kind, bound, frameStatus, owned, committed, stateEq⟩ :=
    releaseMemory_accepted state family slot accepted
  have member := family_frame_member state family frame parent committed
  have which : slot = 2 ∨ slot = 3 := by unfold memoryBase parentSlots at *; omega
  have invariants := family_memoryGate_invariants state family (.release slot)
  simp only [MemoryOperation.apply] at invariants
  obtain ⟨resources, accounting, tree⟩ := invariants
  obtain ⟨capabilities, ownedMemory, frameOwner, endpointOwner, addressOwner, current, frames,
    status, binding, mode, context, issuers, budgets, spawnSame⟩ :=
    releasedState_fields state capability.object frame
  rw [stateEq] at resources accounting tree abstractionEq ⊢
  generalize hpost : releasedState state capability.object frame = post at *
  clear hpost
  have postSlotsSome : ∀ subject namedSlot found,
      post.capabilities.slots subject namedSlot = some found →
        state.capabilities.slots subject namedSlot = some found ∧ found.object ≠ capability.object := by
    intro subject namedSlot found heldNow
    rw [capabilities] at heldNow
    exact (retireCapabilities_slots_some _ _).1 heldNow
  have keepSlot : ∀ namedSlot found, state.capabilities.slots parent namedSlot = some found →
      found.object ≠ capability.object → post.capabilities.slots parent namedSlot = some found := by
    intro namedSlot found heldBefore ne
    rw [capabilities]
    exact (retireCapabilities_slots_some _ _).2 ⟨heldBefore, ne⟩
  have postObjects : ∀ object, object ≠ capability.object →
      post.capabilities.objects object = state.capabilities.objects object := by
    intro object ne; rw [capabilities]; exact retireCapabilities_objects_of_ne _ _ ne
  have postKinds : ∀ object, object ≠ capability.object →
      post.capabilities.kinds object = state.capabilities.kinds object := by
    intro object ne; rw [capabilities]; exact retireCapabilities_kinds_of_ne _ _ ne
  have ownedSub : ∀ object record, post.lifecycle.ownedMemory object = some record →
      state.lifecycle.ownedMemory object = some record := by
    intro object record heldNow
    rw [ownedMemory] at heldNow
    exact releasedOwnership_sub heldNow
  have otherMemory : ∀ otherSlot other, (otherSlot = 2 ∨ otherSlot = 3) → otherSlot ≠ slot →
      state.capabilities.slots parent otherSlot = some other → other.object ≠ capability.object := by
    intro otherSlot other otherWhich ne otherHeld
    rcases which with rfl | rfl <;> rcases otherWhich with rfl | rfl
    · exact absurd rfl ne
    · exact (family.memoryDistinct _ _ held otherHeld).symm
    · exact family.memoryDistinct _ _ otherHeld held
    · exact absurd rfl ne
  refine ⟨resources, accounting, tree, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mode]; exact family.running
  · rw [context]; exact family.current
  · rw [current]; exact family.lifecycleCurrent
  · intro subject; rw [capabilities]; exact family.capacity subject
  · rw [capabilities]; exact family.parentLive
  · rw [spawnSame]; exact family.parentRoot
  · obtain ⟨object, endpointSlot, objectLive, objectKind, owner⟩ := family.endpoint
    have ne : object ≠ capability.object := by
      exact family_kind_object_ne state family endpointSlot held (by rw [kind]; intro h; cases h)
    exact ⟨object, keepSlot 0 _ endpointSlot ne, by rw [postObjects object ne]; exact objectLive,
      by rw [postKinds object ne]; exact objectKind, by rw [endpointOwner]; exact owner⟩
  · obtain ⟨space, spaceSlot, spaceKind, identity, owner⟩ := family.space
    have ne : space.object ≠ capability.object :=
      family_kind_object_ne state family spaceSlot held (by rw [kind, spaceKind]; intro h; cases h)
    exact ⟨space, keepSlot 1 _ spaceSlot ne, spaceKind, identity, by rw [addressOwner]; exact owner⟩
  · intro memorySlot memoryWhich
    by_cases same : memorySlot = slot
    · subst same
      left
      cases heldNow : post.capabilities.slots parent memorySlot with
      | none => rfl
      | some found =>
          obtain ⟨heldBefore, ne⟩ := postSlotsSome _ _ _ heldNow
          rw [held] at heldBefore
          cases heldBefore
          exact absurd rfl ne
    · rcases family.memory memorySlot memoryWhich with none | ⟨other, otherFrame, otherHeld, otherKind,
        revoke, otherIdentity, otherBound, otherStatus, otherOwned, otherCommitted⟩
      · left
        cases heldNow : post.capabilities.slots parent memorySlot with
        | none => rfl
        | some found =>
            obtain ⟨heldBefore, _⟩ := postSlotsSome _ _ _ heldNow
            rw [none] at heldBefore
            cases heldBefore
      · right
        have objectNe := otherMemory memorySlot other memoryWhich same otherHeld
        have frameNe : otherFrame ≠ frame := by
          intro sameFrame
          rw [sameFrame, frameStatus] at otherStatus
          injection otherStatus with sameObject
          exact objectNe sameObject.symm
        refine ⟨other, otherFrame, keepSlot _ _ otherHeld objectNe, otherKind, revoke, otherIdentity,
          ?_, ?_, ?_, by rw [budgets]; exact otherCommitted⟩
        · rw [binding]; simp [objectNe, otherBound]
        · rw [status]; simp [frameNe, otherStatus]
        · rw [ownedMemory]; exact releasedOwnership_keep otherOwned objectNe frameNe
  · intro first second held2 held3
    obtain ⟨before2, _⟩ := postSlotsSome _ _ _ held2
    obtain ⟨before3, _⟩ := postSlotsSome _ _ _ held3
    exact family.memoryDistinct first second before2 before3
  · intro candidateSlot high; rw [spawnSame]; exact family.childSlots candidateSlot high
  · intro found heldAuthority
    rw [spawnSame] at heldAuthority ⊢; exact family.authority found heldAuthority
  · intro subject other; rw [spawnSame]; exact family.others subject other
  · intro candidateSlot entry found
    rw [spawnSame] at found
    obtain ⟨live, positive, limit⟩ := family.childLive candidateSlot entry found
    refine ⟨by rw [capabilities]; exact live, positive, ?_⟩
    rw [budgetLimit_countP, frames, budgets, ← budgetLimit_countP]; exact limit
  · intro subject liveNow
    rw [capabilities] at liveNow
    rw [spawnSame]; exact family.live subject liveNow
  · intro otherFrame subject committedNow
    rw [budgets] at committedNow
    rcases family.committed otherFrame subject committedNow with parentIs |
      ⟨freeFrame, unownedFrame, candidateSlot, entry, found, childIs⟩
    · exact Or.inl parentIs
    · right
      have ne : otherFrame ≠ frame := by
        intro same; rw [same, frameStatus] at freeFrame; cases freeFrame
      refine ⟨by rw [status]; simp [ne, freeFrame], by rw [frameOwner]; simp [ne, unownedFrame],
        candidateSlot, entry, by rw [spawnSame]; exact found, childIs⟩
  · rw [frames]; exact family.framesNodup
  · intro namedSlot found subject heldNow ownedNow
    obtain ⟨heldBefore, _⟩ := postSlotsSome _ _ _ heldNow
    rw [spawnSame]
    apply family.parentNames namedSlot found subject heldBefore
    unfold OwnedBy at ownedNow ⊢
    rw [endpointOwner, addressOwner] at ownedNow
    rcases ownedNow with endpoint | address | memory
    · exact Or.inl endpoint
    · exact Or.inr (Or.inl address)
    · right; right
      cases ownedAfter : post.lifecycle.ownedMemory found.object with
      | none => rw [ownedAfter] at memory; cases memory
      | some record => rw [ownedAfter] at memory; rw [ownedSub _ _ ownedAfter]; exact memory
  · intro object high
    rw [issuers] at high
    obtain ⟨objectDead, objectOwned, objectEndpoint⟩ := family.fresh object high
    refine ⟨?_, ?_, by rw [endpointOwner]; exact objectEndpoint⟩
    · rw [capabilities, retireCapabilities_objects]; split <;> simp [objectDead]
    · cases ownedAfter : post.lifecycle.ownedMemory object with
      | none => rfl
      | some record =>
          have before := ownedSub _ _ ownedAfter
          rw [objectOwned] at before
          cases before
  · intro otherFrame committedNow freeNow
    rw [budgets] at committedNow
    rw [frameOwner]
    by_cases same : otherFrame = frame
    · simp [same]
    · rw [status] at freeNow
      simp only [same, ↓reduceIte] at freeNow ⊢
      exact family.parentFree otherFrame committedNow freeNow
  · rw [abstractionEq]
    have usedAfter : (released (abstraction state) slot).memoryUsed + 1 =
        (abstraction state).memoryUsed := by
      have inRange : slot - memoryBase < (abstraction state).memory.length := by
        have : (abstraction state).memory.length = 2 := rfl
        unfold memoryBase parentSlots at *; omega
      have used := memoryUsed_set (next := released (abstraction state) slot) rfl inRange
      have someAt : (abstraction state).memory[slot - memoryBase] = some identity := by
        unfold State.memoryAt at heldIdentity
        simp only [Nat.not_lt.2 low, ↓reduceIte] at heldIdentity
        rw [List.getElem?_eq_getElem inRange] at heldIdentity
        simpa using heldIdentity
      simp only [someAt, Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte]
        at used
      omega
    have before := family.usage
    rw [← usedAfter] at before
    rw [budgetUsage_committed] at before ⊢
    have committedSame : committedFrames post parent = committedFrames state parent := by
      unfold committedFrames; rw [frames, budgets]
    rw [committedSame]
    have committedNodup : (committedFrames state parent).Nodup :=
      List.Nodup.sublist List.filter_sublist family.framesNodup
    have flip := countP_flip _ committedNodup frame (by unfold committedFrames; simp [member, committed])
      (isOwned post) (isOwned state) (by simp [isOwned, status]) (by simp [isOwned, frameStatus])
      (fun other _ ne => by simp [isOwned, status, ne])
    omega
  · rw [capabilities]; exact family.capabilityBound
  · rw [spawnSame]; exact family.controlBound
  · rw [spawnSame]; exact family.generationBound
  · rw [abstractionEq, released_chargeSum]
    rw [budgetLimit_countP, frames, budgets, ← budgetLimit_countP]
    exact family.frameBound

end LeanOS.SpawnAllocator
