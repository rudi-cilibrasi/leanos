import LeanOS.SpawnAllocatorGrantStep

/-!
# A child termination on a family state is the allocator's termination (#575)

On every composite state satisfying `Family`, `FailStop.terminateChild`
returns the allocator's status and value (`terminateChild_status_family`); an
accepted termination's post-state has the allocator's successor as its
abstraction (`terminateChild_abstraction`) and satisfies `Family` again
(`terminateChild_family_preserved`).
-/
namespace LeanOS.SpawnAllocator

open LeanOS
open LeanOS.FailStop

set_option linter.unusedSimpArgs false

/-! ## The composite termination of a child -/

/-- What the composite termination of a live child does to the projections
the allocator and the family invariant read. -/
theorem terminatedChild_family (state : CompositeState) (family : Family state) (child : Nat)
    (live : state.capabilities.subjects child = true) (notParent : child ≠ parent) :
    let next := terminatedChild state child
    next.execution.mode = state.execution.mode ∧
      next.execution.core.context.currentSubject = parent ∧
      next.lifecycle.current = some parent ∧
      next.capabilities = ResumablePreemption.retireOwnedAddressSpaces state.lifecycle child
        (SubjectLifecycle.terminatedCapabilities state.lifecycle child) ∧
      next.lifecycle.capabilities = next.capabilities ∧
      next.lifecycle.endpointOwner = (fun object =>
        if state.lifecycle.endpointOwner object = some child then none
        else state.lifecycle.endpointOwner object) ∧
      next.lifecycle.addressOwner = (fun space =>
        if state.lifecycle.addressOwner space = some child then none
        else state.lifecycle.addressOwner space) ∧
      next.lifecycle.ownedMemory = (fun object =>
        match state.lifecycle.ownedMemory object with
        | some ownership => if ownership.1 = child then none else some ownership
        | none => none) ∧
      next.lifecycle.frameOwner = (fun frame =>
        if state.lifecycle.frameOwner frame = some child then none
        else state.lifecycle.frameOwner frame) := by
  intro next
  have runtime := family_runtime state family
  have coherent := runtime.1
  have resumableLifecycle : state.resumable.scheduler.lifecycle = state.lifecycle := by
    rw [coherent.2.2.2.2.2.2.2.1, coherent.2.1]
  have lifeCaps := family_lifecycleCapabilities state family
  have issued := live_issued runtime live
  have liveLife : state.lifecycle.capabilities.subjects child = true := by rw [lifeCaps]; exact live
  have accepted : (SubjectLifecycle.terminate state.lifecycle child).result = .accepted := by
    simp [SubjectLifecycle.terminate, issued, liveLife]
  have currentNe : state.lifecycle.current ≠ some child := by
    rw [family.lifecycleCurrent]; simp [Ne.symm notParent]
  simp only [next, terminatedChild, authoritativeGate_ordinary_state, gate, family.running,
    applyOperation, accepted, installTerminatedSubject, installTerminatedResumable,
    ResumablePreemption.cleanupSubject, resumableLifecycle, SubjectLifecycle.terminateState]
  simp [family.lifecycleCurrent, Ne.symm notParent]
  funext object
  cases owned : state.lifecycle.ownedMemory object <;> simp [owned]

/-! ## What the termination keeps -/

/-- A child recorded in the parent's table owns nothing the parent's slots
name. -/
theorem child_not_owner (state : CompositeState) (family : Family state) (slot : Nat)
    (entry : ChildEntry) (found : state.spawn.children parent slot = some entry)
    (namedSlot : Nat) (capability : Capability.Capability)
    (held : state.capabilities.slots parent namedSlot = some capability) :
    ¬OwnedBy state.lifecycle entry.child capability.object := by
  intro owned
  have none := family.parentNames namedSlot capability entry.child held owned
  rw [family.tree.recorded parent slot entry found] at none
  cases none

/-- The parent's slots survive the termination of a child. -/
theorem terminated_parentSlots (state : CompositeState) (family : Family state) (slot : Nat)
    (entry : ChildEntry) (found : state.spawn.children parent slot = some entry)
    (live : state.capabilities.subjects entry.child = true) (notParent : entry.child ≠ parent)
    (namedSlot : Nat) :
    (terminatedChild state entry.child).capabilities.slots parent namedSlot =
      state.capabilities.slots parent namedSlot := by
  obtain ⟨_, _, _, capabilities, _⟩ := terminatedChild_family state family entry.child live notParent
  rw [capabilities]
  have lifeCaps := family_lifecycleCapabilities state family
  unfold ResumablePreemption.retireOwnedAddressSpaces SubjectLifecycle.terminatedCapabilities
  simp only [lifeCaps]
  cases held : state.capabilities.slots parent namedSlot with
  | none => simp
  | some capability =>
      have notOwned := child_not_owner state family slot entry found namedSlot capability held
      unfold OwnedBy at notOwned
      simp only [not_or] at notOwned
      obtain ⟨endpoint, address, memory⟩ := notOwned
      have parentNe : (parent == entry.child) = false := by
        simpa using Ne.symm notParent
      simp [held, parentNe, endpoint, address, memory, Ne.symm notParent]

/-- Reclaiming a child's frames does nothing when every frame committed to
it is free. -/
theorem reclaim_noop (state : CompositeState) (child : Nat)
    (free : ∀ frame, state.frameBudgets.commitment frame = some child →
      state.virtualMemory.memory.allocator.status frame = .free) :
    (reclaimChildFrames state child).virtualMemory.memory.allocator =
        state.virtualMemory.memory.allocator ∧
      (reclaimChildFrames state child).virtualMemory.memory.binding =
        state.virtualMemory.memory.binding := by
  have never : ∀ frame, reclaimable state child frame = false := by
    intro frame
    unfold reclaimable
    by_cases committed : state.frameBudgets.commitment frame = some child
    · simp [committed, free frame committed]
    · simp [committed]
  constructor
  · simp only [reclaimChildFrames, reclaimedVirtualMemory, never]
    simp
  · simp only [reclaimChildFrames, reclaimedVirtualMemory]
    funext object
    cases bound : state.virtualMemory.memory.binding object <;> simp [never]

/-! ## The status of a termination -/

/-- **A child termination on a family state returns the allocator's status
and value.** -/
theorem terminateChild_status_family (state : CompositeState) (family : Family state)
    (control : UInt64) :
    SpawnBoundary.childStatus (FailStop.terminateChild state control).result =
      ((terminateStep (abstraction state) control).status,
        (terminateStep (abstraction state) control).value) := by
  unfold FailStop.terminateChild terminateStep
  cases allocatorResolved : (abstraction state).resolveControl control with
  | error denial =>
      rw [resolveControl_family_error state family control denial allocatorResolved]
      simp [rejectWith, SpawnBoundary.childStatus]
  | ok found =>
      obtain ⟨slot, record⟩ := found
      obtain ⟨entry, resolved, recordEq⟩ :=
        resolveControl_family_ok state family control slot record allocatorResolved
      rw [resolved]
      obtain ⟨_, _, _, limit⟩ := resolved_entry state family control slot entry resolved
      subst recordEq
      simp [acceptWith, SpawnBoundary.childStatus, limit, recordOf]

/-! ## The post-state of an accepted termination -/

/-- The termination's post-state, read where the allocator and the family
invariant look. -/
theorem terminate_post (state : CompositeState) (family : Family state) (slot : Nat)
    (entry : ChildEntry) (found : state.spawn.children parent slot = some entry) :
    let post := releaseChild (terminatedChild state entry.child) parent slot entry.child
    (∀ namedSlot, post.capabilities.slots parent namedSlot =
        state.capabilities.slots parent namedSlot) ∧
      (∀ subject, post.capabilities.subjects subject =
        if subject = entry.child then false else state.capabilities.subjects subject) ∧
      (∀ object, ¬OwnedBy state.lifecycle entry.child object →
        post.capabilities.objects object = state.capabilities.objects object ∧
          post.capabilities.kinds object = state.capabilities.kinds object) ∧
      (∀ object, post.capabilities.objects object = true →
        state.capabilities.objects object = true) ∧
      post.capabilities.slotCapacity = state.capabilities.slotCapacity ∧
      post.capabilities.nextIdentity = state.capabilities.nextIdentity ∧
      (∀ subject object, OwnedBy post.lifecycle subject object →
        OwnedBy state.lifecycle subject object) ∧
      post.lifecycle.endpointOwner = (fun object =>
        if state.lifecycle.endpointOwner object = some entry.child then none
        else state.lifecycle.endpointOwner object) ∧
      post.lifecycle.addressOwner = (fun space =>
        if state.lifecycle.addressOwner space = some entry.child then none
        else state.lifecycle.addressOwner space) ∧
      post.lifecycle.ownedMemory = (fun object =>
        match state.lifecycle.ownedMemory object with
        | some ownership => if ownership.1 = entry.child then none else some ownership
        | none => none) ∧
      post.lifecycle.frameOwner = (fun frame =>
        if state.lifecycle.frameOwner frame = some entry.child then none
        else state.lifecycle.frameOwner frame) ∧
      post.execution.mode = state.execution.mode ∧
      post.execution.core.context.currentSubject = parent ∧
      post.lifecycle.current = some parent ∧
      post.issuers = state.issuers ∧
      post.virtualMemory.memory.allocator = state.virtualMemory.memory.allocator ∧
      post.virtualMemory.memory.binding = state.virtualMemory.memory.binding ∧
      post.frameBudgets = returnFrames state.frameBudgets entry.child parent ∧
      (∀ candidateSlot, post.spawn.children parent candidateSlot =
        if candidateSlot = slot then none else state.spawn.children parent candidateSlot) ∧
      post.spawn.parent = (fun candidate =>
        if candidate = entry.child then none else state.spawn.parent candidate) ∧
      post.spawn.authority = state.spawn.authority ∧
      post.spawn.nextGeneration = state.spawn.nextGeneration ∧
      post.spawn.nextChildGeneration = state.spawn.nextChildGeneration := by
  intro post
  obtain ⟨live, _, _⟩ := family.childLive slot entry found
  obtain ⟨_, _, notParent, _, _⟩ := family.accounting.entries parent slot entry found
  obtain ⟨_, agrees, spawnSame⟩ := terminatedChild_facts state entry.child family.resources
  obtain ⟨issuers, budgets, _, _, _, _, allocator, binding⟩ := agrees
  obtain ⟨mode, current, lifecycleCurrent, capabilities, _, endpointOwner, addressOwner,
    ownedMemory, frameOwner⟩ := terminatedChild_family state family entry.child live notParent
  have childFree : ∀ frame,
      (terminatedChild state entry.child).frameBudgets.commitment frame = some entry.child →
      (terminatedChild state entry.child).virtualMemory.memory.allocator.status frame = .free := by
    intro frame committed
    rw [budgets] at committed
    rw [allocator]
    rcases family.committed frame entry.child committed with same | ⟨free, _⟩
    · exact absurd same notParent
    · exact free
  obtain ⟨allocatorReclaim, bindingReclaim⟩ := reclaim_noop _ entry.child childFree
  have lifeCaps := family_lifecycleCapabilities state family
  have postCaps : post.capabilities = (terminatedChild state entry.child).capabilities := rfl
  have postLife : post.lifecycle = (terminatedChild state entry.child).lifecycle := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · intro namedSlot
    rw [postCaps]
    exact terminated_parentSlots state family slot entry found live notParent namedSlot
  · intro subject
    rw [postCaps, capabilities]
    unfold ResumablePreemption.retireOwnedAddressSpaces SubjectLifecycle.terminatedCapabilities
    simp only [lifeCaps]
    by_cases same : subject = entry.child
    · subst same; simp [SubjectLifecycle.setBool]
    · simp [SubjectLifecycle.setBool, same]
  · intro object notOwned
    unfold OwnedBy at notOwned
    simp only [not_or] at notOwned
    obtain ⟨endpoint, address, memory⟩ := notOwned
    rw [postCaps, capabilities]
    unfold ResumablePreemption.retireOwnedAddressSpaces SubjectLifecycle.terminatedCapabilities
    simp only [lifeCaps]
    simp [endpoint, address, memory]
  · intro object liveNow
    rw [postCaps, capabilities] at liveNow
    unfold ResumablePreemption.retireOwnedAddressSpaces SubjectLifecycle.terminatedCapabilities
      at liveNow
    simp only [lifeCaps] at liveNow
    split at liveNow
    · cases liveNow
    · split at liveNow
      · cases liveNow
      · exact liveNow
  · rw [postCaps, capabilities]
    simp [ResumablePreemption.retireOwnedAddressSpaces, SubjectLifecycle.terminatedCapabilities,
      lifeCaps]
  · rw [postCaps, capabilities]
    simp [ResumablePreemption.retireOwnedAddressSpaces, SubjectLifecycle.terminatedCapabilities,
      lifeCaps]
  · intro subject object owned
    rw [postLife] at owned
    unfold OwnedBy at owned ⊢
    rw [endpointOwner, addressOwner, ownedMemory] at owned
    dsimp only at owned
    rcases owned with endpoint | address | memory
    · left; split at endpoint
      · cases endpoint
      · exact endpoint
    · right; left; split at address
      · cases address
      · exact address
    · right; right
      cases held : state.lifecycle.ownedMemory object with
      | none => rw [held] at memory; cases memory
      | some ownership =>
          rw [held] at memory
          simp only at memory
          split at memory
          · cases memory
          · simpa using memory
  · rw [postLife]; exact endpointOwner
  · rw [postLife]; exact addressOwner
  · rw [postLife]; exact ownedMemory
  · rw [postLife]; exact frameOwner
  · show (terminatedChild state entry.child).execution.mode = _
    exact mode
  · show (terminatedChild state entry.child).execution.core.context.currentSubject = _
    exact current
  · rw [postLife]; exact lifecycleCurrent
  · show (terminatedChild state entry.child).issuers = _
    exact issuers
  · show (reclaimChildFrames (terminatedChild state entry.child) entry.child).virtualMemory.memory.allocator = _
    rw [allocatorReclaim, allocator]
  · show (reclaimChildFrames (terminatedChild state entry.child) entry.child).virtualMemory.memory.binding = _
    rw [bindingReclaim, binding]
  · show returnFrames (terminatedChild state entry.child).frameBudgets entry.child parent = _
    rw [budgets]
  · intro candidateSlot
    show (if parent = parent ∧ candidateSlot = slot then none
      else (terminatedChild state entry.child).spawn.children parent candidateSlot) = _
    rw [spawnSame]; simp
  · show (fun candidate => if candidate = entry.child then none
      else (terminatedChild state entry.child).spawn.parent candidate) = _
    rw [spawnSame]
  · show (terminatedChild state entry.child).spawn.authority = _
    rw [spawnSame]
  · show (terminatedChild state entry.child).spawn.nextGeneration = _
    rw [spawnSame]
  · show (terminatedChild state entry.child).spawn.nextChildGeneration = _
    rw [spawnSame]

/-- Returning a child's free frames leaves the parent's usage unchanged. -/
theorem usage_returned (state post : CompositeState) (child : Nat)
    (frames : post.virtualMemory.memory.allocator = state.virtualMemory.memory.allocator)
    (budgets : post.frameBudgets = returnFrames state.frameBudgets child parent)
    (free : ∀ frame, state.frameBudgets.commitment frame = some child →
      state.virtualMemory.memory.allocator.status frame = .free) :
    post.budgetUsage parent = state.budgetUsage parent := by
  rw [budgetUsage_committed, budgetUsage_committed]
  unfold committedFrames isOwned
  rw [frames, budgets, List.countP_filter, List.countP_filter]
  apply List.countP_congr
  intro frame _
  simp only [returnFrames]
  by_cases returned : state.frameBudgets.commitment frame = some child
  · have freeFrame := free frame returned
    simp [returned, freeFrame]
  · simp [returned]

/-- An accepted termination on a family state, unfolded. -/
theorem terminateChild_accepted (state : CompositeState) (family : Family state)
    (control : UInt64) (accepted : (terminateStep (abstraction state) control).status = 0x01) :
    ∃ slot entry, FailStop.resolveControl state control = .ok (slot, entry) ∧
      (terminateStep (abstraction state) control).next =
        terminated (abstraction state) slot (recordOf entry) ∧
      (FailStop.terminateChild state control).state =
        releaseChild (terminatedChild state entry.child) parent slot entry.child := by
  obtain ⟨slot, record, allocatorResolved, stepEq⟩ :=
    terminateStep_accepted (abstraction state) control accepted
  obtain ⟨entry, resolved, recordEq⟩ :=
    resolveControl_family_ok state family control slot record allocatorResolved
  refine ⟨slot, entry, resolved, by rw [stepEq, recordEq]; rfl, ?_⟩
  simp [FailStop.terminateChild, resolved, family_spawnParent state family]

/-- **The abstraction of an accepted termination's post-state is the
allocator's successor.** -/
theorem terminateChild_abstraction (state : CompositeState) (family : Family state)
    (control : UInt64) (accepted : (terminateStep (abstraction state) control).status = 0x01) :
    abstraction (FailStop.terminateChild state control).state =
      (terminateStep (abstraction state) control).next := by
  obtain ⟨slot, entry, resolved, nextEq, stateEq⟩ :=
    terminateChild_accepted state family control accepted
  obtain ⟨found, live, _, limit⟩ := resolved_entry state family control slot entry resolved
  obtain ⟨_, _, notParent, _, _⟩ := family.accounting.entries parent slot entry found
  obtain ⟨parentSlots, _, _, _, _, nextIdentity, _, _, _, _, _, _, _, _, issuers, allocator,
    _, budgets, children, _, authority, nextGeneration, nextChild⟩ :=
    terminate_post state family slot entry found
  have slotSmall : slot < childCapacity := by
    by_cases small : slot < childCapacity
    · exact small
    · rw [family.childSlots slot (by omega)] at found; cases found
  obtain ⟨_, agrees, _⟩ := terminatedChild_facts state entry.child family.resources
  obtain ⟨_, budgetsT, _, _, _, _, allocatorT, _⟩ := agrees
  have limitsT := fun subject => (budget_eq_of_allocator budgetsT allocatorT subject).2
  obtain ⟨limitParent, _, _⟩ := releaseChild_limits (terminatedChild state entry.child) parent slot
    entry.child notParent
  rw [limitsT, limitsT, limit] at limitParent
  rw [nextEq, stateEq]
  simp only [terminated, abstraction, State.mk.injEq]
  refine ⟨by rw [issuers], by rw [issuers], nextIdentity, nextChild, nextGeneration,
    by rw [authority], by simp only [subjectBudget, authority], ?_, ?_, ?_⟩
  · apply map_range_set childCapacity slot slotSmall
    intro index
    rw [children]
    by_cases same : index = slot
    · simp [same]
    · simp [same]
  · simp [memoryIn, parentSlots]
  · rw [limitParent]; rfl

/-! ## The family invariant after a termination -/

/-- **An accepted termination keeps the family invariant.** -/
theorem terminateChild_family_preserved (state : CompositeState) (family : Family state)
    (control : UInt64) (accepted : (terminateStep (abstraction state) control).status = 0x01) :
    Family (FailStop.terminateChild state control).state := by
  have abstractionEq := terminateChild_abstraction state family control accepted
  obtain ⟨slot, entry, resolved, nextEq, stateEq⟩ :=
    terminateChild_accepted state family control accepted
  rw [nextEq] at abstractionEq
  obtain ⟨found, live, _, limit⟩ := resolved_entry state family control slot entry resolved
  obtain ⟨_, _, notParent, _, _⟩ := family.accounting.entries parent slot entry found
  obtain ⟨parentSlots, subjects, objectsKinds, objectsLive, capacity, nextIdentity, ownedBy,
    endpointOwner, addressOwner, ownedMemory, frameOwner, mode, current, lifecycleCurrent,
    issuers, allocator, binding, budgets, children, parentRecord, authority, nextGeneration,
    nextChild⟩ := terminate_post state family slot entry found
  have invariants := family_childGate_invariants state family (.terminateChild control)
  simp only [ChildOperation.apply] at invariants
  obtain ⟨resources, accounting, tree⟩ := invariants
  have slotSmall : slot < childCapacity := by
    by_cases small : slot < childCapacity
    · exact small
    · rw [family.childSlots slot (by omega)] at found; cases found
  have childFree : ∀ frame, state.frameBudgets.commitment frame = some entry.child →
      state.virtualMemory.memory.allocator.status frame = .free ∧
        state.lifecycle.frameOwner frame = none := by
    intro frame committed
    rcases family.committed frame entry.child committed with same | ⟨free, unowned, _⟩
    · exact absurd same notParent
    · exact ⟨free, unowned⟩
  rw [stateEq] at resources accounting tree abstractionEq ⊢
  generalize hpost : releaseChild (terminatedChild state entry.child) parent slot entry.child =
    post at *
  have postLimits := releaseChild_limits (terminatedChild state entry.child) parent slot
    entry.child notParent
  rw [hpost] at postLimits
  obtain ⟨_, agrees, _⟩ := terminatedChild_facts state entry.child family.resources
  obtain ⟨_, budgetsT, _, _, _, _, allocatorT, _⟩ := agrees
  have limitsT := fun subject => (budget_eq_of_allocator budgetsT allocatorT subject).2
  obtain ⟨limitParent, _, limitOther⟩ := postLimits
  clear hpost
  have notOwned : ∀ namedSlot capability, state.capabilities.slots parent namedSlot = some capability →
      ¬OwnedBy state.lifecycle entry.child capability.object :=
    fun namedSlot capability held => child_not_owner state family slot entry found namedSlot
      capability held
  have oldSlot : ∀ candidateSlot other, state.spawn.children parent candidateSlot = some other →
      candidateSlot ≠ slot → post.spawn.children parent candidateSlot = some other := by
    intro candidateSlot other found' ne; rw [children]; simp [ne, found']
  have otherChild : ∀ candidateSlot other, state.spawn.children parent candidateSlot = some other →
      candidateSlot ≠ slot → other.child ≠ entry.child := by
    intro candidateSlot other found' ne same
    exact ne (family.accounting.unique parent candidateSlot other parent slot entry found' found
      same).2
  refine ⟨resources, accounting, tree, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mode]; exact family.running
  · exact current
  · exact lifecycleCurrent
  · intro subject; rw [capacity]; exact family.capacity subject
  · rw [subjects]; simp [Ne.symm notParent, family.parentLive]
  · rw [parentRecord]; simp [Ne.symm notParent, family.parentRoot]
  · obtain ⟨object, endpointSlot, objectLive, objectKind, owner⟩ := family.endpoint
    have notOwnedObject := notOwned 0 _ endpointSlot
    obtain ⟨objectsSame, kindsSame⟩ := objectsKinds object notOwnedObject
    refine ⟨object, by rw [parentSlots]; exact endpointSlot, by rw [objectsSame]; exact objectLive,
      by rw [kindsSame]; exact objectKind, ?_⟩
    rw [endpointOwner]
    have ne : state.lifecycle.endpointOwner object ≠ some entry.child := by
      intro same; exact notOwnedObject (Or.inl same)
    have bystanderNe : bystander ≠ entry.child := by
      intro same; rw [owner, same] at ne; exact ne rfl
    simp [ne, owner, bystanderNe]
  · obtain ⟨capability, held, kind, identity, owner⟩ := family.space
    refine ⟨capability, by rw [parentSlots]; exact held, kind, identity, ?_⟩
    rw [addressOwner]
    have ne : state.lifecycle.addressOwner capability.object ≠ some entry.child := by
      intro same; exact notOwned 1 capability held (Or.inr (Or.inl same))
    simp [ne, owner, Ne.symm notParent]
  · intro memorySlot which
    rcases family.memory memorySlot which with empty | ⟨capability, frame, held, kind, revoke,
      identity, bound, status, owned, committed⟩
    · left; rw [parentSlots]; exact empty
    · right
      refine ⟨capability, frame, by rw [parentSlots]; exact held, kind, revoke, identity,
        by rw [binding]; exact bound, by rw [allocator]; exact status, ?_, ?_⟩
      · rw [ownedMemory]; simp [owned, notParent.symm, Ne.symm notParent]
      · rw [budgets]
        have ne : state.frameBudgets.commitment frame ≠ some entry.child := by
          rw [committed]; simp [Ne.symm notParent]
        simp [returnFrames, ne, committed]
  · intro first second held2 held3
    rw [parentSlots] at held2 held3
    exact family.memoryDistinct first second held2 held3
  · intro candidateSlot high
    rw [children]
    have : candidateSlot ≠ slot := by omega
    simp [this, family.childSlots candidateSlot high]
  · intro capability held
    rw [authority] at held
    rw [nextGeneration]; exact family.authority capability held
  · intro subject other
    rw [authority]; exact family.others subject other
  · intro candidateSlot other found'
    rw [children] at found'
    by_cases same : candidateSlot = slot
    · simp [same] at found'
    · simp only [same, ↓reduceIte] at found'
      obtain ⟨otherLive, otherPositive, otherLimit⟩ := family.childLive candidateSlot other found'
      obtain ⟨_, _, otherNe, _, _⟩ := family.accounting.entries parent candidateSlot other found'
      have distinct := otherChild candidateSlot other found' same
      refine ⟨by rw [subjects]; simp [distinct, otherLive], otherPositive, ?_⟩
      rw [limitOther other.child otherNe distinct, limitsT, otherLimit]
  · intro subject liveNow
    rw [subjects] at liveNow
    by_cases isChild : subject = entry.child
    · simp [isChild] at liveNow
    · simp only [isChild, ↓reduceIte] at liveNow
      rcases family.live subject liveNow with bystanderIs | parentIs |
        ⟨candidateSlot, other, found', childIs⟩
      · exact Or.inl bystanderIs
      · exact Or.inr (Or.inl parentIs)
      · right; right
        have ne : candidateSlot ≠ slot := by
          intro same; subst same
          rw [found] at found'
          have := Option.some.inj found'
          subst this
          exact isChild childIs.symm
        exact ⟨candidateSlot, other, oldSlot candidateSlot other found' ne, childIs⟩
  · intro frame subject committedNow
    rw [budgets] at committedNow
    simp only [returnFrames] at committedNow
    by_cases returned : state.frameBudgets.commitment frame = some entry.child
    · simp only [returned, ↓reduceIte, Option.some.injEq] at committedNow
      exact Or.inl committedNow.symm
    · simp only [returned, ↓reduceIte] at committedNow
      rcases family.committed frame subject committedNow with parentIs |
        ⟨freeFrame, unowned, candidateSlot, other, found', childIs⟩
      · exact Or.inl parentIs
      · right
        have ne : candidateSlot ≠ slot := by
          intro same; subst same
          rw [found] at found'
          have := Option.some.inj found'
          subst this
          exact returned (childIs ▸ committedNow)
        refine ⟨by rw [allocator]; exact freeFrame, ?_, candidateSlot, other,
          oldSlot candidateSlot other found' ne, childIs⟩
        rw [frameOwner]; simp [unowned]
  · rw [allocator]; exact family.framesNodup
  · intro namedSlot capability subject held owned
    rw [parentSlots] at held
    have ownedBefore := ownedBy subject capability.object owned
    have none := family.parentNames namedSlot capability subject held ownedBefore
    rw [parentRecord]; simp [none]
  · intro object high
    rw [issuers] at high
    obtain ⟨dead, owned, endpoint⟩ := family.fresh object high
    refine ⟨?_, ?_, ?_⟩
    · cases liveNow : post.capabilities.objects object with
      | false => rfl
      | true => rw [objectsLive object liveNow] at dead; cases dead
    · rw [ownedMemory]; simp [owned]
    · rw [endpointOwner]; simp [endpoint]
  · intro frame committedNow freeNow
    rw [budgets] at committedNow
    rw [allocator] at freeNow
    rw [frameOwner]
    simp only [returnFrames] at committedNow
    by_cases returned : state.frameBudgets.commitment frame = some entry.child
    · simp [(childFree frame returned).2]
    · simp only [returned, ↓reduceIte] at committedNow
      simp [family.parentFree frame committedNow freeNow]
  · rw [abstractionEq, terminated_memoryUsed,
      usage_returned state post entry.child allocator budgets
        (fun frame committed => (childFree frame committed).1)]
    exact family.usage
  · rw [nextIdentity]; exact family.capabilityBound
  · rw [nextChild]; exact family.controlBound
  · rw [nextGeneration]; exact family.generationBound
  · have record : (abstraction state).childAt slot = some (recordOf entry) := by
      rw [abstraction_childAt_family state family, found]; rfl
    have sum := terminated_chargeSum (abstraction state) slot (recordOf entry) record
    rw [abstractionEq]
    have frameBound := family.frameBound
    rw [limitsT, limitsT, limit] at limitParent
    have charge : (recordOf entry).charge = entry.charge := rfl
    omega

end LeanOS.SpawnAllocator
