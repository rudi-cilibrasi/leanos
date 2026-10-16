import LeanOS.FailStop.SpawnTree

namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

theorem copy_subjects (state : Capability.State) (actor source destination destinationSlot : Nat)
    (requested : Capability.Rights) :
    (Capability.copy state actor source destination destinationSlot requested).state.subjects =
      state.subjects ∧
    (Capability.copy state actor source destination destinationSlot requested).state.objects =
      state.objects := by
  unfold Capability.copy
  repeat' split
  all_goals simp [Capability.reject, Capability.install]

/-- What an accepted spawn writes into the lifecycle records. -/
theorem spawn_lifecycle_records (state : CompositeState) (request : SpawnRequest)
    (child addressSpace : Nat) (holds : RuntimeWellFormed state)
    (spawned : (spawn state request).result = .spawned child addressSpace) :
    (spawn state request).state.lifecycle.ownedMemory = state.lifecycle.ownedMemory ∧
      (spawn state request).state.lifecycle.endpointOwner = state.lifecycle.endpointOwner ∧
      (spawn state request).state.lifecycle.addressOwner =
        VirtualMapping.setOwner state.lifecycle.addressOwner addressSpace (some child) ∧
      (spawn state request).state.capabilities.subjects =
        SubjectLifecycle.setBool state.capabilities.subjects child true ∧
      state.capabilities.objects addressSpace = false ∧
      state.virtualMemory.issuedAddressSpace addressSpace = false := by
  obtain ⟨_, issued, _, spaceAccepted, resolution, _, _, _, copied, stateEq⟩ :=
    spawn_spawned_stages state request child addressSpace spawned
  obtain ⟨_, _, created, eq⟩ := issueSubject_issued state child issued
  obtain ⟨createdCaps, createdVm⟩ := issueSubject_capabilities state child issued
  have lifeCaps : state.lifecycle.capabilities = state.capabilities := holds.1.2.2.2.1.symm
  have copySame := copy_subjects
    (spawnSpaced (issueSubject state).state child addressSpace).capabilities
    (spawnParent state) resolution.handle.slot child childEndpointSlot request.rights
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [stateEq]
    simp [recordSpawn, installCopiedCapabilities, spawnSpaced, installCreatedAddressSpace, eq,
      applyOperation, created, installCreatedSubject,
      SubjectLifecycle.create_accepted_state _ _ created]
  · rw [stateEq]
    simp [recordSpawn, installCopiedCapabilities, spawnSpaced, installCreatedAddressSpace, eq,
      applyOperation, created, installCreatedSubject,
      SubjectLifecycle.create_accepted_state _ _ created]
  · rw [stateEq]
    simp [recordSpawn, installCopiedCapabilities, spawnSpaced, installCreatedAddressSpace, eq,
      applyOperation, created, installCreatedSubject,
      SubjectLifecycle.create_accepted_state _ _ created]
  · rw [stateEq]
    simp only [recordSpawn, installCopiedCapabilities]
    rw [copySame.1]
    simp only [spawnSpaced, installCreatedAddressSpace, createdVirtualMemory_capabilities,
      createdVm]
    simp [addressSpaceCapabilities, Capability.installRoot, Capability.install,
      VirtualMapping.activateAddressSpace, createdCaps, lifeCaps]
  · have dead := spaceAccepted
    simp only [VirtualMapping.createAddressSpace] at dead
    split at dead
    · simp [VirtualMapping.reject] at dead
    split at dead
    · simp [VirtualMapping.reject] at dead
    split at dead
    · simp [VirtualMapping.reject] at dead
    split at dead
    · simp [VirtualMapping.reject] at dead
    split at dead
    · simp [VirtualMapping.reject] at dead
    split at dead
    · simp [VirtualMapping.reject] at dead
    next notLive =>
    rw [createdVm, createdCaps, lifeCaps] at notLive
    simpa using notLive
  · have fresh := spaceAccepted
    simp only [VirtualMapping.createAddressSpace] at fresh
    split at fresh
    · simp [VirtualMapping.reject] at fresh
    split at fresh
    · simp [VirtualMapping.reject] at fresh
    split at fresh
    · simp [VirtualMapping.reject] at fresh
    split at fresh
    · simp [VirtualMapping.reject] at fresh
    split at fresh
    · simp [VirtualMapping.reject] at fresh
    next unissued =>
    have vm : (issueSubject state).state.virtualMemory.issuedAddressSpace =
        state.virtualMemory.issuedAddressSpace := by
      rw [eq]; simp [applyOperation, created, installCreatedSubject]
    rw [vm] at unissued
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at unissued
    exact unissued.1

/-- An accepted spawn keeps the running latch and the current subject. -/
theorem spawn_execution (state : CompositeState) (request : SpawnRequest)
    (child addressSpace : Nat)
    (spawned : (spawn state request).result = .spawned child addressSpace) :
    (spawn state request).state.execution.mode = state.execution.mode ∧
      spawnParent (spawn state request).state = spawnParent state := by
  obtain ⟨_, issued, _, _, _, _, _, _, _, stateEq⟩ :=
    spawn_spawned_stages state request child addressSpace spawned
  obtain ⟨_, _, created, eq⟩ := issueSubject_issued state child issued
  rw [stateEq]
  simp [recordSpawn, installCopiedCapabilities, spawnSpaced, installCreatedAddressSpace, eq,
    applyOperation, created, installCreatedSubject, spawnParent]

/-- The #489 spawn records exactly the new child's address space. -/
theorem spawn_addressSpace_record (state : CompositeState) (request : SpawnRequest)
    (child addressSpace : Nat)
    (spawned : (spawn state request).result = .spawned child addressSpace) (candidate : Nat) :
    (spawn state request).state.spawn.addressSpace candidate =
      if candidate = child then some addressSpace
      else state.spawn.addressSpace candidate := by
  obtain ⟨_, issued, _, _, _, _, _, _, _, stateEq⟩ :=
    spawn_spawned_stages state request child addressSpace spawned
  obtain ⟨_, _, created, eq⟩ := issueSubject_issued state child issued
  rw [stateEq]
  simp [recordSpawn, installCopiedCapabilities, spawnSpaced, installCreatedAddressSpace, eq,
    applyOperation, created, installCreatedSubject]

/-- The capability registry and lifecycle of an accepted composite
termination of `child`. -/
theorem terminatedChild_registry (state : CompositeState) (child : Nat)
    (running : state.execution.mode = .running) (holds : RuntimeWellFormed state)
    (accepted : (SubjectLifecycle.terminate state.lifecycle child).result = .accepted) :
    (terminatedChild state child).capabilities =
        ResumablePreemption.retireOwnedAddressSpaces state.lifecycle child
          (SubjectLifecycle.terminatedCapabilities state.lifecycle child) ∧
      (terminatedChild state child).lifecycle.runnable =
        SubjectLifecycle.setBool state.lifecycle.runnable child false ∧
      (terminatedChild state child).lifecycle.current =
        (if state.lifecycle.current = some child then none else state.lifecycle.current) ∧
      (terminatedChild state child).lifecycle.addressOwner = (fun addressSpace =>
        if state.lifecycle.addressOwner addressSpace = some child then none
        else state.lifecycle.addressOwner addressSpace) ∧
      (terminatedChild state child).lifecycle.ownedMemory = (fun object =>
        match state.lifecycle.ownedMemory object with
        | some ownership => if ownership.1 = child then none else some ownership
        | none => none) ∧
      (terminatedChild state child).lifecycle.endpointOwner = (fun object =>
        if state.lifecycle.endpointOwner object = some child then none
        else state.lifecycle.endpointOwner object) := by
  have coherent := holds.1
  have resumableLifecycle : state.resumable.scheduler.lifecycle = state.lifecycle := by
    rw [coherent.2.2.2.2.2.2.2.1, coherent.2.1]
  simp only [terminatedChild, authoritativeGate_ordinary_state, gate, running, applyOperation,
    accepted]
  simp [installTerminatedSubject, installTerminatedResumable,
    ResumablePreemption.cleanupSubject, SubjectLifecycle.terminateState, resumableLifecycle]
  funext object
  cases state.lifecycle.ownedMemory object <;> rfl

/-! ## Frame grants between spawn and rollback -/

/-- Run frame grants for one control word through the gate, in order. -/
def grantAll (state : CompositeState) (control : UInt64) : List Nat → CompositeState
  | [] => state
  | frames :: rest => grantAll (childGate state (.grantFrames control frames)).state control rest

/-- A state reached from `spawned` by frame grants to the child in the
parent's table slot `slot`: only the child's table entry (its charge) and the
frame commitments differ, and every commitment that differs moved a free
frame of the parent to the child. -/
structure GrantedFrom (spawned state : CompositeState) (parent slot child generation : Nat) :
    Prop where
  rest : { state with spawn := spawned.spawn, frameBudgets := spawned.frameBudgets } = spawned
  entry : ∃ charge, state.spawn = { spawned.spawn with
    children := fun candidate candidateSlot =>
      if candidate = parent ∧ candidateSlot = slot then some ⟨child, generation, charge⟩
      else spawned.spawn.children candidate candidateSlot }
  frames : ∀ frame, state.frameBudgets.commitment frame =
      spawned.frameBudgets.commitment frame ∨
    (spawned.frameBudgets.commitment frame = some parent ∧
      state.frameBudgets.commitment frame = some child ∧
      spawned.virtualMemory.memory.allocator.status frame = .free)

theorem GrantedFrom.refl (spawned : CompositeState) (parent slot child generation : Nat)
    (found : spawned.spawn.children parent slot = some ⟨child, generation, 0⟩) :
    GrantedFrom spawned spawned parent slot child generation := by
  refine ⟨rfl, ⟨0, ?_⟩, fun _ => Or.inl rfl⟩
  have same : (fun candidate candidateSlot =>
      if candidate = parent ∧ candidateSlot = slot then some (⟨child, generation, 0⟩ : ChildEntry)
      else spawned.spawn.children candidate candidateSlot) = spawned.spawn.children := by
    funext candidate candidateSlot
    split
    · next h => obtain ⟨rfl, rfl⟩ := h; exact found.symm
    · rfl
  rw [same]

/-- A frame grant for the child's control word keeps the shape. -/
theorem GrantedFrom.grant {spawned state : CompositeState} {parent slot child generation : Nat}
    (granted : GrantedFrom spawned state parent slot child generation) (control : UInt64)
    (frames : Nat)
    (decoded : CapabilityHandle.decode control = .ok (controlHandle slot generation))
    (parentEq : spawnParent spawned = parent) (ne : child ≠ parent) :
    GrantedFrom spawned (childGate state (.grantFrames control frames)).state parent slot child
      generation := by
  have exec : state.execution = spawned.execution := by
    have := congrArg CompositeState.execution granted.rest; exact this
  have vm : state.virtualMemory = spawned.virtualMemory := by
    have := congrArg CompositeState.virtualMemory granted.rest; exact this
  have parentState : spawnParent state = parent := by
    rw [← parentEq]; simp [spawnParent, exec]
  cases mode : state.execution.mode with
  | handling _ => simp only [childGate, mode]; exact granted
  | halted _ => simp only [childGate, mode]; exact granted
  | running =>
  simp only [childGate, mode, ChildOperation.apply]
  rcases grantFrames_shape state control frames with ⟨same, _⟩ | ⟨named, moved, result⟩
  · rw [same]; exact granted
  obtain ⟨slot', entry', resolved, childEq, _, _, _, stateEq⟩ :=
    grantFrames_granted state control frames named moved result
  obtain ⟨_, decoded', found⟩ := resolveControl_ok resolved
  rw [decoded] at decoded'
  simp only [Except.ok.injEq, controlHandle, CapabilityHandle.Handle.mk.injEq] at decoded'
  obtain ⟨rfl, generationEq⟩ := decoded'
  obtain ⟨charge, spawnEq⟩ := granted.entry
  rw [parentState, spawnEq] at found
  simp only [and_self, ↓reduceIte, Option.some.injEq] at found
  subst found
  simp only at childEq generationEq
  subst childEq
  rw [stateEq]
  refine ⟨granted.rest, ⟨charge + moved, ?_⟩, fun frame => ?_⟩
  · simp only [setChildEntry, parentState, spawnEq, chargeEntry]
    congr 1
    funext candidate candidateSlot
    split <;> rfl
  · simp only [moveFrames]
    split
    · next member =>
      have inGrant : frame ∈ grantedFrames state (spawnParent state) frames := by
        simpa using member
      obtain ⟨_, committed, free⟩ :=
        mem_availableFrames (List.mem_of_mem_take inGrant)
      rw [parentState] at committed
      rcases granted.frames frame with same | ⟨_, toChild, _⟩
      · rw [vm] at free
        exact Or.inr ⟨same ▸ committed, rfl, free⟩
      · rw [toChild] at committed
        simp only [Option.some.injEq] at committed
        exact absurd committed ne
    · exact granted.frames frame

theorem GrantedFrom.same {spawned state : CompositeState} {parent slot child generation : Nat}
    (granted : GrantedFrom spawned state parent slot child generation) :
    state.execution = spawned.execution ∧ state.capabilities = spawned.capabilities ∧
      state.lifecycle = spawned.lifecycle ∧ state.virtualMemory = spawned.virtualMemory ∧
      state.scrub = spawned.scrub := by
  have e := congrArg CompositeState.execution granted.rest
  have c := congrArg CompositeState.capabilities granted.rest
  have l := congrArg CompositeState.lifecycle granted.rest
  have v := congrArg CompositeState.virtualMemory granted.rest
  have s := congrArg CompositeState.scrub granted.rest
  exact ⟨e, c, l, v, s⟩

theorem GrantedFrom.grantAll {spawned state : CompositeState} {parent slot child generation : Nat}
    (granted : GrantedFrom spawned state parent slot child generation) (control : UInt64)
    (grants : List Nat)
    (decoded : CapabilityHandle.decode control = .ok (controlHandle slot generation))
    (parentEq : spawnParent spawned = parent) (ne : child ≠ parent) :
    GrantedFrom spawned (grantAll state control grants) parent slot child generation := by
  induction grants generalizing state with
  | nil => exact granted
  | cons frames rest ih => exact ih (granted.grant control frames decoded parentEq ne)

theorem grantAll_preserves (state : CompositeState) (control : UInt64) (grants : List Nat)
    (holds : ResourceRuntimeWellFormed state) (accounting : ChildAccountingWellFormed state) :
    ResourceRuntimeWellFormed (grantAll state control grants) ∧
      ChildAccountingWellFormed (grantAll state control grants) := by
  induction grants generalizing state with
  | nil => exact ⟨holds, accounting⟩
  | cons frames rest ih =>
      obtain ⟨h1, h2, _⟩ := childGate_preserves state (.grantFrames control frames) holds accounting
      exact ih _ h1 h2

/-! ## The restored state -/

/-- **What a rollback restores.**  `post` agrees with the pre-spawn state
`pre` on every authority and resource projection: which subjects are live,
every capability slot of every subject, the runnable set and the current
subject, every lifecycle ownership record, every frame commitment, the frame
allocator, the object bindings and the frame contents, and every parent's
child table and spawn authority.  The child's own spawn records are cleared.
What differs is history that is never reused: the child's identity stays in
the issued history, and the control-handle generation counter has advanced
past the child's control word. -/
structure SpawnRestored (pre post : CompositeState) (child : Nat) : Prop where
  subjects : post.capabilities.subjects = pre.capabilities.subjects
  slots : post.capabilities.slots = pre.capabilities.slots
  runnable : post.lifecycle.runnable = pre.lifecycle.runnable
  current : post.lifecycle.current = pre.lifecycle.current
  addressOwner : post.lifecycle.addressOwner = pre.lifecycle.addressOwner
  ownedMemory : post.lifecycle.ownedMemory = pre.lifecycle.ownedMemory
  endpointOwner : post.lifecycle.endpointOwner = pre.lifecycle.endpointOwner
  frameBudgets : post.frameBudgets = pre.frameBudgets
  allocator : post.virtualMemory.memory.allocator = pre.virtualMemory.memory.allocator
  binding : post.virtualMemory.memory.binding = pre.virtualMemory.memory.binding
  scrub : post.scrub = pre.scrub
  children : post.spawn.children = pre.spawn.children
  authority : post.spawn.authority = pre.spawn.authority
  parent : post.spawn.parent = fun candidate =>
    if candidate = child then none else pre.spawn.parent candidate
  addressSpace : post.spawn.addressSpace = fun candidate =>
    if candidate = child then none else pre.spawn.addressSpace candidate
  issued : post.lifecycle.issuedSubjects =
    SubjectLifecycle.setBool pre.lifecycle.issuedSubjects child true
  generation : post.spawn.nextChildGeneration = pre.spawn.nextChildGeneration + 1

/-- **Rollback restores the pre-spawn state** (the composite half of the
loader's rollback).  Spawn a child through the gate, give it frames any
number of times with its control word, and terminate it with the same word:
the termination is accepted, and the result is `SpawnRestored` against the
state before the spawn. -/
theorem spawn_rollback_restores (pre : CompositeState) (request : SpawnRequest)
    (grants : List Nat) (child addressSpace : Nat) (control : UInt64)
    (running : pre.execution.mode = .running) (holds : ResourceRuntimeWellFormed pre)
    (accounting : ChildAccountingWellFormed pre)
    (spawned : (childGate pre (.spawn request)).result =
      .completed (.spawned child addressSpace control)) :
    (∃ returned, (childGate (grantAll (childGate pre (.spawn request)).state control grants)
        (.terminateChild control)).result = .completed (.terminated child returned)) ∧
      SpawnRestored pre (childGate (grantAll (childGate pre (.spawn request)).state control grants)
        (.terminateChild control)).state child := by
  have charged : (spawnCharged pre request).result = .spawned child addressSpace control := by
    simpa [childGate, running, ChildOperation.apply] using spawned
  obtain ⟨slot, authorized, _, free, available, spawnedRaw, controlEq, firstEq⟩ :=
    spawnCharged_spawned pre request child addressSpace control charged
  have firstState : (childGate pre (.spawn request)).state =
      installChild (spawn pre request).state (spawnParent pre) slot child := by
    simp only [childGate, running, ChildOperation.apply]; exact firstEq
  obtain ⟨inRange, freeSlot⟩ := freeChildSlot_some free
  obtain ⟨childrenEq, nextEq, authorityEq⟩ := spawn_childTable pre request child addressSpace
    spawnedRaw
  obtain ⟨runnableEq, currentEq, _, _, _, _, _, _, _, _, _, _, _, budgetsEq, scrubEq, allocatorEq,
    bindingEq, issuedEq⟩ := spawn_keeps pre request child addressSpace spawnedRaw
  obtain ⟨ownedEq, endpointEq, ownerEq, subjectsEq, spaceDead, spaceUnissued⟩ :=
    spawn_lifecycle_records pre request child addressSpace holds.1.left spawnedRaw
  obtain ⟨modeEq, parentSpawnEq⟩ := spawn_execution pre request child addressSpace spawnedRaw
  obtain ⟨parentNe, deadChild⟩ := spawn_parent_ne_child pre request child addressSpace
    holds.1.left spawnedRaw
  obtain ⟨_, unissued, _, _, _, _⟩ := spawn_fresh_identity pre request child addressSpace holds
    spawnedRaw
  obtain ⟨parentLive, _⟩ := spawnAuthorize_live authorized
  have positive : 0 < pre.spawn.nextChildGeneration ∧ pre.spawn.nextChildGeneration < CapabilityHandle.generationReserved := by
    simpa [controlGenerationAvailable] using available
  have decoded : CapabilityHandle.decode control = .ok (controlHandle slot pre.spawn.nextChildGeneration) := by
    rw [controlEq]; exact decode_controlWord slot pre.spawn.nextChildGeneration inRange positive.1 positive.2
  -- the shape after the grants
  have firstFound : (childGate pre (.spawn request)).state.spawn.children (spawnParent pre) slot =
      some ⟨child, pre.spawn.nextChildGeneration, 0⟩ := by
    rw [firstState]; simp [installChild, nextEq]
  have firstParent : spawnParent (childGate pre (.spawn request)).state = spawnParent pre := by
    rw [firstState]; simpa [installChild, spawnParent] using parentSpawnEq
  have shape := (GrantedFrom.refl _ (spawnParent pre) slot child pre.spawn.nextChildGeneration firstFound).grantAll control
    grants decoded firstParent (Ne.symm parentNe)
  obtain ⟨firstHolds, firstAccounting, _⟩ :=
    childGate_preserves pre (.spawn request) holds accounting
  have grantedHolds := (grantAll_preserves _ control grants firstHolds firstAccounting).1
  generalize grantAll (childGate pre (.spawn request)).state control grants = granted
    at shape grantedHolds ⊢
  obtain ⟨grantedExec, grantedCaps, grantedLifecycle, grantedVm, grantedScrub⟩ := shape.same
  rw [firstState] at grantedExec grantedCaps grantedLifecycle grantedVm grantedScrub
  simp only [installChild] at grantedExec grantedCaps grantedLifecycle grantedVm grantedScrub
  obtain ⟨charge, grantedSpawn⟩ := shape.entry
  have grantedRunning : granted.execution.mode = .running := by
    rw [grantedExec, modeEq, running]
  have grantedParent : spawnParent granted = spawnParent pre := by
    simp only [spawnParent] at parentSpawnEq ⊢; rw [grantedExec]; exact parentSpawnEq
  -- invariants along the way
  have spawnedHolds := spawn_preserves_resourceRuntimeWellFormed pre request running holds
  have spawnedCoherent := spawnedHolds.1.left.1
  -- the termination resolves the child
  have parentLiveGranted : granted.capabilities.subjects (spawnParent pre) = true := by
    rw [grantedCaps, subjectsEq]; simp [SubjectLifecycle.setBool, parentNe, parentLive]
  have resolved : resolveControl granted control = .ok (slot, ⟨child, pre.spawn.nextChildGeneration, charge⟩) := by
    simp [resolveControl, grantedParent, parentLiveGranted, decoded, grantedSpawn, controlHandle]
  have terminateEq : (childGate granted (.terminateChild control)) =
      { state := releaseChild (terminatedChild granted child) (spawnParent pre) slot child
        result := .completed (.terminated child (granted.budgetLimit child)) } := by
    simp [childGate, grantedRunning, ChildOperation.apply, terminateChild, resolved,
      grantedParent]
  refine ⟨⟨_, by rw [terminateEq]⟩, ?_⟩
  rw [terminateEq]
  -- the composite termination of the child
  have runtimeG := grantedHolds.1.left
  have spawnedCaps : (spawn pre request).state.capabilities =
      (spawn pre request).state.lifecycle.capabilities := spawnedCoherent.2.2.2.1
  have preCaps : pre.capabilities = pre.lifecycle.capabilities := holds.1.left.1.2.2.2.1
  have lifecycleWf := holds.1.left.2.2.1
  have deadLife : pre.lifecycle.capabilities.subjects child = false := by
    rw [← preCaps]; exact deadChild
  have accepted : (SubjectLifecycle.terminate granted.lifecycle child).result = .accepted := by
    have liveL : granted.lifecycle.capabilities.subjects child = true := by
      rw [grantedLifecycle, ← spawnedCaps, subjectsEq]; simp [SubjectLifecycle.setBool]
    have issuedL : granted.lifecycle.issuedSubjects child = true := by
      rw [grantedLifecycle, issuedEq]; simp [SubjectLifecycle.setBool]
    simp [SubjectLifecycle.terminate, liveL, issuedL]
  obtain ⟨capsT, runnableT, currentT, ownerT, ownedT, endpointT⟩ :=
    terminatedChild_registry granted child grantedRunning runtimeG accepted
  obtain ⟨_, agreesT, spawnT⟩ := terminatedChild_facts granted child grantedHolds
  obtain ⟨_, budgetsT, scrubT, issuedT, _, _, allocatorT, bindingT⟩ := agreesT
  have budgetAgreement := ((resourceWellFormed_iff pre).1 holds.2).2.2.1
  have preNotChild : ∀ frame, pre.frameBudgets.commitment frame ≠ some child := by
    intro frame committed
    have := (budgetAgreement frame child committed).2.2
    rw [unissued] at this; cases this
  have framesShape : ∀ frame, granted.frameBudgets.commitment frame =
      pre.frameBudgets.commitment frame ∨
      (pre.frameBudgets.commitment frame = some (spawnParent pre) ∧
        granted.frameBudgets.commitment frame = some child ∧
        pre.virtualMemory.memory.allocator.status frame = .free) := by
    intro frame
    have := shape.frames frame
    rw [firstState] at this
    simp only [installChild, budgetsEq, allocatorEq] at this
    exact this
  have notReclaimable : ∀ frame,
      reclaimable (terminatedChild granted child) child frame = false := by
    intro frame
    simp only [reclaimable, budgetsT, allocatorT, grantedVm, allocatorEq]
    rcases framesShape frame with same | ⟨_, _, free⟩
    · have : (granted.frameBudgets.commitment frame == some child) = false := by
        rw [same]; simpa using preNotChild frame
      simp [this]
    · simp [free]
  have spawnSpawn : granted.spawn = { (spawn pre request).state.spawn with
      children := fun candidate candidateSlot =>
        if candidate = spawnParent pre ∧ candidateSlot = slot then
          some ⟨child, pre.spawn.nextChildGeneration, charge⟩
        else if candidate = spawnParent pre ∧ candidateSlot = slot then
          some ⟨child, (spawn pre request).state.spawn.nextChildGeneration, 0⟩
        else (spawn pre request).state.spawn.children candidate candidateSlot
      nextChildGeneration := (spawn pre request).state.spawn.nextChildGeneration + 1 } := by
    rw [grantedSpawn, firstState]
    rfl
  have ownerFree : pre.lifecycle.addressOwner addressSpace = none :=
    addressOwner_none_of_unissued holds.1.left spaceUnissued
  refine ⟨?subjects, ?slots, ?runnable, ?current, ?addressOwner, ?ownedMemory, ?endpointOwner,
    ?frameBudgets, ?allocator, ?binding, ?scrub, ?children, ?authority, ?parent, ?addressSpace,
    ?issued, ?generation⟩
  case subjects =>
    show (terminatedChild granted child).capabilities.subjects = _
    rw [capsT]
    simp only [ResumablePreemption.retireOwnedAddressSpaces,
      SubjectLifecycle.terminatedCapabilities, grantedLifecycle, ← spawnedCaps, subjectsEq]
    funext candidate
    by_cases same : candidate = child
    · subst same; simp [SubjectLifecycle.setBool, deadChild]
    · simp [SubjectLifecycle.setBool, same]
  case slots =>
    show (terminatedChild granted child).capabilities.slots = _
    rw [capsT]
    funext holder candidateSlot
    simp only [ResumablePreemption.retireOwnedAddressSpaces,
      SubjectLifecycle.terminatedCapabilities, grantedLifecycle, ← spawnedCaps, ownedEq,
      endpointEq, ownerEq]
    by_cases holderChild : holder = child
    · subst holderChild
      have empty : pre.capabilities.slots holder candidateSlot = none := by
        cases held : pre.capabilities.slots holder candidateSlot with
        | none => rfl
        | some capability =>
            have := (holds.1.left.2.2.2.1.1 _ _ _ held).1
            rw [deadChild] at this; cases this
      rw [empty]
      cases (spawn pre request).state.capabilities.slots holder candidateSlot <;> simp
    · rw [spawn_other_slots_unchanged pre request child addressSpace holds.1.left spawnedRaw
        holder holderChild]
      cases held : pre.capabilities.slots holder candidateSlot with
      | none => simp
      | some capability =>
          have objectLive := (holds.1.left.2.2.2.1.1 _ _ _ held).2.1
          have notSpace : capability.object ≠ addressSpace := by
            intro same; rw [same, spaceDead] at objectLive; cases objectLive
          have notOwned : (pre.lifecycle.ownedMemory capability.object).any
              (fun owner => owner.1 = child) = false := by
            cases owned : pre.lifecycle.ownedMemory capability.object with
            | none => rfl
            | some owner =>
                obtain ⟨subject, frame⟩ := owner
                have := (lifecycleWf.2.1 _ _ _ owned).1
                have ne : subject ≠ child := by
                  intro same; subst same; rw [deadLife] at this; cases this
                simp [ne]
          have notEndpoint : pre.lifecycle.endpointOwner capability.object ≠ some child := by
            intro owned
            have := lifecycleWf.2.2.2.1 _ _ owned
            rw [deadLife] at this; cases this
          have notAddress : VirtualMapping.setOwner pre.lifecycle.addressOwner addressSpace
              (some child) capability.object ≠ some child := by
            simp only [VirtualMapping.setOwner, notSpace, ↓reduceIte]
            intro owned
            have := lifecycleWf.2.2.1 _ _ owned
            rw [deadLife] at this; cases this
          simp [holderChild, notOwned, notEndpoint, notAddress]
  case runnable =>
    show (terminatedChild granted child).lifecycle.runnable = _
    rw [runnableT, grantedLifecycle, runnableEq]
    funext candidate
    by_cases same : candidate = child
    · subst same
      cases runs : pre.lifecycle.runnable candidate with
      | false => simp [SubjectLifecycle.setBool, runs]
      | true =>
          have := lifecycleWf.2.2.2.2.1 _ runs
          rw [deadLife] at this; cases this
    · simp [SubjectLifecycle.setBool, same]
  case current =>
    show (terminatedChild granted child).lifecycle.current = _
    rw [currentT, grantedLifecycle, currentEq]
    split
    · next isChild =>
      have := lifecycleWf.2.2.2.2.2 _ isChild
      rw [deadLife] at this; cases this
    · rfl
  case addressOwner =>
    show (terminatedChild granted child).lifecycle.addressOwner = _
    rw [ownerT, grantedLifecycle, ownerEq]
    funext candidate
    by_cases same : candidate = addressSpace
    · subst same; simp [VirtualMapping.setOwner, ownerFree]
    · simp only [VirtualMapping.setOwner, same, ↓reduceIte]
      split
      · next owned =>
        have := lifecycleWf.2.2.1 _ _ owned
        rw [deadLife] at this; cases this
      · rfl
  case ownedMemory =>
    show (terminatedChild granted child).lifecycle.ownedMemory = _
    rw [ownedT, grantedLifecycle, ownedEq]
    funext object
    cases owned : pre.lifecycle.ownedMemory object with
    | none => rfl
    | some owner =>
        obtain ⟨subject, frame⟩ := owner
        have := (lifecycleWf.2.1 _ _ _ owned).1
        have ne : subject ≠ child := by
          intro same; subst same; rw [deadLife] at this; cases this
        simp [ne]
  case endpointOwner =>
    show (terminatedChild granted child).lifecycle.endpointOwner = _
    rw [endpointT, grantedLifecycle, endpointEq]
    funext object
    split
    · next owned =>
      have := lifecycleWf.2.2.2.1 _ _ owned
      rw [deadLife] at this; cases this
    · rfl
  case frameBudgets =>
    show returnFrames (terminatedChild granted child).frameBudgets child (spawnParent pre) = _
    rw [budgetsT]
    have eta : ∀ budgets : FrameBudgets, budgets = ⟨budgets.commitment⟩ := fun _ => rfl
    rw [eta pre.frameBudgets]
    simp only [returnFrames, FrameBudgets.mk.injEq]
    funext frame
    rcases framesShape frame with same | ⟨wasParent, toChild, _⟩
    · rw [same]; simp [preNotChild frame]
    · rw [toChild, wasParent]; simp
  case allocator =>
    show (reclaimedVirtualMemory (terminatedChild granted child) child).memory.allocator = _
    simp only [reclaimedVirtualMemory, notReclaimable, Bool.false_eq_true, ↓reduceIte]
    rw [allocatorT, grantedVm, allocatorEq]
  case binding =>
    show (reclaimedVirtualMemory (terminatedChild granted child) child).memory.binding = _
    simp only [reclaimedVirtualMemory, notReclaimable, Bool.false_eq_true, ↓reduceIte]
    rw [bindingT, grantedVm, bindingEq]
    funext object
    cases pre.virtualMemory.memory.binding object <;> rfl
  case scrub =>
    show { (terminatedChild granted child).scrub with
      bytes := fun frame offset =>
        if reclaimable (terminatedChild granted child) child frame = true ∧
            offset < FrameScrub.frameBytes then FrameScrub.initialByte
        else (terminatedChild granted child).scrub.bytes frame offset } = _
    simp only [notReclaimable, Bool.false_eq_true, false_and, ↓reduceIte]
    rw [scrubT, grantedScrub, scrubEq]
  case children =>
    show (fun candidate candidateSlot =>
      if candidate = spawnParent pre ∧ candidateSlot = slot then none
      else (terminatedChild granted child).spawn.children candidate candidateSlot) = _
    rw [spawnT, spawnSpawn]
    funext candidate candidateSlot
    split
    · next here => obtain ⟨rfl, rfl⟩ := here; exact freeSlot.symm
    · next notHere => simp [notHere, childrenEq]
  case authority =>
    show (terminatedChild granted child).spawn.authority = _
    rw [spawnT, spawnSpawn]
    exact authorityEq
  case parent =>
    show (fun candidate => if candidate = child then none
      else (terminatedChild granted child).spawn.parent candidate) = _
    rw [spawnT, spawnSpawn]
    funext candidate
    split
    · rfl
    · next ne =>
      simp only
      rw [spawn_parent_record pre request child addressSpace spawnedRaw]
      simp [ne]
  case addressSpace =>
    show (fun candidate => if candidate = child then none
      else (terminatedChild granted child).spawn.addressSpace candidate) = _
    rw [spawnT, spawnSpawn]
    funext candidate
    split
    · rfl
    · next ne =>
      simp only
      rw [spawn_addressSpace_record pre request child addressSpace spawnedRaw]
      simp [ne]
  case issued =>
    show (terminatedChild granted child).lifecycle.issuedSubjects = _
    rw [issuedT, grantedLifecycle, issuedEq]
  case generation =>
    show (terminatedChild granted child).spawn.nextChildGeneration = _
    rw [spawnT, spawnSpawn]
    simp [nextEq]

/-- **The child between spawn and rollback.**  After a spawn through the gate
and any frame grants with its control word, the latch is still running, the
capability registry is exactly the one spawn left, the invariants hold, and
the control word still names the spawned child in the parent's table. -/
theorem spawn_grants_child (pre : CompositeState) (request : SpawnRequest)
    (grants : List Nat) (child addressSpace : Nat) (control : UInt64)
    (running : pre.execution.mode = .running) (holds : ResourceRuntimeWellFormed pre)
    (accounting : ChildAccountingWellFormed pre)
    (spawned : (childGate pre (.spawn request)).result =
      .completed (.spawned child addressSpace control)) :
    (spawn pre request).result = .spawned child addressSpace ∧
      (grantAll (childGate pre (.spawn request)).state control grants).execution.mode =
        .running ∧
      (grantAll (childGate pre (.spawn request)).state control grants).capabilities =
        (spawn pre request).state.capabilities ∧
      ResourceRuntimeWellFormed (grantAll (childGate pre (.spawn request)).state control grants) ∧
      ∃ slot entry, resolveControl (grantAll (childGate pre (.spawn request)).state control grants)
        control = .ok (slot, entry) ∧ entry.child = child := by
  have charged : (spawnCharged pre request).result = .spawned child addressSpace control := by
    simpa [childGate, running, ChildOperation.apply] using spawned
  obtain ⟨slot, authorized, _, free, available, spawnedRaw, controlEq, firstEq⟩ :=
    spawnCharged_spawned pre request child addressSpace control charged
  have firstState : (childGate pre (.spawn request)).state =
      installChild (spawn pre request).state (spawnParent pre) slot child := by
    simp only [childGate, running, ChildOperation.apply]; exact firstEq
  obtain ⟨inRange, _⟩ := freeChildSlot_some free
  obtain ⟨_, nextEq, _⟩ := spawn_childTable pre request child addressSpace spawnedRaw
  obtain ⟨_, _, _, subjectsEq, _, _⟩ :=
    spawn_lifecycle_records pre request child addressSpace holds.1.left spawnedRaw
  obtain ⟨modeEq, parentSpawnEq⟩ := spawn_execution pre request child addressSpace spawnedRaw
  obtain ⟨parentNe, _⟩ := spawn_parent_ne_child pre request child addressSpace
    holds.1.left spawnedRaw
  obtain ⟨parentLive, _⟩ := spawnAuthorize_live authorized
  have positive : 0 < pre.spawn.nextChildGeneration ∧
      pre.spawn.nextChildGeneration < CapabilityHandle.generationReserved := by
    simpa [controlGenerationAvailable] using available
  have decoded : CapabilityHandle.decode control =
      .ok (controlHandle slot pre.spawn.nextChildGeneration) := by
    rw [controlEq]
    exact decode_controlWord slot pre.spawn.nextChildGeneration inRange positive.1 positive.2
  have firstFound : (childGate pre (.spawn request)).state.spawn.children (spawnParent pre) slot =
      some ⟨child, pre.spawn.nextChildGeneration, 0⟩ := by
    rw [firstState]; simp [installChild, nextEq]
  have firstParent : spawnParent (childGate pre (.spawn request)).state = spawnParent pre := by
    rw [firstState]; simpa [installChild, spawnParent] using parentSpawnEq
  have shape := (GrantedFrom.refl _ (spawnParent pre) slot child pre.spawn.nextChildGeneration
    firstFound).grantAll control grants decoded firstParent (Ne.symm parentNe)
  obtain ⟨firstHolds, firstAccounting, _⟩ :=
    childGate_preserves pre (.spawn request) holds accounting
  have grantedHolds := (grantAll_preserves _ control grants firstHolds firstAccounting).1
  generalize grantAll (childGate pre (.spawn request)).state control grants = granted
    at shape grantedHolds ⊢
  obtain ⟨grantedExec, grantedCaps, _, _, _⟩ := shape.same
  rw [firstState] at grantedExec grantedCaps
  simp only [installChild] at grantedExec grantedCaps
  obtain ⟨charge, grantedSpawn⟩ := shape.entry
  have grantedParent : spawnParent granted = spawnParent pre := by
    simp only [spawnParent] at parentSpawnEq ⊢; rw [grantedExec]; exact parentSpawnEq
  have parentLiveGranted : granted.capabilities.subjects (spawnParent pre) = true := by
    rw [grantedCaps, subjectsEq]; simp [SubjectLifecycle.setBool, parentNe, parentLive]
  refine ⟨spawnedRaw, by rw [grantedExec, modeEq, running], grantedCaps, grantedHolds, slot,
    ⟨child, pre.spawn.nextChildGeneration, charge⟩, ?_, rfl⟩
  simp [resolveControl, grantedParent, parentLiveGranted, decoded, grantedSpawn, controlHandle]

end LeanOS.FailStop
