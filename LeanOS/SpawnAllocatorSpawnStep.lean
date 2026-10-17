import LeanOS.SpawnAllocatorFamily

/-!
# Spawn on a family state is the allocator's spawn (#575)

On every composite state satisfying `Family`, the typed result of
`FailStop.spawn` is decided by the allocator record of the state: subject,
object and capability exhaustion, then the parent's endpoint handle and the
requested rights, exactly as `SpawnAllocator.spawnStep` decides them
(`spawn_result_family`).  The stages that the composite runs but the allocator
does not model (the child's slot table, a free address-space identifier, the
address-space creation and the endpoint copy) always succeed on a family
state.  `spawnCharged` returns the allocator's status and control word
(`spawnCharged_family`); an accepted charged spawn's post-state has the
allocator's successor as its abstraction (`spawnCharged_abstraction`) and
satisfies `Family` again (`spawnCharged_family_preserved`).
-/
namespace LeanOS.SpawnAllocator

open LeanOS
open LeanOS.FailStop

set_option linter.unusedSimpArgs false

/-! ## The created child -/

theorem family_runtime (state : CompositeState) (family : Family state) :
    RuntimeWellFormed state := family.resources.1.left

theorem family_lifecycleCapabilities (state : CompositeState) (family : Family state) :
    state.lifecycle.capabilities = state.capabilities :=
  (family_runtime state family).1.2.2.2.1.symm

theorem family_spawnParent (state : CompositeState) (family : Family state) :
    spawnParent state = parent := family.current

theorem identityExhausted_issuer {domain : LifetimeIssuer.Domain}
    (issuer : LifetimeIssuer.Issuer domain) :
    LifetimeIssuer.exhausted issuer = identityExhausted issuer.next := rfl

theorem family_issueSubject (state : CompositeState) (family : Family state)
    (live : identityExhausted state.issuers.subject.next = false) :
    (issueSubject state).result = .issued state.issuers.subject.next := by
  have agreement := ((resourceWellFormed_iff state).1 family.resources.2).2.1
  exact issueSubject_total state agreement (family_runtime state family).2.2.1 live

/-- A subject that is not live holds no capability. -/
theorem family_dead_slots (state : CompositeState) (family : Family state) (subject : Nat)
    (dead : state.capabilities.subjects subject = false) (slot : Nat) :
    state.capabilities.slots subject slot = none := by
  cases held : state.capabilities.slots subject slot with
  | none => rfl
  | some capability =>
      have := ((family_runtime state family).2.2.2.1.1 subject slot capability held).1
      rw [dead] at this; contradiction

/-- The next subject identity is not live. -/
theorem family_next_dead (state : CompositeState) (family : Family state)
    (live : identityExhausted state.issuers.subject.next = false) :
    state.capabilities.subjects state.issuers.subject.next = false := by
  have fresh := (issueSubject_fresh state _ (family_issueSubject state family live)).2.1
  rw [family_lifecycleCapabilities state family] at fresh
  exact fresh

/-- The next object identity is fresh under every kind. -/
theorem family_next_object (state : CompositeState) (family : Family state) :
    state.virtualMemory.issuedAddressSpace state.issuers.object.next = false ∧
      state.virtualMemory.memory.issued state.issuers.object.next = false ∧
      state.capabilities.objects state.issuers.object.next = false ∧
      state.lifecycle.ownedMemory state.issuers.object.next = none ∧
      state.lifecycle.endpointOwner state.issuers.object.next = none := by
  have agreement := ((resourceWellFormed_iff state).1 family.resources.2).2.1
  obtain ⟨dead, owned, endpoint⟩ := family.fresh state.issuers.object.next (Nat.le_refl _)
  have unissued : BoundedLifecycle.issuedObject state.lifecycleRuntime
      state.issuers.object.next = false := by
    cases h : BoundedLifecycle.issuedObject state.lifecycleRuntime state.issuers.object.next with
    | false => rfl
    | true => exact absurd (agreement.2 _ h).2 (Nat.lt_irrefl _)
  simp only [BoundedLifecycle.issuedObject, CompositeState.lifecycleRuntime, Bool.or_eq_false_iff]
    at unissued
  exact ⟨unissued.2, unissued.1, dead, owned, endpoint⟩

/-! ## The created and spaced states -/

theorem created_capabilities (state : CompositeState) (family : Family state)
    (live : identityExhausted state.issuers.subject.next = false) :
    (issueSubject state).state.capabilities =
        { state.capabilities with
          subjects := SubjectLifecycle.setBool state.capabilities.subjects
            state.issuers.subject.next true } ∧
      (issueSubject state).state.virtualMemory.memory.capabilities =
        (issueSubject state).state.capabilities := by
  obtain ⟨caps, vm⟩ := issueSubject_capabilities state _ (family_issueSubject state family live)
  rw [family_lifecycleCapabilities state family] at caps
  exact ⟨caps, vm⟩

theorem created_records (state : CompositeState) (family : Family state)
    (live : identityExhausted state.issuers.subject.next = false) :
    (issueSubject state).state.lifecycle.ownedMemory = state.lifecycle.ownedMemory ∧
      (issueSubject state).state.lifecycle.endpointOwner = state.lifecycle.endpointOwner ∧
      (issueSubject state).state.virtualMemory.issuedAddressSpace =
        state.virtualMemory.issuedAddressSpace ∧
      (issueSubject state).state.virtualMemory.memory.issued =
        state.virtualMemory.memory.issued := by
  obtain ⟨_, _, created, eq⟩ := issueSubject_issued state _ (family_issueSubject state family live)
  rw [eq]
  simp [applyOperation, created, installCreatedSubject,
    SubjectLifecycle.create_accepted_state _ _ created]

/-- What spawn returns on a family state, read from the allocator record. -/
def spawnResultOf (state : CompositeState) (request : SpawnRequest) : SpawnResult :=
  if identityExhausted state.issuers.subject.next then .rejected .identityExhausted
  else if identityExhausted state.issuers.object.next then
    .rejected .addressSpaceIdentityExhausted
  else if capabilityExhausted state.capabilities.nextIdentity then
    .rejected (.addressSpaceRejected .generationExhausted)
  else match (abstraction state).resolveEndpoint request.endpointWord with
    | some denial => .rejected (.endpointHandle denial)
    | none =>
        if Capability.rightsValid .endpoint request.rights = false then .rejected .invalidRights
        else .spawned state.issuers.subject.next state.issuers.object.next

theorem endpointRights_subset (rights : Capability.Rights)
    (valid : Capability.rightsValid .endpoint rights = true) :
    Capability.rightsSubset rights endpointRights = true := by
  obtain ⟨read, write, send, receive, grant, revoke⟩ := rights
  cases read <;> cases write <;> cases send <;> cases receive <;> cases grant <;> cases revoke <;>
    simp_all [Capability.rightsValid, Capability.rightsSubset, endpointRights]

/-- The parent's slots in the state after the address-space stage. -/
theorem spaced_parentSlots (state : CompositeState) (family : Family state)
    (live : identityExhausted state.issuers.subject.next = false) (object : Nat)
    (slots : ParentSlots state.capabilities (abstraction state) object) :
    ParentSlots (spawnSpaced (issueSubject state).state state.issuers.subject.next
      state.issuers.object.next).capabilities (abstraction state) object := by
  obtain ⟨createdCaps, createdVm⟩ := created_capabilities state family live
  have spacedCaps : (spawnSpaced (issueSubject state).state state.issuers.subject.next
      state.issuers.object.next).capabilities =
      addressSpaceCapabilities (issueSubject state).state.capabilities state.issuers.object.next
        state.issuers.subject.next childAddressSpaceSlot := by
    simp [spawnSpaced, installCreatedAddressSpace, createdVirtualMemory_capabilities, createdVm]
  have parentNe : parent ≠ state.issuers.subject.next := by
    intro same
    have dead := family_next_dead state family live
    rw [← same, family.parentLive] at dead
    contradiction
  have objectNe : object ≠ state.issuers.object.next := by
    intro same
    have := (family_next_object state family).2.2.1
    rw [← same, slots.objectLive] at this
    contradiction
  have parentSlot : ∀ slot, (addressSpaceCapabilities (issueSubject state).state.capabilities
      state.issuers.object.next state.issuers.subject.next childAddressSpaceSlot).slots parent slot =
      state.capabilities.slots parent slot := by
    intro slot
    rw [addressSpaceCapabilities_slots, createdCaps]
    simp [parentNe]
  obtain ⟨liveParent, capacity, endpoint, objectLive, objectKind, space, memory⟩ := slots
  rw [spacedCaps]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [addressSpaceCapabilities_subjects, createdCaps]
    simp [SubjectLifecycle.setBool, parentNe, liveParent]
  · rw [addressSpaceCapabilities_slotCapacity, createdCaps]; exact capacity
  · rw [parentSlot]; exact endpoint
  · rw [addressSpaceCapabilities_objects_of_ne _ _ _ _ objectNe, createdCaps]; exact objectLive
  · rw [addressSpaceCapabilities_kinds_of_ne _ _ _ _ objectNe, createdCaps]; exact objectKind
  · rw [parentSlot]; exact space
  · intro slot which
    rw [parentSlot]; exact memory slot which

/-- The endpoint copy into the new child's slot 0 is accepted. -/
theorem spaced_copy_accepted (state : CompositeState) (family : Family state)
    (live : identityExhausted state.issuers.subject.next = false) (object : Nat)
    (slots : ParentSlots state.capabilities (abstraction state) object)
    (rights : Capability.Rights) (valid : Capability.rightsValid .endpoint rights = true) :
    (Capability.copy (spawnSpaced (issueSubject state).state state.issuers.subject.next
      state.issuers.object.next).capabilities parent 0 state.issuers.subject.next
      childEndpointSlot rights).result = .accepted := by
  obtain ⟨createdCaps, createdVm⟩ := created_capabilities state family live
  have spacedCaps : (spawnSpaced (issueSubject state).state state.issuers.subject.next
      state.issuers.object.next).capabilities =
      addressSpaceCapabilities (issueSubject state).state.capabilities state.issuers.object.next
        state.issuers.subject.next childAddressSpaceSlot := by
    simp [spawnSpaced, installCreatedAddressSpace, createdVirtualMemory_capabilities, createdVm]
  have spacedSlots := spaced_parentSlots state family live object slots
  have stateChildEmpty := family_dead_slots state family _ (family_next_dead state family live)
  have endpointSlot := spacedSlots.endpoint
  have parentLive := spacedSlots.live
  have parentCapacity := spacedSlots.capacity
  simp only [Capability.copy, Capability.lookup, parentLive, ↓reduceIte, Capability.slotInRange,
    parentCapacity, endpointSlot]
  simp only [spacedCaps, addressSpaceCapabilities_subjects, addressSpaceCapabilities_slots,
    addressSpaceCapabilities_slotCapacity, createdCaps]
  have subset := endpointRights_subset rights valid
  simp only [endpointRights] at subset
  simp [SubjectLifecycle.setBool, family.capacity, parentSlots, childEndpointSlot,
    childAddressSpaceSlot, stateChildEmpty, endpointCapability, endpointRights, valid, subset]

/-- **Spawn on a family state is decided by the allocator record.** -/
theorem spawn_result_family (state : CompositeState) (family : Family state)
    (request : SpawnRequest) (authorized : spawnAuthorize state request.spawnWord = none) :
    (spawn state request).result = spawnResultOf state request := by
  have buildResult : ∀ outcome : Except SpawnError SpawnBuilt,
      spawnBuild state request = outcome →
      (spawn state request).result = match outcome with
        | .error reason => .rejected reason
        | .ok built => .spawned built.child built.addressSpace := by
    intro outcome eq
    unfold spawn; rw [eq]; cases outcome <;> rfl
  unfold spawnResultOf
  by_cases subjects : identityExhausted state.issuers.subject.next = true
  · have exhausted : (issueSubject state).result = .exhausted :=
      (issueSubject_exhausted_iff state).2 subjects
    rw [buildResult (.error .identityExhausted) (by simp [spawnBuild, authorized, exhausted])]
    simp [subjects]
  have live : identityExhausted state.issuers.subject.next = false := by simpa using subjects
  have issued := family_issueSubject state family live
  obtain ⟨createdCaps, createdVm⟩ := created_capabilities state family live
  obtain ⟨ownedSame, endpointSame, spaceSame, issuedSame⟩ := created_records state family live
  have objectIssuer : (issueSubject state).state.issuers.object = state.issuers.object :=
    (issueSubject_execution state _ issued).2.2
  have context : (issueSubject state).state.execution.core.context =
      state.execution.core.context := (issueSubject_execution state _ issued).2.1
  have room : ¬(issueSubject state).state.capabilities.slotCapacity state.issuers.subject.next < 2 := by
    rw [createdCaps]; simp only [family.capacity, parentSlots]; decide
  by_cases objects : identityExhausted state.issuers.object.next = true
  · rw [buildResult (.error .addressSpaceIdentityExhausted) (by
      simp [spawnBuild, authorized, issued, room, spawnAddressSpace, LifetimeIssuer.issue,
        objectIssuer, identityExhausted_issuer, objects])]
    simp [subjects, objects]
  have objectsLive : identityExhausted state.issuers.object.next = false := by simpa using objects
  obtain ⟨unissuedSpace, unissued, dead, owned, endpointFree⟩ := family_next_object state family
  have issueObject : LifetimeIssuer.issue (issueSubject state).state.issuers.object =
      .issued state.issuers.object.next { next := state.issuers.object.next + 1 } := by
    rw [objectIssuer]; simp [LifetimeIssuer.issue, identityExhausted_issuer, objectsLive]
  have free : addressSpaceFree (issueSubject state).state state.issuers.object.next = true := by
    simp [addressSpaceFree, ownedSame, endpointSame, owned, endpointFree]
  have childLive : (issueSubject state).state.capabilities.subjects state.issuers.subject.next =
      true := by
    rw [createdCaps]; simp [SubjectLifecycle.setBool]
  have childEmpty : ∀ slot,
      (issueSubject state).state.capabilities.slots state.issuers.subject.next slot = none := by
    intro slot; rw [createdCaps]
    exact family_dead_slots state family _ (family_next_dead state family live) slot
  have stateChildEmpty := family_dead_slots state family _ (family_next_dead state family live)
  have createdDead : (issueSubject state).state.capabilities.objects state.issuers.object.next =
      false := by rw [createdCaps]; exact dead
  by_cases capabilities : capabilityExhausted state.capabilities.nextIdentity = true
  · have rejected : (VirtualMapping.createAddressSpace (issueSubject state).state.virtualMemory
        state.issuers.object.next state.issuers.subject.next childAddressSpaceSlot).result =
        .rejected .generationExhausted := by
      unfold VirtualMapping.createAddressSpace
      rw [createdVm]
      simp only [capabilityExhausted, Bool.or_eq_true, decide_eq_true_eq] at capabilities
      have nextSame : (issueSubject state).state.capabilities.nextIdentity =
          state.capabilities.nextIdentity := by rw [createdCaps]
      simp [childLive, childAddressSpaceSlot, Capability.slotInRange, createdCaps, family.capacity,
        parentSlots, CapabilityHandle.slotReserved, CapabilityHandle.slotRadix, VirtualMapping.reject,
        nextSame, capabilities, SubjectLifecycle.setBool]
    rw [buildResult (.error (.addressSpaceRejected .generationExhausted)) (by
      simp [spawnBuild, authorized, issued, room, spawnAddressSpace, issueObject, free, rejected])]
    simp [subjects, objects, capabilities]
  have capabilitiesLive : capabilityExhausted state.capabilities.nextIdentity = false := by
    simpa using capabilities
  have accepted : (VirtualMapping.createAddressSpace (issueSubject state).state.virtualMemory
      state.issuers.object.next state.issuers.subject.next childAddressSpaceSlot).result =
      .accepted := by
    unfold VirtualMapping.createAddressSpace
    rw [createdVm]
    simp only [capabilityExhausted, Bool.or_eq_false_iff, decide_eq_false_iff_not] at capabilitiesLive
    have nextSame : (issueSubject state).state.capabilities.nextIdentity =
        state.capabilities.nextIdentity := by rw [createdCaps]
    simp [childLive, childAddressSpaceSlot, Capability.slotInRange, createdCaps, family.capacity,
      parentSlots, CapabilityHandle.slotReserved, CapabilityHandle.slotRadix, nextSame,
      capabilitiesLive, stateChildEmpty, spaceSame, issuedSame, unissuedSpace, unissued, dead,
      SubjectLifecycle.setBool]
  obtain ⟨object, slots, _⟩ := family_parentSlots state family
  have spacedSlots := spaced_parentSlots state family live object slots
  have spacedParent : spawnParent (spawnSpaced (issueSubject state).state
      state.issuers.subject.next state.issuers.object.next) = parent := by
    simp [spawnParent, spawnSpaced, installCreatedAddressSpace, context, family.current]
  have resolved := resolveEndpoint_parentSlots _ _ _ spacedSlots request.endpointWord
  cases endpoint : (abstraction state).resolveEndpoint request.endpointWord with
  | some denial =>
      rw [endpoint] at resolved
      rw [buildResult (.error (.endpointHandle denial)) (by
        simp [spawnBuild, authorized, issued, room, spawnAddressSpace, issueObject, free, accepted,
          spawnGrant, spacedParent, resolved])]
      simp [subjects, objects, capabilities]
  | none =>
      rw [endpoint] at resolved
      by_cases valid : Capability.rightsValid .endpoint request.rights = true
      · have copied := spaced_copy_accepted state family live object slots request.rights valid
        have subset := endpointRights_subset request.rights valid
        simp only [endpointRights] at subset
        rw [buildResult (.ok ⟨recordSpawn
            (applyOperation (spawnSpaced (issueSubject state).state state.issuers.subject.next
              state.issuers.object.next)
              (.capabilityCopy 0 state.issuers.subject.next childEndpointSlot request.rights))
            parent state.issuers.subject.next state.issuers.object.next,
          state.issuers.subject.next, state.issuers.object.next⟩) (by
          simp [spawnBuild, authorized, issued, room, spawnAddressSpace, issueObject, free,
            accepted, spawnGrant, spacedParent, resolved, endpointCapability, endpointRights, valid,
            subset, copied])]
        simp [subjects, objects, capabilities, valid]
      · simp only [Bool.not_eq_true] at valid
        rw [buildResult (.error .invalidRights) (by
          simp [spawnBuild, authorized, issued, room, spawnAddressSpace, issueObject, free,
            accepted, spawnGrant, spacedParent, resolved, endpointCapability, endpointRights, valid])]
        simp [subjects, objects, capabilities, valid]

/-! ## Charged spawn -/

theorem controlWord_eq (slot generation : Nat) (inRange : slot < childSlots)
    (positive : 0 < generation) (bounded : generation < CapabilityHandle.generationReserved) :
    FailStop.controlWord slot generation = SpawnAllocator.controlWord slot generation := by
  have encodable : CapabilityHandle.Encodable { slot, identity := generation } :=
    ⟨Nat.lt_trans inRange childSlots_encodable, positive, bounded⟩
  unfold FailStop.controlWord SpawnAllocator.controlWord
  simp [CapabilityHandle.encode, controlHandle, encodable, CapabilityHandle.slotRadix]

theorem controlGenerationAvailable_eq (state : CompositeState) :
    controlGenerationAvailable state = controlAvailable (abstraction state).controlNext := rfl

/-- All four child slots full: the allocator finds no free slot exactly when
the parent has four children. -/
theorem freeSlot_none_count (state : CompositeState)
    (none : (abstraction state).freeSlot = none) : (abstraction state).childCount = childCapacity := by
  unfold State.freeSlot at none
  unfold State.childCount
  rw [abstraction_children] at none ⊢
  unfold childCapacity at none ⊢
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append] at none ⊢
  cases c0 : state.spawn.children parent 0 <;> cases c1 : state.spawn.children parent 1 <;>
    cases c2 : state.spawn.children parent 2 <;> cases c3 : state.spawn.children parent 3 <;>
    simp_all [List.findIdx?_cons]

theorem spawnAuthorize_family (state : CompositeState) (family : Family state) (word : UInt64) :
    spawnAuthorize state word =
      match (abstraction state).authority with
      | none => some .missingSpawnRight
      | some generation =>
          if generation = word.toNat then none else some .staleSpawnCapability := by
  unfold spawnAuthorize
  rw [family_spawnParent state family, family.parentLive]
  simp only [↓reduceIte, abstraction]
  cases state.spawn.authority parent <;> rfl

/-- **Charged spawn on a family state is the allocator's spawn**: the same
status and value, and the abstraction of the post-state is the allocator's
successor. -/
theorem spawnCharged_family (state : CompositeState) (family : Family state)
    (request : SpawnRequest) :
    SpawnBoundary.childStatus (spawnCharged state request).result =
        ((spawnStep (abstraction state) request).status,
          (spawnStep (abstraction state) request).value) ∧
      ((spawnCharged state request).result.rejected = true →
        (spawnCharged state request).state = state) := by
  have stays : (spawnCharged state request).result.rejected = true →
      (spawnCharged state request).state = state := by
    intro rejected
    rcases spawnCharged_shape state request with ⟨same, _⟩ | ⟨_, _, _, spawned⟩
    · exact same
    · rw [spawned] at rejected; simp [ChildResult.rejected] at rejected
  refine ⟨?_, stays⟩
  have authorizedIff := spawnAuthorize_family state family request.spawnWord
  unfold spawnCharged spawnStep
  rw [authorizedIff]
  dsimp only
  cases auth : (abstraction state).authority with
  | none =>
      simp [rejectWith, SpawnBoundary.childStatus]
  | some generation =>
      have held : ∃ capability, state.spawn.authority parent = some capability ∧
          capability.generation = generation := by
        simp only [abstraction, Option.map_eq_some_iff] at auth
        exact auth
      obtain ⟨capability, heldCapability, generationEq⟩ := held
      have budgetBound := (family.authority capability heldCapability).1
      have budgetEq : (abstraction state).budget = capability.subjectBudget := by
        simp [abstraction, subjectBudget, heldCapability]
      by_cases stale : generation = request.spawnWord.toNat
      · have authorized : spawnAuthorize state request.spawnWord = none := by
          rw [authorizedIff, auth]; simp [stale]
        simp only [stale, ↓reduceIte, ne_eq, not_true_eq_false]
        rw [family_spawnParent state family, subjectBudget_family, childCount_family state family]
        by_cases full : (abstraction state).budget ≤ (abstraction state).childCount
        · simp [full, rejectWith, SpawnBoundary.childStatus]
        simp only [full, ↓reduceIte]
        cases free : (abstraction state).freeSlot with
        | none =>
            have count := freeSlot_none_count state free
            rw [budgetEq] at full
            exfalso; unfold childCapacity at count budgetBound; omega
        | some slot =>
            rw [freeChildSlot_family state slot free]
            simp only
            rw [controlGenerationAvailable_eq]
            by_cases control : controlAvailable (abstraction state).controlNext = false
            · simp [control, rejectWith, SpawnBoundary.childStatus]
            simp only [control, ↓reduceIte, Bool.false_eq_true]
            rw [spawn_result_family state family request authorized]
            unfold spawnResultOf
            have subjectsEq : (abstraction state).subjectNext = state.issuers.subject.next := rfl
            have objectsEq : (abstraction state).objectNext = state.issuers.object.next := rfl
            have capabilitiesEq : (abstraction state).capabilityNext =
                state.capabilities.nextIdentity := rfl
            rw [subjectsEq, objectsEq, capabilitiesEq]
            by_cases subjects : identityExhausted state.issuers.subject.next = true
            · simp [subjects, rejectWith, SpawnBoundary.childStatus,
                SpawnAccountingOracle.childSpawnErrorCode]
            simp only [subjects, Bool.false_eq_true, ↓reduceIte]
            by_cases objects : identityExhausted state.issuers.object.next = true
            · simp [objects, rejectWith, SpawnBoundary.childStatus,
                SpawnAccountingOracle.childSpawnErrorCode]
            simp only [objects, Bool.false_eq_true, ↓reduceIte]
            by_cases capabilities : capabilityExhausted state.capabilities.nextIdentity = true
            · simp [capabilities, rejectWith, SpawnBoundary.childStatus,
                SpawnAccountingOracle.childSpawnErrorCode]
            simp only [capabilities, Bool.false_eq_true, ↓reduceIte]
            cases (abstraction state).resolveEndpoint request.endpointWord with
            | some denial =>
                simp [rejectWith, SpawnBoundary.childStatus, SpawnAccountingOracle.childSpawnErrorCode]
            | none =>
                by_cases valid : Capability.rightsValid .endpoint request.rights = false
                · simp [valid, rejectWith, SpawnBoundary.childStatus,
                    SpawnAccountingOracle.childSpawnErrorCode]
                simp only [valid, ↓reduceIte]
                obtain ⟨positive, bounded⟩ := controlAvailable_true (by simpa using control)
                have slotRange : slot < childSlots := by
                  obtain ⟨inRange, _⟩ := freeSlot_some free
                  have : (abstraction state).children.length = childCapacity := by
                    rw [abstraction_children]; simp
                  unfold childCapacity at this; unfold childSlots; omega
                simp only [acceptWith, SpawnBoundary.childStatus]
                exact congrArg (fun word => ((0x01 : UInt64), word))
                  (controlWord_eq slot _ slotRange positive bounded)
      · simp [stale, rejectWith, SpawnBoundary.childStatus, SpawnAccountingOracle.childSpawnErrorCode,
          SpawnOracle.spawnErrorCode]

/-! ## The post-state of an accepted spawn -/

/-- An accepted copy advances the identity counter by one and changes no
subject, object, kind or slot capacity. -/
theorem copy_accepted_fields (capabilities : Capability.State) (actor source destination
    destinationSlot : Nat) (requested : Capability.Rights)
    (accepted : (Capability.copy capabilities actor source destination destinationSlot
      requested).result = .accepted) :
    let next := (Capability.copy capabilities actor source destination destinationSlot
      requested).state
    next.nextIdentity = capabilities.nextIdentity + 1 ∧
      next.slotCapacity = capabilities.slotCapacity ∧ next.subjects = capabilities.subjects ∧
      next.objects = capabilities.objects ∧ next.kinds = capabilities.kinds := by
  intro next
  unfold next
  unfold Capability.copy at accepted ⊢
  split at accepted
  · simp [Capability.reject] at accepted
  · simp [Capability.reject] at accepted
  next capability _ =>
    split at accepted
    · simp [Capability.reject] at accepted
    split at accepted
    · simp [Capability.reject] at accepted
    split at accepted
    · simp [Capability.reject] at accepted
    split at accepted
    · split at accepted
      · split at accepted
        · next a b c d e f => simp [a, b, c, d, e, f, Capability.install]
        · simp [Capability.reject] at accepted
      · simp [Capability.reject] at accepted
    · simp [Capability.reject] at accepted

/-- The projections the allocator and the family invariant read, after an
accepted spawn of `child` with address space `addressSpace`. -/
theorem spawn_post (state : CompositeState) (family : Family state) (request : SpawnRequest)
    (child addressSpace : Nat)
    (spawned : (spawn state request).result = .spawned child addressSpace) :
    let post := (spawn state request).state
    post.issuers.subject.next = state.issuers.subject.next + 1 ∧
      post.issuers.object.next = state.issuers.object.next + 1 ∧
      post.capabilities.nextIdentity = state.capabilities.nextIdentity + 2 ∧
      post.capabilities.slotCapacity = state.capabilities.slotCapacity ∧
      post.capabilities.subjects = SubjectLifecycle.setBool state.capabilities.subjects child true ∧
      (∀ object, object ≠ addressSpace → post.capabilities.objects object = state.capabilities.objects object) ∧
      (∀ object, object ≠ addressSpace → post.capabilities.kinds object = state.capabilities.kinds object) ∧
      post.spawn.children = state.spawn.children ∧
      post.spawn.nextChildGeneration = state.spawn.nextChildGeneration ∧
      post.spawn.parent = (fun candidate => if candidate = child then some parent
        else state.spawn.parent candidate) ∧
      post.execution.mode = state.execution.mode ∧
      post.execution.core.context = state.execution.core.context ∧
      post.lifecycle.ownedMemory = state.lifecycle.ownedMemory ∧
      post.lifecycle.endpointOwner = state.lifecycle.endpointOwner ∧
      post.lifecycle.frameOwner = state.lifecycle.frameOwner ∧
      (∀ object, object ≠ addressSpace →
        post.lifecycle.addressOwner object = state.lifecycle.addressOwner object) := by
  intro post
  obtain ⟨_, issued, objectIssued, _, resolution, _, _, _, copied, stateEq⟩ :=
    spawn_spawned_stages state request child addressSpace spawned
  obtain ⟨identity, _, created, createdEq⟩ := issueSubject_issued state child issued
  have objectIssuer := (issueSubject_execution state child issued).2.2
  rw [objectIssuer] at objectIssued
  obtain ⟨addressSame, _, _, _⟩ := LifetimeIssuer.issued_facts objectIssued
  have lifeCaps := family_lifecycleCapabilities state family
  obtain ⟨copyNext, copyCapacity, copySubjects, copyObjects, copyKinds⟩ :=
    copy_accepted_fields _ _ _ _ _ _ copied
  subst identity addressSame
  have spawnParentEq := family_spawnParent state family
  simp only [spawnSpaced, installCreatedAddressSpace, createdVirtualMemory_capabilities, createdEq,
    applyOperation, created, installCreatedSubject, SubjectLifecycle.create_accepted_state _ _ created,
    spawnParentEq, lifeCaps] at copyNext copyCapacity copySubjects copyObjects copyKinds
  simp only [post, stateEq, recordSpawn, installCopiedCapabilities, spawnSpaced,
    installCreatedAddressSpace, createdVirtualMemory_capabilities, createdEq, applyOperation, created,
    installCreatedSubject, SubjectLifecycle.create_accepted_state _ _ created, spawnParentEq, lifeCaps]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (try simp [copyNext, copyCapacity, copySubjects, copyObjects, copyKinds,
    VirtualMapping.setOwner, addressSpaceCapabilities_objects, addressSpaceCapabilities_kinds])
  all_goals (intro object different same; exact absurd same different)

theorem map_range_set {α : Type} (count slot : Nat) (inRange : slot < count) (f g : Nat → α)
    (value : α) (updated : ∀ index, g index = if index = slot then value else f index) :
    (List.range count).map g = ((List.range count).map f).set slot value := by
  apply List.ext_getElem
  · simp
  · intro index left right
    simp only [List.getElem_map, List.getElem_range, List.getElem_set]
    rw [updated]
    by_cases same : index = slot
    · subst same; simp
    · simp [same, Ne.symm same]

theorem spawnResultOf_spawned (state : CompositeState) (request : SpawnRequest)
    (child addressSpace : Nat) (spawned : spawnResultOf state request = .spawned child addressSpace) :
    child = state.issuers.subject.next ∧ addressSpace = state.issuers.object.next := by
  unfold spawnResultOf at spawned
  repeat' split at spawned
  all_goals simp only [reduceCtorEq, SpawnResult.spawned.injEq] at spawned
  exact ⟨spawned.1.symm, spawned.2.symm⟩

/-- An accepted charged spawn on a family state: the composite result and
post-state. -/
theorem spawnCharged_accepted (state : CompositeState) (family : Family state)
    (request : SpawnRequest) (slot : Nat) (free : (abstraction state).freeSlot = some slot)
    (accepted : (spawnStep (abstraction state) request).status = 0x01) :
    (spawn state request).result = .spawned state.issuers.subject.next state.issuers.object.next ∧
      (spawnCharged state request).state =
        installChild (spawn state request).state parent slot state.issuers.subject.next := by
  have status := (spawnCharged_family state family request).1
  rw [accepted] at status
  rcases spawnCharged_result state request with ⟨child, addressSpace, control, result⟩ |
    ⟨reason, result⟩
  · obtain ⟨slot', _, _, free', _, spawned, _, stateEq⟩ :=
      spawnCharged_spawned state request child addressSpace control result
    rw [family_spawnParent state family] at free' stateEq
    rw [freeChildSlot_family state slot free] at free'
    simp only [Option.some.injEq] at free'
    subst free'
    have authorized : spawnAuthorize state request.spawnWord = none := by
      unfold spawnCharged at result
      split at result
      · simp at result
      · assumption
    have resultEq := spawn_result_family state family request authorized
    rw [spawned] at resultEq
    obtain ⟨childEq, spaceEq⟩ := spawnResultOf_spawned state request child addressSpace resultEq.symm
    subst childEq spaceEq
    exact ⟨spawned, stateEq⟩
  · rw [result] at status
    have small := childSpawnErrorCode_lt reason
    simp only [SpawnBoundary.childStatus, Prod.mk.injEq] at status
    exact absurd status.1 (reject_status_ne small)

@[simp] theorem installChild_issuers (state : CompositeState) (p slot child : Nat) :
    (installChild state p slot child).issuers = state.issuers := rfl
@[simp] theorem installChild_capabilities (state : CompositeState) (p slot child : Nat) :
    (installChild state p slot child).capabilities = state.capabilities := rfl
@[simp] theorem installChild_nextChildGeneration (state : CompositeState) (p slot child : Nat) :
    (installChild state p slot child).spawn.nextChildGeneration =
      state.spawn.nextChildGeneration + 1 := rfl
@[simp] theorem installChild_nextGeneration (state : CompositeState) (p slot child : Nat) :
    (installChild state p slot child).spawn.nextGeneration = state.spawn.nextGeneration := rfl
@[simp] theorem installChild_authority (state : CompositeState) (p slot child : Nat) :
    (installChild state p slot child).spawn.authority = state.spawn.authority := rfl
@[simp] theorem installChild_budgetLimit (state : CompositeState) (p slot child subject : Nat) :
    (installChild state p slot child).budgetLimit subject = state.budgetLimit subject := rfl
theorem installChild_children (state : CompositeState) (p slot child : Nat) :
    (installChild state p slot child).spawn.children = fun candidate candidateSlot =>
      if candidate = p ∧ candidateSlot = slot then
        some { child, generation := state.spawn.nextChildGeneration, charge := 0 }
      else state.spawn.children candidate candidateSlot := rfl

/-- **The abstraction of an accepted charged spawn's post-state is the
allocator's successor.** -/
theorem spawnCharged_abstraction (state : CompositeState) (family : Family state)
    (request : SpawnRequest) (accepted : (spawnStep (abstraction state) request).status = 0x01) :
    abstraction (spawnCharged state request).state = (spawnStep (abstraction state) request).next := by
  obtain ⟨slot, _, _, free, _, _, _, _, _, _, stepEq⟩ :=
    spawnStep_accepted (abstraction state) request accepted
  obtain ⟨spawnedResult, stateEq⟩ := spawnCharged_accepted state family request slot free accepted
  obtain ⟨subjectNext, objectNext, capabilityNext, _, _, _, _, children, nextChild, _⟩ :=
    spawn_post state family request _ _ spawnedResult
  obtain ⟨authority, nextGeneration, _, _⟩ := spawn_registry state request _ _ spawnedResult
  have parentSlots := spawn_parent_unchanged state request _ _ (family_runtime state family) spawnedResult
  rw [family_spawnParent state family] at parentSlots
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, budgets, _, allocator, _, _⟩ :=
    spawn_keeps state request _ _ spawnedResult
  have limit := (budget_eq_of_allocator budgets allocator parent).2
  obtain ⟨inRange, _⟩ := freeSlot_some free
  have slotSmall : slot < childCapacity := by
    have : (abstraction state).children.length = childCapacity := by
      rw [abstraction_children]; simp
    omega
  rw [stepEq, stateEq]
  simp only [acceptWith, SpawnAllocator.spawned, abstraction, State.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [subjectNext]
  · simp [objectNext]
  · simp [capabilityNext]
  · simp [nextChild]
  · simp [nextGeneration]
  · simp [authority]
  · simp [subjectBudget, authority]
  · apply map_range_set childCapacity slot slotSmall
    intro index
    rw [installChild_children, children, nextChild]
    by_cases same : index = slot
    · simp [same]
    · simp [same]
  · simp [memoryIn, parentSlots]
  · simp [limit]


/-! ## The family invariant after a spawn -/

theorem family_childGate_invariants (state : CompositeState) (family : Family state)
    (operation : ChildOperation) :
    ResourceRuntimeWellFormed (operation.apply state).state ∧
      ChildAccountingWellFormed (operation.apply state).state ∧
      SpawnTreeWellFormed (operation.apply state).state := by
  have gateEq : (childGate state operation).state = (operation.apply state).state := by
    simp [childGate, family.running]
  obtain ⟨resources, accounting, _⟩ :=
    childGate_preserves state operation family.resources family.accounting
  have tree := childGate_spawnTree state operation family.resources family.accounting family.tree
  rw [gateEq] at resources accounting tree
  exact ⟨resources, accounting, tree⟩

/-- An address space someone owns is not the next object identity. -/
theorem family_owned_space_ne (state : CompositeState) (family : Family state) (object owner : Nat)
    (owned : state.lifecycle.addressOwner object = some owner) :
    object ≠ state.issuers.object.next := by
  intro same
  subst same
  have none := addressOwner_none_of_unissued (family_runtime state family)
    (family_next_object state family).1
  rw [owned] at none; cases none

/-- A live object is not the next object identity. -/
theorem family_live_object_ne (state : CompositeState) (family : Family state) (object : Nat)
    (live : state.capabilities.objects object = true) : object ≠ state.issuers.object.next := by
  intro same; subst same
  rw [(family_next_object state family).2.2.1] at live; cases live

/-- **An accepted charged spawn keeps the family invariant.** -/
theorem spawnCharged_family_preserved (state : CompositeState) (family : Family state)
    (request : SpawnRequest) (accepted : (spawnStep (abstraction state) request).status = 0x01) :
    Family (spawnCharged state request).state := by
  obtain ⟨slot, _, _, free, control, subjectsLive, _, capabilitiesLive, _, _, stepEq⟩ :=
    spawnStep_accepted (abstraction state) request accepted
  have abstractionEq := spawnCharged_abstraction state family request accepted
  rw [stepEq] at abstractionEq
  simp only [acceptWith] at abstractionEq
  obtain ⟨spawnedResult, stateEq⟩ := spawnCharged_accepted state family request slot free accepted
  obtain ⟨_, objectNext, capabilityNext, capacity, subjects, objects, kinds, children,
    nextChild, parentRecord, mode, context, ownedMemory, endpointOwner, frameOwner, addressOwner⟩ :=
    spawn_post state family request _ _ spawnedResult
  obtain ⟨authority, nextGeneration, _, _⟩ := spawn_registry state request _ _ spawnedResult
  have parentSlotsSame := spawn_parent_unchanged state request _ _ (family_runtime state family)
    spawnedResult
  rw [family_spawnParent state family] at parentSlotsSame
  obtain ⟨_, current, _, _, _, _, _, _, _, _, _, _, _, budgets, _, allocator, binding, _⟩ :=
    spawn_keeps state request _ _ spawnedResult
  have budgetsSame := budget_eq_of_allocator budgets allocator
  obtain ⟨childLimit, _⟩ := spawn_child_starts_empty state request _ _ family.resources spawnedResult
  obtain ⟨inRange, emptySlot⟩ := freeSlot_some free
  have slotSmall : slot < childCapacity := by
    have : (abstraction state).children.length = childCapacity := by
      rw [abstraction_children]; simp
    omega
  have slotEmpty : state.spawn.children parent slot = none := by
    have := abstraction_childAt_lt state slot slotSmall
    rw [State.childAt, List.getElem?_eq_getElem inRange, emptySlot] at this
    simp only [Option.join_some] at this
    cases found : state.spawn.children parent slot with
    | none => rfl
    | some entry => rw [found] at this; simp at this
  have subjectsLive' : identityExhausted state.issuers.subject.next = false := subjectsLive
  have parentNe : parent ≠ state.issuers.subject.next := by
    intro same
    have dead := family_next_dead state family subjectsLive'
    rw [← same, family.parentLive] at dead; cases dead
  have invariants := family_childGate_invariants state family (.spawn request)
  simp only [ChildOperation.apply] at invariants
  obtain ⟨resources, accounting, tree⟩ := invariants
  obtain ⟨controlPositive, controlBounded⟩ := controlAvailable_true control
  obtain ⟨_, capabilitiesBounded⟩ := capabilityExhausted_false capabilitiesLive
  have postChildren : ∀ candidateSlot,
      (spawnCharged state request).state.spawn.children parent candidateSlot =
        if candidateSlot = slot then
          some ⟨state.issuers.subject.next, state.spawn.nextChildGeneration, 0⟩
        else state.spawn.children parent candidateSlot := by
    intro candidateSlot
    rw [stateEq, installChild_children, children, nextChild]
    simp
  rw [stateEq] at resources accounting tree abstractionEq postChildren ⊢
  have setBoolOther : ∀ subject, subject ≠ state.issuers.subject.next →
      SubjectLifecycle.setBool state.capabilities.subjects state.issuers.subject.next true subject =
        state.capabilities.subjects subject := by
    intro subject ne; simp [SubjectLifecycle.setBool, ne]
  have oldSlot : ∀ candidateSlot entry, state.spawn.children parent candidateSlot = some entry →
      candidateSlot ≠ slot := by
    intro candidateSlot entry found same
    rw [same, slotEmpty] at found; cases found
  refine ⟨resources, accounting, tree, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mode.trans family.running
  · show (spawn state request).state.execution.core.context.currentSubject = parent
    rw [context]; exact family.current
  · show (spawn state request).state.lifecycle.current = some parent
    rw [current]; exact family.lifecycleCurrent
  · intro subject
    show (spawn state request).state.capabilities.slotCapacity subject = parentSlots
    rw [capacity]; exact family.capacity subject
  · show (spawn state request).state.capabilities.subjects parent = true
    rw [subjects, setBoolOther parent parentNe]; exact family.parentLive
  · show (spawn state request).state.spawn.parent parent = none
    rw [parentRecord]; simp [parentNe, family.parentRoot]
  · obtain ⟨object, endpointSlot, objectLive, objectKind, owner⟩ := family.endpoint
    have ne := family_live_object_ne state family object objectLive
    refine ⟨object, ?_, ?_, ?_, ?_⟩
    · show (spawn state request).state.capabilities.slots parent 0 = _
      rw [parentSlotsSame]; exact endpointSlot
    · show (spawn state request).state.capabilities.objects object = true
      rw [objects object ne]; exact objectLive
    · show (spawn state request).state.capabilities.kinds object = _
      rw [kinds object ne]; exact objectKind
    · show (spawn state request).state.lifecycle.endpointOwner object = _
      rw [endpointOwner]; exact owner
  · obtain ⟨capability, held, kind, identity, owner⟩ := family.space
    have ne := family_owned_space_ne state family _ _ owner
    refine ⟨capability, ?_, kind, identity, ?_⟩
    · show (spawn state request).state.capabilities.slots parent 1 = _
      rw [parentSlotsSame]; exact held
    · show (spawn state request).state.lifecycle.addressOwner capability.object = _
      rw [addressOwner _ ne]; exact owner
  · intro memorySlot which
    rcases family.memory memorySlot which with empty | ⟨capability, frame, held, kind, revoke,
      positive, bound, status, owned, committed⟩
    · left
      show (spawn state request).state.capabilities.slots parent memorySlot = none
      rw [parentSlotsSame]; exact empty
    · right
      refine ⟨capability, frame, ?_, kind, revoke, positive, ?_, ?_, ?_, ?_⟩
      · show (spawn state request).state.capabilities.slots parent memorySlot = _
        rw [parentSlotsSame]; exact held
      · show (spawn state request).state.virtualMemory.memory.binding capability.object = _
        rw [binding]; exact bound
      · show (spawn state request).state.virtualMemory.memory.allocator.status frame = _
        rw [allocator]; exact status
      · show (spawn state request).state.lifecycle.ownedMemory capability.object = _
        rw [ownedMemory]; exact owned
      · show (spawn state request).state.frameBudgets.commitment frame = _
        rw [budgets]; exact committed
  · intro first second held2 held3
    change (spawn state request).state.capabilities.slots parent 2 = some first at held2
    change (spawn state request).state.capabilities.slots parent 3 = some second at held3
    rw [parentSlotsSame] at held2 held3
    exact family.memoryDistinct first second held2 held3
  · intro candidateSlot high
    rw [postChildren]
    have : candidateSlot ≠ slot := by omega
    simp [this, family.childSlots candidateSlot high]
  · intro capability held
    have held' : state.spawn.authority parent = some capability := by
      rw [← authority]; exact held
    have := family.authority capability held'
    show capability.subjectBudget ≤ childCapacity ∧ 0 < capability.generation ∧
      capability.generation < (spawn state request).state.spawn.nextGeneration
    rw [nextGeneration]; exact this
  · intro subject other
    show (spawn state request).state.spawn.authority subject = none
    rw [authority]; exact family.others subject other
  · intro candidateSlot entry found
    rw [postChildren] at found
    by_cases same : candidateSlot = slot
    · simp only [same, ↓reduceIte, Option.some.injEq] at found
      subst found
      refine ⟨?_, controlPositive, ?_⟩
      · show (spawn state request).state.capabilities.subjects _ = true
        rw [subjects]; simp [SubjectLifecycle.setBool]
      · exact childLimit
    · simp only [same, ↓reduceIte] at found
      obtain ⟨live, positive, limit⟩ := family.childLive candidateSlot entry found
      have childNe : entry.child ≠ state.issuers.subject.next := by
        intro eq
        have dead := family_next_dead state family subjectsLive'
        rw [← eq, live] at dead; cases dead
      refine ⟨?_, positive, ?_⟩
      · show (spawn state request).state.capabilities.subjects entry.child = true
        rw [subjects, setBoolOther _ childNe]; exact live
      · show (spawn state request).state.budgetLimit entry.child = entry.charge
        rw [(budgetsSame entry.child).2]; exact limit
  · intro subject liveNow
    change (spawn state request).state.capabilities.subjects subject = true at liveNow
    rw [subjects] at liveNow
    by_cases isChild : subject = state.issuers.subject.next
    · right; right
      refine ⟨slot, ⟨state.issuers.subject.next, state.spawn.nextChildGeneration, 0⟩, ?_, isChild.symm⟩
      rw [postChildren]; simp
    · rw [setBoolOther _ isChild] at liveNow
      rcases family.live subject liveNow with bystanderIs | parentIs | ⟨candidateSlot, entry, found, childIs⟩
      · exact Or.inl bystanderIs
      · exact Or.inr (Or.inl parentIs)
      · right; right
        refine ⟨candidateSlot, entry, ?_, childIs⟩
        rw [postChildren]; simp [oldSlot candidateSlot entry found, found]
  · intro frame subject committedNow
    change (spawn state request).state.frameBudgets.commitment frame = some subject at committedNow
    rw [budgets] at committedNow
    rcases family.committed frame subject committedNow with parentIs |
      ⟨freeFrame, unowned, candidateSlot, entry, found, childIs⟩
    · exact Or.inl parentIs
    · right
      refine ⟨?_, ?_, candidateSlot, entry, ?_, childIs⟩
      · show (spawn state request).state.virtualMemory.memory.allocator.status frame = _
        rw [allocator]; exact freeFrame
      · show (spawn state request).state.lifecycle.frameOwner frame = none
        rw [frameOwner]; exact unowned
      · rw [postChildren]; simp [oldSlot candidateSlot entry found, found]
  · show (spawn state request).state.virtualMemory.memory.allocator.frames.Nodup
    rw [allocator]; exact family.framesNodup
  · intro namedSlot capability subject held owned
    change (spawn state request).state.capabilities.slots parent namedSlot = some capability at held
    rw [parentSlotsSame] at held
    have live := ((family_runtime state family).2.2.2.1.1 parent namedSlot capability held).2.1
    have ne := family_live_object_ne state family _ live
    unfold OwnedBy at owned
    change (spawn state request).state.lifecycle.endpointOwner capability.object = some subject ∨
      (spawn state request).state.lifecycle.addressOwner capability.object = some subject ∨
      ((spawn state request).state.lifecycle.ownedMemory capability.object).any
        (fun owner => owner.1 = subject) = true at owned
    rw [endpointOwner, addressOwner _ ne, ownedMemory] at owned
    have ownedBefore : OwnedBy state.lifecycle subject capability.object := owned
    have subjectLive := owner_live state family subject capability.object ownedBefore
    have subjectNe : subject ≠ state.issuers.subject.next := by
      intro same
      have dead := family_next_dead state family subjectsLive'
      rw [← same, subjectLive] at dead; cases dead
    show (spawn state request).state.spawn.parent subject = none
    rw [parentRecord]
    simp [subjectNe, family.parentNames namedSlot capability subject held ownedBefore]
  · intro object high
    change (spawn state request).state.issuers.object.next ≤ object at high
    rw [objectNext] at high
    have ne : object ≠ state.issuers.object.next := by omega
    obtain ⟨dead, owned, endpoint⟩ := family.fresh object (by omega)
    refine ⟨?_, ?_, ?_⟩
    · show (spawn state request).state.capabilities.objects object = false
      rw [objects object ne]; exact dead
    · show (spawn state request).state.lifecycle.ownedMemory object = none
      rw [ownedMemory]; exact owned
    · show (spawn state request).state.lifecycle.endpointOwner object = none
      rw [endpointOwner]; exact endpoint
  · intro frame committedNow freeNow
    change (spawn state request).state.frameBudgets.commitment frame = some parent at committedNow
    change (spawn state request).state.virtualMemory.memory.allocator.status frame = .free at freeNow
    rw [budgets] at committedNow
    rw [allocator] at freeNow
    show (spawn state request).state.lifecycle.frameOwner frame = none
    rw [frameOwner]; exact family.parentFree frame committedNow freeNow
  · rw [abstractionEq, spawned_memoryUsed]
    show (spawn state request).state.budgetUsage parent = _
    rw [(budgetsSame parent).1]; exact family.usage
  · have same : (abstraction state).capabilityNext = state.capabilities.nextIdentity := rfl
    show (spawn state request).state.capabilities.nextIdentity ≤ _
    rw [capabilityNext]; omega
  · have same : (abstraction state).controlNext = state.spawn.nextChildGeneration := rfl
    show (spawn state request).state.spawn.nextChildGeneration + 1 ≤ _
    rw [nextChild]; omega
  · show 0 < (spawn state request).state.spawn.nextGeneration ∧
      (spawn state request).state.spawn.nextGeneration < wordBound
    rw [nextGeneration]; exact family.generationBound
  · rw [abstractionEq, spawned_chargeSum _ _ free]
    show (spawn state request).state.budgetLimit parent + _ < _
    rw [(budgetsSame parent).2]; exact family.frameBound

end LeanOS.SpawnAllocator
