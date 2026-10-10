import LeanOS.FailStop.SpawnInvariants

/-!
# Fail-stop composite: what a spawned child receives

The ADR 0010 inheritance set, as theorems about an accepted
`spawn state request` from a state satisfying `RuntimeWellFormed`
(`ResourceRuntimeWellFormed` where budgets are involved):

- **Exactness** (`spawn_child_capabilities`, `spawn_child_authority`).  The
  child's capability space is exactly slot `0`, a `Capability.copy` of an
  endpoint capability the parent held with `grant`, carrying exactly the
  requested rights, which are a subset of the parent's; and slot `1`, the
  root capability of its own new address space.  Every other slot is empty.
  So the child's authority over any object that existed before the spawn is
  exactly the granted endpoint, attenuated.
- **No amplification** (`spawn_other_slots_unchanged`,
  `spawn_no_authority_amplification`).  Every subject other than the child,
  the parent included, has exactly the slots and the authority it had before.
  The spawn-authority table is unchanged, so the child receives no spawn
  capability (`spawn_registry`).
- **Fresh identity** (`spawn_fresh_identity`).  The child is the subject
  issuer's next identity, was never issued and never live, and is above every
  subject identity ever issued; its address space is the object issuer's
  next identity and was never issued.
- **Nothing else** (`spawn_child_starts_empty`).  Zero frame budget; not
  runnable, not current, not queued; no saved, blocked, or deferred context
  (so its first context will be the reviewed reset value); not an IPC waiter;
  no queued message or sealed transfer from it; the device projections are
  unchanged; its address space has no mappings.
- **Relation, not authority** (`spawn_registry`).  `spawn.parent child` is
  the parent; no stage of `spawn` reads `spawn.parent`
  (`spawnBuild_ignores_parent_record`).
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

/-! ## Stage shapes -/

theorem SubjectLifecycle.create_accepted_state (state : SubjectLifecycle.State) (subject : Nat)
    (accepted : (SubjectLifecycle.create state subject).result = .accepted) :
    (SubjectLifecycle.create state subject).state =
      { state with
        capabilities := { state.capabilities with
          subjects := SubjectLifecycle.setBool state.capabilities.subjects subject true }
        issuedSubjects := SubjectLifecycle.setBool state.issuedSubjects subject true } := by
  simp only [SubjectLifecycle.create] at accepted ⊢
  split at accepted
  · simp [SubjectLifecycle.reject] at accepted
  · split at accepted
    · simp [SubjectLifecycle.reject] at accepted
    · next live issued => simp [live, issued]

/-- An accepted `Capability.copy` installs exactly one derived capability in
the destination slot and changes no other slot. -/
theorem Capability.copy_accepted_slots (state : Capability.State) (actor source destination
    destinationSlot : Nat) (requested : Capability.Rights)
    (accepted : (Capability.copy state actor source destination destinationSlot requested).result =
      .accepted) :
    ∃ capability, state.slots actor source = some capability ∧
      (Capability.copy state actor source destination destinationSlot requested).state.slots =
        fun subject slot => if subject = destination ∧ slot = destinationSlot then
          some ⟨capability.object, capability.kind, requested, state.nextIdentity,
            some capability.identity⟩
        else state.slots subject slot := by
  unfold Capability.copy at accepted ⊢
  split at accepted
  · simp [Capability.reject] at accepted
  · simp [Capability.reject] at accepted
  next capability found =>
    refine ⟨capability, Capability.lookup_found_slot state actor source capability found, ?_⟩
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

/-- The concrete stages of an accepted spawn. -/
theorem spawn_spawned_stages (state : CompositeState) (request : SpawnRequest)
    (child addressSpace : Nat)
    (spawned : (spawn state request).result = .spawned child addressSpace) :
    spawnAuthorize state request.spawnWord = none ∧
      (issueSubject state).result = .issued child ∧
      LifetimeIssuer.issue (issueSubject state).state.issuers.object =
        .issued addressSpace { next := addressSpace + 1 } ∧
      (VirtualMapping.createAddressSpace (issueSubject state).state.virtualMemory addressSpace
        child childAddressSpaceSlot).result = .accepted ∧
      ∃ resolution : CapabilityHandle.Resolution,
        CapabilityHandle.resolveCurrent
            (spawnSpaced (issueSubject state).state child addressSpace).capabilities
            { caller := spawnParent state } request.endpointWord .endpoint = .ok resolution ∧
          resolution.capability.rights.grant = true ∧
          Capability.rightsSubset request.rights resolution.capability.rights = true ∧
          (Capability.copy (spawnSpaced (issueSubject state).state child addressSpace).capabilities
            (spawnParent state) resolution.handle.slot child childEndpointSlot
            request.rights).result = .accepted ∧
          (spawn state request).state = recordSpawn
            (installCopiedCapabilities (spawnSpaced (issueSubject state).state child addressSpace)
              (Capability.copy (spawnSpaced (issueSubject state).state child addressSpace).capabilities
                (spawnParent state) resolution.handle.slot child childEndpointSlot
                request.rights).state)
            (spawnParent state) child addressSpace := by
  obtain ⟨built, ok, hchild, haddress, eq⟩ := spawn_spawned_build state request child addressSpace
    spawned
  subst hchild haddress
  have trace := spawnBuild_ok state request built ok
  have parentEq : spawnParent (spawnSpaced (issueSubject state).state built.child
      built.addressSpace) = spawnParent state := by
    simp [spawnParent, spawnSpaced, installCreatedAddressSpace,
      (issueSubject_execution state built.child trace.issued).2.1]
  obtain ⟨resolution, resolved, grant, _, subset, copied, stateEq⟩ := trace.granted
  rw [parentEq] at resolved copied stateEq
  refine ⟨trace.authorized, trace.issued, trace.objectIssued, trace.spaceAccepted, resolution,
    resolved, grant, subset, copied, ?_⟩
  have current : (spawnSpaced (issueSubject state).state built.child
      built.addressSpace).execution.core.context.currentSubject = spawnParent state := parentEq
  rw [eq, stateEq]
  simp only [applyOperation, current, copied]

/-- The capability registry after issued creation. -/
theorem issueSubject_capabilities (state : CompositeState) (child : Nat)
    (issued : (issueSubject state).result = .issued child) :
    (issueSubject state).state.capabilities =
        { state.lifecycle.capabilities with
          subjects := SubjectLifecycle.setBool state.lifecycle.capabilities.subjects child true } ∧
      (issueSubject state).state.virtualMemory.memory.capabilities =
        (issueSubject state).state.capabilities := by
  obtain ⟨_, _, created, eq⟩ := issueSubject_issued state child issued
  rw [eq]
  simp [applyOperation, created, installCreatedSubject,
    SubjectLifecycle.create_accepted_state _ _ created]

/-! ## The child's capability space -/

/-- The parent is live and the child was not, so they differ. -/
theorem spawn_parent_ne_child (state : CompositeState) (request : SpawnRequest)
    (child addressSpace : Nat) (holds : RuntimeWellFormed state)
    (spawned : (spawn state request).result = .spawned child addressSpace) :
    spawnParent state ≠ child ∧ state.capabilities.subjects child = false := by
  obtain ⟨authorized, issued, _⟩ := spawn_spawned_stages state request child addressSpace spawned
  have live : state.capabilities.subjects (spawnParent state) = true := by
    unfold spawnAuthorize at authorized; split at authorized
    · assumption
    · simp at authorized
  have dead : state.capabilities.subjects child = false := by
    rw [holds.1.2.2.2.1]; exact (issueSubject_fresh state child issued).2.1
  refine ⟨fun same => ?_, dead⟩
  rw [same, dead] at live; contradiction

/-- **Inheritance-set exactness.**  After an accepted spawn the child holds
exactly two capabilities: in slot `0` a copy of the parent's endpoint
capability, which the parent held with `grant`, with exactly the requested
rights (a subset of the parent's); and in slot `1` the root capability of its
new address space.  Every other slot is empty. -/
theorem spawn_child_capabilities (state : CompositeState) (request : SpawnRequest)
    (child addressSpace : Nat) (holds : RuntimeWellFormed state)
    (spawned : (spawn state request).result = .spawned child addressSpace) :
    ∃ slot endpoint,
      state.capabilities.slots (spawnParent state) slot = some endpoint ∧
      endpoint.kind = .endpoint ∧ endpoint.rights.grant = true ∧
      Capability.rightsSubset request.rights endpoint.rights = true ∧
      ∀ candidateSlot, (spawn state request).state.capabilities.slots child candidateSlot =
        if candidateSlot = childEndpointSlot then
          some ⟨endpoint.object, .endpoint, request.rights, state.capabilities.nextIdentity + 1,
            some endpoint.identity⟩
        else if candidateSlot = childAddressSpaceSlot then
          some (addressSpaceRoot state.capabilities addressSpace)
        else none := by
  obtain ⟨_, issued, _, _, resolution, resolved, grant, subset, copied, stateEq⟩ :=
    spawn_spawned_stages state request child addressSpace spawned
  obtain ⟨ne, dead⟩ := spawn_parent_ne_child state request child addressSpace holds spawned
  obtain ⟨createdCaps, createdVm⟩ := issueSubject_capabilities state child issued
  have lifeCaps : state.lifecycle.capabilities = state.capabilities := holds.1.2.2.2.1.symm
  -- The spaced registry.
  have spacedCaps : (spawnSpaced (issueSubject state).state child addressSpace).capabilities =
      addressSpaceCapabilities (issueSubject state).state.capabilities addressSpace child
        childAddressSpaceSlot := by
    simp [spawnSpaced, installCreatedAddressSpace, createdVirtualMemory_capabilities, createdVm]
  obtain ⟨source, sourceHeld, slotsEq⟩ := Capability.copy_accepted_slots _ _ _ _ _ _ copied
  have resolvedFacts := CapabilityHandle.resolveCurrent_sound _ _ _ _ _ resolved
  have sourceIs : source = resolution.capability := by
    rw [resolvedFacts.2.2.2.1] at sourceHeld; cases sourceHeld; rfl
  subst sourceIs
  have parentSlot : state.capabilities.slots (spawnParent state) resolution.handle.slot =
      some resolution.capability := by
    have := resolvedFacts.2.2.2.1
    rw [spacedCaps, addressSpaceCapabilities_slots] at this
    simp only [ne, false_and, ↓reduceIte, createdCaps] at this
    rw [lifeCaps] at this
    exact this
  have childEmpty : ∀ slot, state.capabilities.slots child slot = none := by
    intro slot
    cases held : state.capabilities.slots child slot with
    | none => rfl
    | some capability =>
        have := (holds.2.2.2.1.1 child slot capability held).1
        rw [dead] at this; contradiction
  refine ⟨resolution.handle.slot, resolution.capability, parentSlot,
    resolvedFacts.2.2.2.2.2.1, grant, subset, ?_⟩
  intro candidateSlot
  rw [stateEq]
  simp only [recordSpawn, installCopiedCapabilities]
  rw [slotsEq]
  simp only [true_and, resolvedFacts.2.2.2.2.2.1]
  rw [spacedCaps, addressSpaceCapabilities_slots, createdCaps]
  simp only [childEndpointSlot, childAddressSpaceSlot, true_and]
  by_cases zero : candidateSlot = 0
  · subst zero
    simp [addressSpaceCapabilities_nextIdentity, lifeCaps]
  · by_cases one : candidateSlot = 1
    · subst one; simp [addressSpaceRoot, lifeCaps]
    · simp [zero, one, lifeCaps, childEmpty]

/-- **The child's authority is exactly the inheritance set.**  The child has
a right over an object exactly when it is a requested right over the granted
endpoint's object, or a root right over its own new address space. -/
theorem spawn_child_authority (state : CompositeState) (request : SpawnRequest)
    (child addressSpace : Nat) (holds : RuntimeWellFormed state)
    (spawned : (spawn state request).result = .spawned child addressSpace) :
    ∃ slot endpoint,
      state.capabilities.slots (spawnParent state) slot = some endpoint ∧
      endpoint.kind = .endpoint ∧ endpoint.rights.grant = true ∧
      Capability.rightsSubset request.rights endpoint.rights = true ∧
      ∀ object right,
        Capability.HasAuthority (spawn state request).state.capabilities child object right ↔
          (object = endpoint.object ∧ Capability.permits request.rights right = true) ∨
            (object = addressSpace ∧
              Capability.permits VirtualMapping.addressSpaceRootRights right = true) := by
  obtain ⟨slot, endpoint, held, kind, grant, subset, slots⟩ :=
    spawn_child_capabilities state request child addressSpace holds spawned
  refine ⟨slot, endpoint, held, kind, grant, subset, fun object right => ?_⟩
  constructor
  · rintro ⟨candidateSlot, capability, found, sameObject, permitted⟩
    rw [slots] at found
    split at found
    · cases found
      exact Or.inl ⟨sameObject.symm, permitted⟩
    · split at found
      · cases found
        exact Or.inr ⟨sameObject.symm, permitted⟩
      · contradiction
  · rintro (⟨hobject, permitted⟩ | ⟨hobject, permitted⟩) <;> rw [hobject]
    · refine ⟨childEndpointSlot, ⟨endpoint.object, .endpoint, request.rights,
        state.capabilities.nextIdentity + 1, some endpoint.identity⟩, ?_, rfl, permitted⟩
      rw [slots]; simp
    · refine ⟨childAddressSpaceSlot, addressSpaceRoot state.capabilities addressSpace, ?_, rfl,
        permitted⟩
      rw [slots]; simp [childAddressSpaceSlot, childEndpointSlot]

/-- **No other subject's slots change**, the parent's included. -/
theorem spawn_other_slots_unchanged (state : CompositeState) (request : SpawnRequest)
    (child addressSpace : Nat) (holds : RuntimeWellFormed state)
    (spawned : (spawn state request).result = .spawned child addressSpace)
    (subject : Nat) (other : subject ≠ child) :
    (spawn state request).state.capabilities.slots subject = state.capabilities.slots subject := by
  obtain ⟨_, issued, _, _, resolution, _, _, _, copied, stateEq⟩ :=
    spawn_spawned_stages state request child addressSpace spawned
  obtain ⟨createdCaps, createdVm⟩ := issueSubject_capabilities state child issued
  have lifeCaps : state.lifecycle.capabilities = state.capabilities := holds.1.2.2.2.1.symm
  obtain ⟨_, _, slotsEq⟩ := Capability.copy_accepted_slots _ _ _ _ _ _ copied
  funext candidateSlot
  rw [stateEq]
  simp only [recordSpawn, installCopiedCapabilities]
  rw [slotsEq]
  simp only [other, false_and, ↓reduceIte]
  simp only [spawnSpaced, installCreatedAddressSpace, createdVirtualMemory_capabilities, createdVm]
  rw [addressSpaceCapabilities_slots, createdCaps]
  simp [other, lifeCaps]

/-- **No authority amplification.**  Every subject other than the child, the
parent included, holds exactly the authority it held before the spawn. -/
theorem spawn_no_authority_amplification (state : CompositeState) (request : SpawnRequest)
    (child addressSpace : Nat) (holds : RuntimeWellFormed state)
    (spawned : (spawn state request).result = .spawned child addressSpace)
    (subject : Nat) (other : subject ≠ child) (object : Nat) (right : Capability.Right) :
    Capability.HasAuthority (spawn state request).state.capabilities subject object right ↔
      Capability.HasAuthority state.capabilities subject object right := by
  have same := spawn_other_slots_unchanged state request child addressSpace holds spawned subject
    other
  simp only [Capability.HasAuthority, same]

/-- **The parent gains nothing.** -/
theorem spawn_parent_unchanged (state : CompositeState) (request : SpawnRequest)
    (child addressSpace : Nat) (holds : RuntimeWellFormed state)
    (spawned : (spawn state request).result = .spawned child addressSpace) :
    (spawn state request).state.capabilities.slots (spawnParent state) =
      state.capabilities.slots (spawnParent state) :=
  spawn_other_slots_unchanged state request child addressSpace holds spawned _
    (spawn_parent_ne_child state request child addressSpace holds spawned).1

/-! ## Registry, identity, and the empty start -/

/-- The spawn record: the spawn-authority table and its generation counter
are unchanged (the child receives no spawn capability), and the parent and
the address space are recorded for the child. -/
theorem spawn_registry (state : CompositeState) (request : SpawnRequest)
    (child addressSpace : Nat)
    (spawned : (spawn state request).result = .spawned child addressSpace) :
    (spawn state request).state.spawn.authority = state.spawn.authority ∧
      (spawn state request).state.spawn.nextGeneration = state.spawn.nextGeneration ∧
      (spawn state request).state.spawn.parent child = some (spawnParent state) ∧
      (spawn state request).state.spawn.addressSpace child = some addressSpace := by
  obtain ⟨_, issued, _, _, _, _, _, _, _, stateEq⟩ :=
    spawn_spawned_stages state request child addressSpace spawned
  obtain ⟨_, _, created, eq⟩ := issueSubject_issued state child issued
  rw [stateEq]
  simp [recordSpawn, installCopiedCapabilities, spawnSpaced, installCreatedAddressSpace, eq,
    applyOperation, created, installCreatedSubject]

/-- **Fresh identity.**  The child is the subject issuer's next identity: it
was never issued and never live, and it is above every subject identity in
the issued history, live or terminated.  Its address space is the object
issuer's next identity and was never issued under any object kind. -/
theorem spawn_fresh_identity (state : CompositeState) (request : SpawnRequest)
    (child addressSpace : Nat) (holds : ResourceRuntimeWellFormed state)
    (spawned : (spawn state request).result = .spawned child addressSpace) :
    child = state.issuers.subject.next ∧
      state.lifecycle.issuedSubjects child = false ∧
      state.lifecycle.capabilities.subjects child = false ∧
      (∀ earlier, state.lifecycle.issuedSubjects earlier = true → earlier < child) ∧
      addressSpace = state.issuers.object.next ∧
      BoundedLifecycle.issuedObject state.lifecycleRuntime addressSpace = false := by
  obtain ⟨_, issued, objectIssued, _⟩ :=
    spawn_spawned_stages state request child addressSpace spawned
  obtain ⟨identity, _, _, _⟩ := issueSubject_issued state child issued
  obtain ⟨before, live, _, _⟩ := issueSubject_fresh state child issued
  have object := (issueSubject_execution state child issued).2.2
  rw [object] at objectIssued
  obtain ⟨addressSame, _, _, _⟩ := LifetimeIssuer.issued_facts objectIssued
  have agreement := ((resourceWellFormed_iff state).1 holds.2).2.1
  refine ⟨identity, before, live, fun earlier issuedEarlier => ?_, addressSame, ?_⟩
  · rw [identity]; exact (agreement.1 earlier issuedEarlier).2
  · cases h : BoundedLifecycle.issuedObject state.lifecycleRuntime addressSpace with
    | false => rfl
    | true =>
        have := (agreement.2 addressSpace h).2
        rw [addressSame] at this
        exact absurd this (Nat.lt_irrefl _)

/-- The projections spawn never writes outside the capability registries,
the lifecycle registry, the new address space, the issuers, and the spawn
record. -/
theorem spawn_keeps (state : CompositeState) (request : SpawnRequest)
    (child addressSpace : Nat)
    (spawned : (spawn state request).result = .spawned child addressSpace) :
    (spawn state request).state.lifecycle.runnable = state.lifecycle.runnable ∧
      (spawn state request).state.lifecycle.current = state.lifecycle.current ∧
      (spawn state request).state.scheduler.ready = state.scheduler.ready ∧
      (spawn state request).state.resumable.contexts = state.resumable.contexts ∧
      (spawn state request).state.blockingContexts = state.blockingContexts ∧
      (spawn state request).state.deferredCancels = state.deferredCancels ∧
      (spawn state request).state.blockingIPC.waiterEndpoint = state.blockingIPC.waiterEndpoint ∧
      (spawn state request).state.blockingIPC.mailbox = state.blockingIPC.mailbox ∧
      (spawn state request).state.ipc.endpoints.mailbox = state.ipc.endpoints.mailbox ∧
      (spawn state request).state.transfers.pending = state.transfers.pending ∧
      (spawn state request).state.directPortIO = state.directPortIO ∧
      (spawn state request).state.dmaAccepted = state.dmaAccepted ∧
      (spawn state request).state.dmaObserved = state.dmaObserved ∧
      (spawn state request).state.frameBudgets = state.frameBudgets ∧
      (spawn state request).state.scrub = state.scrub ∧
      (spawn state request).state.virtualMemory.memory.allocator = state.virtualMemory.memory.allocator ∧
      (spawn state request).state.virtualMemory.memory.binding = state.virtualMemory.memory.binding ∧
      (spawn state request).state.lifecycle.issuedSubjects = SubjectLifecycle.setBool state.lifecycle.issuedSubjects
        child true := by
  obtain ⟨_, issued, _, _, _, _, _, _, _, stateEq⟩ :=
    spawn_spawned_stages state request child addressSpace spawned
  obtain ⟨_, _, created, eq⟩ := issueSubject_issued state child issued
  simp only [stateEq, recordSpawn, installCopiedCapabilities, spawnSpaced,
    installCreatedAddressSpace, createdVirtualMemory, VirtualMapping.clearAddressSpaceMappings, eq,
    applyOperation, created, installCreatedSubject, SubjectLifecycle.create_accepted_state _ _ created]
  simp

/-- **The child starts with nothing else.**  After an accepted spawn the
child has a zero frame budget; is not runnable, not current, and not queued;
has no saved, blocked, or deferred context; waits on no endpoint; has sent no
queued message and no sealed transfer; the device projections are exactly
the pre-state's; and its address space is owned by it and has no mappings. -/
theorem spawn_child_starts_empty (state : CompositeState) (request : SpawnRequest)
    (child addressSpace : Nat) (holds : ResourceRuntimeWellFormed state)
    (spawned : (spawn state request).result = .spawned child addressSpace) :
    (spawn state request).state.budgetLimit child = 0 ∧ (spawn state request).state.budgetUsage child = 0 ∧
      (spawn state request).state.lifecycle.runnable child = false ∧
      (spawn state request).state.lifecycle.current ≠ some child ∧
      child ∉ (spawn state request).state.scheduler.ready ∧
      ResumablePreemption.contextFor (spawn state request).state.resumable.contexts child = none ∧
      (spawn state request).state.blockingContexts child = none ∧
      (spawn state request).state.deferredCancels.retained child = none ∧
      (spawn state request).state.blockingIPC.waiterEndpoint child = none ∧
      (∀ object envelope, (spawn state request).state.ipc.endpoints.mailbox object = some envelope →
        envelope.sender ≠ child) ∧
      (∀ endpoint transfer, (spawn state request).state.transfers.pending endpoint = some transfer →
        transfer.sender ≠ child) ∧
      (spawn state request).state.directPortIO = state.directPortIO ∧ (spawn state request).state.dmaAccepted = state.dmaAccepted ∧
      (spawn state request).state.dmaObserved = state.dmaObserved ∧
      (spawn state request).state.virtualMemory.owner addressSpace = some child ∧
      ∀ page, (spawn state request).state.virtualMemory.mappings addressSpace page = none := by
  obtain ⟨runnable, current, ready, contexts, blocked, deferred, waiter, _, mailbox, pending,
    devices, accepted, observed, budgets, _, allocator, _, _⟩ :=
    spawn_keeps state request child addressSpace spawned
  obtain ⟨_, issued, _, _, _, _, _, _, _, stateEq⟩ :=
    spawn_spawned_stages state request child addressSpace spawned
  have runtime := holds.1.left
  have dead : state.lifecycle.capabilities.subjects child = false :=
    (issueSubject_fresh state child issued).2.1
  have unissued : state.lifecycle.issuedSubjects child = false :=
    (issueSubject_fresh state child issued).1
  have notLive : ∀ subject, state.lifecycle.capabilities.subjects subject = true →
      subject ≠ child := by
    intro subject live same; rw [same, dead] at live; contradiction
  obtain ⟨coherent, _, lifecycle, _, _, _, scheduler, _, resumable, transfers, _⟩ := runtime
  -- Budget.
  have budgetBefore : state.budgetLimit child = 0 := by
    have budget := ((resourceWellFormed_iff state).1 holds.2).2.2.1
    simp only [CompositeState.budgetLimit, FrameBudget.limit, FrameBudget.budgetFrames,
      CompositeState.budgetState, List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro frame _ committed
    have := (budget frame child (of_decide_eq_true committed)).2.2
    rw [unissued] at this; contradiction
  have budgetSame := budget_eq_of_allocator budgets allocator child
  have limit : (spawn state request).state.budgetLimit child = 0 := by rw [budgetSame.2, budgetBefore]
  refine ⟨limit, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, devices, accepted, observed, ?_, ?_⟩
  · have bound := FrameBudget.usage_le_limit (spawn state request).state.budgetState child
    simp only [CompositeState.budgetLimit, CompositeState.budgetUsage] at limit ⊢
    omega
  · rw [runnable]
    cases h : state.lifecycle.runnable child with
    | false => rfl
    | true => exact absurd (lifecycle.2.2.2.2.1 child h) (by rw [dead]; simp)
  · rw [current]; intro h
    exact absurd (lifecycle.2.2.2.2.2 child h) (by rw [dead]; simp)
  · rw [ready]; intro member
    have := (scheduler.2.2.2.1 child member).1
    rw [coherent.2.1, dead] at this; contradiction
  · rw [contexts]
    cases h : ResumablePreemption.contextFor state.resumable.contexts child with
    | none => rfl
    | some context =>
        have member : context ∈ state.resumable.contexts :=
          List.mem_of_find?_eq_some h
        have owner := ResumablePreemption.contextFor_owner _ _ _ h
        have valid := resumable.2.2.2.1 context member
        simp only [ResumablePreemption.validContext] at valid
        rw [owner] at valid
        have := valid.2.2.1
        rw [coherent.2.2.2.2.2.2.2.1, coherent.2.1, dead] at this; contradiction
  · rw [blocked]
    have deferredWF := holds.1.right
    cases h : state.blockingContexts child with
    | none => rfl
    | some saved =>
        have agree := deferredWF.1.1.2.1 child
        simp only [CompositeState.blockingIPCContext, h, Option.isSome_some] at agree
        cases w : state.blockingIPC.waiterEndpoint child with
        | none => rw [w] at agree; simp at agree
        | some endpoint =>
            have member := (deferredWF.1.1.1.2.2.2.2.1 endpoint child).2 w
            have := (deferredWF.1.1.1.2.2.1 endpoint child member).2.2.1
            simp only [CompositeState.blockingIPCContext] at this
            rw [holds.1.left.blockingLifecycle, dead] at this; contradiction
  · rw [deferred]
    cases h : state.deferredCancels.retained child with
    | none => rfl
    | some saved =>
        have := (holds.1.right.1.2.2 child saved h).2.2.1
        simp only [CompositeState.blockingIPCContext] at this
        rw [holds.1.left.blockingLifecycle, dead] at this; contradiction
  · rw [waiter]
    cases w : state.blockingIPC.waiterEndpoint child with
    | none => rfl
    | some endpoint =>
        have member := (holds.1.right.1.1.1.2.2.2.2.1 endpoint child).2 w
        have := (holds.1.right.1.1.1.2.2.1 endpoint child member).2.2.1
        simp only [CompositeState.blockingIPCContext] at this
        rw [holds.1.left.blockingLifecycle, dead] at this; contradiction
  · intro object envelope held
    rw [mailbox] at held
    exact notLive _ (coherent.2.2.2.2.2.2.2.2.2.2.2.2 object envelope held)
  · intro endpoint transfer held
    rw [pending] at held
    obtain ⟨⟨envelope, found, _, sender⟩, _⟩ := transfers.2 endpoint transfer held
    have mailboxSame : state.transfers.mailbox = state.ipc.endpoints.mailbox := by
      rw [coherent.2.2.2.2.2.2.2.2.2.1]
    rw [mailboxSame] at found
    rw [← sender]
    exact notLive _ (coherent.2.2.2.2.2.2.2.2.2.2.2.2 endpoint envelope found)
  · rw [stateEq]
    simp [recordSpawn, installCopiedCapabilities, spawnSpaced, installCreatedAddressSpace,
      createdVirtualMemory, VirtualMapping.clearAddressSpaceMappings, VirtualMapping.setOwner]
  · intro page
    rw [stateEq]
    simp [recordSpawn, installCopiedCapabilities, spawnSpaced, installCreatedAddressSpace,
      createdVirtualMemory, VirtualMapping.clearAddressSpaceMappings]

/-! ## The parent/child record is not authority -/

/-- Spawn authorization reads only the spawn-authority table and the parent's
liveness: the parent/child and address-space records never authorize. -/
theorem spawnAuthorize_ignores_records (state : CompositeState) (word : UInt64)
    (parent : Nat → Option Nat) (addressSpaces : Nat → Option Nat) :
    spawnAuthorize { state with spawn := { state.spawn with parent, addressSpace := addressSpaces } }
      word = spawnAuthorize state word := rfl

/-- No issued-lifecycle, authoritative, or invalidation operation reads the
spawn projection, so the parent/child record reaches no authorization outside
the spawn family. -/
theorem footprints_unread_spawn :
    (∀ operation : LifecycleOperation, operation.footprint.reads .spawn = false) ∧
      (∀ operation : AuthoritativeOperation, operation.footprint.reads .spawn = false) ∧
      (∀ operation : InvalidationOperation, operation.footprint.reads .spawn = false) := by
  refine ⟨fun operation => ?_, fun operation => ?_, fun operation => ?_⟩
  · cases operation; simp only [LifecycleOperation.footprint]; decide
  · cases operation with
    | ordinary operation => cases operation <;> simp only [AuthoritativeOperation.footprint,
        Operation.footprint] <;> decide
    | blocking operation =>
        cases operation <;>
          simp only [AuthoritativeOperation.footprint, CompositeBlockingOperation.footprint] <;>
          decide
    | drainDeferred _ => simp only [AuthoritativeOperation.footprint]; decide
  · cases operation <;> simp only [InvalidationOperation.footprint] <;> decide

/-! ## Stale parent handles -/

/-- An accepted spawn resolved the endpoint word in the parent's pre-state
capability space: the same word, against the pre-state, resolves to a live
endpoint capability with `grant` whose rights cover the requested rights. -/
theorem spawn_endpoint_resolves (state : CompositeState) (request : SpawnRequest)
    (child addressSpace : Nat) (holds : RuntimeWellFormed state)
    (spawned : (spawn state request).result = .spawned child addressSpace) :
    ∃ resolution : CapabilityHandle.Resolution,
      CapabilityHandle.resolveCurrent state.capabilities { caller := spawnParent state }
          request.endpointWord .endpoint = .ok resolution ∧
        resolution.capability.rights.grant = true ∧
        Capability.rightsSubset request.rights resolution.capability.rights = true := by
  obtain ⟨_, issued, _, _, resolution, resolved, grant, subset, _, _⟩ :=
    spawn_spawned_stages state request child addressSpace spawned
  obtain ⟨ne, _⟩ := spawn_parent_ne_child state request child addressSpace holds spawned
  obtain ⟨createdCaps, createdVm⟩ := issueSubject_capabilities state child issued
  have lifeCaps : state.lifecycle.capabilities = state.capabilities := holds.1.2.2.2.1.symm
  have spacedCaps : (spawnSpaced (issueSubject state).state child addressSpace).capabilities =
      addressSpaceCapabilities (issueSubject state).state.capabilities addressSpace child
        childAddressSpaceSlot := by
    simp [spawnSpaced, installCreatedAddressSpace, createdVirtualMemory_capabilities, createdVm]
  obtain ⟨decoded, live, inRange, held, identity, kind, objectLive, objectKind⟩ :=
    CapabilityHandle.resolveCurrent_sound _ _ _ _ _ resolved
  rw [spacedCaps] at live inRange held objectLive objectKind
  rw [addressSpaceCapabilities_slots, createdCaps] at held
  simp only [ne, false_and, ↓reduceIte, lifeCaps] at held
  have liveBefore : state.capabilities.subjects (spawnParent state) = true := by
    rw [addressSpaceCapabilities_subjects, createdCaps] at live
    simpa [SubjectLifecycle.setBool, ne, lifeCaps] using live
  have rangeBefore : Capability.slotInRange state.capabilities (spawnParent state)
      resolution.handle.slot = true := by
    simpa [Capability.slotInRange, createdCaps, lifeCaps] using inRange
  have objectBefore : state.capabilities.objects resolution.capability.object = true :=
    (holds.2.2.2.1.1 _ _ _ held).2.1
  have kindBefore : state.capabilities.kinds resolution.capability.object = some .endpoint := by
    rw [← kind]; exact (holds.2.2.2.1.1 _ _ _ held).2.2.1
  refine ⟨resolution, ?_, grant, subset⟩
  obtain ⟨handle, capability⟩ := resolution
  simp only at decoded held identity kind objectBefore kindBefore rangeBefore ⊢
  simp only [CapabilityHandle.resolveCurrent, decoded, CapabilityHandle.resolve, liveBefore,
    rangeBefore, held, identity, kind, objectBefore, kindBefore]
  simp

/-- **A stale parent handle rolls back.**  If the endpoint word does not
resolve in the parent's pre-state capability space (a malformed, stale,
revoked, wrong-kind, or out-of-range handle), spawn rejects and returns the
pre-state, even though the identity and address-space stages before it
succeeded on the candidate state. -/
theorem spawn_stale_endpoint_rejected (state : CompositeState) (request : SpawnRequest)
    (holds : RuntimeWellFormed state) (reason : CapabilityHandle.WordResolveDenial)
    (stale : CapabilityHandle.resolveCurrent state.capabilities { caller := spawnParent state }
      request.endpointWord .endpoint = .error reason) :
    (∃ error, (spawn state request).result = .rejected error) ∧
      (spawn state request).state = state := by
  cases result : (spawn state request).result with
  | rejected error => exact ⟨⟨error, rfl⟩, spawn_rejected_unchanged state request error result⟩
  | spawned child addressSpace =>
      obtain ⟨resolution, resolves, _⟩ :=
        spawn_endpoint_resolves state request child addressSpace holds result
      rw [stale] at resolves; contradiction

/-- A busy or halted latch rejects every spawn-family step with the state
unchanged. -/
theorem spawnGate_unchanged_of_not_running (state : CompositeState) (operation : SpawnOperation)
    (notRunning : state.execution.mode ≠ .running) :
    (spawnGate state operation).state = state := by
  cases hmode : state.execution.mode <;> simp_all [spawnGate]

end LeanOS.FailStop
