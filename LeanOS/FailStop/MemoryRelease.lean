import LeanOS.FailStop.MemoryAllocation

/-!
# Fail-stop composite: releasing a memory object

The counterpart of `LeanOS.FailStop.MemoryAllocation`.  `installReleasedMemory
state object frame` publishes the release of memory object `object`, bound to
`frame`, to every composite copy at once:

- every capability naming `object` is removed from every slot, and the
  object is retired (`MemoryLifecycle.retireCapabilities`, the registry
  `MemoryLifecycle.release` publishes);
- every mapping of `object`, in every address space, is removed from both the
  virtual-memory view and the lifecycle's mapping record, and the cached
  translations are flushed (the reviewed no-PCID full flush that subject
  cleanup also uses), so no stale translation can reach the frame;
- every pending sealed transfer carrying `object` is cancelled together with
  its envelope (`CapabilityTransfer.cancelWhere`);
- the allocator records `frame` as free and the binding of `object` is
  removed, while the issued history keeps `object`, so its identifier is
  never reused;
- the lifecycle drops every ownership record naming `object` or `frame`, and
  records `frame` as free.

`MemoryReleasable` names the two facts the proof needs: `object` is a memory
object, and the allocator attributes `frame` to it.
`installReleasedMemory_preserves_authoritativeRuntimeWellFormed` proves the
publication keeps `AuthoritativeRuntimeWellFormed`.  Scrubbing the frame is
part of the operation (`LeanOS.FailStop.MemoryOperations`).
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

/-! ## The released state -/

/-- Remove every mapping of `object`. -/
def stripObjectMappings (mappings : VirtualMapping.AddressSpaceId → VirtualMapping.VirtualPage →
    Option VirtualMapping.Mapping) (object : Nat) :
    VirtualMapping.AddressSpaceId → VirtualMapping.VirtualPage → Option VirtualMapping.Mapping :=
  fun space page => match mappings space page with
    | some mapping => if mapping.object = object then none else some mapping
    | none => none

/-- Drop every ownership record naming `object` or `frame`. -/
def releasedOwnership (owned : Capability.ObjectId → Option (Capability.SubjectId × Nat))
    (object frame : Nat) : Capability.ObjectId → Option (Capability.SubjectId × Nat) :=
  fun candidate => match owned candidate with
    | some ownership => if candidate = object ∨ ownership.2 = frame then none else some ownership
    | none => none

/-- The lifecycle after the release. -/
def releasedLifecycle (lifecycle : SubjectLifecycle.State) (capabilities : Capability.State)
    (object frame : Nat) : SubjectLifecycle.State :=
  { lifecycle with
    capabilities
    ownedMemory := releasedOwnership lifecycle.ownedMemory object frame
    mapping := fun space page => match lifecycle.mapping space page with
      | some mapped => if mapped = object then none else some mapped
      | none => none
    frameOwner := fun candidate => if candidate = frame then none else lifecycle.frameOwner candidate
    freeFrame := fun candidate => if candidate = frame then true else lifecycle.freeFrame candidate }

/-- The memory state after the release: the retired registry, the frame
free, the binding removed, the issued history kept. -/
def releasedMemory (memory : MemoryLifecycle.State) (capabilities : Capability.State)
    (object frame : Nat) : MemoryLifecycle.State :=
  { capabilities
    allocator := FrameAllocator.setStatus memory.allocator frame .free
    binding := MemoryLifecycle.setBinding memory.binding object none
    issued := memory.issued }

/-- Cancel every pending sealed transfer carrying `object`, over the endpoint
view with the retired registry. -/
def releasedTransfers (transfers : CapabilityTransfer.State) (endpoints : EndpointIPC.State)
    (object : Nat) : CapabilityTransfer.State :=
  CapabilityTransfer.cancelWhere { transfers with toEndpointState := endpoints }
    (fun transfer => transfer.object == object)

/-- The facts the release publication relies on. -/
structure MemoryReleasable (state : CompositeState) (object frame : Nat) : Prop where
  kind : state.capabilities.kinds object = some .memory
  frameOwned : state.virtualMemory.memory.allocator.status frame = .owned object

/-- Publish one released memory object to every composite copy. -/
def installReleasedMemory (state : CompositeState) (object frame : Nat) : CompositeState :=
  let capabilities := MemoryLifecycle.retireCapabilities state.capabilities object
  let lifecycle := releasedLifecycle state.lifecycle capabilities object frame
  let scheduler := { state.scheduler with lifecycle }
  let virtualMemory := { state.virtualMemory with
    memory := releasedMemory state.virtualMemory.memory capabilities object frame
    mappings := stripObjectMappings state.virtualMemory.mappings object }
  let transfers := releasedTransfers state.transfers
    { state.ipc.endpoints with capabilities } object
  { state with
    execution := { state.execution with
      core := { state.execution.core with lifecycle }
      returnAuthorityArmed := false }
    scheduler
    preemption := { state.preemption with scheduler }
    virtualMemory
    ipc := { state.ipc with virtualMemory, endpoints := transfers.toEndpointState }
    capabilities
    lifecycle
    resumable := { state.resumable with
      scheduler
      translations := { state.resumable.translations with
        virtual := virtualMemory
        entries := [] } }
    transfers
    blockingIPC := { state.blockingIPC with scheduler } }

/-! ## The retired registry -/

section Retired

variable (capabilities : Capability.State) (object : Nat)

@[simp] theorem retireCapabilities_subjects :
    (MemoryLifecycle.retireCapabilities capabilities object).subjects = capabilities.subjects :=
  rfl

@[simp] theorem retireCapabilities_nextIdentity :
    (MemoryLifecycle.retireCapabilities capabilities object).nextIdentity =
      capabilities.nextIdentity := rfl

@[simp] theorem retireCapabilities_derivations :
    (MemoryLifecycle.retireCapabilities capabilities object).derivations =
      capabilities.derivations := rfl

@[simp] theorem retireCapabilities_slotCapacity :
    (MemoryLifecycle.retireCapabilities capabilities object).slotCapacity =
      capabilities.slotCapacity := rfl

theorem retireCapabilities_objects (candidate : Nat) :
    (MemoryLifecycle.retireCapabilities capabilities object).objects candidate =
      if candidate = object then false else capabilities.objects candidate := by
  simp [MemoryLifecycle.retireCapabilities, MemoryLifecycle.setObject]

theorem retireCapabilities_kinds (candidate : Nat) :
    (MemoryLifecycle.retireCapabilities capabilities object).kinds candidate =
      if candidate = object then none else capabilities.kinds candidate := by
  simp [MemoryLifecycle.retireCapabilities]

theorem retireCapabilities_slots_some {subject slot : Nat} {capability : Capability.Capability} :
    (MemoryLifecycle.retireCapabilities capabilities object).slots subject slot =
        some capability ↔
      capabilities.slots subject slot = some capability ∧ capability.object ≠ object := by
  simp only [MemoryLifecycle.retireCapabilities]
  cases held : capabilities.slots subject slot with
  | none => simp
  | some found =>
      by_cases same : found.object = object
      · simp only [same, ↓reduceIte]
        constructor
        · intro h; cases h
        · rintro ⟨eq, ne⟩; cases eq; exact absurd same ne
      · simp only [same, ↓reduceIte, Option.some.injEq]
        constructor
        · rintro rfl; exact ⟨rfl, same⟩
        · rintro ⟨rfl, _⟩; rfl

theorem retireCapabilities_objects_of_ne {candidate : Nat} (ne : candidate ≠ object) :
    (MemoryLifecycle.retireCapabilities capabilities object).objects candidate =
      capabilities.objects candidate := by
  rw [retireCapabilities_objects]; simp [ne]

theorem retireCapabilities_kinds_of_ne {candidate : Nat} (ne : candidate ≠ object) :
    (MemoryLifecycle.retireCapabilities capabilities object).kinds candidate =
      capabilities.kinds candidate := by
  rw [retireCapabilities_kinds]; simp [ne]

/-- Authority over any other object survives the retirement. -/
theorem retireCapabilities_authority {subject candidate : Nat} {right : Capability.Right}
    (ne : candidate ≠ object) (holds : Capability.HasAuthority capabilities subject candidate right) :
    Capability.HasAuthority (MemoryLifecycle.retireCapabilities capabilities object) subject
      candidate right := by
  obtain ⟨slot, capability, held, sameObject, permitted⟩ := holds
  refine ⟨slot, capability, ?_, sameObject, permitted⟩
  rw [retireCapabilities_slots_some]
  exact ⟨held, by rw [sameObject]; exact ne⟩

/-- **The retired registry is well formed.** -/
theorem retireCapabilities_wellFormed (wellFormed : Capability.WellFormed capabilities) :
    Capability.WellFormed (MemoryLifecycle.retireCapabilities capabilities object) := by
  obtain ⟨hslots, hderivations, hunique, hspaces⟩ := wellFormed
  refine ⟨?_, hderivations, ?_, ?_⟩
  · intro subject slot capability held
    rw [retireCapabilities_slots_some] at held
    obtain ⟨held, ne⟩ := held
    obtain ⟨hsub, hlive, hkind, hrights, hid, hentry, hedge⟩ := hslots subject slot capability held
    exact ⟨hsub, by rw [retireCapabilities_objects_of_ne _ _ ne]; exact hlive,
      by rw [retireCapabilities_kinds_of_ne _ _ ne]; exact hkind, hrights, hid, hentry, hedge⟩
  · intro left leftSlot leftCap right rightSlot rightCap hleft hright hid
    rw [retireCapabilities_slots_some] at hleft hright
    exact hunique left leftSlot leftCap right rightSlot rightCap hleft.1 hright.1 hid
  · intro subject slot outside
    cases held : (MemoryLifecycle.retireCapabilities capabilities object).slots subject slot with
    | none => rfl
    | some capability =>
        rw [retireCapabilities_slots_some] at held
        rw [hspaces subject slot outside] at held
        cases held.1

end Retired

/-! ## Facts about the published state -/

@[simp] theorem installReleasedMemory_mode (state : CompositeState) object frame :
    (installReleasedMemory state object frame).execution.mode = state.execution.mode := rfl

@[simp] theorem installReleasedMemory_capabilities (state : CompositeState) object frame :
    (installReleasedMemory state object frame).capabilities =
      MemoryLifecycle.retireCapabilities state.capabilities object := rfl

/-- After the release `object` is dead, no slot names it, nothing maps it, no
pending transfer carries it, its binding is gone, its frame is free, and no
translation is cached. -/
theorem installReleasedMemory_released (state : CompositeState) object frame :
    (installReleasedMemory state object frame).capabilities.objects object = false ∧
      (∀ subject slot capability,
        (installReleasedMemory state object frame).capabilities.slots subject slot =
          some capability → capability.object ≠ object) ∧
      (∀ space page mapping,
        (installReleasedMemory state object frame).virtualMemory.mappings space page =
          some mapping → mapping.object ≠ object) ∧
      (∀ endpoint transfer,
        (installReleasedMemory state object frame).transfers.pending endpoint = some transfer →
          transfer.object ≠ object) ∧
      (installReleasedMemory state object frame).virtualMemory.memory.binding object = none ∧
      (installReleasedMemory state object frame).virtualMemory.memory.allocator.status frame =
        .free ∧
      (installReleasedMemory state object frame).resumable.translations.entries = [] := by
  refine ⟨by simp [installReleasedMemory, retireCapabilities_objects], ?_, ?_, ?_, ?_, ?_, rfl⟩
  · intro subject slot capability held
    exact ((retireCapabilities_slots_some _ _).1 held).2
  · intro space page mapping held
    simp only [installReleasedMemory, stripObjectMappings] at held
    split at held
    · split at held
      · cases held
      · next ne => cases held; exact ne
    · cases held
  · intro endpoint transfer pending
    simp only [installReleasedMemory, releasedTransfers, CapabilityTransfer.cancelWhere] at pending
    split at pending
    · next found _ =>
      split at pending
      · cases pending
      · next keep =>
        cases pending
        simpa using keep
    · cases pending
  · simp [installReleasedMemory, releasedMemory, MemoryLifecycle.setBinding]
  · simp [installReleasedMemory, releasedMemory, FrameAllocator.setStatus]

/-! ## Invariant preservation -/

theorem releasedTransfers_pending {transfers : CapabilityTransfer.State}
    {endpoints : EndpointIPC.State} {object endpoint : Nat} {transfer : CapabilityTransfer.Sealed}
    (pending : (releasedTransfers transfers endpoints object).pending endpoint = some transfer) :
    transfers.pending endpoint = some transfer ∧ transfer.object ≠ object ∧
      (releasedTransfers transfers endpoints object).mailbox endpoint =
        endpoints.mailbox endpoint := by
  simp only [releasedTransfers, CapabilityTransfer.cancelWhere] at pending ⊢
  split at pending
  · next found held =>
    split at pending
    · cases pending
    · next keep =>
      cases pending
      refine ⟨held, by simpa using keep, ?_⟩
      simp only [held, keep, Bool.false_eq_true, ↓reduceIte]
  · cases pending

theorem releasedTransfers_mailbox_some {transfers : CapabilityTransfer.State}
    {endpoints : EndpointIPC.State} {object endpoint : Nat} {envelope : EndpointIPC.Envelope}
    (held : (releasedTransfers transfers endpoints object).mailbox endpoint = some envelope) :
    endpoints.mailbox endpoint = some envelope := by
  simp only [releasedTransfers, CapabilityTransfer.cancelWhere] at held
  split at held
  · split at held
    · cases held
    · exact held
  · exact held

theorem releasedTransfers_mailbox_none {transfers : CapabilityTransfer.State}
    {endpoints : EndpointIPC.State} {object endpoint : Nat}
    (empty : endpoints.mailbox endpoint = none) :
    (releasedTransfers transfers endpoints object).mailbox endpoint = none := by
  simp only [releasedTransfers, CapabilityTransfer.cancelWhere]
  split
  · split
    · rfl
    · exact empty
  · exact empty

/-- **Release keeps the runtime invariant.** -/
theorem installReleasedMemory_preserves_runtimeWellFormed (state : CompositeState)
    (object frame : Nat) (holds : RuntimeWellFormed state)
    (releasable : MemoryReleasable state object frame) :
    RuntimeWellFormed (installReleasedMemory state object frame) := by
  obtain ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
    hscheduler, hpreemption, hresumable, htransfers, hhalted, _hlivePlan,
    hblockingCoherent, hdevices⟩ := holds
  obtain ⟨hexecutionCoherent, hschedulerCoherent, hpreemptionCoherent,
    hcapabilitiesCoherent, hvirtualCapabilitiesCoherent, hipcVirtualCoherent,
    hipcCapabilitiesCoherent, hresumableSchedulerCoherent,
    hresumableVirtualCoherent, htransfersCoherent, hauthorityCoherent,
    hdeadMailbox, hliveSender⟩ := hcoherent
  have vmCaps : state.virtualMemory.memory.capabilities = state.capabilities :=
    hvirtualCapabilitiesCoherent.trans hcapabilitiesCoherent.symm
  have lifeCaps : state.lifecycle.capabilities = state.capabilities :=
    hcapabilitiesCoherent.symm
  have endCaps : state.ipc.endpoints.capabilities = state.capabilities :=
    hipcCapabilitiesCoherent.trans hcapabilitiesCoherent.symm
  let retired := MemoryLifecycle.retireCapabilities state.capabilities object
  have retiredDef : retired = MemoryLifecycle.retireCapabilities state.capabilities object := rfl
  have hcaps' : Capability.WellFormed retired :=
    retireCapabilities_wellFormed state.capabilities object hcapabilities
  -- An object of another kind than memory is not `object`.
  have kindNe : ∀ candidate kind, state.capabilities.kinds candidate = some kind →
      kind ≠ .memory → candidate ≠ object := by
    intro candidate kind held ne same
    rw [same, releasable.kind] at held
    cases held; exact ne rfl
  have objectsKept : ∀ candidate, candidate ≠ object →
      retired.objects candidate = state.capabilities.objects candidate :=
    fun candidate ne => retireCapabilities_objects_of_ne state.capabilities object ne
  have kindsKept : ∀ candidate, candidate ≠ object →
      retired.kinds candidate = state.capabilities.kinds candidate :=
    fun candidate ne => retireCapabilities_kinds_of_ne state.capabilities object ne
  have retiredDead : ∀ candidate, retired.objects candidate ≠ true →
      candidate = object ∨ state.capabilities.objects candidate ≠ true := by
    intro candidate hdead
    by_cases same : candidate = object
    · exact Or.inl same
    · right; rw [← objectsKept candidate same]; exact hdead
  -- The lifecycle.
  let lifecycle' := releasedLifecycle state.lifecycle retired object frame
  have lifecycleDef : lifecycle' = releasedLifecycle state.lifecycle retired object frame := rfl
  have ownershipSome : ∀ candidate ownership,
      releasedOwnership state.lifecycle.ownedMemory object frame candidate = some ownership →
        state.lifecycle.ownedMemory candidate = some ownership ∧ candidate ≠ object ∧
          ownership.2 ≠ frame := by
    intro candidate ownership held
    simp only [releasedOwnership] at held
    split at held
    · next found heldOld =>
      split at held
      · cases held
      · next keep =>
        cases held
        simp only [not_or] at keep
        exact ⟨heldOld, keep.1, keep.2⟩
    · cases held
  have hlifecycle' : SubjectLifecycle.WellFormed lifecycle' := by
    obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hlifecycle
    rw [lifeCaps] at l1 l2 l3 l4 l5 l6
    refine ⟨l1, ?_, l3, l4, l5, l6⟩
    intro candidate subject owned held
    simp only [lifecycleDef, releasedLifecycle] at held ⊢
    obtain ⟨heldOld, _, ne⟩ := ownershipSome candidate (subject, owned) held
    obtain ⟨hlive, hframe, hfree⟩ := l2 candidate subject owned heldOld
    exact ⟨hlive, by simp [ne, hframe], by simp [ne, hfree]⟩
  -- The virtual memory.
  let vm' : VirtualMapping.State := { state.virtualMemory with
    memory := releasedMemory state.virtualMemory.memory retired object frame
    mappings := stripObjectMappings state.virtualMemory.mappings object }
  have vmDef : vm' = { state.virtualMemory with
      memory := releasedMemory state.virtualMemory.memory retired object frame
      mappings := stripObjectMappings state.virtualMemory.mappings object } := rfl
  have hvirtual' : VirtualMapping.LifecycleWellFormed vm' := by
    obtain ⟨⟨hownerLive, hmappings⟩, _, haddressSpaces, hownedAddressSpaces⟩ := hvirtual
    rw [vmCaps] at hownerLive hmappings haddressSpaces hownedAddressSpaces
    refine ⟨⟨?_, ?_⟩, hcaps', ?_, ?_⟩
    · intro space subject held
      exact hownerLive space subject held
    · intro space page mapping held
      change stripObjectMappings state.virtualMemory.mappings object space page = some mapping
        at held
      simp only [stripObjectMappings] at held
      cases heldOld : state.virtualMemory.mappings space page with
      | none => simp [heldOld] at held
      | some found =>
        simp only [heldOld] at held
        split at held
        · cases held
        · next ne =>
          have same : found = mapping := by simpa using held
          subst same
          obtain ⟨subject, mappedFrame, howner, hperm, hbinding, hframe, hread, hwrite⟩ :=
            hmappings space page found heldOld
          have frameNe : mappedFrame ≠ frame := by
            intro same
            rw [same] at hframe
            unfold FrameAllocator.IsOwnedBy at hframe
            rw [releasable.frameOwned] at hframe
            cases hframe; exact ne rfl
          refine ⟨subject, mappedFrame, howner, hperm, ?_, ?_, ?_, ?_⟩
          · simpa [vmDef, releasedMemory, MemoryLifecycle.setBinding, ne] using hbinding
          · simp only [vmDef, releasedMemory, FrameAllocator.IsOwnedBy, FrameAllocator.setStatus,
              frameNe, ↓reduceIte]
            exact hframe
          · intro p; exact retireCapabilities_authority _ _ ne (hread p)
          · intro p; exact retireCapabilities_authority _ _ ne (hwrite p)
    · intro space subject held
      obtain ⟨hlive, hkind, hissuedSpace, hissued, hrevoke⟩ := haddressSpaces space subject held
      have ne := kindNe space .addressSpace hkind (by decide)
      simp only [vmDef, releasedMemory]
      refine ⟨?_, ?_, hissuedSpace, hissued, retireCapabilities_authority _ _ ne hrevoke⟩
      · rw [objectsKept space ne]; exact hlive
      · rw [kindsKept space ne]; exact hkind
    · intro space hlive hkind
      change retired.objects space = true at hlive
      change retired.kinds space = some .addressSpace at hkind
      by_cases same : space = object
      · subst same
        rw [retiredDef, retireCapabilities_kinds] at hkind
        simp at hkind
      · rw [objectsKept space same] at hlive
        rw [kindsKept space same] at hkind
        exact hownedAddressSpaces space hlive hkind
  -- The endpoint view and the transfer store.
  let endpoints0 : EndpointIPC.State := { state.ipc.endpoints with capabilities := retired }
  have endpoints0Def : endpoints0 = { state.ipc.endpoints with capabilities := retired } := rfl
  let transfers' := releasedTransfers state.transfers endpoints0 object
  have transfersDef : transfers' = releasedTransfers state.transfers endpoints0 object := rfl
  have transfersCaps : transfers'.capabilities = retired := rfl
  have transfersHistory : transfers'.sendHistory = state.ipc.endpoints.sendHistory := rfl
  have transfersIssued : transfers'.issued = state.ipc.endpoints.issued := rfl
  have objectMailbox : state.ipc.endpoints.mailbox object = none := by
    cases held : state.ipc.endpoints.mailbox object with
    | none => rfl
    | some envelope =>
        have := (hipc.2.2.2.1 object envelope held).2.1
        rw [endCaps, releasable.kind] at this
        cases this
  have hendpoint' : EndpointIPC.WellFormed transfers'.toEndpointState := by
    obtain ⟨_, hissued, hmailbox, hdeadMail, hhistory⟩ := hipc.2
    rw [endCaps] at hissued hmailbox hdeadMail
    refine ⟨hcaps', ?_, ?_, ?_, by rw [transfersHistory]; exact hhistory⟩
    · intro candidate hlive hkind
      change retired.objects candidate = true at hlive
      change retired.kinds candidate = some .endpoint at hkind
      change state.ipc.endpoints.issued candidate = true
      have ne : candidate ≠ object := by
        intro same; rw [same, retiredDef, retireCapabilities_kinds] at hkind; simp at hkind
      rw [objectsKept candidate ne] at hlive
      rw [kindsKept candidate ne] at hkind
      exact hissued candidate hlive hkind
    · intro candidate envelope held
      have old := releasedTransfers_mailbox_some held
      obtain ⟨hlive, hkind, hend, hsent⟩ := hmailbox candidate envelope old
      have ne := kindNe candidate .endpoint hkind (by decide)
      refine ⟨?_, ?_, hend, ?_⟩
      · change retired.objects candidate = true
        rw [objectsKept candidate ne]; exact hlive
      · change retired.kinds candidate = some .endpoint
        rw [kindsKept candidate ne]; exact hkind
      · rw [transfersHistory]; exact hsent
    · intro candidate hdead
      change retired.objects candidate ≠ true at hdead
      apply releasedTransfers_mailbox_none
      rcases retiredDead candidate hdead with same | old
      · rw [same]; exact objectMailbox
      · exact hdeadMail candidate old
  have htransfers' : CapabilityTransfer.WellFormed transfers' := by
    refine ⟨hendpoint', ?_⟩
    intro endpoint transfer pending
    obtain ⟨pendingOld, ne, mailboxSame⟩ := releasedTransfers_pending pending
    obtain ⟨henvelope, hlive, hkind, hrights, hderivation, hparent, hparentIdentity,
      hidentity, habsent, huniquePending⟩ := htransfers.2 endpoint transfer pendingOld
    have transferCaps : state.transfers.capabilities = state.capabilities := by
      rw [htransfersCoherent]; exact endCaps
    rw [transferCaps] at hlive hkind hderivation hparent hidentity habsent
    refine ⟨?_, ?_, ?_, hrights, hderivation, hparent, hparentIdentity, hidentity, ?_, ?_⟩
    · obtain ⟨envelope, held, hend, hsender⟩ := henvelope
      refine ⟨envelope, ?_, hend, hsender⟩
      rw [mailboxSame]
      have : state.transfers.mailbox endpoint = state.ipc.endpoints.mailbox endpoint := by
        rw [htransfersCoherent]
      rw [← this]; exact held
    · change retired.objects transfer.object = true
      rw [objectsKept _ ne]; exact hlive
    · change retired.kinds transfer.object = some transfer.kind
      rw [kindsKept _ ne]; exact hkind
    · intro subject slot capability held
      change retired.slots subject slot = some capability at held
      rw [retiredDef, retireCapabilities_slots_some] at held
      exact habsent subject slot capability held.1
    · intro other otherTransfer otherPending same
      exact huniquePending other otherTransfer (releasedTransfers_pending otherPending).1 same
  have hipc' : IPCSyscall.WellFormed
      { state.ipc with virtualMemory := vm', endpoints := transfers'.toEndpointState } :=
    ⟨hvirtual', hendpoint'⟩
  -- Scheduler views.
  let scheduler' : Scheduler.State := { state.scheduler with lifecycle := lifecycle' }
  have schedulerDef : scheduler' = { state.scheduler with lifecycle := lifecycle' } := rfl
  have ownsSame : ∀ subject, Scheduler.ownsAddressSpace scheduler' subject =
      Scheduler.ownsAddressSpace state.scheduler subject := by
    intro subject
    simp [Scheduler.ownsAddressSpace, schedulerDef, lifecycleDef, releasedLifecycle,
      hschedulerCoherent]
  have hscheduler' : Scheduler.WellFormed scheduler' := by
    obtain ⟨_, hnodup, hcapacity, hready, hcurrent⟩ := hscheduler
    refine ⟨hlifecycle', hnodup, hcapacity, ?_, ?_⟩
    · intro subject member
      obtain ⟨hlive, hrunnable, howns⟩ := hready subject member
      rw [hschedulerCoherent, lifeCaps] at hlive
      rw [hschedulerCoherent] at hrunnable
      exact ⟨hlive, hrunnable, by rw [ownsSame]; exact howns⟩
    · intro subject selected
      have selectedOld : state.scheduler.lifecycle.current = some subject := by
        rw [hschedulerCoherent]; exact selected
      obtain ⟨hlive, hrunnable, howns, hnot⟩ := hcurrent subject selectedOld
      rw [hschedulerCoherent, lifeCaps] at hlive
      rw [hschedulerCoherent] at hrunnable
      exact ⟨hlive, hrunnable, by rw [ownsSame]; exact howns, hnot⟩
  have hpreemption' : Preemption.WellFormed { state.preemption with scheduler := scheduler' } :=
    ⟨hscheduler', hpreemption.2⟩
  have hresumable' : ResumablePreemption.WellFormed
      { state.resumable with
        scheduler := scheduler'
        translations := { state.resumable.translations with virtual := vm', entries := [] } } := by
    have activeOld := hresumable.2.2.2.2.2.2.1.2
    have ownerOld := hresumable.2.2.2.2.2.2.1.1
    obtain ⟨_, hcapacity, hunique, hvalid, habsent, hreadyAgree, _, _, hkindsAgree, _⟩ :=
      hresumable
    simp only [ResumablePreemption.validContext, ResumablePreemption.ReadyContextAgreement,
      ResumablePreemption.ResourceKindAgreement, hresumableSchedulerCoherent,
      hschedulerCoherent] at hvalid habsent hreadyAgree hkindsAgree
    rw [hresumableSchedulerCoherent, hschedulerCoherent, hresumableVirtualCoherent] at ownerOld
    refine ⟨hscheduler', hcapacity, hunique, ?_, habsent, hreadyAgree, ?_, ?_, ?_, ?_⟩
    · intro context member
      obtain ⟨hframe, hspace, hlive, hrunnable, howner⟩ := hvalid context member
      rw [lifeCaps] at hlive
      exact ⟨hframe, hspace, hlive, hrunnable, howner⟩
    · refine ⟨by simpa [vmDef, schedulerDef, lifecycleDef, releasedLifecycle] using ownerOld, ?_⟩
      rw [hresumableSchedulerCoherent, hschedulerCoherent] at activeOld
      exact activeOld
    · exact ⟨rfl, hvirtual'⟩
    · obtain ⟨hmem, hend⟩ := hkindsAgree
      refine ⟨?_, ?_⟩
      · intro candidate subject owned held
        change releasedOwnership state.lifecycle.ownedMemory object frame candidate =
          some (subject, owned) at held
        obtain ⟨heldOld, ne, _⟩ := ownershipSome candidate (subject, owned) held
        show retired.kinds candidate = some .memory
        rw [kindsKept candidate ne, ← lifeCaps]
        exact hmem candidate subject owned heldOld
      · intro candidate subject held
        change state.lifecycle.endpointOwner candidate = some subject at held
        have old := hend candidate subject held
        rw [lifeCaps] at old
        have ne := kindNe candidate .endpoint old (by decide)
        show retired.kinds candidate = some .endpoint
        rw [kindsKept candidate ne]; exact old
    · show ([] : List TLB.Entry).length ≤ TLB.capacity
      simp
  -- Publish: fold every composite copy onto the names above.
  have installed : installReleasedMemory state object frame =
      { state with
        execution := { state.execution with
          core := { state.execution.core with lifecycle := lifecycle' }
          returnAuthorityArmed := false }
        scheduler := scheduler'
        preemption := { state.preemption with scheduler := scheduler' }
        virtualMemory := vm'
        ipc := { state.ipc with virtualMemory := vm', endpoints := transfers'.toEndpointState }
        capabilities := retired
        lifecycle := lifecycle'
        resumable := { state.resumable with
          scheduler := scheduler'
          translations := { state.resumable.translations with virtual := vm', entries := [] } }
        transfers := transfers'
        blockingIPC := { state.blockingIPC with scheduler := scheduler' } } := rfl
  rw [installed]
  have hexecution' : WellFormed
      { state.execution with
        core := { state.execution.core with lifecycle := lifecycle' }
        returnAuthorityArmed := false } := by
    obtain ⟨_, _, hmodeWellFormed⟩ := hexecution
    exact ⟨hlifecycle', by simp, hmodeWellFormed⟩
  refine ⟨?_, hexecution', hlifecycle', hcaps', hvirtual', hipc', hscheduler', hpreemption',
    hresumable', htransfers', hhalted, by simp, ⟨rfl, rfl⟩, hdevices⟩
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro subject current
    exact hauthorityCoherent subject current
  · intro candidate hdead
    change transfers'.mailbox candidate = none
    apply releasedTransfers_mailbox_none
    rcases retiredDead candidate hdead with same | old
    · rw [same]; exact objectMailbox
    · exact hdeadMailbox candidate (by rw [lifeCaps]; exact old)
  · intro candidate envelope held
    change transfers'.mailbox candidate = some envelope at held
    have := hliveSender candidate envelope (releasedTransfers_mailbox_some held)
    rw [lifeCaps] at this
    exact this

/-- **Release keeps the authoritative runtime invariant**, including the
blocking store, its saved contexts, the deferred cancellations, and
invalidation publication. -/
theorem installReleasedMemory_preserves_authoritativeRuntimeWellFormed
    (state : CompositeState) (object frame : Nat)
    (holds : AuthoritativeRuntimeWellFormed state)
    (releasable : MemoryReleasable state object frame) :
    AuthoritativeRuntimeWellFormed (installReleasedMemory state object frame) := by
  have runtime := installReleasedMemory_preserves_runtimeWellFormed state object frame
    holds.left releasable
  have coherent := holds.left.1
  have blockingScheduler : state.blockingIPC.scheduler = state.scheduler :=
    holds.left.blockingScheduler
  have schedLife : state.scheduler.lifecycle = state.lifecycle := coherent.2.1
  have lifeCaps : state.lifecycle.capabilities = state.capabilities := coherent.2.2.2.1.symm
  have kindNe : ∀ candidate kind, state.capabilities.kinds candidate = some kind →
      kind ≠ .memory → candidate ≠ object := by
    intro candidate kind held ne same
    rw [same, releasable.kind] at held
    cases held; exact ne rfl
  have ownsSame : ∀ subject,
      Scheduler.ownsAddressSpace
          { state.scheduler with
            lifecycle := releasedLifecycle state.lifecycle
              (MemoryLifecycle.retireCapabilities state.capabilities object) object frame }
          subject =
        Scheduler.ownsAddressSpace state.blockingIPC.scheduler subject := by
    intro subject
    simp [Scheduler.ownsAddressSpace, releasedLifecycle, blockingScheduler, schedLife]
  obtain ⟨⟨⟨hipc, hctx⟩, hblockedDeferred, hretained⟩, hblockedResumable, hdeferredResumable⟩ :=
    holds.right
  refine ⟨runtime, ⟨⟨⟨?_, hctx⟩, hblockedDeferred, ?_⟩, hblockedResumable, hdeferredResumable⟩,
    holds.publication⟩
  · obtain ⟨_, hqueue, hwaiters, hunique, hiff, hmail, _⟩ := hipc
    simp only [CompositeState.blockingIPCContext, installReleasedMemory]
    refine ⟨?_, hqueue, ?_, hunique, hiff, ?_, ?_⟩
    · have := runtime.2.2.2.2.2.2.1
      simpa [installReleasedMemory, releasedLifecycle] using this
    · intro endpoint subject member
      obtain ⟨hlive, ⟨authSlot, cap, held, sameObject, kind, receive, authLive⟩, hsubject,
        hrunnable, howns, hcurrent, hready⟩ := hwaiters endpoint subject member
      simp only [CompositeState.blockingIPCContext, blockingScheduler, schedLife, lifeCaps]
        at hlive held authLive hsubject hrunnable hcurrent hready
      have capKind : state.capabilities.kinds cap.object = some .endpoint := by
        have := (holds.left.2.2.2.1.1 _ _ _ held).2.2.1
        rw [kind] at this; exact this
      have ne := kindNe cap.object .endpoint capKind (by decide)
      have endpointNe : endpoint ≠ object := by rw [← sameObject]; exact ne
      refine ⟨?_, ⟨authSlot, cap, ?_, sameObject, kind, receive, ?_⟩,
        hsubject, hrunnable, ?_, hcurrent, by simpa [blockingScheduler] using hready⟩
      · show (MemoryLifecycle.retireCapabilities state.capabilities object).objects endpoint = true
        rw [retireCapabilities_objects_of_ne _ _ endpointNe]; exact hlive
      · show (MemoryLifecycle.retireCapabilities state.capabilities object).slots subject authSlot =
          some cap
        rw [retireCapabilities_slots_some]; exact ⟨held, ne⟩
      · show (MemoryLifecycle.retireCapabilities state.capabilities object).objects endpoint =
          true
        rw [retireCapabilities_objects_of_ne _ _ endpointNe]; exact authLive
      · simp only [releasedLifecycle] at ownsSame ⊢
        rw [ownsSame]; exact howns
    · intro endpoint envelope held
      obtain ⟨hlive0, hkind0, hend, hempty⟩ := hmail endpoint envelope held
      have hlive : state.capabilities.objects endpoint = true := by
        simpa [CompositeState.blockingIPCContext, blockingScheduler, schedLife, lifeCaps]
          using hlive0
      have hkind : state.capabilities.kinds endpoint = some .endpoint := by
        simpa [CompositeState.blockingIPCContext, blockingScheduler, schedLife, lifeCaps]
          using hkind0
      have ne := kindNe endpoint .endpoint hkind (by decide)
      refine ⟨?_, ?_, hend, hempty⟩
      · show (MemoryLifecycle.retireCapabilities state.capabilities object).objects endpoint =
          true
        rw [retireCapabilities_objects_of_ne _ _ ne]; exact hlive
      · show (MemoryLifecycle.retireCapabilities state.capabilities object).kinds endpoint =
          some .endpoint
        rw [retireCapabilities_kinds_of_ne _ _ ne]; exact hkind
    · have := runtime.2.2.2.1
      simpa [installReleasedMemory, releasedLifecycle] using this
  · intro subject saved retained
    obtain ⟨hvalid, hwaiter, hsubject, hrunnable, hcurrent, hready, howns⟩ :=
      hretained subject saved retained
    simp only [CompositeState.blockingIPCContext, blockingScheduler, schedLife, lifeCaps]
      at hsubject hrunnable hcurrent hready
    simp only [CompositeState.blockingIPCContext, installReleasedMemory]
    refine ⟨hvalid, hwaiter, hsubject, hrunnable, hcurrent,
      by simpa [blockingScheduler] using hready, ?_⟩
    simp only [releasedLifecycle] at ownsSame ⊢
    rw [ownsSame]; exact howns

end LeanOS.FailStop
