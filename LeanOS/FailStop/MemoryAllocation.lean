import LeanOS.FailStop.SpawnAddressSpace

/-!
# Fail-stop composite: publishing a budget-charged memory object

Gate item 1 of ADR 0010 asks that the composite own resource budgets, and
#490's accounting left one gap: no composite step changed a subject's frame
usage, because no composite step allocated or released memory.  This module
adds the composite publication of one memory-object allocation and proves it
keeps the whole runtime invariant.  The operation that draws the identity
from the object issuer, charges the frame to the acting subject's budget, and
scrubs the frame is `LeanOS.FailStop.MemoryOperations`.

`installAllocatedMemory state object owner slot frame` publishes exactly the
memory state `FrameBudget.allocate` produces (`allocatedMemory`) to every copy
the composite keeps of it:

- the capability registry gains the live memory object `object` and its root
  capability with every memory right in `owner`'s `slot`
  (`allocatedCapabilities`, the registry `MemoryLifecycle.allocate` installs);
- the virtual-memory view records `object` as issued and bound to `frame`,
  and the allocator records `frame` as owned by `object`;
- the lifecycle records the ownership (`ownedMemory`, `frameOwner`,
  `freeFrame`), as `SubjectLifecycle.WellFormed` requires of owned memory;
- the endpoint view's issued history records `object` as well.

`MemoryAllocatable` names the preconditions.  The allocator frame must be
free, and the lifecycle must not attribute it to anyone, so no existing
ownership record names it.
`installAllocatedMemory_preserves_authoritativeRuntimeWellFormed` proves the
publication keeps `AuthoritativeRuntimeWellFormed`.
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

/-! ## The allocated state -/

/-- The capability registry after allocating memory object `object` with its
root capability in `owner`'s `slot`: exactly the registry
`MemoryLifecycle.allocate` and `FrameBudget.allocate` install. -/
def allocatedCapabilities (capabilities : Capability.State) (object owner slot : Nat) :
    Capability.State :=
  Capability.installRoot (MemoryLifecycle.activateObject capabilities object) owner slot object
    .memory Capability.allRights

/-- The memory state `FrameBudget.allocate` produces on acceptance, over a
given capability registry. -/
def allocatedMemory (memory : MemoryLifecycle.State) (capabilities : Capability.State)
    (object frame : Nat) : MemoryLifecycle.State :=
  { capabilities
    allocator := FrameAllocator.setStatus memory.allocator frame (.owned object)
    binding := MemoryLifecycle.setBinding memory.binding object (some frame)
    issued := MemoryLifecycle.setIssued memory.issued object }

/-- The lifecycle after the allocation: the new registry, and the ownership
of `object` and `frame` by `owner`. -/
def allocatedLifecycle (lifecycle : SubjectLifecycle.State) (capabilities : Capability.State)
    (object owner frame : Nat) : SubjectLifecycle.State :=
  { lifecycle with
    capabilities
    ownedMemory := fun candidate =>
      if candidate = object then some (owner, frame) else lifecycle.ownedMemory candidate
    frameOwner := fun candidate =>
      if candidate = frame then some owner else lifecycle.frameOwner candidate
    freeFrame := fun candidate =>
      if candidate = frame then false else lifecycle.freeFrame candidate }

/-- The preconditions under which the composite publishes memory object
`object` for `owner` in `slot`, backed by `frame`.  The first five are the
registry checks of `MemoryLifecycle.allocate`; then the identity is unused
under every kind, the frame is free, and no lifecycle record names the
identity as an endpoint or the frame as owned. -/
structure MemoryAllocatable (state : CompositeState) (object owner slot frame : Nat) :
    Prop where
  ownerLive : state.capabilities.subjects owner = true
  slotBounded : slot < CapabilityHandle.slotReserved
  slotInRange : Capability.slotInRange state.capabilities owner slot = true
  generation : state.capabilities.nextIdentity ≠ 0 ∧
    state.capabilities.nextIdentity < CapabilityHandle.generationReserved
  slotEmpty : state.capabilities.slots owner slot = none
  dead : state.capabilities.objects object = false
  endpointFree : state.lifecycle.endpointOwner object = none
  frameFree : state.virtualMemory.memory.allocator.status frame = .free
  frameUnowned : state.lifecycle.frameOwner frame = none

/-- Publish one allocated memory object to every composite copy. -/
def installAllocatedMemory (state : CompositeState) (object owner slot frame : Nat) :
    CompositeState :=
  let capabilities := allocatedCapabilities state.capabilities object owner slot
  let lifecycle := allocatedLifecycle state.lifecycle capabilities object owner frame
  let scheduler := { state.scheduler with lifecycle }
  let virtualMemory := { state.virtualMemory with
    memory := allocatedMemory state.virtualMemory.memory capabilities object frame }
  let endpoints := { state.ipc.endpoints with
    capabilities
    issued := MemoryLifecycle.setIssued state.ipc.endpoints.issued object }
  { state with
    execution := { state.execution with
      core := { state.execution.core with lifecycle }
      returnAuthorityArmed := false }
    scheduler
    preemption := { state.preemption with scheduler }
    virtualMemory
    ipc := { state.ipc with virtualMemory, endpoints }
    capabilities
    lifecycle
    resumable := { state.resumable with
      scheduler
      translations := { state.resumable.translations with virtual := virtualMemory } }
    transfers := { state.transfers with toEndpointState := endpoints }
    blockingIPC := { state.blockingIPC with scheduler } }

/-! ## The allocated registry -/

section Registry

variable (capabilities : Capability.State) (object owner slot : Nat)

/-- The root capability installed for the new memory object. -/
def memoryRoot : Capability.Capability :=
  { object, kind := .memory, rights := Capability.allRights,
    identity := capabilities.nextIdentity, parent := none }

@[simp] theorem allocatedCapabilities_subjects :
    (allocatedCapabilities capabilities object owner slot).subjects = capabilities.subjects := rfl

@[simp] theorem allocatedCapabilities_slotCapacity :
    (allocatedCapabilities capabilities object owner slot).slotCapacity =
      capabilities.slotCapacity := rfl

@[simp] theorem allocatedCapabilities_nextIdentity :
    (allocatedCapabilities capabilities object owner slot).nextIdentity =
      capabilities.nextIdentity + 1 := rfl

theorem allocatedCapabilities_objects (candidate : Nat) :
    (allocatedCapabilities capabilities object owner slot).objects candidate =
      if candidate = object then true else capabilities.objects candidate := by
  simp [allocatedCapabilities, Capability.installRoot, Capability.install,
    MemoryLifecycle.activateObject, MemoryLifecycle.setObject]

theorem allocatedCapabilities_kinds (candidate : Nat) :
    (allocatedCapabilities capabilities object owner slot).kinds candidate =
      if candidate = object then some .memory else capabilities.kinds candidate := by
  simp [allocatedCapabilities, Capability.installRoot, Capability.install,
    MemoryLifecycle.activateObject]

theorem allocatedCapabilities_slots (subject candidateSlot : Nat) :
    (allocatedCapabilities capabilities object owner slot).slots subject candidateSlot =
      if subject = owner ∧ candidateSlot = slot then some (memoryRoot capabilities object)
      else capabilities.slots subject candidateSlot := by
  simp [allocatedCapabilities, Capability.installRoot, Capability.install,
    MemoryLifecycle.activateObject, memoryRoot]

theorem allocatedCapabilities_derivations (identity : Nat) :
    (allocatedCapabilities capabilities object owner slot).derivations identity =
      if identity = capabilities.nextIdentity then
        some (none, object, .memory, Capability.allRights)
      else capabilities.derivations identity := rfl

theorem allocatedCapabilities_objects_mono {candidate : Nat}
    (live : capabilities.objects candidate = true) :
    (allocatedCapabilities capabilities object owner slot).objects candidate = true := by
  rw [allocatedCapabilities_objects]; split <;> simp_all

theorem allocatedCapabilities_slots_mono
    (empty : capabilities.slots owner slot = none) {subject candidateSlot : Nat}
    {capability : Capability.Capability}
    (held : capabilities.slots subject candidateSlot = some capability) :
    (allocatedCapabilities capabilities object owner slot).slots subject candidateSlot =
      some capability := by
  rw [allocatedCapabilities_slots]
  split
  · next target => obtain ⟨rfl, rfl⟩ := target; rw [empty] at held; contradiction
  · exact held

theorem allocatedCapabilities_authority_mono
    (empty : capabilities.slots owner slot = none) {subject candidate : Nat}
    {right : Capability.Right}
    (holds : Capability.HasAuthority capabilities subject candidate right) :
    Capability.HasAuthority (allocatedCapabilities capabilities object owner slot)
      subject candidate right := by
  obtain ⟨candidateSlot, capability, held, sameObject, permitted⟩ := holds
  exact ⟨candidateSlot, capability,
    allocatedCapabilities_slots_mono capabilities object owner slot empty held,
    sameObject, permitted⟩

theorem allocatedCapabilities_kinds_of_ne {candidate : Nat} (ne : candidate ≠ object) :
    (allocatedCapabilities capabilities object owner slot).kinds candidate =
      capabilities.kinds candidate := by
  rw [allocatedCapabilities_kinds]; simp [ne]

theorem allocatedCapabilities_objects_of_ne {candidate : Nat} (ne : candidate ≠ object) :
    (allocatedCapabilities capabilities object owner slot).objects candidate =
      capabilities.objects candidate := by
  rw [allocatedCapabilities_objects]; simp [ne]

theorem allocatedCapabilities_derivations_of_lt {identity : Nat}
    (lt : identity < capabilities.nextIdentity) :
    (allocatedCapabilities capabilities object owner slot).derivations identity =
      capabilities.derivations identity := by
  rw [allocatedCapabilities_derivations]; simp [Nat.ne_of_lt lt]

/-- **The allocated registry is well formed.**  Installing a root memory
capability for a dead object into an empty in-range slot of a live subject
keeps `Capability.WellFormed`. -/
theorem allocatedCapabilities_wellFormed (wellFormed : Capability.WellFormed capabilities)
    (ownerLive : capabilities.subjects owner = true)
    (inRange : Capability.slotInRange capabilities owner slot = true)
    (empty : capabilities.slots owner slot = none)
    (dead : capabilities.objects object = false) :
    Capability.WellFormed (allocatedCapabilities capabilities object owner slot) := by
  obtain ⟨hslots, hderivations, hunique, hspaces⟩ := wellFormed
  have objectNe : ∀ subject candidateSlot capability,
      capabilities.slots subject candidateSlot = some capability →
        capability.object ≠ object := by
    intro subject candidateSlot capability held same
    have := (hslots subject candidateSlot capability held).2.1
    rw [same, dead] at this; contradiction
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro subject candidateSlot capability held
    rw [allocatedCapabilities_slots] at held
    split at held
    · next target =>
      obtain ⟨rfl, rfl⟩ := target
      cases held
      refine ⟨ownerLive, ?_, ?_, by simp [memoryRoot, Capability.rightsValid, Capability.allRights,
        Capability.nonemptyRights], Nat.lt_succ_self _, ?_, trivial⟩
      · simp [allocatedCapabilities_objects, memoryRoot]
      · simp [allocatedCapabilities_kinds, memoryRoot]
      · simp [allocatedCapabilities_derivations, memoryRoot]
    · obtain ⟨hsub, hlive, hkind, hrights, hid, hentry, hedge⟩ :=
        hslots subject candidateSlot capability held
      have ne := objectNe subject candidateSlot capability held
      refine ⟨hsub, ?_, ?_, hrights, Nat.lt_succ_of_lt hid, ?_, ?_⟩
      · rw [allocatedCapabilities_objects_of_ne _ _ _ _ ne]; exact hlive
      · rw [allocatedCapabilities_kinds_of_ne _ _ _ _ ne]; exact hkind
      · rw [allocatedCapabilities_derivations_of_lt _ _ _ _ hid]; exact hentry
      · cases hp : capability.parent with
        | none => trivial
        | some parentIdentity =>
            rw [hp] at hedge
            obtain ⟨hparent, pp, pr, hpentry, hsubset⟩ := hedge
            refine ⟨hparent, pp, pr, ?_, hsubset⟩
            rw [allocatedCapabilities_derivations_of_lt _ _ _ _ (Nat.lt_trans hparent hid)]
            exact hpentry
  · intro identity parent candidate kind rights hentry
    rw [allocatedCapabilities_derivations] at hentry
    split at hentry
    · next same =>
      subst same
      cases hentry
      exact ⟨Nat.lt_succ_self _, trivial⟩
    · have old := hderivations identity parent candidate kind rights hentry
      refine ⟨Nat.lt_succ_of_lt old.1, ?_⟩
      cases parent with
      | none => trivial
      | some parentIdentity =>
          obtain ⟨hparent, pp, pr, hpentry, hsubset⟩ := old.2
          refine ⟨hparent, pp, pr, ?_, hsubset⟩
          rw [allocatedCapabilities_derivations_of_lt _ _ _ _ (Nat.lt_trans hparent old.1)]
          exact hpentry
  · intro left leftSlot leftCap right rightSlot rightCap hleft hright hid
    rw [allocatedCapabilities_slots] at hleft hright
    split at hleft
    · next hl =>
      split at hright
      · next hr => exact ⟨hl.1.trans hr.1.symm, hl.2.trans hr.2.symm⟩
      · cases hleft
        have := (hslots right rightSlot rightCap hright).2.2.2.2.1
        simp only [memoryRoot] at hid
        omega
    · split at hright
      · cases hright
        have := (hslots left leftSlot leftCap hleft).2.2.2.2.1
        simp only [memoryRoot] at hid
        omega
      · exact hunique left leftSlot leftCap right rightSlot rightCap hleft hright hid
  · intro subject candidateSlot outside
    rw [allocatedCapabilities_slots]
    split
    · next target =>
      obtain ⟨rfl, rfl⟩ := target
      have lt : candidateSlot < capabilities.slotCapacity subject := by
        unfold Capability.slotInRange at inRange; simpa using inRange
      have ge : capabilities.slotCapacity subject ≤ candidateSlot := outside
      omega
    · exact hspaces subject candidateSlot outside

end Registry

/-! ## Facts about the published state -/

@[simp] theorem installAllocatedMemory_mode (state : CompositeState) object owner slot frame :
    (installAllocatedMemory state object owner slot frame).execution.mode =
      state.execution.mode := rfl

@[simp] theorem installAllocatedMemory_capabilities (state : CompositeState)
    object owner slot frame :
    (installAllocatedMemory state object owner slot frame).capabilities =
      allocatedCapabilities state.capabilities object owner slot := rfl

/-- The new object is bound to `frame`, which the allocator and the lifecycle
attribute to it and to `owner`. -/
theorem installAllocatedMemory_owned (state : CompositeState) object owner slot frame :
    (installAllocatedMemory state object owner slot frame).virtualMemory.memory.binding object =
        some frame ∧
      (installAllocatedMemory state object owner slot frame).virtualMemory.memory.allocator.status
        frame = .owned object ∧
      (installAllocatedMemory state object owner slot frame).lifecycle.ownedMemory object =
        some (owner, frame) ∧
      (installAllocatedMemory state object owner slot frame).virtualMemory.memory.issued object =
        true := by
  simp [installAllocatedMemory, allocatedMemory, allocatedLifecycle, FrameAllocator.setStatus,
    MemoryLifecycle.setBinding, MemoryLifecycle.setIssued]

/-! ## Invariant preservation -/

/-- **Allocation keeps the runtime invariant.** -/
theorem installAllocatedMemory_preserves_runtimeWellFormed (state : CompositeState)
    (object owner slot frame : Nat) (holds : RuntimeWellFormed state)
    (allocatable : MemoryAllocatable state object owner slot frame) :
    RuntimeWellFormed (installAllocatedMemory state object owner slot frame) := by
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
  let created := allocatedCapabilities state.capabilities object owner slot
  have createdDef : created = allocatedCapabilities state.capabilities object owner slot := rfl
  have empty := allocatable.slotEmpty
  have dead := allocatable.dead
  have hcaps' : Capability.WellFormed created :=
    allocatedCapabilities_wellFormed state.capabilities object owner slot hcapabilities
      allocatable.ownerLive allocatable.slotInRange empty dead
  have objMono : ∀ candidate, state.capabilities.objects candidate = true →
      created.objects candidate = true :=
    fun candidate live => allocatedCapabilities_objects_mono state.capabilities object owner slot
      live
  have liveNe : ∀ candidate, state.capabilities.objects candidate = true →
      candidate ≠ object := by
    intro candidate live same; rw [same, dead] at live; contradiction
  have kindsLive : ∀ candidate, state.capabilities.objects candidate = true →
      created.kinds candidate = state.capabilities.kinds candidate :=
    fun candidate live => allocatedCapabilities_kinds_of_ne state.capabilities object owner slot
      (liveNe candidate live)
  have authMono : ∀ subject candidate right,
      Capability.HasAuthority state.capabilities subject candidate right →
        Capability.HasAuthority created subject candidate right :=
    fun _ _ _ h => allocatedCapabilities_authority_mono state.capabilities object owner slot
      empty h
  have deadOld : ∀ candidate, created.objects candidate ≠ true →
      state.capabilities.objects candidate ≠ true :=
    fun candidate hdead hlive => hdead (objMono candidate hlive)
  -- The lifecycle.
  let lifecycle' := allocatedLifecycle state.lifecycle created object owner frame
  have lifecycleDef : lifecycle' = allocatedLifecycle state.lifecycle created object owner frame :=
    rfl
  have hlifecycle' : SubjectLifecycle.WellFormed lifecycle' := by
    obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hlifecycle
    rw [lifeCaps] at l1 l2 l3 l4 l5 l6
    refine ⟨l1, ?_, l3, l4, l5, l6⟩
    intro candidate subject owned held
    simp only [lifecycleDef, allocatedLifecycle] at held ⊢
    split at held
    · cases held
      exact ⟨allocatable.ownerLive, by simp, by simp⟩
    · obtain ⟨hlive, hframe, hfree⟩ := l2 candidate subject owned held
      have ne : owned ≠ frame := by
        intro same; rw [same, allocatable.frameUnowned] at hframe; contradiction
      exact ⟨hlive, by simp [ne, hframe], by simp [ne, hfree]⟩
  -- The virtual memory.
  let vm' : VirtualMapping.State := { state.virtualMemory with
    memory := allocatedMemory state.virtualMemory.memory created object frame }
  have vmDef : vm' = { state.virtualMemory with
      memory := allocatedMemory state.virtualMemory.memory created object frame } := rfl
  have hvirtual' : VirtualMapping.LifecycleWellFormed vm' := by
    obtain ⟨⟨hownerLive, hmappings⟩, _, haddressSpaces, hownedAddressSpaces⟩ := hvirtual
    rw [vmCaps] at hownerLive hmappings haddressSpaces hownedAddressSpaces
    refine ⟨⟨?_, ?_⟩, hcaps', ?_, ?_⟩
    · intro space subject held
      exact hownerLive space subject held
    · intro space page mapping held
      obtain ⟨subject, mappedFrame, howner, hperm, hbinding, hframe, hread, hwrite⟩ :=
        hmappings space page mapping held
      have frameNe : mappedFrame ≠ frame := by
        intro same
        rw [same] at hframe
        unfold FrameAllocator.IsOwnedBy at hframe
        rw [allocatable.frameFree] at hframe
        contradiction
      refine ⟨subject, mappedFrame, howner, hperm, ?_, ?_, ?_, ?_⟩
      · by_cases same : mapping.object = object
        · rw [same] at hbinding hframe
          exfalso
          obtain ⟨_, owned⟩ : True ∧ FrameAllocator.IsOwnedBy
              state.virtualMemory.memory.allocator mappedFrame object := ⟨trivial, hframe⟩
          -- a mapped object is live, but `object` is dead
          have permits : mapping.permissions.read = true ∨ mapping.permissions.write = true := by
            simp only [VirtualMapping.Permissions.nonempty, Bool.or_eq_true] at hperm
            exact hperm
          rcases permits with readable | writable
          · obtain ⟨_, capability, heldCap, sameObject, _⟩ := hread readable
            have := (hcapabilities.1 _ _ _ heldCap).2.1
            rw [sameObject, same, dead] at this; contradiction
          · obtain ⟨_, capability, heldCap, sameObject, _⟩ := hwrite writable
            have := (hcapabilities.1 _ _ _ heldCap).2.1
            rw [sameObject, same, dead] at this; contradiction
        · simpa [vmDef, allocatedMemory, MemoryLifecycle.setBinding, same] using hbinding
      · simp only [vmDef, allocatedMemory, FrameAllocator.IsOwnedBy, FrameAllocator.setStatus,
          frameNe, ↓reduceIte]
        exact hframe
      · intro p; exact authMono _ _ _ (hread p)
      · intro p; exact authMono _ _ _ (hwrite p)
    · intro space subject held
      obtain ⟨hlive, hkind, hissuedSpace, hissued, hrevoke⟩ := haddressSpaces space subject held
      simp only [vmDef, allocatedMemory]
      refine ⟨objMono space hlive, ?_, hissuedSpace, ?_, authMono _ _ _ hrevoke⟩
      · rw [kindsLive space hlive]; exact hkind
      · simp [MemoryLifecycle.setIssued, hissued]
    · intro space hlive hkind
      change created.objects space = true at hlive
      change created.kinds space = some .addressSpace at hkind
      by_cases same : space = object
      · subst same
        rw [createdDef, allocatedCapabilities_kinds] at hkind
        simp at hkind
      · have oldLive : state.capabilities.objects space = true := by
          rw [createdDef, allocatedCapabilities_objects_of_ne _ _ _ _ same] at hlive; exact hlive
        have oldKind : state.capabilities.kinds space = some .addressSpace := by
          rw [createdDef, allocatedCapabilities_kinds_of_ne _ _ _ _ same] at hkind; exact hkind
        exact hownedAddressSpaces space oldLive oldKind
  -- The endpoint view.
  let endpoints' : EndpointIPC.State := { state.ipc.endpoints with
    capabilities := created
    issued := MemoryLifecycle.setIssued state.ipc.endpoints.issued object }
  have endpointsDef : endpoints' = { state.ipc.endpoints with
    capabilities := created
    issued := MemoryLifecycle.setIssued state.ipc.endpoints.issued object } := rfl
  have hendpoint' : EndpointIPC.WellFormed endpoints' := by
    obtain ⟨_, hissued, hmailbox, hdeadMail, hhistory⟩ := hipc.2
    rw [endCaps] at hissued hmailbox hdeadMail
    refine ⟨by rw [endpointsDef]; exact hcaps', ?_, ?_, ?_, by rw [endpointsDef]; exact hhistory⟩
    · intro candidate hlive hkind
      simp only [endpointsDef] at hlive hkind ⊢
      simp only [MemoryLifecycle.setIssued]
      by_cases same : candidate = object
      · simp [same]
      · rw [createdDef, allocatedCapabilities_objects_of_ne _ _ _ _ same] at hlive
        rw [createdDef, allocatedCapabilities_kinds_of_ne _ _ _ _ same] at hkind
        simp [same, hissued candidate hlive hkind]
    · intro candidate envelope held
      obtain ⟨hlive, hkind, hend, hsent⟩ := hmailbox candidate envelope held
      simp only [endpointsDef]
      exact ⟨objMono candidate hlive, by rw [kindsLive candidate hlive]; exact hkind, hend, hsent⟩
    · intro candidate hdead
      simp only [endpointsDef] at hdead
      exact hdeadMail candidate (deadOld candidate hdead)
  have hipc' : IPCSyscall.WellFormed
      { state.ipc with virtualMemory := vm', endpoints := endpoints' } :=
    ⟨hvirtual', hendpoint'⟩
  -- Scheduler views.
  let scheduler' : Scheduler.State := { state.scheduler with lifecycle := lifecycle' }
  have schedulerDef : scheduler' = { state.scheduler with lifecycle := lifecycle' } := rfl
  have ownsSame : ∀ subject, Scheduler.ownsAddressSpace scheduler' subject =
      Scheduler.ownsAddressSpace state.scheduler subject := by
    intro subject
    simp [Scheduler.ownsAddressSpace, schedulerDef, lifecycleDef, allocatedLifecycle,
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
        translations := { state.resumable.translations with virtual := vm' } } := by
    have activeOld := hresumable.2.2.2.2.2.2.1.2
    have ownerOld := hresumable.2.2.2.2.2.2.1.1
    obtain ⟨_, hcapacity, hunique, hvalid, habsent, hreadyAgree, _, _, hkindsAgree, htlb⟩ :=
      hresumable
    simp only [ResumablePreemption.validContext, ResumablePreemption.ReadyContextAgreement,
      ResumablePreemption.ResourceKindAgreement, hresumableSchedulerCoherent,
      hschedulerCoherent] at hvalid habsent hreadyAgree hkindsAgree
    rw [hresumableSchedulerCoherent, hschedulerCoherent, hresumableVirtualCoherent] at ownerOld
    refine ⟨hscheduler', hcapacity, hunique, ?_, habsent, hreadyAgree, ?_, ?_, ?_, htlb⟩
    · intro context member
      obtain ⟨hframe, hspace, hlive, hrunnable, howner⟩ := hvalid context member
      rw [lifeCaps] at hlive
      exact ⟨hframe, hspace, hlive, hrunnable, howner⟩
    · refine ⟨by simpa [vmDef, schedulerDef, lifecycleDef, allocatedLifecycle] using ownerOld, ?_⟩
      rw [hresumableSchedulerCoherent, hschedulerCoherent] at activeOld
      exact activeOld
    · exact ⟨rfl, hvirtual'⟩
    · obtain ⟨hmem, hend⟩ := hkindsAgree
      refine ⟨?_, ?_⟩
      · intro candidate subject owned held
        show created.kinds candidate = some .memory
        simp only [schedulerDef, lifecycleDef, allocatedLifecycle] at held
        rw [createdDef, allocatedCapabilities_kinds]
        split
        · rfl
        · next ne =>
          simp only [ne, ↓reduceIte] at held
          rw [← lifeCaps]; exact hmem candidate subject owned held
      · intro candidate subject held
        change state.lifecycle.endpointOwner candidate = some subject at held
        have old := hend candidate subject held
        have ne : candidate ≠ object := by
          intro same; rw [same, allocatable.endpointFree] at held; contradiction
        show created.kinds candidate = some .endpoint
        rw [createdDef, allocatedCapabilities_kinds_of_ne _ _ _ _ ne, ← lifeCaps]; exact old
  have htransfers' : CapabilityTransfer.WellFormed
      { state.transfers with toEndpointState := endpoints' } := by
    refine ⟨hendpoint', ?_⟩
    intro endpoint transfer pending
    have pendingOld : state.transfers.pending endpoint = some transfer := pending
    obtain ⟨henvelope, hlive, hkind, hrights, hderivation, hparent, hparentIdentity,
      hidentity, habsent, huniquePending⟩ := htransfers.2 endpoint transfer pendingOld
    have transferCaps : state.transfers.capabilities = state.capabilities := by
      rw [htransfersCoherent]; exact endCaps
    rw [transferCaps] at hlive hkind hderivation hparent hidentity habsent
    have endpointsCaps : endpoints'.capabilities = created := rfl
    change ∃ envelope, state.transfers.mailbox endpoint = some envelope ∧ _ at henvelope
    obtain ⟨parentParent, parentRights, hparentDerivation, hsubset⟩ := hparent
    refine ⟨?_, ?_, ?_, hrights, ?_, ?_, hparentIdentity, ?_, ?_, huniquePending⟩
    · simpa [endpointsDef, htransfersCoherent] using henvelope
    · change endpoints'.capabilities.objects transfer.object = true
      rw [endpointsCaps]; exact objMono _ hlive
    · change endpoints'.capabilities.kinds transfer.object = some transfer.kind
      rw [endpointsCaps, kindsLive _ hlive]; exact hkind
    · change endpoints'.capabilities.derivations transfer.identity = _
      rw [endpointsCaps, createdDef, allocatedCapabilities_derivations_of_lt _ _ _ _ hidentity]
      exact hderivation
    · refine ⟨parentParent, parentRights, ?_, hsubset⟩
      change endpoints'.capabilities.derivations transfer.parent = _
      rw [endpointsCaps, createdDef, allocatedCapabilities_derivations_of_lt _ _ _ _
        (Nat.lt_trans hparentIdentity hidentity)]
      exact hparentDerivation
    · change transfer.identity < endpoints'.capabilities.nextIdentity
      rw [endpointsCaps, createdDef, allocatedCapabilities_nextIdentity]; omega
    · intro subject candidateSlot capability held
      change endpoints'.capabilities.slots subject candidateSlot = some capability at held
      rw [endpointsCaps, createdDef, allocatedCapabilities_slots] at held
      split at held
      · cases held; simp only [memoryRoot]; omega
      · exact habsent subject candidateSlot capability held
  -- Publish: fold every composite copy onto the names above.
  have installed : installAllocatedMemory state object owner slot frame =
      { state with
        execution := { state.execution with
          core := { state.execution.core with lifecycle := lifecycle' }
          returnAuthorityArmed := false }
        scheduler := scheduler'
        preemption := { state.preemption with scheduler := scheduler' }
        virtualMemory := vm'
        ipc := { state.ipc with virtualMemory := vm', endpoints := endpoints' }
        capabilities := created
        lifecycle := lifecycle'
        resumable := { state.resumable with
          scheduler := scheduler'
          translations := { state.resumable.translations with virtual := vm' } }
        transfers := { state.transfers with toEndpointState := endpoints' }
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
    change endpoints'.mailbox candidate = none
    exact hdeadMailbox candidate (by rw [lifeCaps]; exact deadOld candidate hdead)
  · intro candidate envelope held
    change endpoints'.mailbox candidate = some envelope at held
    have := hliveSender candidate envelope held
    rw [lifeCaps] at this
    exact this

/-- **Allocation keeps the authoritative runtime invariant**, including the
blocking store, its saved contexts, the deferred cancellations, and
invalidation publication. -/
theorem installAllocatedMemory_preserves_authoritativeRuntimeWellFormed
    (state : CompositeState) (object owner slot frame : Nat)
    (holds : AuthoritativeRuntimeWellFormed state)
    (allocatable : MemoryAllocatable state object owner slot frame) :
    AuthoritativeRuntimeWellFormed (installAllocatedMemory state object owner slot frame) := by
  have runtime := installAllocatedMemory_preserves_runtimeWellFormed state object owner slot
    frame holds.left allocatable
  have coherent := holds.left.1
  have blockingScheduler : state.blockingIPC.scheduler = state.scheduler :=
    holds.left.blockingScheduler
  have schedLife : state.scheduler.lifecycle = state.lifecycle := coherent.2.1
  have lifeCaps : state.lifecycle.capabilities = state.capabilities := coherent.2.2.2.1.symm
  have empty := allocatable.slotEmpty
  have dead := allocatable.dead
  have liveNe : ∀ candidate, state.capabilities.objects candidate = true → candidate ≠ object := by
    intro candidate live same; rw [same, dead] at live; contradiction
  have ownsSame : ∀ subject,
      Scheduler.ownsAddressSpace
          { state.scheduler with
            lifecycle := allocatedLifecycle state.lifecycle
              (allocatedCapabilities state.capabilities object owner slot) object owner frame }
          subject =
        Scheduler.ownsAddressSpace state.blockingIPC.scheduler subject := by
    intro subject
    simp [Scheduler.ownsAddressSpace, allocatedLifecycle, blockingScheduler, schedLife]
  obtain ⟨⟨⟨hipc, hctx⟩, hblockedDeferred, hretained⟩, hblockedResumable, hdeferredResumable⟩ :=
    holds.right
  refine ⟨runtime, ⟨⟨⟨?_, hctx⟩, hblockedDeferred, ?_⟩, hblockedResumable, hdeferredResumable⟩,
    holds.publication⟩
  · obtain ⟨_, hqueue, hwaiters, hunique, hiff, hmail, _⟩ := hipc
    simp only [CompositeState.blockingIPCContext, installAllocatedMemory]
    refine ⟨?_, hqueue, ?_, hunique, hiff, ?_, ?_⟩
    · have := runtime.2.2.2.2.2.2.1
      simpa [installAllocatedMemory, allocatedLifecycle] using this
    · intro endpoint subject member
      obtain ⟨hlive, ⟨authSlot, cap, held, sameObject, kind, receive, authLive⟩, hsubject,
        hrunnable, howns, hcurrent, hready⟩ := hwaiters endpoint subject member
      simp only [CompositeState.blockingIPCContext, blockingScheduler, schedLife, lifeCaps]
        at hlive held authLive hsubject hrunnable hcurrent hready
      refine ⟨allocatedCapabilities_objects_mono _ _ _ _ hlive,
        ⟨authSlot, cap, allocatedCapabilities_slots_mono _ _ _ _ empty held, sameObject, kind,
          receive, allocatedCapabilities_objects_mono _ _ _ _ authLive⟩,
        hsubject, hrunnable, ?_, hcurrent, by simpa [blockingScheduler] using hready⟩
      simp only [allocatedLifecycle] at ownsSame ⊢
      rw [ownsSame]; exact howns
    · intro endpoint envelope held
      obtain ⟨hlive0, hkind0, hend, hempty⟩ := hmail endpoint envelope held
      have hlive : state.capabilities.objects endpoint = true := by
        simpa [CompositeState.blockingIPCContext, blockingScheduler, schedLife, lifeCaps]
          using hlive0
      have hkind : state.capabilities.kinds endpoint = some .endpoint := by
        simpa [CompositeState.blockingIPCContext, blockingScheduler, schedLife, lifeCaps]
          using hkind0
      refine ⟨allocatedCapabilities_objects_mono _ _ _ _ hlive, ?_, hend, hempty⟩
      show (allocatedCapabilities state.capabilities object owner slot).kinds endpoint =
        some .endpoint
      rw [allocatedCapabilities_kinds_of_ne _ _ _ _ (liveNe endpoint hlive)]
      exact hkind
    · have := runtime.2.2.2.1
      simpa [installAllocatedMemory, allocatedLifecycle] using this
  · intro subject saved retained
    obtain ⟨hvalid, hwaiter, hsubject, hrunnable, hcurrent, hready, howns⟩ :=
      hretained subject saved retained
    simp only [CompositeState.blockingIPCContext, blockingScheduler, schedLife, lifeCaps]
      at hsubject hrunnable hcurrent hready
    simp only [CompositeState.blockingIPCContext, installAllocatedMemory]
    refine ⟨hvalid, hwaiter, hsubject, hrunnable, hcurrent,
      by simpa [blockingScheduler] using hready, ?_⟩
    simp only [allocatedLifecycle] at ownsSame ⊢
    rw [ownsSame]; exact howns

end LeanOS.FailStop
