import LeanOS.FailStop.Resources

/-!
# Fail-stop composite: creating an empty address space

Explicit spawn (#489, ADR 0010) gives the child a fresh, empty address space.
No composite operation created an address space before: `VirtualMapping`
and `BoundedLifecycle` each had a standalone `createAddressSpace`, but the
composite only carried address spaces in from boot.  This module adds the
composite publication of `VirtualMapping.createAddressSpace` and proves it
keeps the whole runtime invariant.

`installCreatedAddressSpace state a owner slot` publishes exactly the state
`VirtualMapping.createAddressSpace` produces (`createdVirtualMemory`) to every
copy the composite keeps of it:

- the capability registry gains the live address-space object `a` and its
  root capability `{grant, revoke}` in `owner`'s `slot`
  (`addressSpaceCapabilities`);
- the virtual-memory view records `a` as issued, owned by `owner`, and with
  no mappings;
- the lifecycle's `addressOwner` records the same owner, as
  `ResumablePreemption.TranslationAgreement` requires;
- the endpoint view's issued histories record `a` as well.

`AddressSpaceCreatable` names the preconditions: the checks of
`VirtualMapping.createAddressSpace` plus two lifecycle records that must not
already name `a`.  `installCreatedAddressSpace_preserves_authoritativeRuntimeWellFormed`
proves the composite publication keeps `AuthoritativeRuntimeWellFormed`.

The address-space identity is drawn from the composite object issuer by the
spawn transition (`LeanOS.FailStop.Spawn`), not here.
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

/-! ## The created state -/

/-- The capability registry after creating address space `addressSpace` with
its root capability in `owner`'s `slot`: exactly the registry
`VirtualMapping.createAddressSpace` installs. -/
def addressSpaceCapabilities (capabilities : Capability.State)
    (addressSpace owner slot : Nat) : Capability.State :=
  Capability.installRoot (VirtualMapping.activateAddressSpace capabilities addressSpace) owner slot
    addressSpace .addressSpace VirtualMapping.addressSpaceRootRights

/-- The virtual-memory state `VirtualMapping.createAddressSpace` produces on
acceptance. -/
def createdVirtualMemory (state : VirtualMapping.State) (addressSpace owner slot : Nat) :
    VirtualMapping.State :=
  VirtualMapping.clearAddressSpaceMappings
    { state with
      memory := { state.memory with
        capabilities := addressSpaceCapabilities state.memory.capabilities addressSpace owner slot
        issued := MemoryLifecycle.setIssued state.memory.issued addressSpace }
      owner := VirtualMapping.setOwner state.owner addressSpace (some owner)
      issuedAddressSpace :=
        VirtualMapping.setIssuedAddressSpace state.issuedAddressSpace addressSpace }
    addressSpace

/-- The preconditions under which the composite creates address space
`addressSpace` for `owner` in `slot`.  The first six are the checks of
`VirtualMapping.createAddressSpace`; the last says no lifecycle record of
owned memory or of an owned endpoint already names the identifier. -/
structure AddressSpaceCreatable (state : CompositeState) (addressSpace owner slot : Nat) :
    Prop where
  ownerLive : state.capabilities.subjects owner = true
  slotBounded : slot < CapabilityHandle.slotReserved
  slotInRange : Capability.slotInRange state.capabilities owner slot = true
  generation : state.capabilities.nextIdentity ≠ 0 ∧
    state.capabilities.nextIdentity < CapabilityHandle.generationReserved
  slotEmpty : state.capabilities.slots owner slot = none
  unissued : state.virtualMemory.issuedAddressSpace addressSpace = false ∧
    state.virtualMemory.memory.issued addressSpace = false
  dead : state.capabilities.objects addressSpace = false
  lifecycleFree : state.lifecycle.ownedMemory addressSpace = none ∧
    state.lifecycle.endpointOwner addressSpace = none

/-- Publish one created address space to every composite copy. -/
def installCreatedAddressSpace (state : CompositeState) (addressSpace owner slot : Nat) :
    CompositeState :=
  let virtualMemory := createdVirtualMemory state.virtualMemory addressSpace owner slot
  let capabilities := virtualMemory.memory.capabilities
  let lifecycle := { state.lifecycle with
    capabilities
    addressOwner := VirtualMapping.setOwner state.lifecycle.addressOwner addressSpace (some owner) }
  let scheduler := { state.scheduler with lifecycle }
  let endpoints := { state.ipc.endpoints with
    capabilities
    issued := MemoryLifecycle.setIssued state.ipc.endpoints.issued addressSpace
    issuedAddressSpace :=
      VirtualMapping.setIssuedAddressSpace state.ipc.endpoints.issuedAddressSpace addressSpace }
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

/-- On acceptance `VirtualMapping.createAddressSpace` produces exactly
`createdVirtualMemory`, and its checks hold. -/
theorem VirtualMapping.createAddressSpace_accepted_state (state : VirtualMapping.State)
    (addressSpace owner slot : Nat)
    (accepted : (VirtualMapping.createAddressSpace state addressSpace owner slot).result =
      .accepted) :
    state.memory.capabilities.subjects owner = true ∧
      slot < CapabilityHandle.slotReserved ∧
      Capability.slotInRange state.memory.capabilities owner slot = true ∧
      (state.memory.capabilities.nextIdentity ≠ 0 ∧
        state.memory.capabilities.nextIdentity < CapabilityHandle.generationReserved) ∧
      state.memory.capabilities.slots owner slot = none ∧
      (state.issuedAddressSpace addressSpace = false ∧ state.memory.issued addressSpace = false) ∧
      state.memory.capabilities.objects addressSpace = false ∧
      (VirtualMapping.createAddressSpace state addressSpace owner slot).state =
        createdVirtualMemory state addressSpace owner slot := by
  unfold VirtualMapping.createAddressSpace at accepted ⊢
  split at accepted
  · simp [VirtualMapping.reject] at accepted
  next live =>
    split at accepted
    · simp [VirtualMapping.reject] at accepted
    next range =>
      split at accepted
      · simp [VirtualMapping.reject] at accepted
      next generation =>
        split at accepted
        · simp [VirtualMapping.reject] at accepted
        next empty =>
          split at accepted
          · simp [VirtualMapping.reject] at accepted
          next fresh =>
            split at accepted
            · simp [VirtualMapping.reject] at accepted
            next dead =>
              have live' : state.memory.capabilities.subjects owner = true := by
                simpa using live
              have range' : slot < CapabilityHandle.slotReserved ∧
                  Capability.slotInRange state.memory.capabilities owner slot = true := by
                simpa [not_or, Nat.not_le] using range
              have generation' : state.memory.capabilities.nextIdentity ≠ 0 ∧
                  state.memory.capabilities.nextIdentity < CapabilityHandle.generationReserved := by
                simpa [not_or, Nat.not_le] using generation
              have empty' : state.memory.capabilities.slots owner slot = none := by
                simpa using empty
              have fresh' : state.issuedAddressSpace addressSpace = false ∧
                  state.memory.issued addressSpace = false := by
                simpa using fresh
              have dead' : state.memory.capabilities.objects addressSpace = false := by
                simpa using dead
              refine ⟨live', range'.1, range'.2, generation', empty', fresh', dead', ?_⟩
              simp only [live, range, generation, empty, fresh, dead, ↓reduceIte]
              rfl

/-! ## The created registry -/

section Registry

variable (capabilities : Capability.State) (addressSpace owner slot : Nat)

/-- The root capability installed for the new address space. -/
def addressSpaceRoot : Capability.Capability :=
  { object := addressSpace, kind := .addressSpace, rights := VirtualMapping.addressSpaceRootRights,
    identity := capabilities.nextIdentity, parent := none }

@[simp] theorem addressSpaceCapabilities_subjects :
    (addressSpaceCapabilities capabilities addressSpace owner slot).subjects =
      capabilities.subjects := rfl

@[simp] theorem addressSpaceCapabilities_slotCapacity :
    (addressSpaceCapabilities capabilities addressSpace owner slot).slotCapacity =
      capabilities.slotCapacity := rfl

@[simp] theorem addressSpaceCapabilities_nextIdentity :
    (addressSpaceCapabilities capabilities addressSpace owner slot).nextIdentity =
      capabilities.nextIdentity + 1 := rfl

theorem addressSpaceCapabilities_objects (object : Nat) :
    (addressSpaceCapabilities capabilities addressSpace owner slot).objects object =
      if object = addressSpace then true else capabilities.objects object := by
  simp [addressSpaceCapabilities, Capability.installRoot, Capability.install,
    VirtualMapping.activateAddressSpace, MemoryLifecycle.setObject]

theorem addressSpaceCapabilities_kinds (object : Nat) :
    (addressSpaceCapabilities capabilities addressSpace owner slot).kinds object =
      if object = addressSpace then some .addressSpace else capabilities.kinds object := by
  simp [addressSpaceCapabilities, Capability.installRoot, Capability.install,
    VirtualMapping.activateAddressSpace]

theorem addressSpaceCapabilities_slots (subject candidateSlot : Nat) :
    (addressSpaceCapabilities capabilities addressSpace owner slot).slots subject candidateSlot =
      if subject = owner ∧ candidateSlot = slot then
        some (addressSpaceRoot capabilities addressSpace)
      else capabilities.slots subject candidateSlot := by
  simp [addressSpaceCapabilities, Capability.installRoot, Capability.install,
    VirtualMapping.activateAddressSpace, addressSpaceRoot]

theorem addressSpaceCapabilities_derivations (identity : Nat) :
    (addressSpaceCapabilities capabilities addressSpace owner slot).derivations identity =
      if identity = capabilities.nextIdentity then
        some (none, addressSpace, .addressSpace, VirtualMapping.addressSpaceRootRights)
      else capabilities.derivations identity := rfl

/-- Live objects stay live. -/
theorem addressSpaceCapabilities_objects_mono {object : Nat}
    (live : capabilities.objects object = true) :
    (addressSpaceCapabilities capabilities addressSpace owner slot).objects object = true := by
  rw [addressSpaceCapabilities_objects]; split <;> simp_all

/-- Every pre-existing slot is kept when the target slot was empty. -/
theorem addressSpaceCapabilities_slots_mono
    (empty : capabilities.slots owner slot = none) {subject candidateSlot : Nat}
    {capability : Capability.Capability}
    (held : capabilities.slots subject candidateSlot = some capability) :
    (addressSpaceCapabilities capabilities addressSpace owner slot).slots subject candidateSlot =
      some capability := by
  rw [addressSpaceCapabilities_slots]
  split
  · next target => obtain ⟨rfl, rfl⟩ := target; rw [empty] at held; contradiction
  · exact held

/-- Authority only grows. -/
theorem addressSpaceCapabilities_authority_mono
    (empty : capabilities.slots owner slot = none) {subject object : Nat}
    {right : Capability.Right}
    (holds : Capability.HasAuthority capabilities subject object right) :
    Capability.HasAuthority (addressSpaceCapabilities capabilities addressSpace owner slot)
      subject object right := by
  obtain ⟨candidateSlot, capability, held, sameObject, permitted⟩ := holds
  exact ⟨candidateSlot, capability,
    addressSpaceCapabilities_slots_mono capabilities addressSpace owner slot empty held,
    sameObject, permitted⟩

/-- A previously live object other than the new one keeps its kind. -/
theorem addressSpaceCapabilities_kinds_of_ne {object : Nat} (ne : object ≠ addressSpace) :
    (addressSpaceCapabilities capabilities addressSpace owner slot).kinds object =
      capabilities.kinds object := by
  rw [addressSpaceCapabilities_kinds]; simp [ne]

theorem addressSpaceCapabilities_objects_of_ne {object : Nat} (ne : object ≠ addressSpace) :
    (addressSpaceCapabilities capabilities addressSpace owner slot).objects object =
      capabilities.objects object := by
  rw [addressSpaceCapabilities_objects]; simp [ne]

/-- Old derivations survive. -/
theorem addressSpaceCapabilities_derivations_of_lt {identity : Nat}
    (lt : identity < capabilities.nextIdentity) :
    (addressSpaceCapabilities capabilities addressSpace owner slot).derivations identity =
      capabilities.derivations identity := by
  rw [addressSpaceCapabilities_derivations]; simp [Nat.ne_of_lt lt]

/-- **The created registry is well formed.**  Installing a root capability
for a dead object into an empty in-range slot of a live subject keeps
`Capability.WellFormed`. -/
theorem addressSpaceCapabilities_wellFormed (wellFormed : Capability.WellFormed capabilities)
    (ownerLive : capabilities.subjects owner = true)
    (inRange : Capability.slotInRange capabilities owner slot = true)
    (empty : capabilities.slots owner slot = none)
    (dead : capabilities.objects addressSpace = false) :
    Capability.WellFormed (addressSpaceCapabilities capabilities addressSpace owner slot) := by
  obtain ⟨hslots, hderivations, hunique, hspaces⟩ := wellFormed
  have objectNe : ∀ subject candidateSlot capability,
      capabilities.slots subject candidateSlot = some capability →
        capability.object ≠ addressSpace := by
    intro subject candidateSlot capability held same
    have := (hslots subject candidateSlot capability held).2.1
    rw [same, dead] at this; contradiction
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro subject candidateSlot capability held
    rw [addressSpaceCapabilities_slots] at held
    split at held
    · next target =>
      obtain ⟨rfl, rfl⟩ := target
      cases held
      refine ⟨ownerLive, ?_, ?_, by simp [addressSpaceRoot, Capability.rightsValid,
        VirtualMapping.addressSpaceRootRights], Nat.lt_succ_self _, ?_, trivial⟩
      · simp [addressSpaceCapabilities_objects, addressSpaceRoot]
      · simp [addressSpaceCapabilities_kinds, addressSpaceRoot]
      · simp [addressSpaceCapabilities_derivations, addressSpaceRoot]
    · obtain ⟨hsub, hlive, hkind, hrights, hid, hentry, hedge⟩ :=
        hslots subject candidateSlot capability held
      have ne := objectNe subject candidateSlot capability held
      refine ⟨hsub, ?_, ?_, hrights, Nat.lt_succ_of_lt hid, ?_, ?_⟩
      · rw [addressSpaceCapabilities_objects_of_ne _ _ _ _ ne]; exact hlive
      · rw [addressSpaceCapabilities_kinds_of_ne _ _ _ _ ne]; exact hkind
      · rw [addressSpaceCapabilities_derivations_of_lt _ _ _ _ hid]; exact hentry
      · cases hp : capability.parent with
        | none => trivial
        | some parentIdentity =>
            rw [hp] at hedge
            obtain ⟨hparent, pp, pr, hpentry, hsubset⟩ := hedge
            refine ⟨hparent, pp, pr, ?_, hsubset⟩
            rw [addressSpaceCapabilities_derivations_of_lt _ _ _ _ (Nat.lt_trans hparent hid)]
            exact hpentry
  · intro identity parent object kind rights hentry
    rw [addressSpaceCapabilities_derivations] at hentry
    split at hentry
    · next same =>
      subst same
      cases hentry
      exact ⟨Nat.lt_succ_self _, trivial⟩
    · have old := hderivations identity parent object kind rights hentry
      refine ⟨Nat.lt_succ_of_lt old.1, ?_⟩
      cases parent with
      | none => trivial
      | some parentIdentity =>
          obtain ⟨hparent, pp, pr, hpentry, hsubset⟩ := old.2
          refine ⟨hparent, pp, pr, ?_, hsubset⟩
          rw [addressSpaceCapabilities_derivations_of_lt _ _ _ _
            (Nat.lt_trans hparent old.1)]
          exact hpentry
  · intro left leftSlot leftCap right rightSlot rightCap hleft hright hid
    rw [addressSpaceCapabilities_slots] at hleft hright
    split at hleft
    · next hl =>
      split at hright
      · next hr => exact ⟨hl.1.trans hr.1.symm, hl.2.trans hr.2.symm⟩
      · cases hleft
        have := (hslots right rightSlot rightCap hright).2.2.2.2.1
        simp only [addressSpaceRoot] at hid
        omega
    · split at hright
      · cases hright
        have := (hslots left leftSlot leftCap hleft).2.2.2.2.1
        simp only [addressSpaceRoot] at hid
        omega
      · exact hunique left leftSlot leftCap right rightSlot rightCap hleft hright hid
  · intro subject candidateSlot outside
    rw [addressSpaceCapabilities_slots]
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

@[simp] theorem installCreatedAddressSpace_mode (state : CompositeState) addressSpace owner slot :
    (installCreatedAddressSpace state addressSpace owner slot).execution.mode =
      state.execution.mode := rfl

@[simp] theorem installCreatedAddressSpace_capabilities (state : CompositeState)
    addressSpace owner slot :
    (installCreatedAddressSpace state addressSpace owner slot).capabilities =
      addressSpaceCapabilities state.virtualMemory.memory.capabilities addressSpace owner slot :=
  rfl

/-- The new address space is owned by `owner` and has no mappings. -/
theorem installCreatedAddressSpace_empty (state : CompositeState) addressSpace owner slot :
    (installCreatedAddressSpace state addressSpace owner slot).virtualMemory.owner addressSpace =
        some owner ∧
      (installCreatedAddressSpace state addressSpace owner slot).lifecycle.addressOwner
        addressSpace = some owner ∧
      ∀ page, (installCreatedAddressSpace state addressSpace owner slot).virtualMemory.mappings
        addressSpace page = none := by
  simp [installCreatedAddressSpace, createdVirtualMemory, VirtualMapping.clearAddressSpaceMappings,
    VirtualMapping.setOwner]

/-! ## Invariant preservation -/

/-- Before creation the lifecycle's owner record of the identifier is empty:
the lifecycle owner view equals the virtual-memory owner view, and an owned
address space is always issued. -/
theorem addressOwner_none_of_unissued {state : CompositeState} {addressSpace : Nat}
    (holds : RuntimeWellFormed state)
    (unissued : state.virtualMemory.issuedAddressSpace addressSpace = false) :
    state.lifecycle.addressOwner addressSpace = none := by
  obtain ⟨coherent, _, _, _, virtual, _, _, _, resumable, _⟩ := holds
  obtain ⟨_, schedulerLifecycle, _, _, _, _, _, resumableScheduler, resumableVirtual, _⟩ :=
    coherent
  have translation := resumable.2.2.2.2.2.2.1.1
  rw [resumableScheduler, schedulerLifecycle, resumableVirtual] at translation
  rw [← translation]
  cases owner : state.virtualMemory.owner addressSpace with
  | none => rfl
  | some subject =>
      have := (virtual.2.2.1 addressSpace subject owner).2.2.1
      rw [unissued] at this; contradiction

/-- **Address-space creation keeps the runtime invariant.** -/
theorem installCreatedAddressSpace_preserves_runtimeWellFormed (state : CompositeState)
    (addressSpace owner slot : Nat) (holds : RuntimeWellFormed state)
    (creatable : AddressSpaceCreatable state addressSpace owner slot) :
    RuntimeWellFormed (installCreatedAddressSpace state addressSpace owner slot) := by
  have ownerNone := addressOwner_none_of_unissued holds creatable.unissued.1
  obtain ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
    hscheduler, hpreemption, hresumable, htransfers, hhalted, _hlivePlan,
    hblockingCoherent, hdevices⟩ := holds
  obtain ⟨hexecutionCoherent, hschedulerCoherent, hpreemptionCoherent,
    hcapabilitiesCoherent, hvirtualCapabilitiesCoherent, hipcVirtualCoherent,
    hipcCapabilitiesCoherent, hresumableSchedulerCoherent,
    hresumableVirtualCoherent, htransfersCoherent, hauthorityCoherent,
    hdeadMailbox, hliveSender⟩ := hcoherent
  -- Normalize every capability copy to `state.capabilities`.
  have vmCaps : state.virtualMemory.memory.capabilities = state.capabilities :=
    hvirtualCapabilitiesCoherent.trans hcapabilitiesCoherent.symm
  have lifeCaps : state.lifecycle.capabilities = state.capabilities :=
    hcapabilitiesCoherent.symm
  have endCaps : state.ipc.endpoints.capabilities = state.capabilities :=
    hipcCapabilitiesCoherent.trans hcapabilitiesCoherent.symm
  let created := addressSpaceCapabilities state.capabilities addressSpace owner slot
  have createdDef : created = addressSpaceCapabilities state.capabilities addressSpace owner slot := rfl
  have createdSubjects : created.subjects = state.capabilities.subjects := by
    rfl
  have empty := creatable.slotEmpty
  have dead := creatable.dead
  have hcaps' : Capability.WellFormed created := by
    exact addressSpaceCapabilities_wellFormed state.capabilities addressSpace owner slot hcapabilities
      creatable.ownerLive creatable.slotInRange empty dead
  have objMono : ∀ object, state.capabilities.objects object = true → created.objects object = true := by
    exact fun object live => addressSpaceCapabilities_objects_mono state.capabilities addressSpace owner slot live
  have liveNe : ∀ object, state.capabilities.objects object = true → object ≠ addressSpace := by
    intro object live same; rw [same, dead] at live; contradiction
  have kindsLive : ∀ object, state.capabilities.objects object = true → created.kinds object = state.capabilities.kinds object := by
    exact fun object live => addressSpaceCapabilities_kinds_of_ne state.capabilities addressSpace owner slot
      (liveNe object live)
  have authMono : ∀ subject object right, Capability.HasAuthority state.capabilities subject object right →
      Capability.HasAuthority created subject object right := by
    exact fun _ _ _ h => addressSpaceCapabilities_authority_mono state.capabilities addressSpace owner slot empty h
  have deadOld : ∀ object, created.objects object ≠ true → state.capabilities.objects object ≠ true :=
    fun object hdead hlive => hdead (objMono object hlive)
  let owners := VirtualMapping.setOwner state.lifecycle.addressOwner addressSpace (some owner)
  have ownersDef : owners = VirtualMapping.setOwner state.lifecycle.addressOwner addressSpace (some owner) := rfl
  have ownerMono : ∀ space subject, state.lifecycle.addressOwner space = some subject →
      owners space = some subject := by
    intro space subject held
    simp only [ownersDef, VirtualMapping.setOwner]
    split
    · next same => subst same; rw [ownerNone] at held; contradiction
    · exact held
  let lifecycle' : SubjectLifecycle.State :=
    { state.lifecycle with capabilities := created, addressOwner := owners }
  have lifecycleDef : lifecycle' =
      { state.lifecycle with capabilities := created, addressOwner := owners } := rfl
  have hlifecycle' : SubjectLifecycle.WellFormed lifecycle' := by
    obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hlifecycle
    rw [lifeCaps] at l1 l2 l3 l4 l5 l6
    refine ⟨l1, l2, ?_, l4, l5, l6⟩
    intro space subject held
    simp only [lifecycleDef, ownersDef, VirtualMapping.setOwner] at held
    split at held
    · cases held; exact creatable.ownerLive
    · exact l3 space subject held
  -- The created virtual memory.
  let vm' := createdVirtualMemory state.virtualMemory addressSpace owner slot
  have vmDef : vm' = createdVirtualMemory state.virtualMemory addressSpace owner slot := rfl
  have vmCapsEq : vm'.memory.capabilities = created := by
    simp [vmDef, createdVirtualMemory, VirtualMapping.clearAddressSpaceMappings, vmCaps, createdDef]
  have vmOwner : vm'.owner = owners := by
    have translation := hresumable.2.2.2.2.2.2.1.1
    rw [hresumableSchedulerCoherent, hschedulerCoherent, hresumableVirtualCoherent] at translation
    simp [vmDef, createdVirtualMemory, VirtualMapping.clearAddressSpaceMappings, ownersDef,
      translation]
  have hvirtual' : VirtualMapping.LifecycleWellFormed vm' := by
    obtain ⟨⟨hownerLive, hmappings⟩, _, haddressSpaces, hownedAddressSpaces⟩ := hvirtual
    rw [vmCaps] at hownerLive hmappings haddressSpaces hownedAddressSpaces
    refine ⟨⟨?_, ?_⟩, by rw [vmCapsEq]; exact hcaps', ?_, ?_⟩
    · intro space subject held
      rw [vmCapsEq]
      simp only [vmDef, createdVirtualMemory, VirtualMapping.clearAddressSpaceMappings,
        VirtualMapping.setOwner] at held
      split at held
      · cases held; rw [createdSubjects]; exact creatable.ownerLive
      · rw [createdSubjects]; exact hownerLive space subject held
    · intro space page mapping held
      simp only [vmDef, createdVirtualMemory, VirtualMapping.clearAddressSpaceMappings] at held
      split at held
      · contradiction
      · next ne =>
        obtain ⟨subject, frame, howner, hperm, hbinding, hframe, hread, hwrite⟩ :=
          hmappings space page mapping held
        refine ⟨subject, frame, ?_, hperm, ?_, ?_, ?_, ?_⟩
        · simp [vmDef, createdVirtualMemory, VirtualMapping.clearAddressSpaceMappings,
            VirtualMapping.setOwner, ne, howner]
        · simpa [vmDef, createdVirtualMemory, VirtualMapping.clearAddressSpaceMappings]
            using hbinding
        · simpa [vmDef, createdVirtualMemory, VirtualMapping.clearAddressSpaceMappings]
            using hframe
        · intro p; rw [vmCapsEq]; exact authMono _ _ _ (hread p)
        · intro p; rw [vmCapsEq]; exact authMono _ _ _ (hwrite p)
    · intro space subject held
      rw [vmCapsEq]
      simp only [vmDef, createdVirtualMemory, VirtualMapping.clearAddressSpaceMappings,
        VirtualMapping.setOwner] at held
      split at held
      · next same =>
        cases held
        subst same
        refine ⟨by simp [createdDef, addressSpaceCapabilities_objects],
          by simp [createdDef, addressSpaceCapabilities_kinds], ?_, ?_, ?_⟩
        · simp [vmDef, createdVirtualMemory, VirtualMapping.clearAddressSpaceMappings,
            VirtualMapping.setIssuedAddressSpace]
        · simp [vmDef, createdVirtualMemory, VirtualMapping.clearAddressSpaceMappings,
            MemoryLifecycle.setIssued]
        · refine ⟨slot, addressSpaceRoot state.capabilities space, ?_, rfl, rfl⟩
          simp [createdDef, addressSpaceCapabilities_slots]
      · next ne =>
        obtain ⟨hlive, hkind, hissuedSpace, hissued, hrevoke⟩ := haddressSpaces space subject held
        refine ⟨objMono space hlive, by rw [kindsLive space hlive]; exact hkind, ?_, ?_,
          authMono _ _ _ hrevoke⟩
        · simp [vmDef, createdVirtualMemory, VirtualMapping.clearAddressSpaceMappings,
            VirtualMapping.setIssuedAddressSpace, hissuedSpace]
        · simp [vmDef, createdVirtualMemory, VirtualMapping.clearAddressSpaceMappings,
            MemoryLifecycle.setIssued, hissued]
    · intro space hlive hkind
      rw [vmCapsEq] at hlive hkind
      simp only [vmDef, createdVirtualMemory, VirtualMapping.clearAddressSpaceMappings,
        VirtualMapping.setOwner]
      by_cases same : space = addressSpace
      · exact ⟨owner, by simp [same]⟩
      · have oldLive : state.capabilities.objects space = true := by
          rw [createdDef, addressSpaceCapabilities_objects_of_ne _ _ _ _ same] at hlive; exact hlive
        have oldKind : state.capabilities.kinds space = some .addressSpace := by
          rw [createdDef, addressSpaceCapabilities_kinds_of_ne _ _ _ _ same] at hkind; exact hkind
        obtain ⟨subject, howner⟩ := hownedAddressSpaces space oldLive oldKind
        exact ⟨subject, by simp [same, howner]⟩
  -- The endpoint view.
  let endpoints' : EndpointIPC.State := { state.ipc.endpoints with
    capabilities := created
    issued := MemoryLifecycle.setIssued state.ipc.endpoints.issued addressSpace
    issuedAddressSpace :=
      VirtualMapping.setIssuedAddressSpace state.ipc.endpoints.issuedAddressSpace addressSpace }
  have endpointsDef : endpoints' = { state.ipc.endpoints with
    capabilities := created
    issued := MemoryLifecycle.setIssued state.ipc.endpoints.issued addressSpace
    issuedAddressSpace :=
      VirtualMapping.setIssuedAddressSpace state.ipc.endpoints.issuedAddressSpace addressSpace } := rfl
  have hendpoint' : EndpointIPC.WellFormed endpoints' := by
    obtain ⟨_, hissued, hmailbox, hdeadMail, hhistory⟩ := hipc.2
    rw [endCaps] at hissued hmailbox hdeadMail
    refine ⟨by rw [endpointsDef]; exact hcaps', ?_, ?_, ?_, by rw [endpointsDef]; exact hhistory⟩
    · intro object hlive hkind
      simp only [endpointsDef] at hlive hkind ⊢
      simp only [MemoryLifecycle.setIssued]
      by_cases same : object = addressSpace
      · simp [same]
      · rw [createdDef, addressSpaceCapabilities_objects_of_ne _ _ _ _ same] at hlive
        rw [createdDef, addressSpaceCapabilities_kinds_of_ne _ _ _ _ same] at hkind
        simp [same, hissued object hlive hkind]
    · intro object envelope held
      obtain ⟨hlive, hkind, hend, hsent⟩ := hmailbox object envelope held
      simp only [endpointsDef]
      exact ⟨objMono object hlive, by rw [kindsLive object hlive]; exact hkind, hend, hsent⟩
    · intro object hdead
      simp only [endpointsDef] at hdead
      exact hdeadMail object (deadOld object hdead)
  have hipc' : IPCSyscall.WellFormed { state.ipc with virtualMemory := vm', endpoints := endpoints' } :=
    ⟨hvirtual', hendpoint'⟩
  -- Scheduler views.
  let scheduler' : Scheduler.State := { state.scheduler with lifecycle := lifecycle' }
  have schedulerDef : scheduler' = { state.scheduler with lifecycle := lifecycle' } := rfl
  have ownsMono : ∀ subject, Scheduler.ownsAddressSpace state.scheduler subject ≠ none →
      Scheduler.ownsAddressSpace scheduler' subject ≠ none := by
    intro subject owns
    unfold Scheduler.ownsAddressSpace at owns ⊢
    rw [hschedulerCoherent] at owns
    split at owns
    · next held =>
      simp [schedulerDef, lifecycleDef, ownerMono subject subject held]
    · contradiction
  have hscheduler' : Scheduler.WellFormed scheduler' := by
    obtain ⟨_, hnodup, hcapacity, hready, hcurrent⟩ := hscheduler
    refine ⟨hlifecycle', hnodup, hcapacity, ?_, ?_⟩
    · intro subject member
      obtain ⟨hlive, hrunnable, howns⟩ := hready subject member
      rw [hschedulerCoherent, lifeCaps] at hlive
      rw [hschedulerCoherent] at hrunnable
      exact ⟨hlive, hrunnable, ownsMono subject howns⟩
    · intro subject selected
      have selectedOld : state.scheduler.lifecycle.current = some subject := by
        rw [hschedulerCoherent]; exact selected
      obtain ⟨hlive, hrunnable, howns, hnot⟩ := hcurrent subject selectedOld
      rw [hschedulerCoherent, lifeCaps] at hlive
      rw [hschedulerCoherent] at hrunnable
      exact ⟨hlive, hrunnable, ownsMono subject howns, hnot⟩
  have hpreemption' : Preemption.WellFormed { state.preemption with scheduler := scheduler' } :=
    ⟨hscheduler', hpreemption.2⟩
  have hresumable' : ResumablePreemption.WellFormed
      { state.resumable with
        scheduler := scheduler'
        translations := { state.resumable.translations with virtual := vm' } } := by
    have activeOld := hresumable.2.2.2.2.2.2.1.2
    obtain ⟨_, hcapacity, hunique, hvalid, habsent, hreadyAgree, _, _, hkindsAgree, htlb⟩ :=
      hresumable
    simp only [ResumablePreemption.validContext, ResumablePreemption.ReadyContextAgreement,
      ResumablePreemption.ResourceKindAgreement, hresumableSchedulerCoherent,
      hschedulerCoherent] at hvalid habsent hreadyAgree hkindsAgree
    refine ⟨hscheduler', hcapacity, hunique, ?_, habsent, hreadyAgree, ?_, ?_, ?_, htlb⟩
    · intro context member
      obtain ⟨hframe, hspace, hlive, hrunnable, howner⟩ := hvalid context member
      rw [lifeCaps] at hlive
      exact ⟨hframe, hspace, hlive, hrunnable, ownerMono _ _ howner⟩
    · refine ⟨vmOwner, ?_⟩
      rw [hresumableSchedulerCoherent, hschedulerCoherent] at activeOld
      exact activeOld
    · exact ⟨by rw [vmCapsEq], hvirtual'⟩
    · obtain ⟨hmem, hend⟩ := hkindsAgree
      refine ⟨?_, ?_⟩
      · intro object subject frame held
        have old := hmem object subject frame held
        have ne : object ≠ addressSpace := by
          intro same; rw [same, creatable.lifecycleFree.1] at held; contradiction
        show created.kinds object = some .memory
        rw [createdDef, addressSpaceCapabilities_kinds_of_ne _ _ _ _ ne, ← lifeCaps]; exact old
      · intro object subject held
        have old := hend object subject held
        have ne : object ≠ addressSpace := by
          intro same; rw [same, creatable.lifecycleFree.2] at held; contradiction
        show created.kinds object = some .endpoint
        rw [createdDef, addressSpaceCapabilities_kinds_of_ne _ _ _ _ ne, ← lifeCaps]; exact old
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
    have endpointsCaps : endpoints'.capabilities = created := by
      simp [endpointsDef, vmCapsEq]
    change ∃ envelope, state.transfers.mailbox endpoint = some envelope ∧ _ at henvelope
    obtain ⟨parentParent, parentRights, hparentDerivation, hsubset⟩ := hparent
    refine ⟨?_, ?_, ?_, hrights, ?_, ?_, hparentIdentity, ?_, ?_, huniquePending⟩
    · simpa [endpointsDef, htransfersCoherent] using henvelope
    · change endpoints'.capabilities.objects transfer.object = true
      rw [endpointsCaps]; exact objMono _ hlive
    · change endpoints'.capabilities.kinds transfer.object = some transfer.kind
      rw [endpointsCaps, kindsLive _ hlive]; exact hkind
    · change endpoints'.capabilities.derivations transfer.identity = _
      rw [endpointsCaps, createdDef, addressSpaceCapabilities_derivations_of_lt _ _ _ _ hidentity]
      exact hderivation
    · refine ⟨parentParent, parentRights, ?_, hsubset⟩
      change endpoints'.capabilities.derivations transfer.parent = _
      rw [endpointsCaps, createdDef, addressSpaceCapabilities_derivations_of_lt _ _ _ _
        (Nat.lt_trans hparentIdentity hidentity)]
      exact hparentDerivation
    · change transfer.identity < endpoints'.capabilities.nextIdentity
      rw [endpointsCaps, createdDef, addressSpaceCapabilities_nextIdentity]; omega
    · intro subject candidateSlot capability held
      change endpoints'.capabilities.slots subject candidateSlot = some capability at held
      rw [endpointsCaps, createdDef, addressSpaceCapabilities_slots] at held
      split at held
      · cases held; simp only [addressSpaceRoot]; omega
      · exact habsent subject candidateSlot capability held
  -- Publish: fold every composite copy onto the names above.
  have installed : installCreatedAddressSpace state addressSpace owner slot =
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
        blockingIPC := { state.blockingIPC with scheduler := scheduler' } } := by
    have vmCreated : (createdVirtualMemory state.virtualMemory addressSpace owner
        slot).memory.capabilities = created := vmCapsEq
    simp only [installCreatedAddressSpace]
    rw [vmCreated]
  rw [installed]
  have hexecution' : WellFormed
      { state.execution with
        core := { state.execution.core with lifecycle := lifecycle' }
        returnAuthorityArmed := false } := by
    obtain ⟨_, _, hmodeWellFormed⟩ := hexecution
    exact ⟨hlifecycle', by simp, hmodeWellFormed⟩
  refine ⟨?_, hexecution', hlifecycle', hcaps', hvirtual', hipc', hscheduler', hpreemption',
    hresumable', htransfers', hhalted, by simp, ⟨rfl, rfl⟩, hdevices⟩
  refine ⟨rfl, rfl, rfl, ?_, ?_, rfl, ?_, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · rw [lifecycleDef]
  · rw [vmCapsEq, lifecycleDef]
  · rw [endpointsDef, lifecycleDef]
  · intro subject current
    rw [lifecycleDef] at current
    exact hauthorityCoherent subject current
  · intro object hdead
    change endpoints'.mailbox object = none
    rw [endpointsDef]
    rw [lifecycleDef] at hdead
    exact hdeadMailbox object (by rw [lifeCaps]; exact deadOld object hdead)
  · intro object envelope held
    change endpoints'.mailbox object = some envelope at held
    rw [endpointsDef] at held
    rw [lifecycleDef]
    have := hliveSender object envelope held
    rw [lifeCaps] at this
    exact this

theorem createdVirtualMemory_capabilities (state : VirtualMapping.State)
    (addressSpace owner slot : Nat) :
    (createdVirtualMemory state addressSpace owner slot).memory.capabilities =
      addressSpaceCapabilities state.memory.capabilities addressSpace owner slot := rfl

/-- Recording a new owner for an identifier that had none keeps every
existing owner record. -/
theorem setOwner_mono {owners : Nat → Option Nat} {addressSpace owner : Nat}
    (free : owners addressSpace = none) {space subject : Nat}
    (held : owners space = some subject) :
    VirtualMapping.setOwner owners addressSpace (some owner) space = some subject := by
  simp only [VirtualMapping.setOwner]
  split
  · next same => subst same; rw [free] at held; contradiction
  · exact held

/-- **Address-space creation keeps the authoritative runtime invariant**,
including the blocking store, its saved contexts, the deferred
cancellations, and invalidation publication. -/
theorem installCreatedAddressSpace_preserves_authoritativeRuntimeWellFormed
    (state : CompositeState) (addressSpace owner slot : Nat)
    (holds : AuthoritativeRuntimeWellFormed state)
    (creatable : AddressSpaceCreatable state addressSpace owner slot) :
    AuthoritativeRuntimeWellFormed (installCreatedAddressSpace state addressSpace owner slot) := by
  have runtime := installCreatedAddressSpace_preserves_runtimeWellFormed state addressSpace owner
    slot holds.left creatable
  have ownerNone := addressOwner_none_of_unissued holds.left creatable.unissued.1
  have coherent := holds.left.1
  have vmCaps : state.virtualMemory.memory.capabilities = state.capabilities :=
    coherent.2.2.2.2.1.trans coherent.2.2.2.1.symm
  have blockingScheduler : state.blockingIPC.scheduler = state.scheduler :=
    holds.left.blockingScheduler
  have schedLife : state.scheduler.lifecycle = state.lifecycle := coherent.2.1
  have lifeCaps : state.lifecycle.capabilities = state.capabilities := coherent.2.2.2.1.symm
  have empty := creatable.slotEmpty
  have dead := creatable.dead
  have liveNe : ∀ object, state.capabilities.objects object = true → object ≠ addressSpace := by
    intro object live same; rw [same, dead] at live; contradiction
  have ownsMono : ∀ subject target,
      Scheduler.ownsAddressSpace state.blockingIPC.scheduler subject = some target →
        Scheduler.ownsAddressSpace
          { state.scheduler with
            lifecycle := { state.lifecycle with
              capabilities := addressSpaceCapabilities state.capabilities addressSpace owner slot
              addressOwner := VirtualMapping.setOwner state.lifecycle.addressOwner addressSpace
                (some owner) } } subject = some target := by
    intro subject target owns
    rw [blockingScheduler, Scheduler.ownsAddressSpace_eq_some_iff, schedLife] at owns
    rw [Scheduler.ownsAddressSpace_eq_some_iff]
    exact ⟨setOwner_mono ownerNone owns.1, owns.2⟩
  obtain ⟨⟨⟨hipc, hctx⟩, hblockedDeferred, hretained⟩, hblockedResumable, hdeferredResumable⟩ :=
    holds.right
  refine ⟨runtime, ⟨⟨⟨?_, hctx⟩, hblockedDeferred, ?_⟩, hblockedResumable, hdeferredResumable⟩,
    holds.publication⟩
  · obtain ⟨_, hqueue, hwaiters, hunique, hiff, hmail, _⟩ := hipc
    simp only [CompositeState.blockingIPCContext, installCreatedAddressSpace,
      createdVirtualMemory_capabilities, vmCaps]
    refine ⟨?_, hqueue, ?_, hunique, hiff, ?_, ?_⟩
    · have := runtime.2.2.2.2.2.2.1
      simpa [installCreatedAddressSpace, createdVirtualMemory_capabilities, vmCaps] using this
    · intro endpoint subject member
      obtain ⟨hlive, ⟨authSlot, cap, held, sameObject, kind, receive, authLive⟩, hsubject,
        hrunnable, howns, hcurrent, hready⟩ := hwaiters endpoint subject member
      simp only [CompositeState.blockingIPCContext, blockingScheduler, schedLife, lifeCaps]
        at hlive held authLive hsubject hrunnable hcurrent hready
      refine ⟨addressSpaceCapabilities_objects_mono _ _ _ _ hlive,
        ⟨authSlot, cap, addressSpaceCapabilities_slots_mono _ _ _ _ empty held, sameObject, kind,
          receive, addressSpaceCapabilities_objects_mono _ _ _ _ authLive⟩,
        hsubject, hrunnable, ?_, hcurrent, by simpa [blockingScheduler] using hready⟩
      cases target : Scheduler.ownsAddressSpace state.blockingIPC.scheduler subject with
      | none => exact absurd target howns
      | some space => rw [ownsMono subject space target]; simp
    · intro endpoint envelope held
      obtain ⟨hlive0, hkind0, hend, hempty⟩ := hmail endpoint envelope held
      have hlive : state.capabilities.objects endpoint = true := by
        simpa [CompositeState.blockingIPCContext, blockingScheduler, schedLife, lifeCaps] using hlive0
      have hkind : state.capabilities.kinds endpoint = some .endpoint := by
        simpa [CompositeState.blockingIPCContext, blockingScheduler, schedLife, lifeCaps] using hkind0
      refine ⟨addressSpaceCapabilities_objects_mono _ _ _ _ hlive, ?_, hend, hempty⟩
      rw [addressSpaceCapabilities_kinds_of_ne _ _ _ _ (liveNe endpoint hlive)]
      exact hkind
    · have := runtime.2.2.2.1
      simpa [installCreatedAddressSpace, createdVirtualMemory_capabilities, vmCaps] using this
  · intro subject saved retained
    obtain ⟨hvalid, hwaiter, hsubject, hrunnable, hcurrent, hready, howns⟩ :=
      hretained subject saved retained
    simp only [CompositeState.blockingIPCContext, blockingScheduler, schedLife, lifeCaps]
      at hsubject hrunnable hcurrent hready
    simp only [CompositeState.blockingIPCContext, installCreatedAddressSpace,
      createdVirtualMemory_capabilities, vmCaps]
    exact ⟨hvalid, hwaiter, hsubject, hrunnable, hcurrent,
      by simpa [blockingScheduler] using hready, ownsMono subject subject howns⟩

end LeanOS.FailStop
