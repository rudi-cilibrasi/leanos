import LeanOS.FailStop.IPC

/-!
# Fail-stop composite: capability delegation and revocation

Accepted capability copy, direct and subtree revocation, and subject creation
publish one capability state to every consumer.  This module proves those
publications preserve the runtime invariant and states the subsystem result
soundness theorems for the authority operations.
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

/-- Accepted capability copying publishes the exact fresh capability state to
every consumer.  The composite reply cannot report success while lifecycle,
IPC, scheduler, mapping, or saved-context projections retain the old registry. -/
theorem gate_capabilityCopy_accepted_synchronizes state source destination destinationSlot
    rights next
    (hmode : state.execution.mode = .running)
    (haccepted : Capability.copy state.capabilities
      state.execution.core.context.currentSubject source destination destinationSlot rights =
        { state := next, result := .accepted })
    (hcoherent : state.Coherent)
    (hwellFormed : Capability.WellFormed state.capabilities) :
    (gate state (.capabilityCopy source destination destinationSlot rights)).result =
        .completed (.capability .accepted) ∧
      let published :=
        (gate state (.capabilityCopy source destination destinationSlot rights)).state
      published.Coherent ∧
        published.capabilities = next ∧
        published.lifecycle.capabilities = next ∧
        published.execution.core.lifecycle.capabilities = next ∧
        published.virtualMemory.memory.capabilities = next ∧
        published.ipc.endpoints.capabilities = next ∧
        published.scheduler.lifecycle.capabilities = next ∧
        published.preemption.scheduler.lifecycle.capabilities = next ∧
        published.resumable.scheduler.lifecycle.capabilities = next ∧
        published.transfers.capabilities = next ∧
        Capability.WellFormed published.capabilities := by
  have hpreserved := Capability.copy_preserves_wellFormed state.capabilities
    state.execution.core.context.currentSubject source destination destinationSlot rights hwellFormed
  rw [haccepted] at hpreserved
  have hregistries := Capability.copy_preserves_registries state.capabilities
    state.execution.core.context.currentSubject source destination destinationSlot rights
  rw [haccepted] at hregistries
  rcases hregistries with ⟨hsubjects, hobjects, _hkinds, _hcapacity⟩
  have hcoherent' : (installCopiedCapabilities state next).Coherent := by
    rcases hcoherent with
      ⟨hexecution, hscheduler, hpreemption, hcapabilities, hvirtualCapabilities,
        hipcVirtual, hipcCapabilities, hresumableScheduler, hresumableVirtual,
        htransfers, hauthority, hdeadMailbox, hliveSender⟩
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · simpa [installCopiedCapabilities] using hauthority
    · intro object hdead
      have hdeadNext : next.objects object ≠ true := by
        simpa [installCopiedCapabilities] using hdead
      apply hdeadMailbox object
      rw [← hcapabilities, ← hobjects]
      exact hdeadNext
    · intro object envelope hmailbox
      have hold := hliveSender object envelope (by
        simpa [installCopiedCapabilities] using hmailbox)
      change next.subjects envelope.sender = true
      rw [hsubjects, hcapabilities]
      exact hold
  rcases installCopiedCapabilities_synchronizes_consumers state next with
    ⟨hcapabilities, hlifecycle, hexecution, hmemory, hipc, hscheduler,
      hpreemption, hresumable, htransfers⟩
  have hpublished : Capability.WellFormed
      (installCopiedCapabilities state next).capabilities := by
    rw [hcapabilities]
    exact hpreserved
  constructor
  · simp [gate, hmode, operationReply, haccepted]
  · simpa [gate, hmode, applyOperation, haccepted] using
      And.intro hcoherent'
        (And.intro hcapabilities
          (And.intro hlifecycle
            (And.intro hexecution
              (And.intro hmemory
                (And.intro hipc
                  (And.intro hscheduler
                    (And.intro hpreemption
                      (And.intro hresumable
                        (And.intro htransfers hpublished)))))))))

/-- Accepted delegation is a complete runtime-preservation slice.  It retains
all resource projections exactly, publishes the fresh derivation to every
capability consumer, preserves authority already used by mappings, and keeps
every pending sealed identity disjoint from live slots. -/
theorem gate_capabilityCopy_accepted_preserves_runtimeWellFormed state source destination
    destinationSlot rights next
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : Capability.copy state.capabilities
      state.execution.core.context.currentSubject source destination destinationSlot rights =
        { state := next, result := .accepted }) :
    RuntimeWellFormed
        (gate state (.capabilityCopy source destination destinationSlot rights)).state ∧
      (gate state (.capabilityCopy source destination destinationSlot rights)).result =
        .completed (.capability .accepted) := by
  rcases hstate with
    ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
      hscheduler, hpreemption, hresumable, htransfers, hhalted, hlivePlan⟩
  rcases hcoherent with
    ⟨hexecutionCoherent, hschedulerCoherent, hpreemptionCoherent,
      hcapabilitiesCoherent, hvirtualCapabilitiesCoherent, hipcVirtualCoherent,
      hipcCapabilitiesCoherent, hresumableSchedulerCoherent,
      hresumableVirtualCoherent, htransfersCoherent, hauthorityCoherent,
      hdeadMailbox, hliveSender⟩
  have hcapabilities' : Capability.WellFormed next := by
    have hpreserved := Capability.copy_preserves_wellFormed state.capabilities
      state.execution.core.context.currentSubject source destination destinationSlot rights
      hcapabilities
    simpa [haccepted] using hpreserved
  have hregistries := Capability.copy_preserves_registries state.capabilities
    state.execution.core.context.currentSubject source destination destinationSlot rights
  rw [haccepted] at hregistries
  rcases hregistries with ⟨hsubjects, hobjects, hkinds, hslotCapacity⟩
  have hsubjectsLifecycle : next.subjects = state.lifecycle.capabilities.subjects :=
    hsubjects.trans (congrArg Capability.State.subjects hcapabilitiesCoherent)
  have hobjectsLifecycle : next.objects = state.lifecycle.capabilities.objects :=
    hobjects.trans (congrArg Capability.State.objects hcapabilitiesCoherent)
  have hkindsLifecycle : next.kinds = state.lifecycle.capabilities.kinds :=
    hkinds.trans (congrArg Capability.State.kinds hcapabilitiesCoherent)
  have hauthority : ∀ subject object right,
      Capability.HasAuthority state.capabilities subject object right →
        Capability.HasAuthority next subject object right := by
    intro subject object right hold
    have hpreserved := Capability.copy_preserves_authority state.capabilities
      state.execution.core.context.currentSubject source destination destinationSlot rights
      subject object right hold
    simpa [haccepted] using hpreserved
  have hlifecycle' : SubjectLifecycle.WellFormed
      { state.lifecycle with capabilities := next } := by
    simpa [SubjectLifecycle.WellFormed, hsubjectsLifecycle] using hlifecycle
  have hvirtual' : VirtualMapping.LifecycleWellFormed
      { state.virtualMemory with
        memory := { state.virtualMemory.memory with capabilities := next } } := by
    rcases hvirtual with ⟨⟨hownerLive, hmappings⟩, _hcapabilities,
      haddressSpaces, hownedAddressSpaces⟩
    refine ⟨⟨?_, ?_⟩, hcapabilities', ?_, ?_⟩
    · intro addressSpace subject howner
      have hold := hownerLive addressSpace subject howner
      rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent] at hold
      rw [hsubjects]
      exact hold
    · intro addressSpace page mapping hmapping
      obtain ⟨subject, frame, howner, hpermissions, hbinding, hframe,
        hread, hwrite⟩ := hmappings addressSpace page mapping hmapping
      refine ⟨subject, frame, howner, hpermissions, hbinding, hframe, ?_, ?_⟩
      · intro hpermission
        apply hauthority subject mapping.object .read
        rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent] at hread
        exact hread hpermission
      · intro hpermission
        apply hauthority subject mapping.object .write
        rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent] at hwrite
        exact hwrite hpermission
    · intro addressSpace subject howner
      obtain ⟨hlive, hkind, hissuedAddressSpace, hissuedMemory, hrevoke⟩ :=
        haddressSpaces addressSpace subject howner
      refine ⟨?_, ?_, hissuedAddressSpace, hissuedMemory, ?_⟩
      · rw [hobjects]
        rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent] at hlive
        exact hlive
      · rw [hkinds]
        rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent] at hkind
        exact hkind
      · apply hauthority subject addressSpace .revoke
        rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent] at hrevoke
        exact hrevoke
    · intro addressSpace hlive hkind
      apply hownedAddressSpaces addressSpace
      · rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent, ← hobjects]
        exact hlive
      · rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent, ← hkinds]
        exact hkind
  have hendpoint' : EndpointIPC.WellFormed
      { state.ipc.endpoints with capabilities := next } := by
    rcases hipc.2 with ⟨_hcapabilities, hissued, hmailbox, hdead, hhistory⟩
    refine ⟨hcapabilities', ?_, ?_, ?_, ?_⟩
    · intro object hlive hkind
      apply hissued object
      · rw [hipcCapabilitiesCoherent, ← hcapabilitiesCoherent, ← hobjects]
        exact hlive
      · rw [hipcCapabilitiesCoherent, ← hcapabilitiesCoherent, ← hkinds]
        exact hkind
    · intro object envelope hmail
      obtain ⟨hlive, hkind, hendpoint, hsent⟩ := hmailbox object envelope hmail
      refine ⟨?_, ?_, hendpoint, hsent⟩
      · rw [hobjects]
        rw [hipcCapabilitiesCoherent, ← hcapabilitiesCoherent] at hlive
        exact hlive
      · rw [hkinds]
        rw [hipcCapabilitiesCoherent, ← hcapabilitiesCoherent] at hkind
        exact hkind
    · intro object hretired
      apply hdead object
      intro hlive
      apply hretired
      rw [hobjects]
      rw [hipcCapabilitiesCoherent, ← hcapabilitiesCoherent] at hlive
      exact hlive
    · exact hhistory
  have hipc' : IPCSyscall.WellFormed
      { state.ipc with
        virtualMemory := { state.virtualMemory with
          memory := { state.virtualMemory.memory with capabilities := next } }
        endpoints := { state.ipc.endpoints with capabilities := next } } :=
    ⟨hvirtual', hendpoint'⟩
  have hscheduler' : Scheduler.WellFormed
      { state.scheduler with lifecycle := { state.lifecycle with capabilities := next } } := by
    rcases hscheduler with
      ⟨_hlifecycle, hnodup, hcapacity, hready, hcurrent⟩
    refine ⟨hlifecycle', hnodup, hcapacity, ?_, ?_⟩
    · intro subject hmember
      simpa [Scheduler.ownsAddressSpace, hschedulerCoherent, hsubjectsLifecycle] using
        hready subject hmember
    · intro subject hselected
      have hselectedOld : state.scheduler.lifecycle.current = some subject := by
        simpa [hschedulerCoherent] using hselected
      simpa [Scheduler.ownsAddressSpace, hschedulerCoherent, hsubjectsLifecycle] using
        hcurrent subject hselectedOld
  have hpreemption' : Preemption.WellFormed
      { state.preemption with scheduler :=
        { state.scheduler with lifecycle := { state.lifecycle with capabilities := next } } } := by
    exact ⟨hscheduler', hpreemption.2⟩
  have hresumable' : ResumablePreemption.WellFormed
      { state.resumable with
        scheduler := { state.scheduler with
          lifecycle := { state.lifecycle with capabilities := next } }
        translations := { state.resumable.translations with
          virtual := { state.virtualMemory with
            memory := { state.virtualMemory.memory with capabilities := next } } } } := by
    rcases hresumable with
      ⟨_hscheduler, hcapacity, hunique, hvalid, habsent, hready,
        htranslation, _hvirtual, hkindsAgreement, htlb⟩
    refine ⟨hscheduler', hcapacity, hunique, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro context hcontext
      obtain ⟨hframe, hspace, hlive, hrunnable, howner⟩ := hvalid context hcontext
      rw [hresumableSchedulerCoherent, hschedulerCoherent] at hlive hrunnable howner
      refine ⟨hframe, hspace, ?_, hrunnable, howner⟩
      rw [hsubjectsLifecycle]
      exact hlive
    · simpa [hresumableSchedulerCoherent, hschedulerCoherent] using habsent
    · simpa [ResumablePreemption.ReadyContextAgreement,
        hresumableSchedulerCoherent, hschedulerCoherent] using hready
    · simpa [ResumablePreemption.TranslationAgreement,
        hresumableSchedulerCoherent, hschedulerCoherent,
        hresumableVirtualCoherent] using htranslation
    · exact ⟨rfl, hvirtual'⟩
    · rcases hkindsAgreement with ⟨hmemoryKinds, hendpointKinds⟩
      refine ⟨?_, ?_⟩
      · intro object owner frame howned
        have hold := hmemoryKinds object owner frame (by
          simpa [hresumableSchedulerCoherent, hschedulerCoherent] using howned)
        rw [hresumableSchedulerCoherent, hschedulerCoherent] at hold
        rw [hkindsLifecycle]
        exact hold
      · intro object owner howned
        have hold := hendpointKinds object owner (by
          simpa [hresumableSchedulerCoherent, hschedulerCoherent] using howned)
        rw [hresumableSchedulerCoherent, hschedulerCoherent] at hold
        rw [hkindsLifecycle]
        exact hold
    · simpa [TLB.Coherent] using htlb
  have htransfers' : CapabilityTransfer.WellFormed
      { state.transfers with
        toEndpointState := { state.ipc.endpoints with capabilities := next } } := by
    rcases htransfers with ⟨_hendpoints, hpending⟩
    refine ⟨hendpoint', ?_⟩
    intro endpoint transfer hpendingNew
    have hpendingOld : state.transfers.pending endpoint = some transfer := hpendingNew
    obtain ⟨henvelope, hlive, hkind, hrights, hderivation, hparent,
      hparentIdentity, hidentity, habsentIdentity, huniquePending⟩ :=
      hpending endpoint transfer hpendingOld
    have htransferCapabilities : state.transfers.capabilities = state.capabilities := by
      rw [htransfersCoherent, hipcCapabilitiesCoherent, ← hcapabilitiesCoherent]
    rw [htransferCapabilities] at hlive hkind hderivation hparent hidentity habsentIdentity
    have hderivation' : next.derivations transfer.identity =
        some (some transfer.parent, transfer.object, transfer.kind, transfer.rights) := by
      have hold := Capability.copy_preserves_derivation_of_lt state.capabilities
        state.execution.core.context.currentSubject source destination destinationSlot rights
        transfer.identity hidentity
      rw [haccepted] at hold
      exact hold.trans hderivation
    obtain ⟨parentParent, parentRights, hparentDerivation, hsubset⟩ := hparent
    have hparentDerivation' : next.derivations transfer.parent =
        some (parentParent, transfer.object, transfer.kind, parentRights) := by
      have hold := Capability.copy_preserves_derivation_of_lt state.capabilities
        state.execution.core.context.currentSubject source destination destinationSlot rights
        transfer.parent (Nat.lt_trans hparentIdentity hidentity)
      rw [haccepted] at hold
      exact hold.trans hparentDerivation
    have habsentIdentity' : ∀ subject slot capability,
        next.slots subject slot = some capability → capability.identity ≠ transfer.identity := by
      have hold := Capability.copy_preserves_absent_identity state.capabilities
        state.execution.core.context.currentSubject source destination destinationSlot rights
        transfer.identity hidentity habsentIdentity
      simpa [haccepted] using hold
    have hidentity' : transfer.identity < next.nextIdentity :=
      (hcapabilities'.2.1 transfer.identity (some transfer.parent) transfer.object
        transfer.kind transfer.rights hderivation').1
    refine ⟨by simpa [htransfersCoherent] using henvelope, ?_, ?_, hrights, hderivation',
      ⟨parentParent, parentRights, hparentDerivation', hsubset⟩,
      hparentIdentity, hidentity', habsentIdentity', huniquePending⟩
    · rw [hobjects]
      exact hlive
    · rw [hkinds]
      exact hkind
  have hcoherent' : (installCopiedCapabilities state next).Coherent := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · simpa [installCopiedCapabilities] using hauthorityCoherent
    · intro object hdead
      apply hdeadMailbox object
      have hdeadNext : next.objects object ≠ true := by
        simpa [installCopiedCapabilities] using hdead
      rw [← hobjectsLifecycle]
      exact hdeadNext
    · intro object envelope hmailbox
      have hold := hliveSender object envelope (by
        simpa [installCopiedCapabilities] using hmailbox)
      change next.subjects envelope.sender = true
      rw [hsubjectsLifecycle]
      exact hold
  have hexecution' : WellFormed
      (installCopiedCapabilities state next).execution := by
    rcases hexecution with ⟨hcore, _hbound, hmodeWellFormed⟩
    refine ⟨?_, by simp [installCopiedCapabilities], hmodeWellFormed⟩
    · simpa [Interrupt.WellFormed, installCopiedCapabilities] using hlifecycle'
  have hlivePlan' :
      (installCopiedCapabilities state next).execution.returnAuthorityArmed = true →
        (installCopiedCapabilities state next).ReturnPlanLive = true := by
    simp [installCopiedCapabilities]
  constructor
  · simp only [gate, hmode, applyOperation, haccepted]
    exact ⟨hcoherent', hexecution', hlifecycle', hcapabilities', hvirtual', hipc',
      hscheduler', hpreemption', hresumable', htransfers',
      by simpa [installCopiedCapabilities] using hhalted, hlivePlan', ⟨rfl, rfl⟩,
      hlivePlan.2.2⟩
  · simp [gate, hmode, operationReply, haccepted]

/-- The authority fragment consumed by live virtual mappings and address-space
ownership.  Revocation may remove arbitrary delegated rights, but a composite
runtime publication is well formed when these three resource-critical rights
remain available through some live capability. -/
def RuntimeAuthorityPreserved (before after : Capability.State) : Prop :=
  ∀ subject object right,
    (right = .read ∨ right = .write ∨ right = .revoke) →
    Capability.HasAuthority before subject object right →
    Capability.HasAuthority after subject object right

/-- Removing slots while retaining registries, history, and runtime-critical
authority preserves every global projection.  This is shared by direct and
transitive revocation; `hslots` also preserves the sealed-transfer invariant
that pending identities are absent from live slots. -/
theorem installRevokedCapabilities_preserves_runtimeWellFormed state next
    (hstate : RuntimeWellFormed state)
    (hwellFormed : Capability.WellFormed next)
    (hsubjects : next.subjects = state.capabilities.subjects)
    (hobjects : next.objects = state.capabilities.objects)
    (hkinds : next.kinds = state.capabilities.kinds)
    (hnextIdentity : next.nextIdentity = state.capabilities.nextIdentity)
    (hderivations : next.derivations = state.capabilities.derivations)
    (hslots : ∀ subject slot capability,
      next.slots subject slot = some capability →
        state.capabilities.slots subject slot = some capability)
    (hauthority : RuntimeAuthorityPreserved state.capabilities next) :
    RuntimeWellFormed (installCopiedCapabilities state next) := by
  rcases hstate with
    ⟨hcoherent, hexecution, hlifecycle, _hcapabilities, hvirtual, hipc,
      hscheduler, hpreemption, hresumable, htransfers, hhalted, _hlivePlan⟩
  rcases hcoherent with
    ⟨hexecutionCoherent, hschedulerCoherent, _hpreemptionCoherent,
      hcapabilitiesCoherent, hvirtualCapabilitiesCoherent, _hipcVirtualCoherent,
      hipcCapabilitiesCoherent, hresumableSchedulerCoherent,
      hresumableVirtualCoherent, htransfersCoherent, hauthorityCoherent,
      hdeadMailbox, hliveSender⟩
  have hsubjectsLifecycle : next.subjects = state.lifecycle.capabilities.subjects :=
    hsubjects.trans (congrArg Capability.State.subjects hcapabilitiesCoherent)
  have hobjectsLifecycle : next.objects = state.lifecycle.capabilities.objects :=
    hobjects.trans (congrArg Capability.State.objects hcapabilitiesCoherent)
  have hkindsLifecycle : next.kinds = state.lifecycle.capabilities.kinds :=
    hkinds.trans (congrArg Capability.State.kinds hcapabilitiesCoherent)
  have hlifecycle' : SubjectLifecycle.WellFormed
      { state.lifecycle with capabilities := next } := by
    simpa [SubjectLifecycle.WellFormed, hsubjectsLifecycle] using hlifecycle
  have hvirtual' : VirtualMapping.LifecycleWellFormed
      { state.virtualMemory with
        memory := { state.virtualMemory.memory with capabilities := next } } := by
    rcases hvirtual with ⟨⟨hownerLive, hmappings⟩, _hcapabilities,
      haddressSpaces, hownedAddressSpaces⟩
    refine ⟨⟨?_, ?_⟩, hwellFormed, ?_, ?_⟩
    · intro addressSpace subject howner
      have hold := hownerLive addressSpace subject howner
      rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent] at hold
      rw [hsubjects]
      exact hold
    · intro addressSpace page mapping hmapping
      obtain ⟨subject, frame, howner, hpermissions, hbinding, hframe,
        hread, hwrite⟩ := hmappings addressSpace page mapping hmapping
      refine ⟨subject, frame, howner, hpermissions, hbinding, hframe, ?_, ?_⟩
      · intro hpermission
        apply hauthority subject mapping.object .read (Or.inl rfl)
        rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent] at hread
        exact hread hpermission
      · intro hpermission
        apply hauthority subject mapping.object .write (Or.inr (Or.inl rfl))
        rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent] at hwrite
        exact hwrite hpermission
    · intro addressSpace subject howner
      obtain ⟨hlive, hkind, hissuedAddressSpace, hissuedMemory, hrevoke⟩ :=
        haddressSpaces addressSpace subject howner
      refine ⟨?_, ?_, hissuedAddressSpace, hissuedMemory, ?_⟩
      · rw [hobjects]
        rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent] at hlive
        exact hlive
      · rw [hkinds]
        rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent] at hkind
        exact hkind
      · apply hauthority subject addressSpace .revoke (Or.inr (Or.inr rfl))
        rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent] at hrevoke
        exact hrevoke
    · intro addressSpace hlive hkind
      apply hownedAddressSpaces addressSpace
      · rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent, ← hobjects]
        exact hlive
      · rw [hvirtualCapabilitiesCoherent, ← hcapabilitiesCoherent, ← hkinds]
        exact hkind
  have hendpoint' : EndpointIPC.WellFormed
      { state.ipc.endpoints with capabilities := next } := by
    rcases hipc.2 with ⟨_hcapabilities, hissued, hmailbox, hdead, hhistory⟩
    refine ⟨hwellFormed, ?_, ?_, ?_, hhistory⟩
    · intro object hlive hkind
      apply hissued object
      · rw [hipcCapabilitiesCoherent, ← hcapabilitiesCoherent, ← hobjects]
        exact hlive
      · rw [hipcCapabilitiesCoherent, ← hcapabilitiesCoherent, ← hkinds]
        exact hkind
    · intro object envelope hmail
      obtain ⟨hlive, hkind, hendpoint, hsent⟩ := hmailbox object envelope hmail
      refine ⟨?_, ?_, hendpoint, hsent⟩
      · change next.objects object = true
        rw [hobjects]
        rw [hipcCapabilitiesCoherent, ← hcapabilitiesCoherent] at hlive
        exact hlive
      · change next.kinds object = some .endpoint
        rw [hkinds]
        rw [hipcCapabilitiesCoherent, ← hcapabilitiesCoherent] at hkind
        exact hkind
    · intro object hretired
      apply hdead object
      intro hlive
      apply hretired
      change next.objects object = true
      rw [hobjects]
      rw [hipcCapabilitiesCoherent, ← hcapabilitiesCoherent] at hlive
      exact hlive
  have hipc' : IPCSyscall.WellFormed
      { state.ipc with
        virtualMemory := { state.virtualMemory with
          memory := { state.virtualMemory.memory with capabilities := next } }
        endpoints := { state.ipc.endpoints with capabilities := next } } :=
    ⟨hvirtual', hendpoint'⟩
  have hscheduler' : Scheduler.WellFormed
      { state.scheduler with lifecycle := { state.lifecycle with capabilities := next } } := by
    rcases hscheduler with ⟨_hlifecycle, hnodup, hcapacity, hready, hcurrent⟩
    refine ⟨hlifecycle', hnodup, hcapacity, ?_, ?_⟩
    · intro subject hmember
      simpa [Scheduler.ownsAddressSpace, hschedulerCoherent, hsubjectsLifecycle] using
        hready subject hmember
    · intro subject hselected
      have hold := hcurrent subject (by simpa [hschedulerCoherent] using hselected)
      simpa [Scheduler.ownsAddressSpace, hschedulerCoherent, hsubjectsLifecycle] using hold
  have hpreemption' : Preemption.WellFormed
      { state.preemption with scheduler :=
        { state.scheduler with lifecycle := { state.lifecycle with capabilities := next } } } :=
    ⟨hscheduler', hpreemption.2⟩
  have hresumable' : ResumablePreemption.WellFormed
      { state.resumable with
        scheduler := { state.scheduler with
          lifecycle := { state.lifecycle with capabilities := next } }
        translations := { state.resumable.translations with
          virtual := { state.virtualMemory with
            memory := { state.virtualMemory.memory with capabilities := next } } } } := by
    rcases hresumable with
      ⟨_hscheduler, hcapacity, hunique, hvalid, habsent, hready,
        htranslation, _hvirtual, hkindsAgreement, htlb⟩
    refine ⟨hscheduler', hcapacity, hunique, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro context hcontext
      obtain ⟨hframe, hspace, hlive, hrunnable, howner⟩ := hvalid context hcontext
      rw [hresumableSchedulerCoherent, hschedulerCoherent] at hlive hrunnable howner
      exact ⟨hframe, hspace, by simpa [hsubjectsLifecycle] using hlive, hrunnable, howner⟩
    · simpa [hresumableSchedulerCoherent, hschedulerCoherent] using habsent
    · simpa [ResumablePreemption.ReadyContextAgreement,
        hresumableSchedulerCoherent, hschedulerCoherent] using hready
    · simpa [ResumablePreemption.TranslationAgreement,
        hresumableSchedulerCoherent, hschedulerCoherent,
        hresumableVirtualCoherent] using htranslation
    · exact ⟨rfl, hvirtual'⟩
    · rcases hkindsAgreement with ⟨hmemoryKinds, hendpointKinds⟩
      refine ⟨?_, ?_⟩
      · intro object owner frame howned
        have hold := hmemoryKinds object owner frame (by
          simpa [hresumableSchedulerCoherent, hschedulerCoherent] using howned)
        rw [hresumableSchedulerCoherent, hschedulerCoherent] at hold
        simpa [hkindsLifecycle] using hold
      · intro object owner howned
        have hold := hendpointKinds object owner (by
          simpa [hresumableSchedulerCoherent, hschedulerCoherent] using howned)
        rw [hresumableSchedulerCoherent, hschedulerCoherent] at hold
        simpa [hkindsLifecycle] using hold
    · simpa [TLB.Coherent] using htlb
  have htransfers' : CapabilityTransfer.WellFormed
      { state.transfers with
        toEndpointState := { state.ipc.endpoints with capabilities := next } } := by
    rcases htransfers with ⟨_hendpoints, hpending⟩
    refine ⟨hendpoint', ?_⟩
    intro endpoint transfer hpendingNew
    obtain ⟨henvelope, hlive, hkind, hrights, hderivation, hparent,
      hparentIdentity, hidentity, habsentIdentity, huniquePending⟩ :=
      hpending endpoint transfer hpendingNew
    have htransferCapabilities : state.transfers.capabilities = state.capabilities := by
      rw [htransfersCoherent, hipcCapabilitiesCoherent, ← hcapabilitiesCoherent]
    rw [htransferCapabilities] at hlive hkind hderivation hparent hidentity habsentIdentity
    obtain ⟨parentParent, parentRights, hparentDerivation, hsubset⟩ := hparent
    have hderivation' : next.derivations transfer.identity =
        some (some transfer.parent, transfer.object, transfer.kind, transfer.rights) := by
      rw [hderivations]
      exact hderivation
    have hparentDerivation' : next.derivations transfer.parent =
        some (parentParent, transfer.object, transfer.kind, parentRights) := by
      rw [hderivations]
      exact hparentDerivation
    have habsentIdentity' : ∀ subject slot capability,
        next.slots subject slot = some capability → capability.identity ≠ transfer.identity := by
      intro subject slot capability hslot
      exact habsentIdentity subject slot capability (hslots subject slot capability hslot)
    refine ⟨by simpa [htransfersCoherent] using henvelope, ?_, ?_, hrights, hderivation',
      ⟨parentParent, parentRights, hparentDerivation', hsubset⟩,
      hparentIdentity, by simpa [hnextIdentity] using hidentity,
      habsentIdentity', huniquePending⟩
    · simpa [hobjects] using hlive
    · simpa [hkinds] using hkind
  have hcoherent' : (installCopiedCapabilities state next).Coherent := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · simpa [installCopiedCapabilities] using hauthorityCoherent
    · intro object hdead
      apply hdeadMailbox object
      rw [← hcapabilitiesCoherent, ← hobjects]
      simpa [installCopiedCapabilities] using hdead
    · intro object envelope hmailbox
      have hold := hliveSender object envelope (by
        simpa [installCopiedCapabilities] using hmailbox)
      change next.subjects envelope.sender = true
      simpa [hsubjectsLifecycle] using hold
  have hexecution' : WellFormed (installCopiedCapabilities state next).execution := by
    rcases hexecution with ⟨hcore, _hbound, hmodeWellFormed⟩
    exact ⟨by simpa [Interrupt.WellFormed, installCopiedCapabilities] using hlifecycle',
      by simp [installCopiedCapabilities], hmodeWellFormed⟩
  exact ⟨hcoherent', hexecution', hlifecycle', hwellFormed, hvirtual', hipc',
    hscheduler', hpreemption', hresumable', htransfers',
    by simpa [installCopiedCapabilities] using hhalted,
    by simp [installCopiedCapabilities], ⟨rfl, rfl⟩, _hlivePlan.2.2⟩

/-- Creating a fresh subject publishes the exact accepted lifecycle through
every lifecycle and capability consumer in one coherent gate step.  The
lifecycle invariant is proved for the published state, rather than merely for
the private `SubjectLifecycle.create` result. -/
theorem gate_createSubject_accepted_synchronizes state subject next
    (hmode : state.execution.mode = .running)
    (haccepted : SubjectLifecycle.create state.lifecycle subject =
      { state := next, result := .accepted })
    (hcoherent : state.Coherent)
    (hwellFormed : SubjectLifecycle.WellFormed state.lifecycle) :
    (gate state (.createSubject subject)).result =
        .completed (.createSubject .accepted) ∧
      let published := (gate state (.createSubject subject)).state
      published.Coherent ∧
        published.lifecycle = next ∧
        published.execution.core.lifecycle = next ∧
        published.scheduler.lifecycle = next ∧
        published.preemption.scheduler.lifecycle = next ∧
        published.resumable.scheduler.lifecycle = next ∧
        published.capabilities = next.capabilities ∧
        published.virtualMemory.memory.capabilities = next.capabilities ∧
        published.ipc.endpoints.capabilities = next.capabilities ∧
        published.transfers.capabilities = next.capabilities ∧
        SubjectLifecycle.WellFormed published.lifecycle := by
  have hpreserved := SubjectLifecycle.create_preserves_wellFormed
    state.lifecycle subject hwellFormed
  rw [haccepted] at hpreserved
  have hpublishedCoherent : (installCreatedSubject state subject).Coherent :=
    installCreatedSubject_coherent state subject hcoherent
  constructor
  · simp [gate, hmode, operationReply, haccepted]
  · simpa [gate, hmode, applyOperation, haccepted, installCreatedSubject] using
      And.intro hpublishedCoherent hpreserved

/-- Accepted single-slot revocation is synchronized with every capability
consumer and retains the exact well-formed subsystem post-state. -/
theorem gate_capabilityRevoke_accepted_synchronizes state authoritySlot victim victimSlot next
    (hmode : state.execution.mode = .running)
    (haccepted : Capability.revokeRuntimeSafe state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot =
        { state := next, result := .accepted })
    (hcoherent : state.Coherent)
    (hwellFormed : Capability.WellFormed state.capabilities) :
    (gate state (.capabilityRevoke authoritySlot victim victimSlot)).result =
        .completed (.capability .accepted) ∧
      let published :=
        (gate state (.capabilityRevoke authoritySlot victim victimSlot)).state
      published.Coherent ∧
        published.capabilities = next ∧
        published.lifecycle.capabilities = next ∧
        published.execution.core.lifecycle.capabilities = next ∧
        published.virtualMemory.memory.capabilities = next ∧
        published.ipc.endpoints.capabilities = next ∧
        published.scheduler.lifecycle.capabilities = next ∧
        published.preemption.scheduler.lifecycle.capabilities = next ∧
        published.resumable.scheduler.lifecycle.capabilities = next ∧
        published.transfers.capabilities = next ∧
        Capability.WellFormed published.capabilities := by
  have hraw := (Capability.revokeRuntimeSafe_accepted_raw state.capabilities
    state.execution.core.context.currentSubject authoritySlot victim victimSlot next haccepted).1
  have hpreserved := Capability.revoke_preserves_wellFormed state.capabilities
    state.execution.core.context.currentSubject authoritySlot victim victimSlot hwellFormed
  rw [hraw] at hpreserved
  have hmetadata := Capability.revoke_preserves_metadata state.capabilities
    state.execution.core.context.currentSubject authoritySlot victim victimSlot
  rw [hraw] at hmetadata
  have hcoherent' : (installCopiedCapabilities state next).Coherent := by
    rcases hcoherent with
      ⟨hexecution, hscheduler, hpreemption, hcapabilities, hvirtualCapabilities,
        hipcVirtual, hipcCapabilities, hresumableScheduler, hresumableVirtual,
        htransfers, hauthority, hdeadMailbox, hliveSender⟩
    rcases hmetadata with ⟨hsubjects, hobjects, _hkinds, _hcapacity, _hnext, _hderivations⟩
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · simpa [installCopiedCapabilities] using hauthority
    · intro object hdead
      apply hdeadMailbox object
      rw [← hcapabilities, ← hobjects]
      simpa [installCopiedCapabilities] using hdead
    · intro object envelope hmailbox
      have hold := hliveSender object envelope (by
        simpa [installCopiedCapabilities] using hmailbox)
      change next.subjects envelope.sender = true
      rw [hsubjects, hcapabilities]
      exact hold
  rcases installCopiedCapabilities_synchronizes_consumers state next with
    ⟨hcapabilities, hlifecycle, hexecution, hmemory, hipc, hscheduler,
      hpreemption, hresumable, htransfers⟩
  have hpublished : Capability.WellFormed
      (installCopiedCapabilities state next).capabilities := by
    rw [hcapabilities]
    exact hpreserved
  constructor
  · simp [gate, hmode, operationReply, haccepted]
  · simpa [gate, hmode, applyOperation, haccepted] using
      And.intro hcoherent'
        (And.intro hcapabilities
          (And.intro hlifecycle
            (And.intro hexecution
              (And.intro hmemory
                (And.intro hipc
                  (And.intro hscheduler
                    (And.intro hpreemption
                      (And.intro hresumable
                        (And.intro htransfers hpublished)))))))))

/-- Accepted subtree revocation is published atomically across every
capability consumer.  The exact authoritative post-state remains well formed,
and the synchronization step establishes the composite coherence equalities
instead of leaving scheduler, IPC, or saved-context views stale. -/
theorem gate_capabilityRevokeSubtree_accepted_synchronizes state authoritySlot victim victimSlot
    next
    (hmode : state.execution.mode = .running)
    (haccepted : Capability.revokeSubtreeRuntimeSafe state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot =
        { state := next, result := .accepted })
    (hcoherent : state.Coherent)
    (hwellFormed : Capability.WellFormed state.capabilities) :
    (gate state (.capabilityRevokeSubtree authoritySlot victim victimSlot)).result =
        .completed (.capability .accepted) ∧
      let published :=
        (gate state (.capabilityRevokeSubtree authoritySlot victim victimSlot)).state
      published.Coherent ∧
        published.capabilities = next ∧
        published.lifecycle.capabilities = next ∧
        published.execution.core.lifecycle.capabilities = next ∧
        published.virtualMemory.memory.capabilities = next ∧
        published.ipc.endpoints.capabilities = next ∧
        published.scheduler.lifecycle.capabilities = next ∧
        published.preemption.scheduler.lifecycle.capabilities = next ∧
        published.resumable.scheduler.lifecycle.capabilities = next ∧
        published.transfers.capabilities = next ∧
        Capability.WellFormed published.capabilities := by
  have hraw := (Capability.revokeSubtreeRuntimeSafe_accepted_raw state.capabilities
    state.execution.core.context.currentSubject authoritySlot victim victimSlot next haccepted).1
  obtain ⟨target, hlookup, _hclear⟩ := Capability.revokeSubtreeRuntimeSafe_accepted_target
    state.capabilities state.execution.core.context.currentSubject authoritySlot victim
    victimSlot next haccepted
  have hpreserved := Capability.revokeSubtree_preserves_wellFormed
    state.capabilities state.execution.core.context.currentSubject authoritySlot victim victimSlot
    hwellFormed
  rw [hraw] at hpreserved
  have hmetadata := Capability.revokeSubtree_preserves_metadata state.capabilities
    state.execution.core.context.currentSubject authoritySlot victim victimSlot
  rw [hraw] at hmetadata
  rcases hmetadata with ⟨hsubjects, hobjects, _hkinds, _hcapacity, _hnext, _hderivations⟩
  rcases hcoherent with
    ⟨_hexecution, _hscheduler, _hpreemption, hcapabilities, _hvirtualCapabilities,
      _hipcVirtual, _hipcCapabilities, _hresumableScheduler, _hresumableVirtual,
      htransfers, hauthority, hdeadMailbox, hliveSender⟩
  have htransferMailbox : state.transfers.mailbox = state.ipc.endpoints.mailbox :=
    congrArg EndpointIPC.State.mailbox htransfers
  have hcoherent' : (installRevokedSubtree state target.identity next).Coherent := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · simpa [installRevokedSubtree, installTransfers] using hauthority
    · intro object hdead
      have hnextDead : next.objects object ≠ true := hdead
      have hold : state.ipc.endpoints.mailbox object = none := by
        apply hdeadMailbox object
        rw [← hcapabilities, ← hobjects]
        exact hnextDead
      change (CapabilityTransfer.publishSubtreeRevocation state.transfers target.identity
        next).mailbox object = none
      cases hmail : (CapabilityTransfer.publishSubtreeRevocation state.transfers
          target.identity next).mailbox object with
      | none => rfl
      | some envelope =>
          have hsome := CapabilityTransfer.publishSubtreeRevocation_mailbox_some
            state.transfers target.identity next object envelope hmail
          rw [htransferMailbox, hold] at hsome
          contradiction
    · intro object envelope hmailbox
      have hold := hliveSender object envelope (by
        rw [← htransferMailbox]
        exact CapabilityTransfer.publishSubtreeRevocation_mailbox_some
          state.transfers target.identity next object envelope hmailbox)
      change next.subjects envelope.sender = true
      rw [hsubjects, hcapabilities]
      exact hold
  have hgate : (gate state (.capabilityRevokeSubtree authoritySlot victim victimSlot)).state =
      installRevokedSubtree state target.identity next := by
    simp [gate, hmode, applyOperation, haccepted, hlookup]
  constructor
  · simp [gate, hmode, operationReply, haccepted]
  · rw [hgate]
    exact ⟨hcoherent', rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hpreserved⟩

/-- Accepted direct revocation preserves the complete runtime invariant when
the removed slot was not the last source of authority used by live mappings or
address-space ownership.  Success is paired with the exact typed capability
reply in the same gate step. -/
theorem gate_capabilityRevoke_accepted_preserves_runtimeWellFormed state authoritySlot victim
    victimSlot next
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : Capability.revokeRuntimeSafe state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot =
        { state := next, result := .accepted }) :
    RuntimeWellFormed
        (gate state (.capabilityRevoke authoritySlot victim victimSlot)).state ∧
      (gate state (.capabilityRevoke authoritySlot victim victimSlot)).result =
        .completed (.capability .accepted) := by
  obtain ⟨hraw, _hsafe⟩ := Capability.revokeRuntimeSafe_accepted_raw state.capabilities
    state.execution.core.context.currentSubject authoritySlot victim victimSlot next haccepted
  have hauthority : RuntimeAuthorityPreserved state.capabilities next :=
    fun subject object right hcritical hold => by
      have hcritical' :
          right = .read ∨ right = .write ∨ right = .revoke ∨ right = .receive := by
        rcases hcritical with hread | hwrite | hrevoke
        · exact Or.inl hread
        · exact Or.inr (Or.inl hwrite)
        · exact Or.inr (Or.inr (Or.inl hrevoke))
      exact Capability.revokeRuntimeSafe_accepted_preserves_critical_authority state.capabilities
        state.execution.core.context.currentSubject authoritySlot victim victimSlot next haccepted
        subject object right hcritical' hold
  have hmetadata := Capability.revoke_preserves_metadata state.capabilities
    state.execution.core.context.currentSubject authoritySlot victim victimSlot
  rw [hraw] at hmetadata
  rcases hmetadata with
    ⟨hsubjects, hobjects, hkinds, _hcapacity, hnextIdentity, hderivations⟩
  have hwellFormed : Capability.WellFormed next := by
    have hold := Capability.revoke_preserves_wellFormed state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot hstate.2.2.2.1
    simpa [hraw] using hold
  have hslots : ∀ subject slot capability,
      next.slots subject slot = some capability →
        state.capabilities.slots subject slot = some capability := by
    intro subject slot capability hslot
    have hold := Capability.revoke_slot_survives state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot
      subject slot capability
    rw [hraw] at hold
    exact hold hslot
  constructor
  · simp only [gate, hmode, applyOperation, haccepted]
    exact installRevokedCapabilities_preserves_runtimeWellFormed state next hstate hwellFormed
      hsubjects hobjects hkinds hnextIdentity hderivations hslots hauthority
  · simp [gate, hmode, operationReply, haccepted]

/-- The same preservation boundary applies to transitive lineage revocation.
The slot-survival projection guarantees that clearing additional descendants
cannot make a pending sealed identity suddenly live. -/
theorem gate_capabilityRevokeSubtree_accepted_preserves_runtimeWellFormed state authoritySlot
    victim victimSlot next
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : Capability.revokeSubtreeRuntimeSafe state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot =
        { state := next, result := .accepted }) :
    RuntimeWellFormed
        (gate state (.capabilityRevokeSubtree authoritySlot victim victimSlot)).state ∧
      (gate state (.capabilityRevokeSubtree authoritySlot victim victimSlot)).result =
        .completed (.capability .accepted) := by
  obtain ⟨hraw, _hsafe⟩ := Capability.revokeSubtreeRuntimeSafe_accepted_raw
    state.capabilities state.execution.core.context.currentSubject authoritySlot victim victimSlot
    next haccepted
  obtain ⟨target, hlookup, _hclear⟩ := Capability.revokeSubtreeRuntimeSafe_accepted_target
    state.capabilities state.execution.core.context.currentSubject authoritySlot victim
    victimSlot next haccepted
  have htransferCapabilities : state.transfers.capabilities = state.capabilities := by
    rcases hstate.1 with
      ⟨_, _, _, hcapabilities, _, _, hipcCapabilities, _, _, htransferEndpoints, _, _, _⟩
    calc
      state.transfers.capabilities = state.ipc.endpoints.capabilities :=
        congrArg (fun endpoints => endpoints.capabilities) htransferEndpoints
      _ = state.lifecycle.capabilities := hipcCapabilities
      _ = state.capabilities := hcapabilities.symm
  have hauthority : ∀ subject object right,
      (right = .read ∨ right = .write ∨ right = .revoke) →
      Capability.HasAuthority state.transfers.capabilities subject object right →
        Capability.HasAuthority next subject object right := by
    intro subject object right hcritical hold
    have hcritical' :
        right = .read ∨ right = .write ∨ right = .revoke ∨ right = .receive := by
      rcases hcritical with hread | hwrite | hrevoke
      · exact Or.inl hread
      · exact Or.inr (Or.inl hwrite)
      · exact Or.inr (Or.inr (Or.inl hrevoke))
    rw [htransferCapabilities] at hold
    exact Capability.revokeSubtreeRuntimeSafe_accepted_preserves_critical_authority
      state.capabilities state.execution.core.context.currentSubject authoritySlot victim
      victimSlot next hstate.2.2.2.1 haccepted subject object right hcritical' hold
  have hmetadata := Capability.revokeSubtree_preserves_metadata state.capabilities
    state.execution.core.context.currentSubject authoritySlot victim victimSlot
  rw [hraw] at hmetadata
  rcases hmetadata with
    ⟨hsubjects, hobjects, hkinds, _hcapacity, hnextIdentity, hderivations⟩
  have hwellFormed : Capability.WellFormed next := by
    have hold := Capability.revokeSubtree_preserves_wellFormed state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot hstate.2.2.2.1
    simpa [hraw] using hold
  have hslots : ∀ subject slot capability,
      next.slots subject slot = some capability →
        state.transfers.capabilities.slots subject slot = some capability := by
    intro subject slot capability hslot
    have hold := Capability.revokeSubtree_slot_survives state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot
      subject slot capability
    rw [hraw] at hold
    rw [htransferCapabilities]
    exact hold hslot
  have htransfer : CapabilityTransfer.WellFormed
      (CapabilityTransfer.publishSubtreeRevocation state.transfers target.identity next) :=
    CapabilityTransfer.publishSubtreeRevocation_preserves_wellFormed state.transfers
      target.identity next hstate.2.2.2.2.2.2.2.2.2.1 hwellFormed
      (hobjects.trans (congrArg Capability.State.objects htransferCapabilities.symm))
      (hkinds.trans (congrArg Capability.State.kinds htransferCapabilities.symm))
      (hnextIdentity.trans (congrArg Capability.State.nextIdentity htransferCapabilities.symm))
      (hderivations.trans (congrArg Capability.State.derivations htransferCapabilities.symm))
      hslots
  constructor
  · simp only [gate, hmode, applyOperation, haccepted, hlookup, installRevokedSubtree]
    exact installTransfers_preserves_runtimeWellFormed state _ hstate htransfer
      (by simpa using
        hsubjects.trans (congrArg Capability.State.subjects htransferCapabilities.symm))
      (by simpa using
        hobjects.trans (congrArg Capability.State.objects htransferCapabilities.symm))
      (by simpa using
        hkinds.trans (congrArg Capability.State.kinds htransferCapabilities.symm))
      (by simpa using hauthority)
      (fun object envelope hmailbox =>
        CapabilityTransfer.publishSubtreeRevocation_mailbox_some state.transfers
          target.identity next object envelope hmailbox)
  · simp [gate, hmode, operationReply, haccepted]

/-- A typed direct-revocation denial is globally atomic and therefore retains
the complete runtime invariant. -/
theorem gate_capabilityRevoke_rejected_atomic state authoritySlot victim victimSlot reason
    (hstate : RuntimeWellFormed state)
    (hresult : (gate state (.capabilityRevoke authoritySlot victim victimSlot)).result =
      .completed (.capability (.rejected reason)))
    (hrejected : (Capability.revokeRuntimeSafe state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot).result =
        .rejected reason) :
    (gate state (.capabilityRevoke authoritySlot victim victimSlot)).state = state ∧
      RuntimeWellFormed
        (gate state (.capabilityRevoke authoritySlot victim victimSlot)).state := by
  have hold := gate_subsystem_rejection_preserves_runtimeWellFormed state
    (.capabilityRevoke authoritySlot victim victimSlot)
    (.capability (.rejected reason)) hstate hresult
    (.capabilityRevoke authoritySlot victim victimSlot reason hrejected)
  exact ⟨hold.2, hold.1⟩

/-- A typed subtree-revocation denial is likewise a literal state-preserving
gate result. -/
theorem gate_capabilityRevokeSubtree_rejected_atomic state authoritySlot victim victimSlot reason
    (hstate : RuntimeWellFormed state)
    (hresult : (gate state (.capabilityRevokeSubtree authoritySlot victim victimSlot)).result =
      .completed (.capability (.rejected reason)))
    (hrejected : (Capability.revokeSubtreeRuntimeSafe state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot).result =
        .rejected reason) :
    (gate state (.capabilityRevokeSubtree authoritySlot victim victimSlot)).state = state ∧
      RuntimeWellFormed
        (gate state (.capabilityRevokeSubtree authoritySlot victim victimSlot)).state := by
  have hold := gate_subsystem_rejection_preserves_runtimeWellFormed state
    (.capabilityRevokeSubtree authoritySlot victim victimSlot)
    (.capability (.rejected reason)) hstate hresult
    (.capabilityRevokeSubtree authoritySlot victim victimSlot reason hrejected)
  exact ⟨hold.2, hold.1⟩

/-- Accepted transitive revocation reaches authority that is still in flight.
Every sealed descendant of the revoked lineage root loses its envelope and its
pending record in the same gate step that clears the installed descendants, and
the IPC mailbox projection observes the identical cleared mailbox.  There is no
intermediate state with only one representation removed. -/
theorem gate_capabilityRevokeSubtree_accepted_cancels_sealed_descendants state authoritySlot
    victim victimSlot next target endpoint transfer published
    (hmode : state.execution.mode = .running)
    (haccepted : Capability.revokeSubtreeRuntimeSafe state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot =
        { state := next, result := .accepted })
    (hlookup : Capability.lookup state.capabilities victim victimSlot = .found target)
    (hpublished : published =
      (gate state (.capabilityRevokeSubtree authoritySlot victim victimSlot)).state)
    (hpending : state.transfers.pending endpoint = some transfer)
    (hdescendant : CapabilityTransfer.descendsFromRoot state.transfers.capabilities
      target.identity transfer = true) :
    published.transfers.pending endpoint = none ∧
      published.transfers.mailbox endpoint = none ∧
      published.ipc.endpoints.mailbox endpoint = none := by
  have hgate : published = installRevokedSubtree state target.identity next := by
    rw [hpublished]
    simp [gate, hmode, applyOperation, haccepted, hlookup]
  subst hgate
  obtain ⟨hpendingNone, hmailboxNone⟩ :=
    CapabilityTransfer.publishSubtreeRevocation_cancels state.transfers target.identity next
      endpoint transfer hpending hdescendant
  exact ⟨hpendingNone, hmailboxNone, hmailboxNone⟩

/-- Authority strictly decreases across both representations: after accepted
transitive revocation, no retained sealed record and no installed slot
descends from the revoked lineage root, so nothing derived from it can be
installed by a later receipt or used directly. -/
theorem gate_capabilityRevokeSubtree_accepted_authority_monotone state authoritySlot
    victim victimSlot next target published
    (hmode : state.execution.mode = .running)
    (haccepted : Capability.revokeSubtreeRuntimeSafe state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot =
        { state := next, result := .accepted })
    (hlookup : Capability.lookup state.capabilities victim victimSlot = .found target)
    (hpublished : published =
      (gate state (.capabilityRevokeSubtree authoritySlot victim victimSlot)).state) :
    (∀ endpoint transfer, published.transfers.pending endpoint = some transfer →
      CapabilityTransfer.descendsFromRoot state.transfers.capabilities target.identity
        transfer = false) ∧
    (∀ subject slot capability,
      published.capabilities.slots subject slot = some capability →
        Capability.descendsFrom state.capabilities capability.identity target.identity
          state.capabilities.nextIdentity = false) := by
  obtain ⟨target', hlookup', hclear⟩ := Capability.revokeSubtreeRuntimeSafe_accepted_target
    state.capabilities state.execution.core.context.currentSubject authoritySlot victim
    victimSlot next haccepted
  rw [hlookup] at hlookup'
  obtain rfl := Capability.LookupOutcome.found.inj hlookup'
  have hgate : published = installRevokedSubtree state target.identity next := by
    rw [hpublished]
    simp [gate, hmode, applyOperation, haccepted, hlookup]
  subst hgate
  constructor
  · intro endpoint transfer hpending
    exact CapabilityTransfer.publishSubtreeRevocation_no_descendant_pending state.transfers
      target.identity next endpoint transfer hpending
  · intro subject slot capability hslot
    change next.slots subject slot = some capability at hslot
    rw [hclear] at hslot
    cases hdescendant : Capability.descendsFrom state.capabilities capability.identity
        target.identity state.capabilities.nextIdentity with
    | false => rfl
    | true =>
        have hsurvives := Capability.clearSubtree_slot_survives state.capabilities
          target.identity subject slot capability hslot
        have hremoved := Capability.clearSubtree_removes_descendant state.capabilities
          target.identity subject slot capability hsurvives hdescendant
        rw [hremoved] at hslot
        contradiction

/-- Derivation history and the identity frontier survive accepted transitive
revocation.  A canceled identity therefore stays allocated forever: no later
copy or offer can reissue it, even after its slot index is reused. -/
theorem gate_capabilityRevokeSubtree_accepted_retains_history state authoritySlot
    victim victimSlot next published
    (hmode : state.execution.mode = .running)
    (haccepted : Capability.revokeSubtreeRuntimeSafe state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot =
        { state := next, result := .accepted })
    (hpublished : published =
      (gate state (.capabilityRevokeSubtree authoritySlot victim victimSlot)).state) :
    published.capabilities.derivations = state.capabilities.derivations ∧
      published.capabilities.nextIdentity = state.capabilities.nextIdentity := by
  obtain ⟨hraw, _hsafe⟩ := Capability.revokeSubtreeRuntimeSafe_accepted_raw
    state.capabilities state.execution.core.context.currentSubject authoritySlot victim victimSlot
    next haccepted
  obtain ⟨target, hlookup, _hclear⟩ := Capability.revokeSubtreeRuntimeSafe_accepted_target
    state.capabilities state.execution.core.context.currentSubject authoritySlot victim
    victimSlot next haccepted
  have hmetadata := Capability.revokeSubtree_preserves_metadata state.capabilities
    state.execution.core.context.currentSubject authoritySlot victim victimSlot
  rw [hraw] at hmetadata
  have hgate : published = installRevokedSubtree state target.identity next := by
    rw [hpublished]
    simp [gate, hmode, applyOperation, haccepted, hlookup]
  subst hgate
  exact ⟨hmetadata.2.2.2.2.2, hmetadata.2.2.2.2.1⟩

/-- Unrelated authority is untouched by accepted transitive revocation: sealed
records and envelopes outside the revoked lineage, every installed slot outside
the subtree, and the scheduler queue, current subject, saved contexts,
mappings, and execution context are exactly the pre-state values. -/
theorem gate_capabilityRevokeSubtree_accepted_preserves_unrelated state authoritySlot
    victim victimSlot next target published
    (hmode : state.execution.mode = .running)
    (haccepted : Capability.revokeSubtreeRuntimeSafe state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot =
        { state := next, result := .accepted })
    (hlookup : Capability.lookup state.capabilities victim victimSlot = .found target)
    (hpublished : published =
      (gate state (.capabilityRevokeSubtree authoritySlot victim victimSlot)).state) :
    (∀ endpoint transfer, state.transfers.pending endpoint = some transfer →
      CapabilityTransfer.descendsFromRoot state.transfers.capabilities target.identity
        transfer = false →
      published.transfers.pending endpoint = some transfer ∧
        published.transfers.mailbox endpoint = state.transfers.mailbox endpoint) ∧
    (∀ endpoint, state.transfers.pending endpoint = none →
      published.transfers.mailbox endpoint = state.transfers.mailbox endpoint) ∧
    (∀ subject slot capability, state.capabilities.slots subject slot = some capability →
      Capability.descendsFrom state.capabilities capability.identity target.identity
        state.capabilities.nextIdentity = false →
      published.capabilities.slots subject slot = some capability) ∧
    published.scheduler.ready = state.scheduler.ready ∧
    published.lifecycle.current = state.lifecycle.current ∧
    published.resumable.contexts = state.resumable.contexts ∧
    published.virtualMemory.mappings = state.virtualMemory.mappings ∧
    published.execution.core.context = state.execution.core.context := by
  obtain ⟨target', hlookup', hclear⟩ := Capability.revokeSubtreeRuntimeSafe_accepted_target
    state.capabilities state.execution.core.context.currentSubject authoritySlot victim
    victimSlot next haccepted
  rw [hlookup] at hlookup'
  obtain rfl := Capability.LookupOutcome.found.inj hlookup'
  have hgate : published = installRevokedSubtree state target.identity next := by
    rw [hpublished]
    simp [gate, hmode, applyOperation, haccepted, hlookup]
  subst hgate
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · intro endpoint transfer hpending hunrelated
    refine ⟨CapabilityTransfer.publishSubtreeRevocation_pending_unrelated state.transfers
      target.identity next endpoint transfer hpending hunrelated, ?_⟩
    apply CapabilityTransfer.publishSubtreeRevocation_mailbox_unrelated
    intro other hother
    rw [hpending] at hother
    cases hother
    exact hunrelated
  · intro endpoint hnone
    apply CapabilityTransfer.publishSubtreeRevocation_mailbox_unrelated
    intro other hother
    rw [hnone] at hother
    cases hother
  · intro subject slot capability hslot hunrelated
    change next.slots subject slot = some capability
    rw [hclear]
    exact Capability.clearSubtree_retains_unrelated state.capabilities target.identity
      subject slot capability hslot hunrelated

/-- A completed syscall exposes exactly the reply produced under the
kernel-selected caller and address space. -/
theorem syscall_result_sound state call
    (hmode : state.execution.mode = .running) :
    (gate state (.syscall call)).result =
      .completed (.syscall (Syscall.dispatch state.virtualMemory state.syscallContext call).reply) :=
  by simp [gate, hmode, operationReply]

/-- A completed IPC call likewise uses only the execution latch's identity;
there is no public constructor capable of supplying another trusted context. -/
theorem ipc_result_sound state call
    (hmode : state.execution.mode = .running) :
    (gate state (.ipc call)).result =
      .completed (.ipc (dispatchIPC state call).reply) :=
  by simp [gate, hmode, operationReply]

/-- Capability authority is always evaluated for the live subject selected by
the execution latch; the public operation has no actor field to vary. -/
theorem capability_copy_result_sound state source destination destinationSlot rights
    (hmode : state.execution.mode = .running) :
    (gate state (.capabilityCopy source destination destinationSlot rights)).result =
      .completed (.capability
        (Capability.copy state.capabilities state.execution.core.context.currentSubject
          source destination destinationSlot rights).result) := by
  simp [gate, hmode, operationReply]

/-- Mapping authority and the target address space are both projected from the
live execution context rather than accepted as public scalar arguments. -/
theorem map_result_sound state slot page permissions
    (hmode : state.execution.mode = .running) :
    (gate state (.map slot page permissions)).result =
      .completed (.map
        (VirtualMapping.map state.virtualMemory state.execution.core.context.currentSubject slot
          state.execution.core.context.activeAddressSpace page permissions).result) := by
  simp [gate, hmode, operationReply]

/-- Every public operation that can consult or change capability authority is
confined to the subject selected by the execution latch.  The operation data
can choose handles, slots, rights, pages, and payload words, but it cannot
supply an actor or active address space: each typed reply is the exact result
of the named subsystem transition under the authoritative kernel identity. -/
theorem authority_operations_result_sound state
    syscallCall ipcCall endpointWord sourceWord sourceKind payload rights
    source destination destinationSlot authoritySlot victim victimSlot slot page permissions
    (hmode : state.execution.mode = .running) :
    (gate state (.syscall syscallCall)).result =
        .completed (.syscall
          (Syscall.dispatch state.virtualMemory state.syscallContext syscallCall).reply) ∧
    (gate state (.ipc ipcCall)).result =
        .completed (.ipc (authoritativeIPCReply state ipcCall)) ∧
    (gate state
        (.transferOffer endpointWord sourceWord sourceKind payload rights)).result =
        .completed (.transferOffer
          (CapabilityTransfer.offerWords state.transfers
            state.execution.core.context.currentSubject endpointWord sourceWord sourceKind
            payload rights).result) ∧
    (gate state (.transferAccept endpointWord destinationSlot)).result =
        .completed (.transferAccept
          (CapabilityTransfer.acceptWord state.transfers
            state.execution.core.context.currentSubject endpointWord destinationSlot).result
          (CapabilityTransfer.acceptWord state.transfers
            state.execution.core.context.currentSubject endpointWord destinationSlot).deliveredWord) ∧
    (gate state (.capabilityCopy source destination destinationSlot rights)).result =
        .completed (.capability
          (Capability.copy state.capabilities
            state.execution.core.context.currentSubject source destination destinationSlot
            rights).result) ∧
    (gate state (.capabilityRevoke authoritySlot victim victimSlot)).result =
        .completed (.capability
          (Capability.revokeRuntimeSafe state.capabilities
            state.execution.core.context.currentSubject authoritySlot victim victimSlot).result) ∧
    (gate state (.capabilityRevokeSubtree authoritySlot victim victimSlot)).result =
        .completed (.capability
          (Capability.revokeSubtreeRuntimeSafe state.capabilities
            state.execution.core.context.currentSubject authoritySlot victim victimSlot).result) ∧
    (gate state (.map slot page permissions)).result =
        .completed (.map
          (VirtualMapping.map state.virtualMemory
            state.execution.core.context.currentSubject slot
            state.execution.core.context.activeAddressSpace page permissions).result) ∧
    (gate state (.unmap page)).result =
        .completed (.unmap
          (VirtualMapping.unmap state.virtualMemory
            state.execution.core.context.currentSubject
            state.execution.core.context.activeAddressSpace page).result) ∧
    (gate state (.protect page permissions)).result =
        .completed (.protect
          (TLB.protect state.resumable.translations
            state.execution.core.context.currentSubject
            state.execution.core.context.activeAddressSpace page permissions).result) := by
  simp [gate, hmode, operationReply, authoritativeIPCReply]

end LeanOS.FailStop
