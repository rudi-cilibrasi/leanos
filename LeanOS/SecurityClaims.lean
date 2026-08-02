import LeanOS.BootInterruptPhase
import LeanOS.BoundedLifecycle
import LeanOS.KernelTransition
import LeanOS.Capability
import LeanOS.FrameAllocator
import LeanOS.FrameBudget
import LeanOS.FrameBudgetScenario
import LeanOS.X86PageTable
import LeanOS.Syscall
import LeanOS.FailStop
import LeanOS.InterruptEntry
import LeanOS.FaultDispatch
import LeanOS.PrivilegeEntryStack
import LeanOS.PrivilegeEntryControl
import LeanOS.ExtendedState
import LeanOS.ScheduledObservation
import LeanOS.DMAQuarantine
import LeanOS.IOMMU
import LeanOS.DirectPortIO
import LeanOS.DirectPortContainment
import LeanOS.UserFaultContainmentVocabulary
import LeanOS.StaleTranslation
import LeanOS.InvalidationPublication

/-! # Stable security-claim contract

Each theorem independently restates one advertised proposition. Changes to an
implementation theorem's assumptions or conclusion therefore require an
explicit change here and in `docs/security-claims.md`.
-/
namespace LeanOS.SecurityClaims

/-- SC-DIRECT-PORT-USER-DENIAL: user-origin port/value words cannot select a
kernel purpose or produce device mutation, and accepted controls produce the
modeled `#GP(0)` denial. -/
theorem direct_port_user_denial_preserves_devices state live request
    (hpolicy : DirectPortIO.AcceptedControls state.controls)
    (hlive : live = state.controls) :
    DirectPortIO.executeUser state live request =
        { state, result := .userDeniedGP } ∧
      (DirectPortIO.executeUser state live request).state.devices = state.devices := by
  exact ⟨DirectPortIO.accepted_user_request_denied_gp state live request hpolicy hlive,
    DirectPortIO.user_request_preserves_device_state state live request⟩

/-- SC-DIRECT-PORT-KERNEL-CONFINEMENT: a typed kernel acceptance requires live
kernel privilege, the exact reviewed purpose/port/direction/width manifest key,
and fresh controls. -/
theorem direct_port_kernel_operation_confined state live request
    (haccepted : (DirectPortIO.executeKernel state live request).result =
      .kernelAccepted) :
    DirectPortIO.AcceptedControls state.controls ∧
      live = state.controls ∧
      DirectPortIO.privilegeAllows live .kernel = true ∧
      DirectPortIO.portManifest.contains request.key = true ∧
      (DirectPortIO.executeKernel state live request).state.controls = state.controls ∧
      (DirectPortIO.executeKernel state live request).state.devices =
        DirectPortIO.applyKernel state.devices request := by
  exact DirectPortIO.kernel_acceptance_confined state live request haccepted

/-- SC-DIRECT-PORT-CONTAINMENT: the composed CPL3 port-denial containment
sequence denies the untrusted user port operation with an unchanged device
projection and a CPL3-denying finite privilege view, then retires the
kernel-selected faulting subject through the atomic cleanup/survivor transition;
the untrusted port/value/width words never reach a kernel operation, and the
denied attempt can never return to the faulting subject. -/
theorem direct_port_denial_survivor_contained
    (devices : DirectPortIO.State) (liveControls : DirectPortIO.Controls)
    (operation : DirectPortIO.PortOperation)
    (schedule : ResumablePreemption.State) (entry : InterruptEntry.Result)
    (hpolicy : DirectPortIO.AcceptedControls devices.controls)
    (hlive : liveControls = devices.controls)
    (hsuccess :
      (∃ reason, (FaultDispatch.dispatch schedule entry).action = .idle reason) ∨
      ∃ reason context,
        (FaultDispatch.dispatch schedule entry).action = .dispatch reason context) :
    let step := DirectPortContainment.containDeniedPort
      devices liveControls operation schedule entry
    step.port.result = .userDeniedGP ∧
      step.port.state.devices = devices.devices ∧
      DirectPortIO.privilegeAllows liveControls .user = false ∧
      ∃ faulting,
        schedule.scheduler.lifecycle.current = some faulting ∧
          step.fault.state.scheduler.lifecycle.capabilities.subjects faulting = false ∧
          step.fault.state.scheduler.lifecycle.runnable faulting = false ∧
          faulting ∉ step.fault.state.scheduler.ready ∧
          step.fault.state.scheduler.lifecycle.current ≠ some faulting ∧
          ResumablePreemption.contextFor step.fault.state.contexts faulting = none := by
  obtain ⟨hdenied, hdevices, hcpl, faulting, hcurrent, _, _, hdead, hnotrun,
      hready, hnotcurrent, hcontext, _⟩ :=
    DirectPortContainment.denied_port_contained devices liveControls operation schedule entry
      hpolicy hlive hsuccess
  exact ⟨hdenied, hdevices, hcpl,
    faulting, hcurrent, hdead, hnotrun, hready, hnotcurrent, hcontext⟩

/-- SC-DMA-QUARANTINE: an accepted nonempty q35 quarantine plus the explicit
bus-master device-control contract preserves every modeled memory projection. -/
theorem dma_quarantine_preserves_complete_projection
    (accepted : DMAQuarantine.AcceptedSnapshot) (target : DMAQuarantine.BDF)
    (before after : DMAQuarantine.MemoryProjection)
    (hcontract : DMAQuarantine.DeviceContract accepted.snapshot target before after)
    (hknown : ∃ function ∈ accepted.snapshot.functions,
      function.bdf = target ∧ function.status = .present) :
    after.physicalMemory = before.physicalMemory ∧
      after.allocatorOwnership = before.allocatorOwnership ∧
      after.pageTableFrames = before.pageTableFrames ∧
      after.kernelOwnedFrames = before.kernelOwnedFrames ∧
      after.kernelState = before.kernelState ∧
      after.subjectVisible = before.subjectVisible := by
  exact DMAQuarantine.unowned_device_preserves_complete_projection accepted target before after
    hcontract hknown

/-- SC-DMA-QUARANTINE-TRACE: every finite issue-local trace of continuing
control operations and contracted unowned-device attempts preserves the live
quarantine invariant and every modeled memory projection. -/
theorem dma_quarantine_nonfatal_trace_preserves_complete_projection
    (before after : DMAQuarantine.RuntimeState)
    (hinvariant : DMAQuarantine.RuntimeInvariant before)
    (trace : DMAQuarantine.QuarantineTrace before after) :
    DMAQuarantine.RuntimeInvariant after ∧
      DMAQuarantine.quarantine after.accepted.snapshot = true ∧
      after.memory.physicalMemory = before.memory.physicalMemory ∧
      after.memory.allocatorOwnership = before.memory.allocatorOwnership ∧
      after.memory.pageTableFrames = before.memory.pageTableFrames ∧
      after.memory.kernelOwnedFrames = before.memory.kernelOwnedFrames ∧
      after.memory.kernelState = before.memory.kernelState ∧
      after.memory.subjectVisible = before.memory.subjectVisible := by
  exact DMAQuarantine.nonfatal_trace_preserves_quarantine_and_memory
    hinvariant trace

/-- The pinned q35 manifest has a concrete accepted, nonempty quarantine
snapshot; SC-DMA-QUARANTINE is not discharged by an empty inventory. -/
theorem dma_quarantine_q35_nonvacuous :
    (DMAQuarantine.validate DMAQuarantine.q35Snapshot).isAccepted = true := by
  native_decide

/-- The finite-trace claim has a concrete nonempty mixed trace containing both
a continuing public-control step and a named present VGA device attempt. -/
theorem dma_quarantine_q35_trace_nonvacuous :
    ∃ middle, DMAQuarantine.QuarantineStep DMAQuarantine.q35Runtime middle ∧
      DMAQuarantine.QuarantineTrace middle DMAQuarantine.q35Runtime :=
  DMAQuarantine.q35_mixed_trace_nonvacuous

/-- SC-DMA-QUARANTINE-GLOBAL: the sole authoritative runtime invariant
contains the exact boot-accepted PCI control observation, and every finite
ordinary/blocking/deferred successor suffix preserves that nonempty deny-all
quarantine. -/
theorem dma_quarantine_global_runtime_preservation
    (state : FailStop.CompositeState)
    (operations : List FailStop.AuthoritativeOperation)
    (hinvariant : FailStop.AuthoritativeRuntimeWellFormed state) :
    let next := FailStop.runAuthoritativeOperations state operations
    next.DMAQuarantined ∧
      DMAQuarantine.quarantine next.dmaObserved = true := by
  exact FailStop.runAuthoritativeOperations_preserves_dmaQuarantined
    state operations hinvariant.dmaQuarantined

set_option maxRecDepth 100000 in
/-- Concrete non-vacuity witness: the accepted bounded sample boot input
produces an authoritative runtime satisfying the global DMA claim's premise. -/
theorem dma_quarantine_global_runtime_nonvacuous :
    match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
    | .ok plan =>
        FailStop.AuthoritativeRuntimeWellFormed (FailStop.bootRuntime plan)
    | .error _ => False := by
  generalize hresult : BootPageTablePlan.compile BootPageTablePlan.sampleInput = result
  cases result with
  | error reason =>
      have hsuccess :
          (match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
            | .ok _ => true
            | .error _ => false) = true := by
        native_decide
      simp [hresult] at hsuccess
  | ok plan =>
      apply (FailStop.bootRuntime_deferredBlockingRuntimeWellFormed
        BootPageTablePlan.sampleInput plan hresult).authoritative
      simpa [FailStop.bootRuntime] using
        InvalidationPublication.initial_wellFormed

/-- SC-DMA-AUTHORITATIVE-PROJECTION: under an explicit caller-supplied
`DeviceContract` assumption over the authoritative live PCI observation, a
named present device preserves the complete modeled memory projection.
Neither `DMAQuarantined` nor the authoritative runtime invariant proves or
discharges that trusted hardware contract. This is an IOMMU-independent model
theorem, not a claim about hardware obedience to the PCI Command register. -/
theorem dma_authoritative_unowned_device_preservation
    (state : FailStop.CompositeState)
    (hinvariant : FailStop.AuthoritativeRuntimeWellFormed state)
    (target : DMAQuarantine.BDF)
    (before after : DMAQuarantine.MemoryProjection)
    (hcontract : DMAQuarantine.DeviceContract
      state.dmaObserved target before after)
    (hknown : ∃ function ∈ state.dmaObserved.functions,
      function.bdf = target ∧ function.status = .present) :
    after.physicalMemory = before.physicalMemory ∧
      after.allocatorOwnership = before.allocatorOwnership ∧
      after.pageTableFrames = before.pageTableFrames ∧
      after.kernelOwnedFrames = before.kernelOwnedFrames ∧
      after.kernelState = before.kernelState ∧
      after.subjectVisible = before.subjectVisible :=
  hinvariant.dmaQuarantined.unownedDevicePreservesCompleteProjection
    target before after hcontract hknown

/-- SC-DMA-CONTROL-FAILSTOP: an invalid live PCI observation is a fatal
composite transition, and every subsequent authoritative successor operation
is absorbed. -/
theorem dma_invalid_live_control_is_fatal_and_absorbing
    (state : FailStop.CompositeState) (snapshot : DMAQuarantine.Snapshot)
    (reason : DMAQuarantine.RejectReason)
    (operations : List FailStop.AuthoritativeOperation)
    (hrunning : state.execution.mode = .running)
    (hinvalid : DMAQuarantine.validate snapshot = .rejected reason) :
    let next := (FailStop.observeDMAControl state snapshot).state
    (∃ record, next.execution.mode = .halted record) ∧
      FailStop.runAuthoritativeOperations next operations = next := by
  have h := FailStop.observeDMAControl_invalid_authoritative_suffix_absorbing
    state snapshot reason operations hrunning hinvalid
  exact ⟨⟨_, h.1⟩, h.2⟩

/-- SC-DMA-CONTROL-DRIFT-FAILSTOP: a valid live PCI observation that differs from
the boot-accepted authority is also a fatal composite transition, and every
subsequent authoritative successor operation is absorbed. -/
theorem dma_changed_live_control_is_fatal_and_absorbing
    (state : FailStop.CompositeState) (snapshot : DMAQuarantine.Snapshot)
    (accepted : DMAQuarantine.AcceptedSnapshot)
    (operations : List FailStop.AuthoritativeOperation)
    (hrunning : state.execution.mode = .running)
    (hvalid : DMAQuarantine.validate snapshot = .accepted accepted)
    (hchanged : snapshot ≠ state.dmaAccepted.snapshot) :
    let next := (FailStop.observeDMAControl state snapshot).state
    (∃ record, next.execution.mode = .halted record) ∧
      FailStop.runAuthoritativeOperations next operations = next := by
  have h := FailStop.observeDMAControl_changed_authoritative_suffix_absorbing
    state snapshot accepted operations hrunning hvalid hchanged
  exact ⟨⟨_, h.1⟩, h.2⟩

set_option maxRecDepth 100000 in
/-- Concrete non-vacuity witness: the accepted bounded sample boot runtime and
the q35 Command-bit drift satisfy the stable claim's validation and inequality
premises, then enter a fatal state that absorbs every authoritative suffix. -/
theorem dma_changed_live_control_nonvacuous :
    match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
    | .ok plan =>
        ∃ accepted,
          DMAQuarantine.validate DMAQuarantine.q35CommandBitFlipSnapshot =
              .accepted accepted ∧
            DMAQuarantine.q35CommandBitFlipSnapshot ≠
              (FailStop.bootRuntime plan).dmaAccepted.snapshot ∧
            ∀ operations,
              let next := (FailStop.observeDMAControl (FailStop.bootRuntime plan)
                DMAQuarantine.q35CommandBitFlipSnapshot).state
              (∃ record, next.execution.mode = .halted record) ∧
                FailStop.runAuthoritativeOperations next operations = next
    | .error _ => False := by
  generalize hresult : BootPageTablePlan.compile BootPageTablePlan.sampleInput = result
  cases result with
  | error reason =>
      have hsuccess :
          (match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
            | .ok _ => true
            | .error _ => false) = true := by
        native_decide
      simp [hresult] at hsuccess
  | ok plan =>
      generalize hvalid :
        DMAQuarantine.validate DMAQuarantine.q35CommandBitFlipSnapshot = validation
      cases validation with
      | rejected reason =>
          have haccepted :
              (DMAQuarantine.validate
                DMAQuarantine.q35CommandBitFlipSnapshot).isAccepted = true := by
            native_decide
          rw [hvalid] at haccepted
          change false = true at haccepted
          exact Bool.noConfusion haccepted
      | accepted accepted =>
          have hchangedAccepted :
              DMAQuarantine.q35CommandBitFlipSnapshot ≠
                DMAQuarantine.q35Accepted.snapshot := by
            native_decide
          have hchanged :
              DMAQuarantine.q35CommandBitFlipSnapshot ≠
                (FailStop.bootRuntime plan).dmaAccepted.snapshot := by
            simpa [FailStop.bootRuntime] using hchangedAccepted
          refine ⟨accepted, rfl, hchanged, ?_⟩
          intro operations
          exact dma_changed_live_control_is_fatal_and_absorbing
            (FailStop.bootRuntime plan) DMAQuarantine.q35CommandBitFlipSnapshot
            accepted operations rfl hvalid hchanged

/-! ## Static assigned-device confinement claims

These wrappers are deliberately model-only.  `IOMMU.DeviceSemantics` trusts
the platform boundary to supply the source identity and transfer range and
trusted software to attach the active assignment generation before lookup;
PCIe does not carry that software generation.  None of these claims proves
VT-d, PCIe, generated code, QEMU, or a binary.
-/

/-- SC-IOMMU-READ-CONFIDENTIALITY: a finite sequence of authorized read views
is insensitive to every byte outside the union of those exact readable
backing-frame ranges. -/
theorem iommu_finite_read_confidentiality
    (state : IOMMU.AuthoritativeExtension) (_hstate : state.Invariant)
    alternateMemory
    (views : List (IOMMU.AuthorizedReadView state.iommu))
    (hequivalent :
      IOMMU.ReadViewsEquivalent state.iommu.core.memory alternateMemory views) :
    IOMMU.actualReadObservations views =
      IOMMU.observeReadViews alternateMemory views :=
  IOMMU.actual_read_trace_confidentiality
    state.iommu alternateMemory views hequivalent

/-- SC-IOMMU-WRITE-INTEGRITY: a finite device trace leaves every byte of a
protected, physically unassigned, or other-owner live frame identical. -/
theorem iommu_finite_write_integrity
    (state : IOMMU.AuthoritativeExtension) (_hstate : state.Invariant)
    (events : List IOMMU.DeviceEvent)
    (frame : IOMMU.FrameId)
    (hisolated : IOMMU.FrameIsolatedFromTrace state.iommu events frame) :
    (IOMMU.runDeviceTrace state.iommu events).1.core.memory frame =
      state.iommu.core.memory frame :=
  IOMMU.isolated_trace_integrity state.iommu events frame hisolated

/-- SC-IOMMU-NONFORGERY: every successful translation binds source,
assignment generation, domain, owner, and live backing frame to the exact
kernel-derived authority already in state. -/
theorem iommu_translation_nonforgery
    (state : IOMMU.AuthoritativeExtension) (_hstate : state.Invariant)
    (translation : IOMMU.Translation state.iommu request direction) :
    IOMMU.findAssignmentBySource state.iommu.core request.source
        request.assignmentGeneration = some translation.assignment ∧
      state.iommu.core.mappings.find? (fun candidate =>
        candidate.assignment == translation.assignment.handle &&
          IOMMU.rangeContained request.iova request.length
            candidate.iova candidate.length) = some translation.mapping ∧
      IOMMU.findFrame state.iommu.core translation.mapping.frame =
          some translation.frame ∧
      translation.assignment.source = request.source ∧
      translation.assignment.handle.generation = request.assignmentGeneration ∧
      translation.mapping.assignment = translation.assignment.handle ∧
      translation.mapping.domain = translation.assignment.domain ∧
      translation.mapping.owner = translation.assignment.owner ∧
      translation.frame.handle = translation.mapping.frame ∧
      translation.frame.owner = translation.assignment.owner :=
  IOMMU.translation_nonforgery translation

/-- SC-IOMMU-CLEANUP: accepted assignment teardown removes every mapping for
the exact generation-checked assignment. -/
theorem iommu_teardown_cleanup
    (state : IOMMU.AuthoritativeExtension) (hstate : state.Invariant)
    (handle : IOMMU.AssignmentHandle)
    (after : IOMMU.AuthoritativeExtension) (hafter : after.Invariant)
    (haccepted :
      IOMMU.gatedByKernel state hstate (.teardown handle) =
        .accepted after hafter .tornDown) :
    after.iommu.core.mappings.all (·.assignment != handle) = true :=
  IOMMU.gated_teardown_removes_all_mappings
    state hstate handle after hafter haccepted

/-- SC-IOMMU-LIFETIME: release of a frame generation reachable through an
active DMA mapping is a typed, complete-state rejection. -/
theorem iommu_reachable_frame_release_denied
    (state : IOMMU.AuthoritativeExtension) (hstate : state.Invariant)
    (handle : IOMMU.FrameHandle)
    (hreachable : state.iommu.core.mappings.any (·.frame == handle) = true) :
    ∃ reason,
      IOMMU.gatedByKernel state hstate (.releaseFrame handle) =
        .rejected reason :=
  IOMMU.gated_release_rejects_reachable_frame
    state hstate handle hreachable

/-- SC-IOMMU-FAILSTOP: once the authoritative global execution latch is
halted, every finite IOMMU control suffix preserves the complete IOMMU state. -/
theorem iommu_fatal_suffix_absorbing
    (state : IOMMU.AuthoritativeExtension) (hstate : state.Invariant)
    (operations : List IOMMU.Operation) (record : FailStop.HaltRecord)
    (hhalted : state.kernel.execution.mode = .halted record) :
    IOMMU.runGated state hstate operations = state :=
  IOMMU.halted_iommu_suffix_absorbing
    state hstate operations record hhalted

/-- SC-LIFETIME-IDENTITY-NO-REUSE: under the bounded-issuer runtime invariant,
every finite sequence of composite lifecycle operations preserves
counter/history agreement, can never make a retired object identity or a
terminated subject identity live again, and keeps an exhausted subject or
object issuer exhausted. -/
theorem lifetime_identity_no_reuse (runtime : BoundedLifecycle.Runtime)
    (operations : List BoundedLifecycle.Operation)
    (hinvariant : BoundedLifecycle.Invariant runtime) :
    BoundedLifecycle.Invariant (BoundedLifecycle.runOperations runtime operations) ∧
      (∀ object, BoundedLifecycle.issuedObject runtime object = true →
        runtime.virtualMemory.memory.capabilities.objects object = false →
        (BoundedLifecycle.runOperations runtime
          operations).virtualMemory.memory.capabilities.objects object = false) ∧
      (∀ subject, runtime.lifecycle.issuedSubjects subject = true →
        runtime.lifecycle.capabilities.subjects subject = false →
        (BoundedLifecycle.runOperations runtime
          operations).lifecycle.capabilities.subjects subject = false) ∧
      (LifetimeIssuer.exhausted runtime.subjectIssuer = true →
        LifetimeIssuer.exhausted (BoundedLifecycle.runOperations runtime
          operations).subjectIssuer = true) ∧
      (LifetimeIssuer.exhausted runtime.objectIssuer = true →
        LifetimeIssuer.exhausted (BoundedLifecycle.runOperations runtime
          operations).objectIssuer = true) := by
  exact BoundedLifecycle.bounded_identity_no_reuse runtime operations hinvariant

/-- The no-reuse bundle is not vacuous: the concrete sample runtime satisfies
the invariant and survives a mixed creation/retirement trace over both
identity domains and all three object kinds. -/
theorem lifetime_identity_no_reuse_nonvacuous :
    BoundedLifecycle.Invariant BoundedLifecycle.sampleRuntime ∧
      BoundedLifecycle.Invariant (BoundedLifecycle.runOperations
        BoundedLifecycle.sampleRuntime
        [.createSubject, .allocateMemory 0 0, .createEndpoint 0 1,
          .createAddressSpace 0 2, .destroyEndpoint 0 1, .allocateMemory 1 0]) := by
  exact ⟨BoundedLifecycle.sampleRuntime_invariant,
    (BoundedLifecycle.bounded_identity_no_reuse _ _
      BoundedLifecycle.sampleRuntime_invariant).1⟩

/-- SC-KERNEL-DET: the first modeled transition is deterministic. -/
theorem kernel_transition_deterministic
    (state : KernelTransition.State) (command : KernelTransition.Command)
    (first second : KernelTransition.Outcome)
    (hfirst : KernelTransition.transition state command = first)
    (hsecond : KernelTransition.transition state command = second) : first = second := by
  exact KernelTransition.transition_deterministic state command first second hfirst hsecond

/-- SC-KERNEL-WF: the first modeled transition preserves well-formedness. -/
theorem kernel_transition_preserves_wellFormed
    (state : KernelTransition.State) (command : KernelTransition.Command)
    (hstate : KernelTransition.WellFormed state) :
    KernelTransition.WellFormed (KernelTransition.transition state command).state := by
  exact KernelTransition.transition_preserves_wellFormed state command hstate

/-- SC-CAP-AUTH: capability copying cannot create authority without provenance. -/
theorem capability_copy_no_authority_amplification
    (state : Capability.State) (actor : Capability.SubjectId)
    (source : Capability.SlotId) (destination : Capability.SubjectId)
    (destinationSlot : Capability.SlotId) (requested : Capability.Rights)
    (candidate : Capability.SubjectId) (object : Capability.ObjectId)
    (right : Capability.Right)
    (hauthority : Capability.HasAuthority
      (Capability.copy state actor source destination destinationSlot requested).state
      candidate object right) :
    Capability.HasAuthority state candidate object right ∨
      Capability.HasAuthority state actor object right := by
  exact Capability.copy_no_authority_amplification state actor source destination
    destinationSlot requested candidate object right hauthority

/-- SC-FRAME-OWNER: a frame cannot have two distinct modeled owners. -/
theorem frame_ownership_exclusive
    (state : FrameAllocator.State) (frame : FrameAllocator.FrameId)
    (left right : FrameAllocator.OwnerId)
    (hleft : FrameAllocator.IsOwnedBy state frame left)
    (hright : FrameAllocator.IsOwnedBy state frame right) : left = right := by
  exact FrameAllocator.ownership_exclusive state frame left right hleft hright

/-- SC-FRAME-BUDGET-ISOLATION: an admitted subject with an available committed
frame and valid object/slot inputs can allocate independently of peer usage. -/
theorem admitted_frame_budget_isolation state subject object slot
    (hlive : state.memory.capabilities.subjects subject = true)
    (hslot : slot < CapabilityHandle.slotReserved)
    (hinrange : Capability.slotInRange state.memory.capabilities subject slot = true)
    (hidentity : state.memory.capabilities.nextIdentity ≠ 0)
    (hidentityBound : state.memory.capabilities.nextIdentity <
      CapabilityHandle.generationReserved)
    (hempty : state.memory.capabilities.slots subject slot = none)
    (hunissued : state.memory.issued object = false)
    (havailable : FrameBudget.hasAvailable state subject = true) :
    (FrameBudget.allocate state subject object slot).result = .accepted := by
  exact FrameBudget.available_allocation_accepted state subject object slot hlive hslot
    hinrange hidentity hidentityBound hempty hunissued havailable

/-- SC-PT-SEPARATION: distinct encoded frames yield distinct read walks. -/
theorem page_table_distinct_spaces_separated
    (state : VirtualMapping.State) first second page firstLeaf secondLeaf
    (hfirst : (X86PageTable.encode state first).leaf page = some firstLeaf)
    (hsecond : (X86PageTable.encode state second).leaf page = some secondLeaf)
    (hne : firstLeaf.frame ≠ secondLeaf.frame) :
    X86PageTable.walk (X86PageTable.encode state first) page .read ≠
      X86PageTable.walk (X86PageTable.encode state second) page .read := by
  exact X86PageTable.distinct_spaces_separated state first second page firstLeaf secondLeaf
    hfirst hsecond hne

/-- SC-SYSCALL-CONFINEMENT: untrusted syscall words cannot add capability authority. -/
theorem syscall_authority_confinement
    (state : VirtualMapping.State) (context : Syscall.TrustedContext)
    (call : Syscall.UntrustedCall)
    (subject : Capability.SubjectId) (object : Capability.ObjectId) (right : Capability.Right)
    (hauthority : Capability.HasAuthority
      (Syscall.dispatch state context call).state.memory.capabilities subject object right) :
    Capability.HasAuthority state.memory.capabilities subject object right := by
  exact Syscall.dispatch_authority_provenance state context call subject object right hauthority

/-- SC-FAILSTOP: every proposed suffix is absorbed after a fatal halt. -/
theorem failstop_halted_suffix_absorbing state record proposals
    (hmode : state.execution.mode = .halted record) :
    FailStop.runOperations state proposals = state := by
  exact FailStop.halted_suffix_absorbing state record proposals hmode

/-- SC-COMPOSITE-AUTHORITATIVE-COMPATIBLE-GATE: the successor gate embeds both
ordinary and blocking operation families under one latch and typed reply.
The complete blocking/deferred invariant now derives every post-state
compatibility fact.  Contained-entry identity validation occurs inside the
transition, classified denial is atomic, and fatal mode absorbs arbitrary mixed
suffixes.  The stable theorem name is retained for the security-claim contract. -/
theorem composite_authoritative_compatible_gate_contract state operation
    (hstate : FailStop.AuthoritativeRuntimeWellFormed state) :
    FailStop.AuthoritativeRuntimeWellFormed
        (FailStop.authoritativeGate state operation).state ∧
      FailStop.AuthoritativeOperationReady state operation ∧
      (∀ reply,
        (FailStop.authoritativeGate state operation).result = .completed reply →
        (state.execution.mode = .running ∨
          ∃ raw context, operation = .ordinary (.nmi raw context)) ∧
          reply = FailStop.authoritativeOperationReply state operation ∧
          (FailStop.authoritativeGate state operation).state =
            FailStop.applyAuthoritativeOperation state operation) ∧
      (∀ _rejection : FailStop.AuthoritativeGateRejection
          (FailStop.authoritativeGate state operation).result,
        (FailStop.authoritativeGate state operation).state = state) ∧
      (∀ blocking,
        operation = .blocking blocking →
        FailStop.BlockingRuntimeWellFormed
          (FailStop.authoritativeGate state operation).state) ∧
      (∀ record suffix,
        state.execution.mode = .halted record →
        FailStop.runAuthoritativeOperations state suffix = state) := by
  refine ⟨FailStop.authoritativeGate_preserves_authoritativeRuntimeWellFormed
      state operation hstate, hstate.operationReady operation,
      ?_, ?_, ?_, ?_⟩
  · intro reply hcompleted
    exact FailStop.authoritativeGate_completed_sound state operation reply hcompleted
  · intro _rejection
    exact FailStop.authoritativeGate_rejection_atomic state operation _rejection
  · intro blocking hoperation
    subst operation
    exact
      (FailStop.authoritativeGate_preserves_authoritativeRuntimeWellFormed
        state (.blocking blocking) hstate).blocking
  · intro record suffix hmode
    exact FailStop.authoritative_halted_suffix_absorbing state record suffix hmode

/-- Compatibility-certified finite mixtures of ordinary and blocking
operations preserve the complete folded global invariant.  This supporting
theorem does not claim that the certificate follows from the pre-invariant. -/
theorem composite_authoritative_compatible_mixed_trace_preserves_runtimeWellFormed
    state operations (hstate : FailStop.AuthoritativeRuntimeWellFormed state)
    (hcompatible : FailStop.AuthoritativeTraceCompatible state operations) :
    FailStop.AuthoritativeRuntimeWellFormed
      (FailStop.runAuthoritativeOperations state operations) := by
  exact FailStop.runAuthoritativeOperations_preserves_authoritativeRuntimeWellFormed_of_compatible
    state operations hstate hcompatible

/-- An arbitrary finite successor-gate trace preserves the complete folded
invariant from the initial authoritative invariant alone. -/
theorem composite_authoritative_admitted_trace_preserves_runtimeWellFormed
    state operations (hstate : FailStop.AuthoritativeRuntimeWellFormed state) :
    FailStop.AuthoritativeRuntimeWellFormed
      (FailStop.runAuthoritativeOperations state operations) := by
  exact
    FailStop.runAuthoritativeOperations_preserves_authoritativeRuntimeWellFormed
      state operations hstate

/-- Mapping and protection changes retain the complete authoritative-gate
blocking precondition, so any integrated raw mapping mutation can be followed
directly by an arbitrary block, wake, or cancellation in the successor gate. -/
theorem composite_authoritative_mapping_then_blocking_preserves_runtimeWellFormed
    state slot page permissions blocking
    (hstate : FailStop.BlockingRuntimeWellFormed state) :
    FailStop.BlockingRuntimeWellFormed
        (FailStop.authoritativeGate
          (FailStop.authoritativeGate state
            (.ordinary (.map slot page permissions))).state
          (.blocking blocking)).state ∧
      FailStop.BlockingRuntimeWellFormed
        (FailStop.authoritativeGate
          (FailStop.authoritativeGate state
            (.ordinary (.unmap page))).state
          (.blocking blocking)).state ∧
      FailStop.BlockingRuntimeWellFormed
        (FailStop.authoritativeGate
          (FailStop.authoritativeGate state
            (.ordinary (.protect page permissions))).state
          (.blocking blocking)).state := by
  constructor
  · exact FailStop.authoritativeGate_ordinary_then_blocking_preserves_blockingRuntimeWellFormed
      state (.map slot page permissions) blocking
      (.map slot page permissions) hstate
  constructor
  · exact FailStop.authoritativeGate_ordinary_then_blocking_preserves_blockingRuntimeWellFormed
      state (.unmap page) blocking (.unmap page) hstate
  · exact FailStop.authoritativeGate_ordinary_then_blocking_preserves_blockingRuntimeWellFormed
      state (.protect page permissions) blocking (.protect page permissions) hstate

/-- Every attacker-controlled syscall tuple preserves the complete blocking
precondition, including accepted handle-based mapping, TLB-invalidating
unmapping, access checks, and all decoder or subsystem denials.  Any syscall
can therefore be followed immediately by an arbitrary authoritative blocking
operation without a reconstructed readiness witness. -/
theorem composite_authoritative_syscall_then_blocking_preserves_runtimeWellFormed
    state call blocking (hstate : FailStop.BlockingRuntimeWellFormed state) :
    FailStop.BlockingRuntimeWellFormed
      (FailStop.authoritativeGate
        (FailStop.authoritativeGate state (.ordinary (.syscall call))).state
        (.blocking blocking)).state := by
  exact FailStop.authoritativeGate_ordinary_then_blocking_preserves_blockingRuntimeWellFormed
    state (.syscall call) blocking (.syscall call) hstate

/-- Every sealed capability-transfer offer retains the complete blocking
precondition.  The pending descendant and tagged mailbox can therefore be
published before an arbitrary block, wake, or cancellation without a separate
readiness reconstruction. -/
theorem composite_authoritative_transferOffer_then_blocking_preserves_runtimeWellFormed
    state endpointWord sourceWord sourceKind payload rights blocking
    (hstate : FailStop.BlockingRuntimeWellFormed state) :
    FailStop.BlockingRuntimeWellFormed
      (FailStop.authoritativeGate
        (FailStop.authoritativeGate state
          (.ordinary (.transferOffer endpointWord sourceWord sourceKind payload rights))).state
        (.blocking blocking)).state := by
  exact FailStop.authoritativeGate_ordinary_then_blocking_preserves_blockingRuntimeWellFormed
    state (.transferOffer endpointWord sourceWord sourceKind payload rights) blocking
      (.transferOffer endpointWord sourceWord sourceKind payload rights) hstate

/-- Every sealed capability-transfer receipt retains the complete blocking
precondition. Filling the checked-empty destination slot and consuming the
sealed mailbox can therefore be followed immediately by an arbitrary block,
wake, or cancellation without a separate readiness reconstruction. -/
theorem composite_authoritative_transferAccept_then_blocking_preserves_runtimeWellFormed
    state endpointWord destinationSlot blocking
    (hstate : FailStop.BlockingRuntimeWellFormed state) :
    FailStop.BlockingRuntimeWellFormed
      (FailStop.authoritativeGate
        (FailStop.authoritativeGate state
          (.ordinary (.transferAccept endpointWord destinationSlot))).state
        (.blocking blocking)).state := by
  exact FailStop.authoritativeGate_ordinary_then_blocking_preserves_blockingRuntimeWellFormed
    state (.transferAccept endpointWord destinationSlot) blocking
      (.transferAccept endpointWord destinationSlot) hstate

/-- Capability delegation is monotonic for every authority held by an indexed
waiter.  Accepted empty-slot installation and every typed denial can therefore
be followed immediately by an arbitrary authoritative blocking operation. -/
theorem composite_authoritative_capabilityCopy_then_blocking_preserves_runtimeWellFormed
    state source destination destinationSlot rights blocking
    (hstate : FailStop.BlockingRuntimeWellFormed state) :
    FailStop.BlockingRuntimeWellFormed
      (FailStop.authoritativeGate
        (FailStop.authoritativeGate state
          (.ordinary (.capabilityCopy source destination destinationSlot rights))).state
        (.blocking blocking)).state := by
  exact FailStop.authoritativeGate_ordinary_then_blocking_preserves_blockingRuntimeWellFormed
    state (.capabilityCopy source destination destinationSlot rights) blocking
      (.capabilityCopy source destination destinationSlot rights) hstate

/-- Composite-safe direct and transitive revocation fail closed before
removing receive authority used by an indexed waiter.  Every accepted
revocation and every typed denial can therefore be followed immediately by an
arbitrary authoritative blocking operation. -/
theorem composite_authoritative_capabilityRevoke_then_blocking_preserves_runtimeWellFormed
    state authoritySlot victim victimSlot blocking
    (hstate : FailStop.BlockingRuntimeWellFormed state) :
    FailStop.BlockingRuntimeWellFormed
        (FailStop.authoritativeGate
          (FailStop.authoritativeGate state
            (.ordinary (.capabilityRevoke authoritySlot victim victimSlot))).state
          (.blocking blocking)).state ∧
      FailStop.BlockingRuntimeWellFormed
        (FailStop.authoritativeGate
          (FailStop.authoritativeGate state
            (.ordinary (.capabilityRevokeSubtree authoritySlot victim victimSlot))).state
          (.blocking blocking)).state := by
  constructor
  · exact FailStop.authoritativeGate_ordinary_then_blocking_preserves_blockingRuntimeWellFormed
      state (.capabilityRevoke authoritySlot victim victimSlot) blocking
        (.capabilityRevoke authoritySlot victim victimSlot) hstate
  · exact FailStop.authoritativeGate_ordinary_then_blocking_preserves_blockingRuntimeWellFormed
      state (.capabilityRevokeSubtree authoritySlot victim victimSlot) blocking
        (.capabilityRevokeSubtree authoritySlot victim victimSlot) hstate

/-- Fresh subject creation is monotonic for every lifecycle fact observed by
an indexed waiter.  Accepted identity publication and every typed denial can
therefore be followed immediately by an arbitrary authoritative blocking
operation. -/
theorem composite_authoritative_createSubject_then_blocking_preserves_runtimeWellFormed
    state subject blocking (hstate : FailStop.BlockingRuntimeWellFormed state) :
    FailStop.BlockingRuntimeWellFormed
      (FailStop.authoritativeGate
        (FailStop.authoritativeGate state
          (.ordinary (.createSubject subject))).state
        (.blocking blocking)).state := by
  exact FailStop.authoritativeGate_ordinary_then_blocking_preserves_blockingRuntimeWellFormed
    state (.createSubject subject) blocking (.createSubject subject) hstate

/-- Context-staged scheduler admission appends a runnable identity, which
cannot alias any non-runnable indexed waiter.  Every accepted admission and
typed denial can therefore precede an arbitrary authoritative blocking
operation without a reconstructed readiness witness. -/
theorem composite_authoritative_schedulerAdmission_then_blocking_preserves_runtimeWellFormed
    state subject blocking (hstate : FailStop.BlockingRuntimeWellFormed state) :
    FailStop.BlockingRuntimeWellFormed
      (FailStop.authoritativeGate
        (FailStop.authoritativeGate state
          (.ordinary (.scheduleAdd subject))).state
        (.blocking blocking)).state := by
  exact FailStop.authoritativeGate_ordinary_then_blocking_preserves_blockingRuntimeWellFormed
    state (.scheduleAdd subject) blocking (.scheduleAdd subject) hstate

/-- Raw scheduler selection without a kernel-owned save/restore payload is a
blocking-state-neutral typed boundary.  Empty dispatch and every forced
missing-context denial can therefore be followed immediately by an arbitrary
authoritative blocking operation without a reconstructed readiness witness. -/
theorem composite_authoritative_raw_scheduler_then_blocking_preserves_runtimeWellFormed
    state blocking (hstate : FailStop.BlockingRuntimeWellFormed state) :
    FailStop.BlockingRuntimeWellFormed
        (FailStop.authoritativeGate
          (FailStop.authoritativeGate state (.ordinary .scheduleNext)).state
          (.blocking blocking)).state ∧
      FailStop.BlockingRuntimeWellFormed
        (FailStop.authoritativeGate
          (FailStop.authoritativeGate state (.ordinary .scheduleYield)).state
          (.blocking blocking)).state ∧
      FailStop.BlockingRuntimeWellFormed
        (FailStop.authoritativeGate
          (FailStop.authoritativeGate state (.ordinary .scheduleTick)).state
          (.blocking blocking)).state := by
  constructor
  · exact FailStop.authoritativeGate_ordinary_then_blocking_preserves_blockingRuntimeWellFormed
      state .scheduleNext blocking (.neutral .scheduleNext) hstate
  constructor
  · exact FailStop.authoritativeGate_ordinary_then_blocking_preserves_blockingRuntimeWellFormed
      state .scheduleYield blocking (.neutral .scheduleYield) hstate
  · exact FailStop.authoritativeGate_ordinary_then_blocking_preserves_blockingRuntimeWellFormed
      state .scheduleTick blocking (.neutral .scheduleTick) hstate

/-- Resumable preemption preserves the complete blocking precondition for
every successful restore, typed denial, fatal entry, and outer-latch result.
Any such result can therefore be followed immediately by an arbitrary block,
wake, or cancellation without reconstructing readiness. -/
theorem composite_authoritative_resumePreempt_then_blocking_preserves_runtimeWellFormed
    state frame registers blocking (hstate : FailStop.BlockingRuntimeWellFormed state) :
    FailStop.BlockingRuntimeWellFormed
      (FailStop.authoritativeGate
        (FailStop.authoritativeGate state
          (.ordinary (.resumePreempt frame registers))).state
        (.blocking blocking)).state := by
  exact FailStop.authoritativeGate_ordinary_then_blocking_preserves_blockingRuntimeWellFormed
    state (.resumePreempt frame registers) blocking (.resumePreempt frame registers) hstate

/-- Every inbound interrupt outcome that does not retire a contained user
subject retains the complete blocking precondition.  Timer/syscall entry,
typed entry rejection, fatal latching, and outer-latch absorption can therefore
be followed immediately by an arbitrary block, wake, or cancellation. -/
theorem composite_authoritative_noncontained_interrupt_then_blocking_preserves_runtimeWellFormed
    state frame blocking
    (hnoncontained : ∀ subject,
      (FailStop.dispatchHardware state.execution frame).action ≠ .contained subject)
    (hstate : FailStop.BlockingRuntimeWellFormed state) :
    FailStop.BlockingRuntimeWellFormed
      (FailStop.authoritativeGate
        (FailStop.authoritativeGate state
          (.ordinary (.interrupt frame))).state
        (.blocking blocking)).state := by
  apply FailStop.authoritativeGate_blocking_preserves_blockingRuntimeWellFormed
  rw [FailStop.authoritativeGate_ordinary_state]
  exact FailStop.gate_interrupt_noncontained_preserves_blockingRuntimeWellFormed
    state frame hnoncontained hstate

/-- The successor contract has a reachable classified rejection at the
boot-produced empty waiter store, rather than being discharged vacuously. -/
theorem composite_authoritative_gate_rejection_reachable_witness plan :
    FailStop.AuthoritativeGateRejection
        (FailStop.authoritativeGate (FailStop.bootRuntime plan)
          (.blocking (.cancel 1))).result ∧
      (FailStop.authoritativeGate (FailStop.bootRuntime plan)
        (.blocking (.cancel 1))).state = FailStop.bootRuntime plan := by
  exact FailStop.authoritativeGate_rejection_reachable_witness plan

/-- SC-COMPOSITE-GATE-WF: the sealed-mailbox rejection path of the public
composite gate preserves the complete runtime invariant and exposes the typed
reason that callers must use capability-transfer acceptance instead.  This is
the first operation-specific preservation slice of the global gate contract. -/
theorem composite_gate_sealed_receive_preserves_runtimeWellFormed
    state handleWord endpoint transfer
    (hstate : FailStop.RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hresolve : CapabilityHandle.resolveCurrent state.transfers.capabilities
      { caller := state.execution.core.context.currentSubject }
      handleWord .endpoint = .ok endpoint)
    (hpending : state.transfers.pending endpoint.capability.object = some transfer) :
    FailStop.RuntimeWellFormed
        (FailStop.gate state (.ipc (.receive handleWord))).state ∧
      (FailStop.gate state (.ipc (.receive handleWord))).result =
        .completed (.ipc .sealedTransferPending) := by
  exact FailStop.gate_sealed_receive_preserves_runtimeWellFormed state handleWord
    endpoint transfer hstate hmode hresolve hpending

/-- SC-COMPOSITE-GATE-SEND-WF: the accepted data-send mutation preserves the
complete runtime invariant while publishing one exact typed success. -/
theorem composite_gate_data_send_preserves_runtimeWellFormed
    state handleWord word0 word1
    (hstate : FailStop.RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hsent : (FailStop.operationReply state
      (.ipc (.send handleWord word0 word1))) = .ipc (.syscall .sent)) :
    FailStop.RuntimeWellFormed
        (FailStop.gate state (.ipc (.send handleWord word0 word1))).state ∧
      (FailStop.gate state (.ipc (.send handleWord word0 word1))).result =
        .completed (.ipc (.syscall .sent)) := by
  apply FailStop.gate_ipc_send_accepted_preserves_runtimeWellFormed
    state handleWord word0 word1 hstate hmode
  simpa [FailStop.operationReply] using hsent

/-- SC-COMPOSITE-GATE-RECEIVE-WF: accepted data receipt preserves the complete
runtime invariant and exposes the exact sender and payload selected by the
kernel-confined endpoint transition. -/
theorem composite_gate_data_receive_preserves_runtimeWellFormed
    state handleWord sender word0 word1
    (hstate : FailStop.RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hdelivered : FailStop.operationReply state (.ipc (.receive handleWord)) =
      .ipc (.syscall (.delivered sender word0 word1))) :
    FailStop.RuntimeWellFormed
        (FailStop.gate state (.ipc (.receive handleWord))).state ∧
      (FailStop.gate state (.ipc (.receive handleWord))).result =
        .completed (.ipc (.syscall (.delivered sender word0 word1))) := by
  apply FailStop.gate_ipc_receive_accepted_preserves_runtimeWellFormed
    state handleWord sender word0 word1 hstate hmode
  simpa [FailStop.operationReply] using hdelivered

/-- Every typed block, wake, cancellation,
ordinary rejection, and execution-latch rejection preserves the exact
waiter/saved-context agreement.  Successful wake and cancellation additionally
pass through the checked resumable-bank restoration boundary. -/
theorem composite_blocking_gate_preserves_contextWellFormed state operation
    (hstate : FailStop.BlockingReceiveWellFormed state) :
    FailStop.BlockingReceiveWellFormed
      (FailStop.blockingGate state operation).state ∧
    (FailStop.CompositeBlockingGateRejection
        (FailStop.blockingGate state operation).result →
      (FailStop.blockingGate state operation).state = state) ∧
    (∀ reply, (FailStop.blockingGate state operation).result = .completed reply →
      state.execution.mode = .running ∧
        reply = FailStop.blockingOperationReply state operation ∧
        (FailStop.blockingGate state operation).state =
          FailStop.applyBlockingOperation state operation) ∧
    (∀ handleWord frame registers envelope,
      FailStop.BlockingRuntimeWellFormed state →
      (FailStop.blockingGate state (.receive handleWord frame registers)).result =
        .completed (.receive (.delivered envelope)) →
      FailStop.BlockingRuntimeWellFormed
        (FailStop.blockingGate state (.receive handleWord frame registers)).state) ∧
    (∀ handleWord frame registers,
      FailStop.BlockingRuntimeWellFormed state →
      (FailStop.blockingGate state (.receive handleWord frame registers)).result =
        .completed (.receive .blocked) →
      (FailStop.blockingGate state
        (.receive handleWord frame registers)).state.scheduler.lifecycle.current = none →
      FailStop.BlockingRuntimeWellFormed
        (FailStop.blockingGate state (.receive handleWord frame registers)).state) ∧
    (∀ handleWord frame registers selected,
      FailStop.BlockingRuntimeWellFormed state →
      (FailStop.blockingGate state (.receive handleWord frame registers)).result =
        .completed (.receive .blocked) →
      (FailStop.blockingGate state
        (.receive handleWord frame registers)).state.scheduler.lifecycle.current =
          some selected →
      FailStop.BlockingRuntimeWellFormed
        (FailStop.blockingGate state (.receive handleWord frame registers)).state) ∧
    (∀ handleWord frame registers,
      FailStop.BlockingRuntimeWellFormed state →
      (FailStop.blockingGate state (.receive handleWord frame registers)).result =
        .completed (.receive .blocked) →
      FailStop.BlockingRuntimeWellFormed
        (FailStop.blockingGate state (.receive handleWord frame registers)).state) ∧
    (∀ handleWord word0 word1,
      FailStop.RuntimeWellFormed state →
      (FailStop.blockingGate state (.send handleWord word0 word1)).result =
        .completed (.send .sent) →
      FailStop.RuntimeWellFormed
        (FailStop.blockingGate state (.send handleWord word0 word1)).state) ∧
    (∀ handleWord word0 word1 saved,
      FailStop.BlockingRuntimeWellFormed state →
      (FailStop.blockingGate state (.send handleWord word0 word1)).result =
        .completed (.send (.woke saved)) →
      FailStop.BlockingRuntimeWellFormed
        (FailStop.blockingGate state (.send handleWord word0 word1)).state) ∧
    (∀ handleWord word0 word1 saved,
      (FailStop.blockingGate state (.send handleWord word0 word1)).result =
        .completed (.send (.woke saved)) →
      ResumablePreemption.validContext
        (FailStop.blockingGate state (.send handleWord word0 word1)).state.resumable saved) ∧
    (∀ subject saved,
      FailStop.BlockingRuntimeWellFormed state →
      (FailStop.blockingGate state (.cancel subject)).result =
        .completed (.cancel (.cancelled saved)) →
      FailStop.BlockingRuntimeWellFormed
        (FailStop.blockingGate state (.cancel subject)).state) ∧
    (∀ subject saved,
      (FailStop.blockingGate state (.cancel subject)).result =
        .completed (.cancel (.cancelled saved)) →
      ResumablePreemption.validContext
        (FailStop.blockingGate state (.cancel subject)).state.resumable saved) := by
  exact ⟨FailStop.blockingGate_preserves_wellFormed state operation hstate,
    FailStop.blockingGate_rejection_atomic state operation,
    FailStop.blockingGate_completed_sound state operation,
    fun handleWord frame registers envelope hglobal hcompleted =>
      FailStop.blockingGate_receive_delivered_preserves_blockingRuntimeWellFormed
        state handleWord frame registers envelope hglobal hcompleted,
    fun handleWord frame registers hglobal hcompleted hidle =>
      FailStop.blockingGate_receive_idle_block_preserves_blockingRuntimeWellFormed
        state handleWord frame registers hglobal hcompleted hidle,
    fun handleWord frame registers selected hglobal hcompleted hselected =>
      FailStop.blockingGate_receive_selected_block_preserves_blockingRuntimeWellFormed
        state handleWord frame registers selected hglobal hcompleted hselected,
    fun handleWord frame registers hglobal hcompleted =>
      FailStop.blockingGate_receive_blocked_preserves_blockingRuntimeWellFormed
        state handleWord frame registers hglobal hcompleted,
    fun handleWord word0 word1 hglobal hcompleted =>
      FailStop.blockingGate_send_sent_preserves_runtimeWellFormed
        state handleWord word0 word1 hglobal hcompleted,
    fun handleWord word0 word1 saved hglobal hcompleted =>
      FailStop.blockingGate_send_woke_preserves_blockingRuntimeWellFormed
        state handleWord word0 word1 saved hglobal hcompleted,
    fun handleWord word0 word1 saved hcompleted =>
      FailStop.blockingGate_send_woke_context_valid
        state handleWord word0 word1 saved hcompleted,
    fun subject saved hglobal hcompleted =>
      FailStop.blockingGate_cancel_cancelled_preserves_blockingRuntimeWellFormed
        state subject saved hglobal hcompleted,
    fun subject saved hcompleted =>
      FailStop.blockingGate_cancel_cancelled_context_valid
        state subject saved hcompleted⟩

/-- SC-COMPOSITE-BLOCKING-CONTEXT-WF: the complete typed blocking gate preserves the integrated global runtime
and authoritative waiter/context invariant without requiring the caller to
classify its result.  This supports SC-COMPOSITE-BLOCKING-CONTEXT-WF. -/
theorem composite_blocking_gate_preserves_blockingRuntimeWellFormed state operation
    (hstate : FailStop.BlockingRuntimeWellFormed state) :
    FailStop.BlockingRuntimeWellFormed
      (FailStop.blockingGate state operation).state := by
  exact FailStop.blockingGate_preserves_blockingRuntimeWellFormed
    state operation hstate

/-- Supporting contained-cleanup theorem: contained entry cleanup keeps the
published scheduler/lifecycle views synchronized and preserves exact waiter /
saved-context agreement while invalidated peers move to typed deferred
cancellation state. -/
theorem composite_contained_fault_cleanup_preserves_context_boundary
    state frame subject
    (hcurrent : state.lifecycle.current = some subject)
    (hcontained :
      (FailStop.dispatchHardware state.execution frame).action = .contained subject)
    (hstate : BlockingIPCContext.ContextAgreement state.blockingIPCContext) :
    let next := FailStop.applyOperation state (.interrupt frame)
    BlockingIPCContext.ContextAgreement next.blockingIPCContext ∧
      next.scheduler.lifecycle = next.execution.core.lifecycle ∧
      next.preemption.scheduler.lifecycle = next.execution.core.lifecycle := by
  exact ⟨FailStop.interrupt_contained_preserves_contextAgreement
      state frame subject hcurrent hcontained hstate,
    FailStop.interrupt_contained_synchronizes_lifecycle
      state frame subject hcurrent hcontained⟩

/-- Supporting contained-cleanup theorem: the faulting identity is retired
from every published lifecycle view and from every scheduler, resumable,
waiter, and blocked-context projection in the same composite operation. -/
theorem composite_contained_fault_cleanup_removes_faulting_subject
    state frame subject
    (hstate : FailStop.RuntimeWellFormed state)
    (hcurrent : state.lifecycle.current = some subject)
    (hcontained :
      (FailStop.dispatchHardware state.execution frame).action = .contained subject) :
    let next := FailStop.applyOperation state (.interrupt frame)
    next.lifecycle.capabilities.subjects subject = false ∧
      next.execution.core.lifecycle.capabilities.subjects subject = false ∧
      next.scheduler.lifecycle.capabilities.subjects subject = false ∧
      next.preemption.scheduler.lifecycle.capabilities.subjects subject = false ∧
      next.resumable.scheduler.lifecycle.capabilities.subjects subject = false ∧
      subject ∉ next.scheduler.ready ∧
      next.scheduler.lifecycle.current ≠ some subject ∧
      ResumablePreemption.contextFor next.resumable.contexts subject = none ∧
      next.blockingIPC.waiterEndpoint subject = none ∧
      next.blockingContexts subject = none := by
  exact FailStop.interrupt_contained_cleans_faulting_subject
    state frame subject hstate hcurrent hcontained

/-- The contained-entry identity binding also excludes the faulting identity
from the deferred bank in the cleanup post-state. -/
theorem composite_contained_fault_cleanup_clears_faulting_deferred
    state frame subject
    (hstate : FailStop.DeferredBlockingRuntimeWellFormed state)
    (hbound : FailStop.ContainedFaultIdentityBound state)
    (hcontained :
      (FailStop.dispatchHardware state.execution frame).action = .contained subject) :
    (FailStop.applyOperation state (.interrupt frame)).deferredCancels.retained subject = none := by
  exact FailStop.interrupt_contained_clears_faulting_deferred
    state frame subject hstate hbound hcontained

/-- Every typed deferred-drain denial is globally atomic, including ready-queue
and resumable-bank exhaustion.  This supports
SC-COMPOSITE-CONTAINED-FAULT-CLEANUP. -/
theorem composite_deferred_cancel_drain_rejection_atomic state subject reason
    (hrejected : (FailStop.drainDeferredCancellation state subject).result =
      .rejected reason) :
    (FailStop.drainDeferredCancellation state subject).state = state := by
  exact FailStop.drainDeferredCancellation_rejected_unchanged
    state subject reason hrejected

/-- A successful drain reserves both finite banks and publishes the exact
retained context through synchronized composite scheduler projections.  This
supports SC-COMPOSITE-CONTAINED-FAULT-CLEANUP. -/
theorem composite_deferred_cancel_drain_success_boundary state subject saved
    (hcoherent : state.BlockingIPCCoherent)
    (hdrained : (FailStop.drainDeferredCancellation state subject).result =
      .drained saved) :
    let next := (FailStop.drainDeferredCancellation state subject).state
    state.deferredCancels.retained subject = some saved ∧
      next.deferredCancels.retained subject = none ∧
      next.blockingIPC.completion subject = some .cancelled ∧
      next.resumable.contexts = saved :: state.resumable.contexts ∧
      ¬ state.scheduler.capacity ≤ state.scheduler.ready.length ∧
      ¬ state.resumable.capacity ≤ state.resumable.contexts.length ∧
      next.scheduler.ready = state.scheduler.ready ++ [subject] ∧
      next.resumable.scheduler = next.scheduler ∧
      next.blockingIPC.scheduler = next.scheduler := by
  have hexact := FailStop.drainDeferredCancellation_drained_exact
    state subject saved hdrained
  have hcapacity := FailStop.drainDeferredCancellation_reserves_capacities
    state subject saved hcoherent hdrained
  exact ⟨hexact.1, hexact.2.1, hexact.2.2.1, hexact.2.2.2.1,
    hcapacity.1, hcapacity.2.1, hcapacity.2.2.1,
    hexact.2.2.2.2.1, hexact.2.2.2.2.2.1⟩

/-- Supporting public-drain theorem: capacity-checked deferred
cancellation is a public successor-gate operation.  One step and every finite
drain-only trace preserve the global invariant, authoritative blocking store,
and exact classification/disjointness of every retained context. -/
theorem composite_deferred_cancel_public_gate_and_trace_preserve
    state subject (subjects : List BlockingIPC.SubjectId)
    (hstate : FailStop.DeferredBlockingRuntimeWellFormed state) :
    FailStop.DeferredBlockingRuntimeWellFormed
        (FailStop.authoritativeGate state (.drainDeferred subject)).state ∧
      FailStop.DeferredBlockingRuntimeWellFormed
        (FailStop.runAuthoritativeOperations state
          (subjects.map FailStop.AuthoritativeOperation.drainDeferred)) := by
  exact ⟨
    FailStop.authoritativeGate_drainDeferred_preserves_deferredBlockingRuntimeWellFormed
      state subject hstate,
    FailStop.runAuthoritativeDeferredDrains_preserves_deferredBlockingRuntimeWellFormed
      state subjects hstate⟩

/-- The complete inbound-interrupt family composes with an arbitrary public
deferred-drain suffix.  The identity premise is consumed only if the interrupt
selects contained user-fault cleanup; all other typed interrupt outcomes retain
the deferred store and context banks exactly. -/
theorem composite_interrupt_then_deferred_trace_preserves
    state frame (subjects : List BlockingIPC.SubjectId)
    (hstate : FailStop.DeferredBlockingRuntimeWellFormed state) :
    FailStop.DeferredBlockingRuntimeWellFormed
      (FailStop.runAuthoritativeOperations state
        (.ordinary (.interrupt frame) ::
          subjects.map FailStop.AuthoritativeOperation.drainDeferred)) := by
  exact FailStop.runAuthoritativeInterruptThenDeferredDrains_preserves
    state frame subjects hstate

/-- Supporting authoritative-gate theorem: an NMI from running or handling
mode preserves the complete deferred invariant while entering fail-stop, and
the resulting terminal state absorbs every proposed public drain suffix. -/
theorem composite_nmi_then_deferred_trace_preserves
    state raw context (subjects : List BlockingIPC.SubjectId)
    (hstate : FailStop.DeferredBlockingRuntimeWellFormed state) :
    FailStop.DeferredBlockingRuntimeWellFormed
      (FailStop.runAuthoritativeOperations state
        (.ordinary (.nmi raw context) ::
          subjects.map FailStop.AuthoritativeOperation.drainDeferred)) := by
  exact FailStop.runAuthoritativeNmiThenDeferredDrains_preserves
    state raw context subjects hstate

/-- Supporting mixed-trace theorem: identity-bound contained interrupt cleanup
and every finite deferred-cancellation suffix execute through the one public
successor gate while preserving the complete deferred invariant. -/
theorem composite_contained_fault_then_deferred_trace_preserves
    state frame faulting (subjects : List BlockingIPC.SubjectId)
    (hstate : FailStop.DeferredBlockingRuntimeWellFormed state)
    (hbound : FailStop.ContainedFaultIdentityBound state)
    (hcontained :
      (FailStop.dispatchHardware state.execution frame).action = .contained faulting) :
    FailStop.DeferredBlockingRuntimeWellFormed
      (FailStop.runAuthoritativeOperations state
        (.ordinary (.interrupt frame) ::
          subjects.map FailStop.AuthoritativeOperation.drainDeferred)) := by
  exact FailStop.runAuthoritativeContainedInterruptThenDeferredDrains_preserves
    state frame faulting subjects hstate hbound hcontained

/-- SC-COMPOSITE-CONTAINED-FAULT-CLEANUP: stable combined contract for the
contained-cleanup boundary and its public deferred-drain continuation. -/
theorem composite_contained_fault_cleanup_and_deferred_trace_contract
    state frame faultSubject drainSubject (subjects : List BlockingIPC.SubjectId)
    (hbound : FailStop.ContainedFaultIdentityBound state)
    (hcontained :
      (FailStop.dispatchHardware state.execution frame).action = .contained faultSubject)
    (hstate : FailStop.DeferredBlockingRuntimeWellFormed state) :
    let cleaned := FailStop.applyOperation state (.interrupt frame)
    BlockingIPCContext.ContextAgreement cleaned.blockingIPCContext ∧
      cleaned.scheduler.lifecycle = cleaned.execution.core.lifecycle ∧
      cleaned.preemption.scheduler.lifecycle = cleaned.execution.core.lifecycle ∧
      FailStop.DeferredBlockingRuntimeWellFormed cleaned ∧
      FailStop.DeferredBlockingRuntimeWellFormed
        (FailStop.runAuthoritativeOperations state
          (.ordinary (.interrupt frame) ::
            subjects.map FailStop.AuthoritativeOperation.drainDeferred)) ∧
      FailStop.DeferredBlockingRuntimeWellFormed
        (FailStop.authoritativeGate state (.drainDeferred drainSubject)).state ∧
      FailStop.DeferredBlockingRuntimeWellFormed
        (FailStop.runAuthoritativeOperations state
          (subjects.map FailStop.AuthoritativeOperation.drainDeferred)) := by
  have hcurrent : state.lifecycle.current = some faultSubject :=
    FailStop.contained_faulting_identity_is_current
      state frame faultSubject hbound hcontained
  have hcleanup := composite_contained_fault_cleanup_preserves_context_boundary
    state frame faultSubject hcurrent hcontained hstate.2.1.1.2
  have hcleaned := FailStop.interrupt_contained_preserves_deferredBlockingRuntimeWellFormed
    state frame faultSubject hstate hbound hcontained
  have hmixed := composite_contained_fault_then_deferred_trace_preserves
    state frame faultSubject subjects hstate hbound hcontained
  have hdrains := composite_deferred_cancel_public_gate_and_trace_preserve
    state drainSubject subjects hstate
  exact ⟨hcleanup.1, hcleanup.2.1, hcleanup.2.2, hcleaned, hmixed,
    hdrains.1, hdrains.2⟩

/-- SC-COMPOSITE-BLOCKING-REJECTION-WF: every finite ordinary denial at the
typed blocking gate preserves the full composite runtime invariant because it
returns the literal pre-state. -/
theorem composite_blocking_gate_rejection_preserves_runtimeWellFormed state operation
    (hstate : FailStop.RuntimeWellFormed state)
    (hrejected : FailStop.CompositeBlockingGateRejection
      (FailStop.blockingGate state operation).result) :
    FailStop.RuntimeWellFormed (FailStop.blockingGate state operation).state := by
  exact FailStop.blockingGate_rejection_preserves_runtimeWellFormed
    state operation hstate hrejected

/-- Concrete non-vacuity for the outer blocking rejection classifier: the
boot-produced empty waiter store classifies cancellation of subject `1` as an
ordinary atomic `notWaiting` denial. -/
theorem composite_blocking_gate_rejection_reachable_witness plan :
    let state := FailStop.bootRuntime plan
    FailStop.CompositeBlockingGateRejection
        (FailStop.blockingGate state (.cancel 1)).result ∧
      (FailStop.blockingGate state (.cancel 1)).state = state := by
  exact ⟨.cancel .notWaiting, rfl⟩

/-- SC-COMPOSITE-TRANSFER-OFFER-WF: every canonical sealed-transfer offer,
including malformed/stale handle rejections and the accepted pending-mailbox
mutation, preserves the complete global runtime invariant. -/
theorem composite_gate_transferOffer_preserves_runtimeWellFormed
    state endpointWord sourceWord sourceKind payload rights
    (hstate : FailStop.RuntimeWellFormed state) :
    FailStop.RuntimeWellFormed
      (FailStop.gate state
        (.transferOffer endpointWord sourceWord sourceKind payload rights)).state := by
  exact FailStop.transferOffer_operationPreservesRuntimeWellFormed endpointWord sourceWord
    sourceKind payload rights state hstate

/-- SC-COMPOSITE-TRANSFER-ACCEPT-WF: every canonical sealed-transfer receipt,
including malformed/stale handle and slot rejections as well as successful
authority installation, preserves the complete global runtime invariant. -/
theorem composite_gate_transferAccept_preserves_runtimeWellFormed
    state endpointWord destinationSlot
    (hstate : FailStop.RuntimeWellFormed state) :
    FailStop.RuntimeWellFormed
      (FailStop.gate state (.transferAccept endpointWord destinationSlot)).state := by
  exact FailStop.transferAccept_operationPreservesRuntimeWellFormed endpointWord
    destinationSlot state hstate

/-- SC-COMPOSITE-GATE-CONTRACT: every completed public gate step identifies
either the running latch or the explicitly out-of-band NMI operation, plus the
exact typed reply and exact composite post-state; both gate-level rejection
classes and every classified nonfatal subsystem rejection preserve the
complete state, and every classified rejection preserves the global invariant
whenever the pre-state satisfies it. -/
theorem composite_gate_typed_result_contract state operation :
    (∀ reply, (FailStop.gate state operation).result = .completed reply →
      (state.execution.mode = .running ∨
        ∃ raw context, operation = .nmi raw context) ∧
        reply = FailStop.operationReply state operation ∧
        (FailStop.gate state operation).state = FailStop.applyOperation state operation) ∧
    (((FailStop.gate state operation).result = .rejectedBusy ∨
      ∃ record, (FailStop.gate state operation).result = .rejectedHalted record) →
      (FailStop.gate state operation).state = state) ∧
    (∀ reply, (FailStop.gate state operation).result = .completed reply →
      FailStop.SubsystemRejection state operation reply →
      (FailStop.gate state operation).state = state ∧
        (FailStop.RuntimeWellFormed state →
          FailStop.RuntimeWellFormed (FailStop.gate state operation).state)) ∧
    ((FailStop.operationReply state operation).isNonfatalRejection = true →
      (FailStop.gate state operation).state = state ∧
        (FailStop.RuntimeWellFormed state →
          FailStop.RuntimeWellFormed (FailStop.gate state operation).state)) := by
  constructor
  · intro reply hcompleted
    exact FailStop.gate_completed_sound state operation reply hcompleted
  constructor
  · exact FailStop.gate_mode_rejection_atomicity state operation
  constructor
  · intro reply hcompleted hrejected
    constructor
    · exact FailStop.gate_subsystem_rejection_atomicity state operation reply
        hcompleted hrejected
    · intro hstate
      exact (FailStop.gate_subsystem_rejection_preserves_runtimeWellFormed
        state operation reply hstate hcompleted hrejected).1
  · intro hrejected
    constructor
    · exact FailStop.gate_classified_rejection_global_atomicity state operation hrejected
    · intro hstate
      exact (FailStop.gate_classified_rejection_preserves_runtimeWellFormed
        state operation hstate hrejected).1

/-- SC-COMPOSITE-AUTHORITY-CONFINEMENT: every public authority-bearing
operation reports the exact subsystem result computed for the current subject
and, where applicable, the active address space selected by the execution
latch.  No operation argument supplies either privileged identity. -/
theorem composite_gate_authority_confinement state
    syscallCall ipcCall endpointWord sourceWord sourceKind payload rights
    source destination destinationSlot authoritySlot victim victimSlot slot page permissions
    (hmode : state.execution.mode = .running) :
    (FailStop.gate state (.syscall syscallCall)).result =
        .completed (.syscall
          (Syscall.dispatch state.virtualMemory state.syscallContext syscallCall).reply) ∧
    (FailStop.gate state (.ipc ipcCall)).result =
        .completed (.ipc (FailStop.authoritativeIPCReply state ipcCall)) ∧
    (FailStop.gate state
        (.transferOffer endpointWord sourceWord sourceKind payload rights)).result =
        .completed (.transferOffer
          (CapabilityTransfer.offerWords state.transfers
            state.execution.core.context.currentSubject endpointWord sourceWord sourceKind
            payload rights).result) ∧
    (FailStop.gate state (.transferAccept endpointWord destinationSlot)).result =
        .completed (.transferAccept
          (CapabilityTransfer.acceptWord state.transfers
            state.execution.core.context.currentSubject endpointWord destinationSlot).result
          (CapabilityTransfer.acceptWord state.transfers
            state.execution.core.context.currentSubject endpointWord destinationSlot).deliveredWord) ∧
    (FailStop.gate state
        (.capabilityCopy source destination destinationSlot rights)).result =
        .completed (.capability
          (Capability.copy state.capabilities
            state.execution.core.context.currentSubject source destination destinationSlot
            rights).result) ∧
    (FailStop.gate state (.capabilityRevoke authoritySlot victim victimSlot)).result =
        .completed (.capability
          (Capability.revokeRuntimeSafe state.capabilities
            state.execution.core.context.currentSubject authoritySlot victim victimSlot).result) ∧
    (FailStop.gate state (.capabilityRevokeSubtree authoritySlot victim victimSlot)).result =
        .completed (.capability
          (Capability.revokeSubtreeRuntimeSafe state.capabilities
            state.execution.core.context.currentSubject authoritySlot victim victimSlot).result) ∧
    (FailStop.gate state (.map slot page permissions)).result =
        .completed (.map
          (VirtualMapping.map state.virtualMemory
            state.execution.core.context.currentSubject slot
            state.execution.core.context.activeAddressSpace page permissions).result) ∧
    (FailStop.gate state (.unmap page)).result =
        .completed (.unmap
          (VirtualMapping.unmap state.virtualMemory
            state.execution.core.context.currentSubject
            state.execution.core.context.activeAddressSpace page).result) ∧
    (FailStop.gate state (.protect page permissions)).result =
        .completed (.protect
          (TLB.protect state.resumable.translations
            state.execution.core.context.currentSubject
            state.execution.core.context.activeAddressSpace page permissions).result) := by
  exact FailStop.authority_operations_result_sound state syscallCall ipcCall endpointWord
    sourceWord sourceKind payload rights source destination destinationSlot authoritySlot victim
    victimSlot slot page permissions hmode

/-- SC-COMPOSITE-CONTROL-WF: both control operations preserve the complete
invariant in every execution mode, including the exact sealed-transfer and
resumable states retained by busy and halted gate rejection. -/
theorem composite_gate_control_preserves_runtimeWellFormed state purpose
    (hstate : FailStop.RuntimeWellFormed state) :
    FailStop.RuntimeWellFormed
        (FailStop.gate state (.selectUserReturn purpose)).state ∧
      FailStop.RuntimeWellFormed (FailStop.gate state .restart).state := by
  exact ⟨FailStop.gate_selectUserReturn_preserves_runtimeWellFormed state purpose
      hstate,
    FailStop.gate_restart_preserves_runtimeWellFormed state hstate⟩

/-- SC-COMPOSITE-MAPPING-WF: all integrated kernel-confined raw mapping
operations preserve the complete runtime invariant in every execution mode. -/
theorem composite_gate_mapping_preserves_runtimeWellFormed state slot page permissions
    (hstate : FailStop.RuntimeWellFormed state) :
    FailStop.RuntimeWellFormed
        (FailStop.gate state (.map slot page permissions)).state ∧
      FailStop.RuntimeWellFormed (FailStop.gate state (.unmap page)).state ∧
      FailStop.RuntimeWellFormed
        (FailStop.gate state (.protect page permissions)).state := by
  exact ⟨FailStop.map_operationPreservesRuntimeWellFormed slot page permissions state hstate,
    FailStop.unmap_operationPreservesRuntimeWellFormed page state hstate,
    FailStop.protect_operationPreservesRuntimeWellFormed page permissions state hstate⟩

/-- SC-COMPOSITE-SYSCALL-WF: every attacker-controlled fixed-width syscall
tuple preserves the complete runtime invariant; privileged caller and address
space selection remain projections of the authoritative execution state. -/
theorem composite_gate_syscall_preserves_runtimeWellFormed state call
    (hstate : FailStop.RuntimeWellFormed state) :
    FailStop.RuntimeWellFormed (FailStop.gate state (.syscall call)).state := by
  exact FailStop.syscall_operationPreservesRuntimeWellFormed call state hstate

/-- SC-COMPOSITE-SCHEDULER-ADMISSION-WF: queue admission is total over public
subject identifiers, rejects a missing kernel-owned context atomically, and
preserves the complete runtime invariant for every typed result. -/
theorem composite_gate_schedulerAdmission_preserves_runtimeWellFormed state subject
    (hstate : FailStop.RuntimeWellFormed state) :
    FailStop.RuntimeWellFormed
      (FailStop.gate state (.scheduleAdd subject)).state := by
  exact FailStop.scheduleAdd_operationPreservesRuntimeWellFormed subject state hstate

/-- SC-COMPOSITE-TERMINATION-WF: every subject identifier is a total public
termination request. Rejections are atomic; acceptance retires the subject's
resources and removes all scheduler, context, mailbox, and sealed-transfer
references while preserving the complete runtime invariant. -/
theorem composite_gate_termination_preserves_runtimeWellFormed state subject
    (hstate : FailStop.RuntimeWellFormed state) :
    FailStop.RuntimeWellFormed
        (FailStop.gate state (.terminateSubject subject)).state ∧
      FailStop.RuntimeWellFormed
        (FailStop.gate state .terminateCurrent).state := by
  exact ⟨FailStop.terminateSubject_operationPreservesRuntimeWellFormed subject state hstate,
    FailStop.terminateCurrent_operationPreservesRuntimeWellFormed state hstate⟩

/-- Supporting termination theorem: an accepted explicit termination removes
the dead identity from every modeled scheduler and saved-context projection,
including the deferred-cancellation bank, and cancels every sealed transfer in
the same composite post-state. -/
theorem composite_gate_termination_cleans_runtime_references
    state subject lifecycle
    (hstate : FailStop.RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : SubjectLifecycle.terminate state.lifecycle subject =
      { state := lifecycle, result := .accepted }) :
    (FailStop.gate state (.terminateSubject subject)).result =
        .completed (.terminateSubject .accepted) ∧
      (FailStop.gate state (.terminateSubject subject)).state.lifecycle.capabilities.subjects
        subject = false ∧
      subject ∉ (FailStop.gate state (.terminateSubject subject)).state.scheduler.ready ∧
      (FailStop.gate state (.terminateSubject subject)).state.scheduler.lifecycle.current ≠
        some subject ∧
      ResumablePreemption.contextFor
        (FailStop.gate state (.terminateSubject subject)).state.resumable.contexts
        subject = none ∧
      (FailStop.gate state (.terminateSubject subject)).state.blockingIPC.waiterEndpoint
        subject = none ∧
      (FailStop.gate state (.terminateSubject subject)).state.blockingContexts subject = none ∧
      (FailStop.gate state (.terminateSubject subject)).state.deferredCancels.retained
        subject = none ∧
      ∀ endpoint,
        (FailStop.gate state (.terminateSubject subject)).state.transfers.pending endpoint =
          none := by
  exact FailStop.terminateSubject_accepted_cleans_runtime_references
    state subject lifecycle hstate hmode haccepted

/-- Supporting endpoint-owner cleanup theorem: accepted termination detaches
every named peer whose waiter endpoint was retired, retains the exact saved
context for a checked deferred drain, and clears that endpoint's mailbox. -/
theorem composite_gate_termination_defers_invalidated_peer
    state owner lifecycle peer endpoint saved
    (hmode : state.execution.mode = .running)
    (haccepted : SubjectLifecycle.terminate state.lifecycle owner =
      { state := lifecycle, result := .accepted })
    (hpeer : peer ≠ owner)
    (hendpoint :
      (BlockingIPCContext.terminate state.blockingIPCContext owner).ipc.waiterEndpoint peer =
        some endpoint)
    (hsaved :
      (BlockingIPCContext.terminate state.blockingIPCContext owner).blocked peer = some saved)
    (hretired :
      (ResumablePreemption.cleanupSubject state.resumable owner).scheduler.lifecycle.capabilities.objects
        endpoint = false) :
    let next := (FailStop.gate state (.terminateSubject owner)).state
    (FailStop.gate state (.terminateSubject owner)).result =
        .completed (.terminateSubject .accepted) ∧
      next.blockingIPC.waiterEndpoint peer = none ∧
      next.blockingContexts peer = none ∧
      next.deferredCancels.retained peer = some saved ∧
      next.blockingIPC.mailbox endpoint = none := by
  exact FailStop.terminateSubject_accepted_defers_invalidated_waiter
    state owner lifecycle peer endpoint saved hmode haccepted hpeer
    hendpoint hsaved hretired

/-- SC-COMPOSITE-LEGACY-OPERATION-TRACE-WF: arbitrary finite interleavings of
every constructor in the legacy `Operation`/`gate` surface preserve
`RuntimeWellFormed` for every accepted, typed-rejected, busy, halted, or fatal
result.  This surface excludes `CompositeBlockingOperation` and deferred
cancellation drains, and `RuntimeWellFormed` excludes their folded
classification. -/
theorem composite_legacy_operation_mixed_trace_preserves_runtimeWellFormed
    state operations
    (hstate : FailStop.RuntimeWellFormed state) :
    FailStop.RuntimeWellFormed (FailStop.runOperations state operations) := by
  exact FailStop.runOperations_preserves_runtimeWellFormed_universally
    state operations hstate

/-- Supporting compatible trace theorem: an arbitrary finite list of ordinary
successor-gate operations preserves the complete folded blocking/deferred
invariant from recursive operation-local premises, without assuming any
intermediate preservation conclusion. -/
theorem composite_authoritative_ordinary_trace_preserves_runtimeWellFormed
    state (operations : List FailStop.Operation)
    (hstate : FailStop.AuthoritativeRuntimeWellFormed state)
    (hcompatible : FailStop.AuthoritativeTraceCompatible state
      (operations.map FailStop.AuthoritativeOperation.ordinary)) :
    FailStop.AuthoritativeRuntimeWellFormed
      (FailStop.runAuthoritativeOperations state
        (operations.map FailStop.AuthoritativeOperation.ordinary)) := by
  exact
    FailStop.runAuthoritativeOrdinaryOperations_preserves_authoritativeRuntimeWellFormed
      state operations hstate hcompatible

/-- Supporting readiness-free mixed-trace theorem: every finite interleaving
of the compatible ordinary family and arbitrary authoritative blocking
operations preserves the complete blocking runtime invariant.  The trace
certificate is state-independent and therefore replaces the legacy recursive
readiness gate throughout this compositional slice. -/
theorem composite_authoritative_readinessFree_mixed_trace_preserves
    state operations
    (hoperations : FailStop.ReadinessFreeMixedTrace operations)
    (hstate : FailStop.BlockingRuntimeWellFormed state) :
    FailStop.BlockingRuntimeWellFormed
      (FailStop.runAuthoritativeOperations state operations) := by
  exact
    FailStop.runAuthoritativeReadinessFreeMixedTrace_preserves_blockingRuntimeWellFormed
      state operations hoperations hstate

/-- Supporting readiness-free termination trace theorem: explicit termination
of any selected identity preserves the complete deferred-cancellation
invariant consumed by any finite capacity-checked drain suffix. -/
theorem composite_terminateSubject_then_deferred_trace_preserves
    state subject (subjects : List BlockingIPC.SubjectId)
    (hstate : FailStop.DeferredBlockingRuntimeWellFormed state) :
    FailStop.DeferredBlockingRuntimeWellFormed
      (FailStop.runAuthoritativeOperations state
        (.ordinary (.terminateSubject subject) ::
          subjects.map FailStop.AuthoritativeOperation.drainDeferred)) := by
  exact FailStop.runAuthoritativeTerminateSubjectThenDeferredDrains_preserves
    state subject subjects hstate

/-- Supporting readiness-free termination trace theorem: scheduler-selected
termination establishes and preserves the complete deferred-cancellation
invariant consumed by any finite capacity-checked drain suffix. -/
theorem composite_terminateCurrent_then_deferred_trace_preserves
    state (subjects : List BlockingIPC.SubjectId)
    (hstate : FailStop.DeferredBlockingRuntimeWellFormed state) :
    FailStop.DeferredBlockingRuntimeWellFormed
      (FailStop.runAuthoritativeOperations state
        (.ordinary .terminateCurrent ::
          subjects.map FailStop.AuthoritativeOperation.drainDeferred)) := by
  exact FailStop.runAuthoritativeTerminateCurrentThenDeferredDrains_preserves
    state subjects hstate

/-- SC-COMPOSITE-DIRECT-PORT-WF: every public composite step and arbitrary
finite mixed trace retain the complete TSS/IOPL control and device projection
literally.  Consequently the deny-all user policy embedded in the global
runtime invariant cannot be relaxed or repaired by an unrelated transition. -/
theorem composite_gate_preserves_direct_port_boundary state operation operations
    (hstate : FailStop.RuntimeWellFormed state) :
    (FailStop.gate state operation).state.directPortIO = state.directPortIO ∧
      (FailStop.runOperations state operations).directPortIO = state.directPortIO ∧
      DirectPortIO.AcceptedControls
        (FailStop.gate state operation).state.directPortIO.controls ∧
      DirectPortIO.AcceptedControls
        (FailStop.runOperations state operations).directPortIO.controls := by
  refine ⟨FailStop.gate_directPortIO state operation,
    FailStop.runOperations_directPortIO state operations, ?_, ?_⟩
  · simpa using hstate.directPortControls
  · simpa using hstate.directPortControls

/-- SC-COMPOSITE-BOOT-WF: every successfully compiled bounded boot page-table
plan produces an idle composite runtime satisfying the complete global
invariant before any subject or trusted return identity is admitted. -/
theorem composite_boot_runtime_wellFormed input plan
    (hcompiled : BootPageTablePlan.compile input = .ok plan) :
    FailStop.RuntimeWellFormed (FailStop.bootRuntime plan) := by
  exact FailStop.bootRuntime_runtimeWellFormed input plan hcompiled

set_option maxRecDepth 100000 in
/-- Concrete non-vacuity witness: the repository's accepted bounded sample
boot input reaches the globally well-formed initial composite runtime. -/
theorem composite_boot_runtime_reachable_witness :
    match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
    | .ok plan => FailStop.RuntimeWellFormed (FailStop.bootRuntime plan)
    | .error _ => False := by
  generalize hresult : BootPageTablePlan.compile BootPageTablePlan.sampleInput = result
  cases result with
  | error reason =>
      have hsuccess :
          (match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
            | .ok _ => true
            | .error _ => false) = true := by
        native_decide
      simp [hresult] at hsuccess
  | ok plan =>
      exact FailStop.bootRuntime_runtimeWellFormed BootPageTablePlan.sampleInput plan hresult

private def registeredMixedTrace : List FailStop.Operation :=
  [.syscall { number := 99, arg0 := 0, arg1 := 0, arg2 := 0 },
   .ipc (.receive 0),
   .transferOffer 0 0 .memory { word0 := 0, word1 := 0 } { read := true },
   .transferAccept 0 0,
   .capabilityCopy 0 1 0 { read := true },
   .capabilityRevoke 0 1 0,
   .capabilityRevokeSubtree 0 1 0,
   .map 0 0 { read := true },
   .unmap 0,
   .createSubject 1,
   .scheduleAdd 1,
   .scheduleRemove 1,
   .terminateSubject 1,
   .terminateCurrent,
   .selectUserReturn .initialDispatch,
   .restart]

private theorem registeredMixedTrace_registered operation
    (hmember : operation ∈ registeredMixedTrace) :
    FailStop.RuntimeTraceOperation operation := by
  simp [registeredMixedTrace] at hmember
  rcases hmember with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst operation
    exact .syscall _
  · subst operation
    exact .ipc _
  · subst operation
    exact .transferOffer _ _ _ _ _
  · subst operation
    exact .transferAccept _ _
  · subst operation
    exact .capabilityCopy _ _ _ _
  · subst operation
    exact .capabilityRevoke _ _ _
  · subst operation
    exact .capabilityRevokeSubtree _ _ _
  · subst operation
    exact .map _ _ _
  · subst operation
    exact .unmap _
  · subst operation
    exact .createSubject _
  · subst operation
    exact .scheduleAdd _
  · subst operation
    exact .scheduleRemove _
  · subst operation
    exact .terminateSubject _
  · subst operation
    exact .terminateCurrent
  · subst operation
    exact .selectUserReturn _
  · subst operation
    exact .restart

set_option maxRecDepth 100000 in
/-- Concrete non-vacuity for the legacy-operation mixed-trace contract: the
accepted repository boot plan runs a finite trace containing attacker-controlled
syscall/IPC/sealed-transfer/capability-copy/revocation/mapping words, lifecycle
creation/termination, resumable-aware scheduler cleanup, return selection, and restart
while retaining `RuntimeWellFormed`.  It is not evidence for the folded
authoritative blocking/deferred invariant. -/
theorem composite_legacy_operation_mixed_trace_reachable_witness :
    match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
    | .ok plan => FailStop.RuntimeWellFormed
        (FailStop.runOperations (FailStop.bootRuntime plan) registeredMixedTrace)
    | .error _ => False := by
  generalize hresult : BootPageTablePlan.compile BootPageTablePlan.sampleInput = result
  cases result with
  | error reason =>
      have hsuccess :
          (match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
            | .ok _ => true
            | .error _ => false) = true := by
        native_decide
      simp [hresult] at hsuccess
  | ok plan =>
      apply composite_legacy_operation_mixed_trace_preserves_runtimeWellFormed
      exact FailStop.bootRuntime_runtimeWellFormed
        BootPageTablePlan.sampleInput plan hresult

/-- SC-INTERRUPT-ENTRY-BINDING: every normalized record constructor copies
authority-bearing context fields from the kernel-owned input. -/
theorem interrupt_entry_context_binding entry raw context :
    (InterruptEntry.makeNormalized entry raw context).currentSubject = context.currentSubject ∧
    (InterruptEntry.makeNormalized entry raw context).activeAddressSpace =
      context.activeAddressSpace ∧
    (InterruptEntry.makeNormalized entry raw context).activeCr3 = context.activeCr3 ∧
    (InterruptEntry.makeNormalized entry raw context).stackIdentity = context.stackIdentity := by
  exact InterruptEntry.makeNormalized_binds_context entry raw context

/-- SC-PAGE-FAULT-PROVENANCE: an accepted normalization proves vector 14,
exact error/access/CR2-page binding, canonical address and origin agreement,
and confinement to the kernel-owned context. -/
theorem page_fault_provenance_binding raw context snapshot
    (haccepted : InterruptEntry.normalizePageFault raw context =
      .accepted snapshot) :
    snapshot.entry.vector = 14 ∧
      ∃ word,
        raw.entry.errorCode = some word ∧
        snapshot.entry.errorCode = some word ∧
        InterruptEntry.decodePageFaultError word = .ok snapshot.error ∧
        snapshot.accessKind = snapshot.error.accessKind ∧
        snapshot.faultAddress = raw.faultAddress ∧
        snapshot.faultPage = raw.faultAddress / 4096 ∧
        InterruptEntry.canonicalLinearAddress raw.faultAddress = true ∧
        decide (snapshot.entry.origin = .user) = snapshot.error.user ∧
        snapshot.entry.currentSubject = context.entry.currentSubject ∧
        snapshot.entry.activeAddressSpace = context.entry.activeAddressSpace ∧
        snapshot.entry.activeCr3 = context.entry.activeCr3 ∧
        snapshot.controls = context.controls := by
  exact InterruptEntry.normalizePageFault_accepted_binding raw context snapshot haccepted

/-- The serialized page-fault action boundary authorizes only independently
supplied subject and address-space identities that fit one canonical codec
word.  Under that checked premise, converting the authorized words back to
`Nat` yields the exact trusted identities rather than a modulo-`2^64` alias. -/
theorem page_fault_authorization_context_binding
    (State : Type) words context (state : State) record
    (hauthorized :
      (InterruptEntry.authorizeCanonicalPageFault words context state).authorized =
        some record) :
    InterruptEntry.AuthorityIdentityRepresentable context.entry.currentSubject ∧
      InterruptEntry.AuthorityIdentityRepresentable
        context.entry.activeAddressSpace ∧
      record.currentSubject.toNat = context.entry.currentSubject ∧
      record.activeAddressSpace.toNat = context.entry.activeAddressSpace ∧
      record.currentSubject = UInt64.ofNat context.entry.currentSubject ∧
      record.activeAddressSpace = UInt64.ofNat context.entry.activeAddressSpace ∧
      record.activeCr3 = context.entry.activeCr3 ∧
      record.controlsCode =
        InterruptEntry.pagingControlsCode context.controls := by
  exact InterruptEntry.authorized_canonical_binds_trusted_context
    State words context state record hauthorized

/-- SC-PAGE-FAULT-ACTIVE-SPACE-AGREEMENT: every successful strengthened
page-fault containment result consumes the exact canonical decoder/action
authorization, checks CR2 only inside the kernel-selected active boot-plan
root, binds and validates the complete decoded live-root report, revalidates
plan/virtual/lifecycle object-and-frame agreement (including absence) and an
empty matching TLB entry, and admits only an architectural error class matching
the live page-table denial. -/
theorem page_fault_active_space_containment_agreement state plan report words trusted
    (hsuccess :
      (FaultDispatch.dispatchPageFault state plan report words trusted).action =
          .idle .pageFault ∨
        ∃ context,
          (FaultDispatch.dispatchPageFault state plan report words trusted).action =
            .dispatch .pageFault context) :
    ∃ record denial space decoded cause,
      InterruptEntry.decodeCanonicalPageFault words = some record ∧
        (InterruptEntry.authorizeCanonicalPageFault words trusted state).authorized =
          some record ∧
        FaultDispatch.pageFaultAgreement state plan report record = .ok denial ∧
        FaultDispatch.selectedBootSpace
          (FaultDispatch.activeFaultAddressSpace state) = some space ∧
        report.space = space ∧
        report.selectedRoot = plan.rootFrame space ∧
        record.activeCr3 = FaultDispatch.expectedCr3 plan space ∧
        BootPageTablePlan.validateDecodedRoot plan report = .ok () ∧
        FaultDispatch.livePlanAgreement state plan space
          (FaultDispatch.activeFaultAddressSpace state) record.faultPage.toNat = true ∧
        FaultDispatch.pageFaultTlbCoherent state
          (FaultDispatch.activeFaultAddressSpace state) record.faultPage.toNat
          (FaultDispatch.pageFaultAccessContext record) = true ∧
        InterruptEntry.decodePageFaultError record.errorWord = .ok decoded ∧
        X86PageTable.classify
          (FaultDispatch.livePageTableAt report record.faultPage.toNat)
          record.faultPage.toNat (FaultDispatch.pageFaultAccessContext record) =
            .error cause ∧
        FaultDispatch.denialAgreement decoded cause = some denial := by
  obtain ⟨record, denial, hdecode, hauthorized, hagreement,
      space, decoded, cause, hspace, hreportSpace, hreportRoot, hroot, hreport,
      hlive, htlb, herror,
      hclassify, hdenial⟩ :=
    FaultDispatch.dispatchPageFault_success_sound state plan report words trusted hsuccess
  exact ⟨record, denial, space, decoded, cause, hdecode, hauthorized,
    hagreement, hspace, hreportSpace, hreportRoot, hroot, hreport, hlive, htlb,
    herror, hclassify, hdenial⟩

/-- SC-PRIVILEGE-ENTRY-STACK: accepted ordinary-entry stack authorization
names the valid guarded layout exactly and carries a checked byte remainder
without changing the modeled composite state. -/
theorem privilege_entry_stack_budget_sound (State : Type)
    layout reserved request (state : State) budget (acceptedState : State)
    (haccepted : PrivilegeEntryStack.authorize layout reserved request state =
      .accepted budget acceptedState) :
    PrivilegeEntryStack.layoutValid layout reserved = true ∧
      acceptedState = state ∧
      budget.stackIdentity = layout.stackIdentity ∧
      budget.stackFirst = layout.usable.first ∧
      budget.stackPastLast = layout.usable.pastLast ∧
      budget.stackTop = layout.stackTop ∧
      budget.remainingBytes + budget.requiredBytes =
        PrivilegeEntryStack.usableBytes layout := by
  have hconditions := PrivilegeEntryStack.accepted_contract_conditions State
    layout reserved request state budget acceptedState haccepted
  have hbudget := PrivilegeEntryStack.accepted_budget_sound State layout reserved
    request state budget acceptedState haccepted
  exact ⟨hconditions.1, hbudget.1, hbudget.2.1, hbudget.2.2.1,
    hbudget.2.2.2.1, hbudget.2.2.2.2.1, hbudget.2.2.2.2.2.2⟩

/-- SC-PRIVILEGE-ENTRY-CONTROL: every accepted finite CPU/MSR state enables
exactly the reviewed manifest-backed `int 0x80` mechanism. -/
theorem privilege_entry_control_single_mechanism control mechanism
    (haccepted : PrivilegeEntryControl.Accepted control) :
    PrivilegeEntryControl.enabled control mechanism =
      decide (mechanism = .int80) := by
  exact PrivilegeEntryControl.accepted_exactly_int80 control haccepted mechanism

/-- SC-USER-RETURN-CONFINEMENT: an accepted return attests the complete
kernel-selected frame/context tuple and its privilege-critical fields. -/
theorem user_return_context_confinement request attested
    (haccepted : Interrupt.validateUserReturn request = .accepted attested) :
    attested = request ∧
      attested.purpose ≠ .diagnosticKernelRecovery ∧
      attested.executionMode = .running ∧
      attested.hardware.savedPrivilege = .user ∧
      attested.hardware.codeSelector = 0x23 ∧
      attested.hardware.stackSelector = 0x1b ∧
      attested.hardware.canonicalInstructionPointer = true ∧
      attested.hardware.canonicalStackPointer = true ∧
      Interrupt.rawReturnFlagsAllowed attested.hardware.flags = true ∧
      attested.lifecycle.capabilities.subjects attested.expectedSubject = true ∧
      attested.lifecycle.runnable attested.expectedSubject = true ∧
      attested.lifecycle.current = some attested.expectedSubject ∧
      attested.frameSubject = attested.expectedSubject ∧
      attested.lifecycle.addressOwner attested.expectedAddressSpace =
        some attested.expectedSubject ∧
      attested.frameAddressSpace = attested.expectedAddressSpace ∧
      attested.frameCr3 = attested.expectedCr3 ∧
      attested.codeRegion.contains attested.hardware.instructionPointer = true ∧
      attested.stackRegion.containsStackPointer attested.hardware.stackPointer = true := by
  exact Interrupt.accepted_user_return_context_confined request attested haccepted

/-- SC-USER-RETURN-AUTHORITY: the executable target policy accepted by the
terminal gate is exactly the kernel-owned policy, never a proposal copy. -/
theorem user_return_authority_confinement state request attested
    (hstate : FailStop.WellFormed state)
    (haccepted : (FailStop.completeUserReturn state request).action = .accepted attested) :
    FailStop.ReturnAuthorityBound state ∧
      attested.purpose = state.returnAuthority.purpose ∧
      attested.expectedCr3 = state.returnAuthority.expectedCr3 ∧
      attested.codeRegion = state.returnAuthority.codeRegion ∧
      attested.stackRegion = state.returnAuthority.stackRegion := by
  have hbound := FailStop.accepted_user_return_has_bound_authority state request attested
    hstate haccepted
  have hmode := FailStop.accepted_user_return_requires_running state request attested haccepted
  exact ⟨hbound, FailStop.accepted_user_return_uses_authority state request attested
    hmode haccepted⟩

/-- SC-USER-RETURN-LIVE-PLAN: any authority armed by the composite selector
was checked against the active virtual-memory mappings and their physical
bindings, not merely against an attached compiled plan. -/
theorem user_return_authority_requires_live_plan state purpose
    (harmed : (FailStop.selectLiveReturnAuthority state purpose).execution.returnAuthorityArmed =
      true) :
    state.ReturnPlanLive = true := by
  exact FailStop.selectLiveReturnAuthority_armed_implies_live state purpose harmed

private def returnWitnessCapabilities : Capability.State :=
  { nextIdentity := 3
    derivations := fun identity =>
      if identity = 0 then
        some (none, 1, .addressSpace, { revoke := true })
      else if identity = 1 then
        some (none, 100, .memory, { read := true })
      else if identity = 2 then
        some (none, 101, .memory, { read := true, write := true })
      else none
    subjects := fun subject => subject = 1
    objects := fun object => object = 1 || object = 100 || object = 101
    kinds := fun object =>
      if object = 1 then some .addressSpace
      else if object = 100 || object = 101 then some .memory
      else none
    slots := fun subject slot =>
      if subject = 1 ∧ slot = 0 then
        some { object := 1, kind := .addressSpace, rights := { revoke := true }, identity := 0 }
      else if subject = 1 ∧ slot = 1 then
        some { object := 100, kind := .memory, rights := { read := true }, identity := 1 }
      else if subject = 1 ∧ slot = 2 then
        some { object := 101, kind := .memory, rights := { read := true, write := true }, identity := 2 }
      else none }

private def returnWitnessLifecycle : SubjectLifecycle.State :=
  { capabilities := returnWitnessCapabilities
    issuedSubjects := fun subject => subject = 1
    ownedMemory := fun object =>
      if object = 100 then some (1, 100)
      else if object = 101 then some (1, 101)
      else none
    addressOwner := fun space => if space = 1 then some 1 else none
    mapping := fun space page =>
      if space = 1 ∧ page = 100 then some 100
      else if space = 1 ∧ page = 101 then some 101
      else none
    endpointOwner := fun _ => none
    mailbox := fun _ => none
    frameOwner := fun frame =>
      if frame = 100 then some 1 else if frame = 101 then some 1 else none
    freeFrame := fun frame =>
      if frame = 100 then false else if frame = 101 then false else true
    runnable := fun subject => subject = 1
    current := some 1 }

private theorem returnWitnessCapabilities_wellFormed :
    Capability.WellFormed returnWitnessCapabilities := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro subject slot capability hslot
    simp only [returnWitnessCapabilities] at hslot ⊢
    split at hslot
    · cases hslot
      simp_all [Capability.rightsValid]
    · split at hslot
      · cases hslot
        simp_all [Capability.rightsValid, Capability.nonemptyRights]
      · split at hslot
        · cases hslot
          simp_all [Capability.rightsValid, Capability.nonemptyRights]
        · contradiction
  · intro identity parent object kind rights hderivation
    simp only [returnWitnessCapabilities] at hderivation ⊢
    split at hderivation
    · cases hderivation
      simp_all
    · split at hderivation
      · cases hderivation
        simp_all
      · split at hderivation
        · cases hderivation
          simp_all
        · contradiction
  · intro subject slot capability otherSubject otherSlot otherCapability
      hslot hother hidentity
    simp only [returnWitnessCapabilities] at hslot hother
    split at hslot
    · cases hslot
      split at hother
      · cases hother
        simp_all
      · split at hother
        · cases hother
          simp at hidentity
        · split at hother
          · cases hother
            simp at hidentity
          · contradiction
    · split at hslot
      · cases hslot
        split at hother
        · cases hother
          simp at hidentity
        · split at hother
          · cases hother
            simp_all
          · split at hother
            · cases hother
              simp at hidentity
            · contradiction
      · split at hslot
        · cases hslot
          split at hother
          · cases hother
            simp at hidentity
          · split at hother
            · cases hother
              simp at hidentity
            · split at hother
              · cases hother
                simp_all
              · contradiction
        · contradiction
  · intro subject slot houtOfRange
    change 4 ≤ slot at houtOfRange
    simp only [returnWitnessCapabilities]
    split
    · simp_all
    · split
      · simp_all
      · split
        · simp_all
        · rfl

@[simp] private theorem returnWitnessLifecycle_capabilities :
    returnWitnessLifecycle.capabilities = returnWitnessCapabilities := rfl

@[simp] private theorem returnWitnessLifecycle_issuedSubjects subject :
    returnWitnessLifecycle.issuedSubjects subject = decide (subject = 1) := rfl

@[simp] private theorem returnWitnessLifecycle_ownedMemory object :
    returnWitnessLifecycle.ownedMemory object =
      if object = 100 then some (1, 100)
      else if object = 101 then some (1, 101)
      else none := rfl

@[simp] private theorem returnWitnessLifecycle_addressOwner addressSpace :
    returnWitnessLifecycle.addressOwner addressSpace =
      if addressSpace = 1 then some 1 else none := rfl

@[simp] private theorem returnWitnessLifecycle_mapping addressSpace page :
    returnWitnessLifecycle.mapping addressSpace page =
      if addressSpace = 1 ∧ page = 100 then some 100
      else if addressSpace = 1 ∧ page = 101 then some 101
      else none := rfl

@[simp] private theorem returnWitnessLifecycle_endpointOwner object :
    returnWitnessLifecycle.endpointOwner object = none := rfl

@[simp] private theorem returnWitnessLifecycle_mailbox object :
    returnWitnessLifecycle.mailbox object = none := rfl

@[simp] private theorem returnWitnessLifecycle_frameOwner frame :
    returnWitnessLifecycle.frameOwner frame =
      if frame = 100 then some 1 else if frame = 101 then some 1 else none := rfl

@[simp] private theorem returnWitnessLifecycle_freeFrame frame :
    returnWitnessLifecycle.freeFrame frame =
      if frame = 100 then false else if frame = 101 then false else true := rfl

@[simp] private theorem returnWitnessLifecycle_runnable subject :
    returnWitnessLifecycle.runnable subject = decide (subject = 1) := rfl

@[simp] private theorem returnWitnessLifecycle_current :
    returnWitnessLifecycle.current = some 1 := rfl

@[simp] private theorem returnWitnessLifecycle_wellFormed :
    SubjectLifecycle.WellFormed returnWitnessLifecycle := by
  simp [SubjectLifecycle.WellFormed, returnWitnessLifecycle,
    returnWitnessCapabilities]
  intro object subject frame howned
  by_cases h100 : object = 100
  · subst object
    simp at howned
    cases howned
    simp_all
  · by_cases h101 : object = 101
    · subst object
      simp [h100] at howned
      cases howned
      simp_all
    · simp [h100, h101] at howned

@[simp] private theorem returnWitnessCapabilities_nextIdentity :
    returnWitnessCapabilities.nextIdentity = 3 := rfl

@[simp] private theorem returnWitnessCapabilities_derivations identity :
    returnWitnessCapabilities.derivations identity =
      if identity = 0 then
        some (none, 1, .addressSpace, { revoke := true })
      else if identity = 1 then
        some (none, 100, .memory, { read := true })
      else if identity = 2 then
        some (none, 101, .memory, { read := true, write := true })
      else none := rfl

@[simp] private theorem returnWitnessCapabilities_subjects subject :
    returnWitnessCapabilities.subjects subject = decide (subject = 1) := rfl

@[simp] private theorem returnWitnessCapabilities_objects object :
    returnWitnessCapabilities.objects object =
      (object = 1 || object = 100 || object = 101) := rfl

@[simp] private theorem returnWitnessCapabilities_kinds object :
    returnWitnessCapabilities.kinds object =
      if object = 1 then some .addressSpace
      else if object = 100 || object = 101 then some .memory
      else none := rfl

@[simp] private theorem returnWitnessCapabilities_slotCapacity subject :
    returnWitnessCapabilities.slotCapacity subject = 4 := rfl

@[simp] private theorem returnWitnessCapabilities_slots subject slot :
    returnWitnessCapabilities.slots subject slot =
      if subject = 1 ∧ slot = 0 then
        some { object := 1, kind := .addressSpace, rights := { revoke := true }, identity := 0 }
      else if subject = 1 ∧ slot = 1 then
        some { object := 100, kind := .memory, rights := { read := true }, identity := 1 }
      else if subject = 1 ∧ slot = 2 then
        some { object := 101, kind := .memory, rights := { read := true, write := true }, identity := 2 }
      else none := rfl

@[simp] private theorem returnWitnessCapabilities_readAuthority subject object :
    Capability.HasAuthority returnWitnessCapabilities subject object .read ↔
      subject = 1 ∧ (object = 100 ∨ object = 101) := by
  constructor
  · rintro ⟨slot, capability, hslot, hobject, hright⟩
    simp only [returnWitnessCapabilities] at hslot
    split at hslot
    · cases hslot
      simp [Capability.hasRight, Capability.permits] at hright
    · split at hslot
      · cases hslot
        simp_all [Capability.hasRight, Capability.permits]
      · split at hslot
        · cases hslot
          simp_all [Capability.hasRight, Capability.permits]
        · contradiction
  · rintro ⟨rfl, rfl | rfl⟩
    · refine ⟨1, {
        object := 100
        kind := .memory
        rights := { read := true }
        identity := 1 }, rfl, rfl, rfl⟩
    · refine ⟨2, {
        object := 101
        kind := .memory
        rights := { read := true, write := true }
        identity := 2 }, rfl, rfl, rfl⟩

@[simp] private theorem returnWitnessCapabilities_writeAuthority subject object :
    Capability.HasAuthority returnWitnessCapabilities subject object .write ↔
      subject = 1 ∧ object = 101 := by
  constructor
  · rintro ⟨slot, capability, hslot, hobject, hright⟩
    simp only [returnWitnessCapabilities] at hslot
    split at hslot
    · cases hslot
      simp [Capability.hasRight, Capability.permits] at hright
    · split at hslot
      · cases hslot
        simp [Capability.hasRight, Capability.permits] at hright
      · split at hslot
        · cases hslot
          simp_all [Capability.hasRight, Capability.permits]
        · contradiction
  · rintro ⟨rfl, rfl⟩
    refine ⟨2, {
      object := 101
      kind := .memory
      rights := { read := true, write := true }
      identity := 2 }, rfl, rfl, rfl⟩

@[simp] private theorem returnWitnessCapabilities_revokeAuthority subject object :
    Capability.HasAuthority returnWitnessCapabilities subject object .revoke ↔
      subject = 1 ∧ object = 1 := by
  constructor
  · rintro ⟨slot, capability, hslot, hobject, hright⟩
    simp only [returnWitnessCapabilities] at hslot
    split at hslot
    · cases hslot
      simp_all [Capability.hasRight, Capability.permits]
    · split at hslot
      · cases hslot
        simp [Capability.hasRight, Capability.permits] at hright
      · split at hslot
        · cases hslot
          simp [Capability.hasRight, Capability.permits] at hright
        · contradiction
  · rintro ⟨rfl, rfl⟩
    refine ⟨0, {
      object := 1
      kind := .addressSpace
      rights := { revoke := true }
      identity := 0 }, rfl, rfl, rfl⟩

private def returnWitnessPlan : Option BootPageTablePlan.Plan :=
  (BootPageTablePlan.compile BootPageTablePlan.sampleInput).toOption

private def returnWitnessView : FailStop.ReturnAddressSpace :=
  { subject := 1
    expectedCr3 := 0xa000
    codeRegion := ⟨0x64000, 0x65000⟩
    stackRegion := ⟨0x65000, 0x66000⟩ }

private def returnWitnessBase : FailStop.State :=
  { core :=
      { lifecycle := returnWitnessLifecycle
        context :=
          { currentSubject := 1
            activeAddressSpace := 1
            kernelStack := 0
            entryActive := false } }
    mode := .running
    returnAddressSpace := fun space => if space = 1 then some returnWitnessView else none
    returnPlan := returnWitnessPlan }

private def returnWitnessState : FailStop.State :=
  FailStop.selectReturnAuthority returnWitnessBase .initialDispatch

private def returnWitnessRequest : Interrupt.UserReturnRequest :=
  { hardware :=
      { vector := 0
        errorCode := 0
        savedPrivilege := .user
        instructionPointer := 0x64100
        stackPointer := 0x65ff8
        codeSelector := 0x23
        stackSelector := 0x1b
        flags := 0x202
        canonicalInstructionPointer := true
        canonicalStackPointer := true
        flagsAllowed := true }
    purpose := .initialDispatch
    frameSubject := 1
    frameAddressSpace := 1
    frameCr3 := 0xa000
    expectedSubject := 1
    expectedAddressSpace := 1
    expectedCr3 := 0xa000
    executionMode := .running
    lifecycle := returnWitnessLifecycle
    codeRegion := ⟨0x64000, 0x65000⟩
    stackRegion := ⟨0x65000, 0x66000⟩
    flags :=
      { interruptEnable := true
        direction := false
        alignmentCheck := false
        nestedTask := false
        virtual8086 := false
        ioPrivilegeLevel := 0
        reservedAllowed := true } }

set_option maxRecDepth 100000 in
/-- The authority-selection transition reaches a well-formed armed state whose
complete return gate accepts the matching live frame. -/
theorem user_return_authority_reachable_witness :
    FailStop.WellFormed returnWitnessState ∧
      (FailStop.completeUserReturn returnWitnessState returnWitnessRequest).action =
        .accepted returnWitnessRequest := by
  constructor
  · apply FailStop.selectReturnAuthority_wellFormed
    simp [returnWitnessBase, returnWitnessLifecycle, FailStop.WellFormed,
      returnWitnessCapabilities, Interrupt.WellFormed,
      SubjectLifecycle.WellFormed]
    intro object subject frame howned
    by_cases h100 : object = 100
    · subst object
      simp at howned
      cases howned
      simp_all
    · by_cases h101 : object = 101
      · subst object
        simp [h100] at howned
        cases howned
        simp_all
      · simp [h100, h101] at howned
  · rfl

private def returnWitnessMemory : MemoryLifecycle.State :=
  { capabilities := returnWitnessLifecycle.capabilities
    allocator :=
      { frames := [100, 101]
        status := fun frame =>
          if frame = 100 then .owned 100
          else if frame = 101 then .owned 101
          else .reserved }
    binding := fun object =>
      if object = 100 then some 100 else if object = 101 then some 101 else none
    issued := fun object => object = 1 || object = 100 || object = 101 }

@[simp] private theorem returnWitnessMemory_capabilities :
    returnWitnessMemory.capabilities = returnWitnessCapabilities := rfl

@[simp] private theorem returnWitnessMemory_binding object :
    returnWitnessMemory.binding object =
      if object = 100 then some 100 else if object = 101 then some 101 else none := rfl

@[simp] private theorem returnWitnessMemory_issued object :
    returnWitnessMemory.issued object =
      (object = 1 || object = 100 || object = 101) := rfl

private def returnWitnessVirtualMemory : VirtualMapping.State :=
  { memory := returnWitnessMemory
    owner := returnWitnessLifecycle.addressOwner
    mappings := fun space page =>
      if space = 1 ∧ page = 100 then
        some { object := 100, permissions := { read := true, write := false } }
      else if space = 1 ∧ page = 101 then
        some { object := 101, permissions := { read := true, write := true } }
      else none
    issuedAddressSpace := fun space => space = 1 }

@[simp] private theorem returnWitnessVirtualMemory_capabilities :
    returnWitnessVirtualMemory.memory.capabilities = returnWitnessCapabilities := rfl

@[simp] private theorem returnWitnessVirtualMemory_owner addressSpace :
    returnWitnessVirtualMemory.owner addressSpace =
      if addressSpace = 1 then some 1 else none := rfl

@[simp] private theorem returnWitnessVirtualMemory_owner_lifecycle :
    returnWitnessVirtualMemory.owner = returnWitnessLifecycle.addressOwner := rfl

@[simp] private theorem returnWitnessVirtualMemory_wellFormed :
    VirtualMapping.LifecycleWellFormed returnWitnessVirtualMemory := by
  refine ⟨?_, returnWitnessCapabilities_wellFormed, ?_, ?_⟩
  · constructor
    · intro addressSpace subject howner
      simp [returnWitnessVirtualMemory, returnWitnessLifecycle] at howner
      rcases howner with ⟨rfl, rfl⟩
      rfl
    · intro addressSpace page mapping hmapping
      simp only [returnWitnessVirtualMemory] at hmapping
      split at hmapping
      next hselected =>
        rcases hselected with ⟨rfl, rfl⟩
        cases hmapping
        refine ⟨1, 100, rfl, rfl, rfl, rfl, ?_, ?_⟩
        · intro
          change Capability.HasAuthority returnWitnessCapabilities 1 100 .read
          simp
        · simp
      next hnotSelected =>
        split at hmapping
        next hselected =>
          rcases hselected with ⟨rfl, rfl⟩
          cases hmapping
          refine ⟨1, 101, rfl, rfl, rfl, rfl, ?_, ?_⟩
          · intro
            change Capability.HasAuthority returnWitnessCapabilities 1 101 .read
            simp
          · intro
            change Capability.HasAuthority returnWitnessCapabilities 1 101 .write
            simp
        next hnotSelected => contradiction
  · intro addressSpace subject howner
    simp [returnWitnessVirtualMemory, returnWitnessLifecycle] at howner
    rcases howner with ⟨rfl, rfl⟩
    have hauthority :
        Capability.HasAuthority returnWitnessCapabilities 1 1 .revoke := by
      simp
    exact ⟨rfl, rfl, rfl, rfl, hauthority⟩
  · intro addressSpace hlive hkind
    by_cases hspace : addressSpace = 1
    · subst addressSpace
      exact ⟨1, rfl⟩
    · change returnWitnessCapabilities.kinds addressSpace =
        some .addressSpace at hkind
      rw [returnWitnessCapabilities_kinds] at hkind
      simp [hspace] at hkind

private def returnWitnessEndpoints : EndpointIPC.State :=
  { capabilities := returnWitnessLifecycle.capabilities
    allocator := returnWitnessMemory.allocator
    binding := returnWitnessMemory.binding
    issued := returnWitnessMemory.issued
    issuedAddressSpace := fun _ => false
    mailbox := fun _ => none
    sendHistory := fun _ => [] }

private def returnWitnessComposite : FailStop.CompositeState :=
  let scheduler : Scheduler.State :=
    { lifecycle := returnWitnessLifecycle, ready := [], capacity := 0 }
  let resumable : ResumablePreemption.State :=
    { scheduler
      contexts := []
      capacity := 0
      translations := { virtual := returnWitnessVirtualMemory, active := some 1, entries := [] } }
  let transfers : CapabilityTransfer.State :=
    { toEndpointState := returnWitnessEndpoints
      pending := fun _ => none }
  { execution := returnWitnessBase
    scheduler
    preemption := { scheduler, timerArmed := false, acceptedTicks := 1 }
    virtualMemory := returnWitnessVirtualMemory
    ipc := { virtualMemory := returnWitnessVirtualMemory, endpoints := returnWitnessEndpoints }
    capabilities := returnWitnessLifecycle.capabilities
    lifecycle := returnWitnessLifecycle
    resumable
    transfers
    blockingIPC :=
      { scheduler
        mailbox := fun _ => none
        waiters := fun _ => []
        waiterEndpoint := fun _ => none
        waiterCapacity := 0
        completion := fun _ => none }
    blockingContexts := fun _ => none }

private def containedFaultWitnessFrame : Interrupt.HardwareFrame :=
  { returnWitnessRequest.hardware with vector := 14 }

set_option maxRecDepth 100000 in
/-- Concrete non-vacuity for the contained-cleanup contract: the live
return-authority fixture binds execution subject `1` to the authoritative
lifecycle, and a user page fault reaches contained cleanup plus an empty
deferred-drain suffix while preserving the complete deferred invariant. -/
theorem composite_contained_fault_cleanup_reachable_witness :
    FailStop.DeferredBlockingRuntimeWellFormed returnWitnessComposite ∧
      FailStop.ContainedFaultIdentityBound returnWitnessComposite ∧
      (FailStop.dispatchHardware returnWitnessComposite.execution
        containedFaultWitnessFrame).action = .contained 1 ∧
      FailStop.DeferredBlockingRuntimeWellFormed
        (FailStop.runAuthoritativeOperations returnWitnessComposite
          [.ordinary (.interrupt containedFaultWitnessFrame)]) := by
  have hstate :
      FailStop.DeferredBlockingRuntimeWellFormed returnWitnessComposite := by
    simp [FailStop.DeferredBlockingRuntimeWellFormed,
      FailStop.RuntimeWellFormed, FailStop.CompositeState.Coherent,
      FailStop.CompositeState.DeferredCancellationWellFormed,
      FailStop.CompositeState.BlockingIPCCoherent,
      FailStop.CompositeState.blockingIPCContext,
      BlockingIPCContext.DeferredWellFormed, BlockingIPCContext.WellFormed,
      BlockingIPCContext.ContextAgreement, returnWitnessComposite,
      returnWitnessBase,
      returnWitnessEndpoints,
      FailStop.WellFormed, Interrupt.WellFormed,
      returnWitnessCapabilities_wellFormed,
      IPCSyscall.WellFormed, EndpointIPC.WellFormed,
      Scheduler.WellFormed, Scheduler.ownsAddressSpace,
      Preemption.WellFormed, ResumablePreemption.WellFormed,
      ResumablePreemption.contextFor,
      ResumablePreemption.ReadyContextAgreement,
      ResumablePreemption.TranslationAgreement,
      ResumablePreemption.VirtualAgreement,
      ResumablePreemption.ResourceKindAgreement,
      CapabilityTransfer.WellFormed, BlockingIPC.WellFormed,
      DirectPortIO.AcceptedControls,
      DMAQuarantine.q35Accepted,
      Capability.rightsValid, Capability.nonemptyRights,
      Capability.rightsSubset, TLB.Coherent,
      BlockingIPCContext.emptyDeferred] <;> grind
  have hbound : FailStop.ContainedFaultIdentityBound returnWitnessComposite := by
    rfl
  have hcontained :
      (FailStop.dispatchHardware returnWitnessComposite.execution
        containedFaultWitnessFrame).action = .contained 1 := by
    native_decide
  exact ⟨hstate, hbound, hcontained,
    composite_contained_fault_then_deferred_trace_preserves
      returnWitnessComposite containedFaultWitnessFrame 1 []
      hstate hbound hcontained⟩

private def nmiWitnessContext (mode : InterruptEntry.InterruptedMode) :
    InterruptEntry.NmiContext :=
  { currentSubject := 1
    activeAddressSpace := 1
    activeCr3 := 0xa000
    stackIdentity := InterruptEntry.nmiStackIdentity
    stackFirst := InterruptEntry.nmiAbstractStackFirst
    stackPastLast := InterruptEntry.nmiAbstractStackPastLast
    interruptedMode := mode }

private def nmiWitnessRaw (origin : Interrupt.Privilege) : InterruptEntry.RawNmiEntry :=
  let frame : InterruptEntry.RawNmiFrame :=
    match origin with
    | .user => ⟨0x64100, 0x23, 0x202, 0x65ff8, 0x1b, true, true⟩
    | .kernel => ⟨0x101000, 0x08, 0x2, 0x700ff8, 0x10, true, true⟩
  { descriptor := InterruptEntry.nmiEntry
    boundStub := InterruptEntry.nmiVector
    errorCode := none
    frame
    claimedOrigin := origin
    frameBytes := 40
    frameAddress := 0x903fd8
    acCleared := true
    dfCleared := true }

/-- Concrete CPL3 and CPL0 raw snapshots both reach the reviewed terminal
normalizer and then the absorbing composite transition. -/
theorem nmi_user_kernel_nonvacuous :
    let userContext := nmiWitnessContext .running
    let kernelContext := nmiWitnessContext .running
    let userRaw := nmiWitnessRaw .user
    let kernelRaw := nmiWitnessRaw .kernel
    let userEvent := InterruptEntry.makeNormalizedNmi userRaw userContext
    let kernelEvent := InterruptEntry.makeNormalizedNmi kernelRaw kernelContext
    InterruptEntry.normalizeNmi userRaw userContext 1 1 = .accepted userEvent ∧
      InterruptEntry.normalizeNmi kernelRaw kernelContext 1 1 = .accepted kernelEvent ∧
      ((FailStop.gate returnWitnessComposite (.nmi userRaw userContext)).state.execution.mode =
        .halted (FailStop.acceptedNmiRecord returnWitnessComposite.execution userEvent)) ∧
      ((FailStop.gate returnWitnessComposite (.nmi kernelRaw kernelContext)).state.execution.mode =
        .halted (FailStop.acceptedNmiRecord returnWitnessComposite.execution kernelEvent)) := by
  native_decide

private def nmiHandlingWitness (vector : Nat) : FailStop.CompositeState :=
  let frame : Interrupt.HardwareFrame :=
    { returnWitnessRequest.hardware with vector }
  { returnWitnessComposite with
    execution :=
      { returnWitnessComposite.execution with
        core :=
          { returnWitnessComposite.execution.core with
            context :=
              { returnWitnessComposite.execution.core.context with entryActive := true } }
        mode := .handling (FailStop.activeEntry frame) } }

/-- Every named handling and post-halt trace class has a concrete executable
witness.  The three active ordinary purposes admit a kernel-origin NMI without
finishing the handler; copy authority is cleared; and repeated, post-double-
fault, ordinary-operation, and return suffixes leave the terminal latch
unchanged. -/
theorem nmi_named_handling_and_after_halt_witnesses :
    let raw := nmiWitnessRaw .kernel
    let handlingContext := nmiWitnessContext .handling
    let handlingEvent := InterruptEntry.makeNormalizedNmi raw handlingContext
    let syscallState := nmiHandlingWitness 128
    let pageFaultState := nmiHandlingWitness 14
    let timerState := nmiHandlingWitness 32
    let syscallNext := (FailStop.gate syscallState (.nmi raw handlingContext)).state
    let pageFaultNext := (FailStop.gate pageFaultState (.nmi raw handlingContext)).state
    let timerNext := (FailStop.gate timerState (.nmi raw handlingContext)).state
    let runningContext := nmiWitnessContext .running
    let runningEvent := InterruptEntry.makeNormalizedNmi raw runningContext
    let copyArmed :=
      { returnWitnessComposite with
        execution := { returnWitnessComposite.execution with copyOverride := true } }
    let runningNext := (FailStop.gate copyArmed (.nmi raw runningContext)).state
    let doubleFaultFrame : Interrupt.HardwareFrame :=
      { returnWitnessRequest.hardware with vector := 14 }
    let doubleFaulted :=
      { pageFaultState with
        execution :=
          (FailStop.dispatchHardware pageFaultState.execution doubleFaultFrame).state }
    syscallNext.execution.mode =
        .halted (FailStop.acceptedNmiRecord syscallState.execution handlingEvent) ∧
      pageFaultNext.execution.mode =
        .halted (FailStop.acceptedNmiRecord pageFaultState.execution handlingEvent) ∧
      timerNext.execution.mode =
        .halted (FailStop.acceptedNmiRecord timerState.execution handlingEvent) ∧
      runningNext.execution.mode =
        .halted (FailStop.acceptedNmiRecord copyArmed.execution runningEvent) ∧
      runningNext.execution.copyOverride = false ∧
      (FailStop.gate runningNext (.nmi raw runningContext)).result =
        .rejectedHalted (FailStop.acceptedNmiRecord copyArmed.execution runningEvent) ∧
      (FailStop.dispatchHardware pageFaultState.execution doubleFaultFrame).action =
        .fatal .doubleFault ∧
      (FailStop.gate doubleFaulted (.nmi raw handlingContext)).state.execution.mode =
        doubleFaulted.execution.mode ∧
      (FailStop.runOperations syscallNext [.scheduleTick, .restart]).execution.mode =
        syscallNext.execution.mode ∧
      (FailStop.runOperations syscallNext
        [.selectUserReturn .initialDispatch, .userReturn returnWitnessRequest]).execution.mode =
          syscallNext.execution.mode := by
  native_decide

/-- SC-BOOT-IDT-PHASE: before the runtime IDT is published, every admitted
bootstrap-phase event is one immediate absorbing terminal latch: it records the
bounded boot-phase reason, preserves the not-yet-published business state, arms
no return authority, never advances the publication chain, and absorbs every
later publication or event. -/
theorem boot_interrupt_phase_early_terminal (α : Type)
    (state : BootInterruptPhase.State α) event operations
    (hphase : state.phase = .bootstrap32 ∨ state.phase = .bootstrap64)
    (hlatched : state.latched = none) :
    let record : BootInterruptPhase.EarlyHaltRecord :=
      ⟨state.phase, event.vector, event.hasErrorCode, event.fromUser, .earlyEvent⟩
    let next := (BootInterruptPhase.dispatch state event).state
    (BootInterruptPhase.dispatch state event).outcome = .terminalLatched record ∧
      next.phase = .terminal ∧
      next.latched = some record ∧
      next.returnAuthorityArmed = false ∧
      next.business = state.business ∧
      BootInterruptPhase.run next operations = next := by
  exact BootInterruptPhase.owned_bootstrap_event_terminal_absorbing state event
    operations hphase hlatched

/-- SC-NMI-FAILSTOP: an exact normalized vector-2 terminal entry from running
or any ordinary handling state freezes every business subsystem, clears return
and copy authority, records the kernel-owned context/CR3, and absorbs every
later typed operation. -/
theorem nmi_terminal_failstop state raw context event proposals
    (hmode : state.execution.mode = .running ∨
      ∃ active, state.execution.mode = .handling active)
    (hcontext : context.interruptedMode =
      FailStop.interruptedModeOf state.execution.mode)
    (haccepted : InterruptEntry.normalizeNmi raw context
      state.execution.core.context.currentSubject
      state.execution.core.context.activeAddressSpace = .accepted event) :
    let next := (FailStop.gate state (.nmi raw context)).state
    next.execution.mode =
        .halted (FailStop.acceptedNmiRecord state.execution event) ∧
      next.execution.core.lifecycle = state.execution.core.lifecycle ∧
      next.execution.core.context.currentSubject =
        state.execution.core.context.currentSubject ∧
      next.execution.core.context.activeAddressSpace =
        state.execution.core.context.activeAddressSpace ∧
      next.execution.core.context.kernelStack =
        state.execution.core.context.kernelStack ∧
      next.execution.returnAddressSpace = state.execution.returnAddressSpace ∧
      next.execution.returnPlan = state.execution.returnPlan ∧
      next.execution.returnAuthority = state.execution.returnAuthority ∧
      next.execution.returnAuthorityArmed = false ∧
      next.execution.copyOverride = false ∧
      next.scheduler = state.scheduler ∧
      next.preemption = state.preemption ∧
      next.virtualMemory = state.virtualMemory ∧
      next.ipc = state.ipc ∧
      next.capabilities = state.capabilities ∧
      next.lifecycle = state.lifecycle ∧
      FailStop.runOperations next proposals = next := by
  exact FailStop.accepted_nmi_composite_atomicity state raw context event proposals
    hmode hcontext haccepted

private def returnWitnessSyscallFrame : Interrupt.HardwareFrame :=
  { returnWitnessRequest.hardware with vector := 128 }

private def returnWitnessSyscallRequest : Interrupt.UserReturnRequest :=
  { returnWitnessRequest with
    hardware := returnWitnessSyscallFrame
    purpose := .syscallResume }

private def returnWitnessSyscallCall : Syscall.UntrustedCall :=
  { number := 2, arg0 := 100, arg1 := 0, arg2 := 0 }

private def returnWitnessRejectedCall : Syscall.UntrustedCall :=
  { number := 99, arg0 := 0, arg1 := 0, arg2 := 0 }

/-- Non-vacuity witness for the composite gate contract: an unknown syscall
is classified as a typed subsystem rejection and preserves the literal
composite pre-state. -/
theorem composite_subsystem_rejection_reachable_witness :
    (FailStop.gate returnWitnessComposite
        (.syscall returnWitnessRejectedCall)).result =
      .completed (.syscall (.rejected (.decode .unknownSyscall))) ∧
    FailStop.SubsystemRejection returnWitnessComposite
      (.syscall returnWitnessRejectedCall)
      (.syscall (.rejected (.decode .unknownSyscall))) ∧
    (FailStop.operationReply returnWitnessComposite
      (.syscall returnWitnessRejectedCall)).isNonfatalRejection = true ∧
    (FailStop.gate returnWitnessComposite
        (.syscall returnWitnessRejectedCall)).state = returnWitnessComposite := by
  have hresult :
      (FailStop.gate returnWitnessComposite
          (.syscall returnWitnessRejectedCall)).result =
        .completed (.syscall (.rejected (.decode .unknownSyscall))) := by
    native_decide
  have hrejected :
      FailStop.SubsystemRejection returnWitnessComposite
        (.syscall returnWitnessRejectedCall)
        (.syscall (.rejected (.decode .unknownSyscall))) :=
    .syscall returnWitnessRejectedCall (.decode .unknownSyscall) (by native_decide)
  have hclassified :
      (FailStop.operationReply returnWitnessComposite
        (.syscall returnWitnessRejectedCall)).isNonfatalRejection = true := by
    native_decide
  exact ⟨hresult, hrejected, hclassified,
    FailStop.gate_classified_rejection_global_atomicity returnWitnessComposite
      (.syscall returnWitnessRejectedCall) hclassified⟩

set_option maxRecDepth 100000 in
/-- Concrete typed composite trace: syscall entry clears old authority, the
syscall body installs its final lifecycle/context and reselects, and the
following return is accepted without changing the composite state. -/
theorem user_return_composite_entry_witness :
    let entered := (FailStop.gate returnWitnessComposite
      (.interrupt returnWitnessSyscallFrame)).state
    let called := (FailStop.gate entered
      (.syscall returnWitnessSyscallCall)).state
    called.ReturnPlanLive = true ∧
      called.execution.returnAuthorityArmed = true ∧
      (FailStop.gate called (.userReturn returnWitnessSyscallRequest)).state = called := by
  dsimp only
  constructor
  · native_decide
  constructor
  · native_decide
  · rfl

set_option maxRecDepth 100000 in
/-- Syscall classification alone cannot authorize a return: the syscall body
must install its final lifecycle/context before authority is reselected. -/
theorem user_return_syscall_entry_cannot_skip_body :
    let entered := (FailStop.gate returnWitnessComposite
      (.interrupt returnWitnessSyscallFrame)).state
    entered.execution.returnAuthorityArmed = false := by
  native_decide

/-- SC-USER-RETURN-FAILSTOP: a rejected outgoing return atomically latches a
typed terminal record, freezes every composite subsystem, and absorbs all
later operations. -/
theorem user_return_rejection_failstop state request reason proposals
    (hmode : state.execution.mode = .running)
    (harmed : state.execution.returnAuthorityArmed = true)
    (hlive : state.ReturnPlanLive = true)
    (hrejected : Interrupt.validateUserReturn
      (FailStop.authoritativeReturnRequest state.execution request) = .rejected reason) :
    let record : FailStop.HaltRecord :=
      { reason := .invalidUserReturn state.execution.returnAuthority.purpose reason
        active := none
        incomingVector := request.hardware.vector
        incomingOrigin := request.hardware.savedPrivilege }
    let next := (FailStop.gate state (.userReturn request)).state
    next.execution.mode = .halted record ∧
      next.execution.core.lifecycle = state.execution.core.lifecycle ∧
      next.scheduler = state.scheduler ∧
      next.preemption = state.preemption ∧
      next.virtualMemory = state.virtualMemory ∧
      next.ipc = state.ipc ∧
      next.capabilities = state.capabilities ∧
      next.lifecycle = state.lifecycle ∧
      FailStop.runOperations next proposals = next := by
  exact FailStop.rejected_user_return_composite_atomicity state request reason proposals
    hmode harmed hlive hrejected

/-- SC-EXTENDED-STATE-DENIAL: a contained unsupported extended-state event is
confined to the authoritative current subject and requires the exact accepted
fail-closed control policy and live address-space binding. -/
theorem extended_state_denial_confined state event subject
    (h : (ExtendedState.classify state event).result = .denied subject) :
    subject = state.currentSubject ∧
      ExtendedState.Denied state.features state.controls ∧
      event.origin = .user ∧
      event.normalizedSubject = state.currentSubject ∧
      event.normalizedAddressSpace = state.activeAddressSpace ∧
      ExtendedState.ContextBound state := by
  exact ExtendedState.denied_subject_confined state event subject h

/-- SC-EXTENDED-STATE-CLEANUP: authoritative denial cleanup removes every
live scheduler and resumable-context reference to the faulting subject. -/
theorem extended_state_denial_cleanup_nonresumable machine subject :
    let cleaned := ResumablePreemption.cleanupSubject machine subject
    cleaned.scheduler.lifecycle.capabilities.subjects subject = false ∧
      subject ∉ cleaned.scheduler.ready ∧
      cleaned.scheduler.lifecycle.current ≠ some subject ∧
      ResumablePreemption.contextFor cleaned.contexts subject = none := by
  exact ExtendedState.denial_cleanup_cannot_resume machine subject

/-- SC-EXTENDED-STATE-GLOBAL: every finite sequence of authoritative composite
operations preserves the exact denied-state predicate. -/
theorem extended_state_global_runtime_preservation state operations
    (hinvariant : ExtendedState.CompositePolicyInvariant state) :
    ExtendedState.CompositePolicyInvariant
      (ExtendedState.runComposite state operations) := by
  exact ExtendedState.runComposite_preserves_policy state operations hinvariant

/-- SC-FAULT-DISPATCH-NONRESUMPTION: every successful atomic user-fault
transition starts from a live, runnable kernel-selected subject and removes it
from live/runnable identity, the ready queue, the current slot, the authoritative
resumable bank, and every address space and mapping it owned. -/
theorem fault_dispatch_success_nonresumption state entry
    (hsuccess : (∃ reason, (FaultDispatch.dispatch state entry).action = .idle reason) ∨
      ∃ reason context,
        (FaultDispatch.dispatch state entry).action = .dispatch reason context) :
    ∃ faulting,
      state.scheduler.lifecycle.current = some faulting ∧
        state.scheduler.lifecycle.capabilities.subjects faulting = true ∧
        state.scheduler.lifecycle.runnable faulting = true ∧
        (FaultDispatch.dispatch state entry).state.scheduler.lifecycle.capabilities.subjects
          faulting = false ∧
        (FaultDispatch.dispatch state entry).state.scheduler.lifecycle.runnable
          faulting = false ∧
        faulting ∉ (FaultDispatch.dispatch state entry).state.scheduler.ready ∧
        (FaultDispatch.dispatch state entry).state.scheduler.lifecycle.current ≠ some faulting ∧
        ResumablePreemption.contextFor
          (FaultDispatch.dispatch state entry).state.contexts faulting = none ∧
        ∀ addressSpace,
          state.scheduler.lifecycle.addressOwner addressSpace = some faulting →
            (FaultDispatch.dispatch state entry).state.scheduler.lifecycle.addressOwner
                addressSpace = none ∧
              ∀ page,
                (FaultDispatch.dispatch state entry).state.translations.virtual.mappings
                  addressSpace page = none := by
  exact FaultDispatch.successful_nonresumption state entry hsuccess

/-- SC-USER-FAULT-CLASS-CONTAINMENT: every accepted modeled CPL3 page-fault,
divide-error, or breakpoint entry that reaches a successful composite result
binds its typed reason to the manifest-decoded vector with the reviewed error
convention, performs the same complete current-subject cleanup with the
authoritative survivor-or-idle selection, and preserves peer resources; a
kernel-origin occurrence of any accepted contained frame is the absorbing
fatal transition, never containment. -/
theorem user_fault_class_containment state frame reason
    (hsuccess : (FaultDispatch.dispatch state (.accepted frame)).action = .idle reason ∨
      ∃ context,
        (FaultDispatch.dispatch state (.accepted frame)).action = .dispatch reason context) :
    (InterruptEntry.containedReason? frame.vector = some reason ∧
      frame.vector = reason.vector ∧
      frame.purpose = .userFault ∧
      frame.origin = .user ∧
      frame.errorCode.isSome = reason.hasErrorWord ∧
      frame.cs % 4 = 3) ∧
    (∃ faulting,
      state.scheduler.lifecycle.current = some faulting ∧
        state.scheduler.lifecycle.capabilities.subjects faulting = true ∧
        state.scheduler.lifecycle.runnable faulting = true ∧
        (FaultDispatch.dispatch state (.accepted frame)).state.scheduler.lifecycle.capabilities.subjects
          faulting = false ∧
        (FaultDispatch.dispatch state (.accepted frame)).state.scheduler.lifecycle.runnable
          faulting = false ∧
        faulting ∉ (FaultDispatch.dispatch state (.accepted frame)).state.scheduler.ready ∧
        (FaultDispatch.dispatch state (.accepted frame)).state.scheduler.lifecycle.current ≠
          some faulting ∧
        ResumablePreemption.contextFor
          (FaultDispatch.dispatch state (.accepted frame)).state.contexts faulting = none ∧
        ∀ addressSpace,
          state.scheduler.lifecycle.addressOwner addressSpace = some faulting →
            (FaultDispatch.dispatch state (.accepted frame)).state.scheduler.lifecycle.addressOwner
                addressSpace = none ∧
              ∀ page,
                (FaultDispatch.dispatch state (.accepted frame)).state.translations.virtual.mappings
                  addressSpace page = none) ∧
    (∀ kernelFrame : InterruptEntry.NormalizedFrame,
      kernelFrame.origin = .kernel → state.halted = false →
        FaultDispatch.dispatch state (.accepted kernelFrame) =
          FaultDispatch.halt state .kernelOrigin) := by
  refine ⟨FaultDispatch.success_reason_vector_binding state frame reason hsuccess, ?_, ?_⟩
  · exact FaultDispatch.successful_nonresumption state (.accepted frame)
      (hsuccess.elim (fun hidle => Or.inl ⟨reason, hidle⟩)
        (fun ⟨context, hdispatch⟩ => Or.inr ⟨reason, context, hdispatch⟩))
  · intro kernelFrame horigin hrunning
    exact FaultDispatch.kernel_origin_is_fatal state kernelFrame hrunning horigin

/-- SC-STALE-TRANSLATION-INVALIDATION: the public invalidation step returns an
effect determined by the accepted logical transition and its checked target.  An
accepted unmap invalidates exactly the requested address-space page and leaves
that translation absent in the returned cache, so a later access cannot use the
old translation; an actor that is not the checked owner is rejected, requests no
invalidation, and preserves the complete cache/model state. -/
theorem stale_translation_invalidation_confined
    (state : TLB.State)
    (actor : VirtualMapping.SubjectId) (addressSpace : VirtualMapping.AddressSpaceId)
    (page : VirtualMapping.VirtualPage) (context : X86PageTable.AccessContext) :
    ((StaleTranslation.step state (.unmap actor addressSpace page)).accepted = true →
      (StaleTranslation.step state (.unmap actor addressSpace page)).effect =
          .page addressSpace page ∧
        TLB.lookup
          (StaleTranslation.step state (.unmap actor addressSpace page)).state.entries
          { addressSpace, page } context = none) ∧
    (∀ owner, state.virtual.owner addressSpace = some owner → owner ≠ actor →
      (StaleTranslation.step state (.unmap actor addressSpace page)).accepted = false ∧
        (StaleTranslation.step state (.unmap actor addressSpace page)).effect = .none ∧
        (StaleTranslation.step state (.unmap actor addressSpace page)).state = state) := by
  refine ⟨fun h => ⟨StaleTranslation.unmap_accepted_effect state actor addressSpace page h,
      StaleTranslation.accepted_unmap_target_absent state actor addressSpace page context h⟩,
    fun owner howner hne =>
      StaleTranslation.unmap_wrong_owner_inert state actor addressSpace page owner howner hne⟩

/-- Protection reduction is sufficient at the sole composite boundary: an
accepted logical protection step exposes exactly the page-local effect, the
authoritative gate preserves its complete folded invariant, and the affected
translation is already absent from the published successor. -/
theorem stale_translation_composite_protect_effect_sufficient
    state page permissions context
    (hstate : FailStop.AuthoritativeRuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted :
      (StaleTranslation.step state.resumable.translations
        (.protect state.execution.core.context.currentSubject
          state.execution.core.context.activeAddressSpace page permissions)).accepted =
        true) :
    (FailStop.authoritativeGate state
        (.ordinary (.protect page permissions))).result =
        .completed (.ordinary (.protect .accepted)) ∧
      FailStop.AuthoritativeRuntimeWellFormed
        (FailStop.authoritativeGate state
          (.ordinary (.protect page permissions))).state ∧
      (StaleTranslation.step state.resumable.translations
        (.protect state.execution.core.context.currentSubject
          state.execution.core.context.activeAddressSpace page permissions)).effect =
        .page state.execution.core.context.activeAddressSpace page ∧
      TLB.lookup
        (FailStop.authoritativeGate state
          (.ordinary (.protect page permissions))).state.resumable.translations.entries
        { addressSpace := state.execution.core.context.activeAddressSpace, page }
        context = none := by
  generalize hprotect :
      TLB.protect state.resumable.translations
        state.execution.core.context.currentSubject
        state.execution.core.context.activeAddressSpace page permissions = outcome
  cases outcome with
  | mk next result =>
      cases result with
      | rejected reason =>
          simp [StaleTranslation.step, hprotect] at haccepted
      | accepted =>
          have hgate :=
            FailStop.gate_protect_accepted_invalidates_tlb state page permissions
              next hmode hprotect hstate.1
          constructor
          · simp [FailStop.authoritativeGate, hmode,
              FailStop.authoritativeOperationReply, FailStop.operationReply, hprotect]
          constructor
          · exact
              FailStop.authoritativeGate_protect_preserves_authoritativeRuntimeWellFormed
                state page permissions hstate
          constructor
          · exact StaleTranslation.protect_accepted_effect
              state.resumable.translations
              state.execution.core.context.currentSubject
              state.execution.core.context.activeAddressSpace page permissions haccepted
          · rw [FailStop.authoritativeGate_ordinary_state]
            exact hgate.2.2.2.2 context

/-- The stale-translation invalidation contract is non-vacuous: the reviewed
fixture caches a live CPL3 translation, an accepted unmap returns the exact page
effect leaving the page absent, and the frame can only be reused after a full
flush while the old virtual page stays unreachable. -/
theorem stale_translation_invalidation_nonvacuous :
    (TLB.access StaleTranslation.filled 7
        StaleTranslation.ctx).toOption.map (fun result => result.1) = some 4 ∧
      (StaleTranslation.step StaleTranslation.filled (.unmap 0 1 7)).effect =
        .page 1 7 ∧
      (TLB.access
        (StaleTranslation.step StaleTranslation.filled (.unmap 0 1 7)).state 7
        StaleTranslation.ctx).isOk = false ∧
      (StaleTranslation.step StaleTranslation.filled (.release 0 0)).effect = .flush ∧
      (StaleTranslation.step StaleTranslation.filled (.release 0 0)).state.entries = [] ∧
      (TLB.access StaleTranslation.reused 7 StaleTranslation.ctx).isOk = false := by
  native_decide

/-- SC-INVALIDATION-PUBLICATION-ORDER: the standalone logical publication
protocol retains the complete published state; only the exact fresh
ticket/effect completion can publish its recorded successor; an older ticket
is inert; and bounded reuse requires acknowledged release and destruction with
no pending effect.  Full-composite projection integration is intentionally not
part of this claim. -/
theorem invalidation_publication_order :
    (∀ state kind request,
      (InvalidationPublication.prepare state kind request).state.published =
        state.published) ∧
    (∀ state ack,
      (InvalidationPublication.acknowledge state ack).accepted = true →
        ∃ pending,
          state.pending = some pending ∧
          ack.ticket = pending.ticket ∧
          ack.effect = pending.step.effect ∧
          (InvalidationPublication.acknowledge state ack).state.published =
            pending.step.state ∧
          (InvalidationPublication.acknowledge state ack).state.pending = none) ∧
    (∀ state ack pending,
      state.pending = some pending →
      ack.ticket ≠ pending.ticket →
        (InvalidationPublication.acknowledge state ack).accepted = false ∧
        (InvalidationPublication.acknowledge state ack).state = state ∧
        (InvalidationPublication.acknowledge state ack).effect = .none) ∧
    (∀ state,
      (InvalidationPublication.publishReuse state).accepted = true →
        state.pending = none ∧
        state.releaseAcknowledged = true ∧
        state.destroyAcknowledged = true) ∧
    (∀ state kind request,
      InvalidationPublication.WellFormed state →
        InvalidationPublication.WellFormed
          (InvalidationPublication.prepare state kind request).state) ∧
    (∀ state ack,
      InvalidationPublication.WellFormed state →
        InvalidationPublication.WellFormed
          (InvalidationPublication.acknowledge state ack).state) ∧
    (∀ state,
      InvalidationPublication.WellFormed state →
        InvalidationPublication.WellFormed
          (InvalidationPublication.publishReuse state).state) := by
  exact ⟨InvalidationPublication.prepare_retains_published,
    InvalidationPublication.acknowledge_accepted_exact,
    fun state ack pending hpending hticket =>
      InvalidationPublication.acknowledge_wrong_ticket_inert
        state ack pending hpending hticket,
    InvalidationPublication.reuse_publication_requires_retirement_ack,
    InvalidationPublication.prepare_preserves_wellFormed,
    InvalidationPublication.acknowledge_preserves_wellFormed,
    InvalidationPublication.publishReuse_preserves_wellFormed⟩

/-- SC-AUTHORITATIVE-RETIREMENT-FLUSH: the authoritative composite retirement
and root-switch paths expose the global half of the invalidation contract:
accepted subject cleanup
preserves the complete runtime invariant and flushes every cached translation
before released capacity is reusable, while every accepted resumable root
switch preserves that invariant and returns the same empty-cache model. -/
theorem authoritative_retirement_and_root_switch_flush :
    (∀ state subject,
      FailStop.RuntimeWellFormed state →
      state.execution.mode = .running →
      (SubjectLifecycle.terminate state.lifecycle subject).result = .accepted →
        FailStop.RuntimeWellFormed
            (FailStop.gate state (.terminateSubject subject)).state ∧
          (FailStop.gate state
            (.terminateSubject subject)).state.resumable.translations.entries = []) ∧
    (∀ state frame registers,
      FailStop.RuntimeWellFormed state →
      state.execution.mode = .running →
      (ResumablePreemption.switch state.resumable state.execution.core
        frame registers).error = none →
        FailStop.RuntimeWellFormed
            (FailStop.gate state (.resumePreempt frame registers)).state ∧
          (FailStop.gate state
            (.resumePreempt frame registers)).state.resumable.translations.entries = []) ∧
    FrameBudgetScenario.retirementEffect .bAllocated .terminateA = .flush ∧
    FrameBudgetScenario.retirementEffect .aAllocated .releaseA = .flush ∧
    FrameBudgetScenario.machineInvalidationEffect
        (FrameBudgetScenario.encodeState .bAllocated)
        (FrameBudgetScenario.encodeCommand .terminateA) =
      FrameBudgetScenario.terminateFlushToken ∧
    FrameBudgetScenario.machineInvalidationEffect
        (FrameBudgetScenario.encodeState .aAllocated)
        (FrameBudgetScenario.encodeCommand .releaseA) =
      FrameBudgetScenario.releaseFlushToken ∧
    (FrameBudgetScenario.publishFreshAfterRetirement
        FrameBudgetScenario.retirementPrepared).accepted = false ∧
    (FrameBudgetScenario.acknowledgeRetirement
        FrameBudgetScenario.retirementPrepared
        FrameBudgetScenario.terminateFlushToken).accepted = true ∧
    FrameBudgetScenario.freshRepublished.published.scrub.memory.binding 21 =
      some 100 ∧
    FrameBudgetScenario.freshRepublished.published.userMapping =
      some (1, 21, { slot := 1, identity := 3 }, 100,
        FrameBudgetScenario.machineUserPage) := by
  exact ⟨fun state subject hstate hmode haccepted =>
      let h := FailStop.gate_terminateSubject_accepted_flushes_translations
        state subject hstate hmode haccepted
      ⟨h.1, h.2.1⟩,
    FailStop.gate_resumePreempt_accepted_flushes_translations,
    FrameBudgetScenario.retirement_effects_are_exact_and_trace_bound.1,
    FrameBudgetScenario.retirement_effects_are_exact_and_trace_bound.2.1,
    FrameBudgetScenario.retirement_effects_are_exact_and_trace_bound.2.2.1,
    FrameBudgetScenario.retirement_effects_are_exact_and_trace_bound.2.2.2.1,
    FrameBudgetScenario.invalidation_acknowledged_fresh_republication.1,
    FrameBudgetScenario.retirement_ack_publishes_reclaimed_frame.1,
    FrameBudgetScenario.invalidation_acknowledged_fresh_republication.2.2.2.1,
    FrameBudgetScenario.invalidation_acknowledged_fresh_republication.2.2.2.2.2.1⟩

/-- SC-USER-FAULT-SHARED-CONTAINMENT: over one shared two-subject pre-state the
real CPL3 divide-error, breakpoint, page-fault, and denied-port entries drive a
single subject-termination/peer-survival transition: each dispatches the same
survivor with its typed reason bound to the manifest vector, the port-denial
composition reuses the identical vector-14 dispatch, and every successful
post-state is byte-for-byte the page-fault post-state. -/
theorem user_fault_shared_containment_vocabulary :
    (FaultDispatch.dispatch DirectPortContainment.witnessSchedule
        UserFaultContainmentVocabulary.divideErrorEntry).action =
        .dispatch .divideError DirectPortContainment.witnessSurvivorContext ∧
      (FaultDispatch.dispatch DirectPortContainment.witnessSchedule
          UserFaultContainmentVocabulary.breakpointEntry).action =
        .dispatch .breakpoint DirectPortContainment.witnessSurvivorContext ∧
      (FaultDispatch.dispatch DirectPortContainment.witnessSchedule
          DirectPortContainment.witnessEntry).action =
        .dispatch .pageFault DirectPortContainment.witnessSurvivorContext ∧
      (DirectPortContainment.containDeniedPort
          DirectPortContainment.witnessDevices DirectPortIO.selectedControls
          DirectPortContainment.serialProbe
          DirectPortContainment.witnessSchedule
          DirectPortContainment.witnessEntry).fault.state =
        (FaultDispatch.dispatch DirectPortContainment.witnessSchedule
          DirectPortContainment.witnessEntry).state ∧
      (FaultDispatch.dispatch DirectPortContainment.witnessSchedule
          UserFaultContainmentVocabulary.divideErrorEntry).state =
        (FaultDispatch.dispatch DirectPortContainment.witnessSchedule
          DirectPortContainment.witnessEntry).state ∧
      (FaultDispatch.dispatch DirectPortContainment.witnessSchedule
          UserFaultContainmentVocabulary.breakpointEntry).state =
        (FaultDispatch.dispatch DirectPortContainment.witnessSchedule
          DirectPortContainment.witnessEntry).state :=
  UserFaultContainmentVocabulary.shared_contained_classes_one_transition

/-- SC-SCHEDULED-ISOLATION: equal finite public traces preserve low-equivalence. -/
theorem scheduled_finite_trace_isolation observer left right leftSteps rightSteps
    (hlow : ScheduledObservation.LowEquiv observer left right)
    (hevents : ScheduledObservation.projection observer left leftSteps =
      ScheduledObservation.projection observer right rightSteps) :
    ScheduledObservation.LowEquiv observer
      (ScheduledObservation.run observer left leftSteps).1
      (ScheduledObservation.run observer right rightSteps).1 := by
  exact ScheduledObservation.finite_trace_lowEquiv observer left right leftSteps rightSteps
    hlow hevents

/-- Non-vacuity: a well-formed state and an accepted transition exist. -/
theorem initial_transition_witness :
    KernelTransition.WellFormed KernelTransition.initialState ∧
      (KernelTransition.transition KernelTransition.initialState .initialize).result = .accepted := by
  exact ⟨KernelTransition.initialState_wellFormed, rfl⟩

/-- Concrete non-vacuity witness for the page-table separation contract: the encoder materializes
two leaves for the same page in distinct address spaces and their walks differ. -/
private def pageTableSeparationState : VirtualMapping.State :=
  { memory :=
      { capabilities :=
          { subjects := fun _ => true
            objects := fun object => object = 10 || object = 11
            kinds := fun object =>
              if object = 10 || object = 11 then some .memory else none
            slots := fun _ _ => none }
        allocator :=
          { frames := [4, 5]
            status := fun frame => if frame = 4 then .owned 10
              else if frame = 5 then .owned 11 else .reserved }
        binding := fun object => if object = 10 then some 4
          else if object = 11 then some 5 else none
        issued := fun object => object = 10 || object = 11 }
    owner := fun addressSpace => if addressSpace = 1 then some 1
      else if addressSpace = 2 then some 2 else none
    mappings := fun addressSpace page =>
      if page != 7 then none
      else if addressSpace = 1 then
        some { object := 10, permissions := { read := true } }
      else if addressSpace = 2 then
        some { object := 11, permissions := { read := true } }
      else none
    issuedAddressSpace := fun addressSpace => addressSpace = 1 || addressSpace = 2 }

theorem page_table_separation_witness :
    (X86PageTable.encode pageTableSeparationState 1).leaf 7 =
        some (X86PageTable.Leaf.mk 4 true false true true true) ∧
      (X86PageTable.encode pageTableSeparationState 2).leaf 7 =
        some (X86PageTable.Leaf.mk 5 true false true true true) ∧
      X86PageTable.walk (X86PageTable.encode pageTableSeparationState 1) 7 .read = .ok 4 ∧
      X86PageTable.walk (X86PageTable.encode pageTableSeparationState 2) 7 .read = .ok 5 ∧
      X86PageTable.walk (X86PageTable.encode pageTableSeparationState 1) 7 .read ≠
        X86PageTable.walk (X86PageTable.encode pageTableSeparationState 2) 7 .read := by
  refine ⟨by decide, by decide, by rfl, by rfl, ?_⟩
  simp [pageTableSeparationState, X86PageTable.walk, X86PageTable.encode,
    X86PageTable.encodedLeaf, X86PageTable.userAncestor, X86PageTable.canonicalPage,
    X86PageTable.lowerCanonicalPages, X86PageTable.representableFrame,
    X86PageTable.physicalFrameLimit]

/-- Adversarial executable check: an unsupported command cannot be accepted. -/
example : (KernelTransition.transition KernelTransition.initialState .unsupported).result =
    .rejected := by decide

end LeanOS.SecurityClaims
