import LeanOS.BootInterruptPhase
import LeanOS.BootTopology
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
import LeanOS.CompositeObservation
import LeanOS.CompositeUnwinding
import LeanOS.CompositeChannels
import LeanOS.CompositeLocalRespect
import LeanOS.CompositeOwnTermination
import LeanOS.CompositeSwitchedChannels
import LeanOS.CompositeRegisterChannels
import LeanOS.CompositeSubjectGate
import LeanOS.CompositeFullChannels
import LeanOS.DMAQuarantine
import LeanOS.QotomPCIFinalAdmission
import LeanOS.QotomBroadcomAssignment
import LeanOS.QotomNoSmapControl
import LeanOS.QotomCopyRootPublication
import LeanOS.QotomEntryIntegration
import LeanOS.QotomBlockingIPCIntegration
import LeanOS.PlatformAdmission
import LeanOS.IOMMU
import LeanOS.DirectPortIO
import LeanOS.DirectPortContainment
import LeanOS.DeviceProgramConfinement
import LeanOS.DeviceCapability
import LeanOS.UserFaultContainmentVocabulary
import LeanOS.FaultHandler
import LeanOS.TimerServer
import LeanOS.FrameServer
import LeanOS.SpawnSyscall
import LeanOS.ChildLoader
import LeanOS.ChildLoaderJoint
import LeanOS.StaleTranslation
import LeanOS.InvalidationPublication
import LeanOS.NotifyReply
import LeanOS.Refinement.BootTransitionC
import LeanOS.Refinement.ChildLoaderC
import LeanOS.Refinement.SpawnSyscallC
import LeanOS.Refinement.NetworkSubjectC
import LeanOS.Refinement.DhcpSubjectC
import LeanOS.ConsoleServer
import LeanOS.EndpointDirectory
import LeanOS.KeyboardEcho
import LeanOS.NetworkSubject
import LeanOS.DhcpSubject
import LeanOS.GtkRekey
import LeanOS.TimingBudget

/-! # Stable security-claim contract

Each theorem independently restates one advertised proposition. Changes to an
implementation theorem's assumptions or conclusion therefore require an
explicit change here and in `docs/security-claims.md`.
-/
namespace LeanOS.SecurityClaims

/-- SC-PLATFORM-PROFILE-ADMISSION: a successful admission identifies one
complete closed profile, and the bounded runtime preserves that identity while
never publishing an AP start. -/
theorem platform_profile_admission_confined raw profile operations
    (hadmitted : PlatformAdmission.admit raw = .accepted profile) :
    PlatformAdmission.completeMatch (PlatformAdmission.manifest profile) raw = true ∧
      (PlatformAdmission.runRuntime
        (PlatformAdmission.initialRuntime profile) operations).admitted = profile ∧
      (PlatformAdmission.runRuntime
        (PlatformAdmission.initialRuntime profile) operations).apStartIssued = false := by
  exact ⟨PlatformAdmission.accepted_identifies_complete_profile raw profile hadmitted,
    PlatformAdmission.run_preserves_profile _ operations,
    PlatformAdmission.run_never_publishes_ap_start _ operations rfl⟩

/-- SC-QOTOM-NOSMAP-NONAUTH: the live-control checkpoint cannot claim either
root has been published and cannot grant CPL3 authority. -/
theorem qotom_nosmap_checkpoint_withholds_authority
    (cr0 cr4Before cr4After efer rflags : UInt64) :
    QotomNoSmapControl.query cr0 cr4Before cr4After efer rflags 8 = 0 ∧
    QotomNoSmapControl.query cr0 cr4Before cr4After efer rflags 9 = 0 ∧
    QotomNoSmapControl.query cr0 cr4Before cr4After efer rflags 10 = 0 := by
  simp [QotomNoSmapControl.query]

/-- SC-QOTOM-COPY-ROOT-NONAUTH: root-publication fields require the complete
checkpoint predicate, while the checkpoint itself cannot grant CPL3 authority. -/
theorem qotom_copy_root_publication_withholds_cpl3_and_gates_roots
    (variant builderStatus protectedCount removed retained aliases closedRoot
      copyRoot closedScan copyScan transferred bytesMatch activeRoot : UInt64) :
    QotomCopyRootPublication.query variant builderStatus protectedCount removed
        retained aliases closedRoot copyRoot closedScan copyScan transferred
        bytesMatch activeRoot 6 = 0 ∧
      (QotomCopyRootPublication.query variant builderStatus protectedCount
          removed retained aliases closedRoot copyRoot closedScan copyScan
          transferred bytesMatch activeRoot 3 = 1 →
        QotomCopyRootPublication.accepted variant builderStatus protectedCount
          removed retained aliases closedRoot copyRoot closedScan copyScan
          transferred bytesMatch activeRoot = true) ∧
      (QotomCopyRootPublication.query variant builderStatus protectedCount
          removed retained aliases closedRoot copyRoot closedScan copyScan
          transferred bytesMatch activeRoot 4 = 1 →
        QotomCopyRootPublication.accepted variant builderStatus protectedCount
          removed retained aliases closedRoot copyRoot closedScan copyScan
          transferred bytesMatch activeRoot = true) := by
  exact ⟨QotomCopyRootPublication.query_never_authorizes_cpl3 _ _ _ _ _ _ _ _ _ _ _ _ _,
    QotomCopyRootPublication.publication_requires_acceptance _ _ _ _ _ _ _ _ _ _ _ _ _,
    QotomCopyRootPublication.publication_requires_acceptance _ _ _ _ _ _ _ _ _ _ _ _ _⟩

/-- SC-QOTOM-ENTRY-CHECKPOINT-NONAUTH: the first physical entry/return
checkpoint is gated by its complete scalar result and grants no general CPL3
authority. -/
theorem qotom_entry_checkpoint_withholds_cpl3_and_gates_result
    (entries returns incomingRoot closedRoot activeRoot frame userIf gprs closeReadback
      returnReload : UInt64) :
    QotomEntryIntegration.query entries returns incomingRoot closedRoot activeRoot
        frame userIf gprs closeReadback returnReload 6 = 0 ∧
      (QotomEntryIntegration.query entries returns incomingRoot closedRoot activeRoot
          frame userIf gprs closeReadback returnReload 3 = 1 →
        QotomEntryIntegration.accepted entries returns incomingRoot closedRoot
          activeRoot frame userIf gprs closeReadback returnReload = true) := by
  exact ⟨QotomEntryIntegration.query_never_authorizes_cpl3 _ _ _ _ _ _ _ _ _ _,
    QotomEntryIntegration.checkpoint_claim_requires_acceptance _ _ _ _ _ _ _ _ _ _⟩

/-- SC-QOTOM-BLOCKING-IPC-CONDITIONAL: a nonzero CPL3 authority word from the
physical blocking-IPC profile requires its complete scalar admission. -/
theorem qotom_blocking_ipc_authority_requires_whole_profile
    (pciTrust noSmap entryCheckpoint closedRoot copyInRoot copyOutRoot
      closedScan copyInScan copyOutScan syscallGate pageFaultGate
      timerGateAbsent picMasked contextBanks modelBindings : UInt64)
    (h : QotomBlockingIPCIntegration.query pciTrust noSmap entryCheckpoint
      closedRoot copyInRoot copyOutRoot closedScan copyInScan copyOutScan
      syscallGate pageFaultGate timerGateAbsent picMasked contextBanks
      modelBindings 3 = 1) :
    QotomBlockingIPCIntegration.accepted pciTrust noSmap entryCheckpoint
      closedRoot copyInRoot copyOutRoot closedScan copyInScan copyOutScan
      syscallGate pageFaultGate timerGateAbsent picMasked contextBanks
      modelBindings = true :=
  QotomBlockingIPCIntegration.cpl3_authority_requires_admission
    pciTrust noSmap entryCheckpoint closedRoot copyInRoot copyOutRoot
    closedScan copyInScan copyOutScan syscallGate pageFaultGate timerGateAbsent
    picMasked contextBanks modelBindings h

/-- SC-QOTOM-PCI-CONDITIONAL: the named initial J1900 trust profile accepts
exactly the final Command vector. The hardware meaning of its five fixed
premises remains an explicit platform assumption, outside this theorem. -/
theorem qotom_pci_initial_trust_contract_confined
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : UInt64) :
    QotomPCIFinalAdmission.exportedInitialTrustContract
        c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 = 1 ↔
      QotomPCIFinalAdmission.commandsAccepted
        c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 = true :=
  QotomPCIFinalAdmission.initial_trust_contract_one_iff
    c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15

/-- SC-QOTOM-BROADCOM-ASSIGNMENT-CONDITIONAL: the named assigned-Broadcom
variant admits a binding only after the permitted single PMCSR store under the
accepted initial trust contract, leaves the device in D0 with Command zero and
Transactions Pending clear, and only for a program that declares no DMA and
can never set Bus Master. The observations' fidelity stays outside. -/
theorem qotom_broadcom_assignment_confined
    (contract d3Status d3CommandBefore d3CommandAfter d3PmcsrBefore d3PmcsrAfter
      preCommand prePmcsr preBar0 preBar1 offset width value
      postCommand postPmcsr postBar0 postBar1 deviceControlStatus quietPolls
      quietDeviceStatus bus device function identity dma cfgWrite cmdSet : UInt64)
    (h : QotomBroadcomAssignment.exportedAdmission contract d3Status d3CommandBefore
      d3CommandAfter d3PmcsrBefore d3PmcsrAfter preCommand prePmcsr preBar0 preBar1
      offset width value postCommand postPmcsr postBar0 postBar1
      deviceControlStatus quietPolls quietDeviceStatus
      bus device function identity dma cfgWrite cmdSet = 1) :
    contract = 1 ∧ offset = 0x44 ∧ width = 2 ∧ value = 0x4008 ∧
      postCommand = 0 ∧ postPmcsr = 0x4008 ∧
      deviceControlStatus &&& QotomBroadcomAssignment.transactionsPendingBit = 0 ∧
      dma = 0 ∧ cmdSet &&& 0x4 = 0 := by
  have hw := QotomBroadcomAssignment.admission_requires_write _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
  have he := QotomBroadcomAssignment.write_exact _ _ _ _ _ _ _ _ _ _ _ _ _ hw.1
  have hp := QotomBroadcomAssignment.admission_post_state _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
  have hb := QotomBroadcomAssignment.admission_policy_no_bus_master _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
  exact ⟨hw.2, he.1, he.2.1, he.2.2, hp.1, hp.2.1, hp.2.2.2.2.1, hb.2.2.2.2.1,
    hb.2.2.2.2.2.1⟩

/-- SC-SINGLE-CORE-BOOT-ADMISSION: accepted topology admission exposes exactly
one enabled processor with BSP/executing-CPU agreement; the admitted runtime
vocabulary preserves that premise and cannot publish an AP-start event. -/
theorem single_core_boot_admission_confined rootTags rootCopy tableCopies executingId
    snapshot processor operations
    (hdecoded : BootTopology.decodeAuthoritativeAcpiTopologySnapshot rootTags rootCopy
      tableCopies executingId = .ok snapshot)
    (haccepted : BootTopology.admit snapshot = .accepted processor) :
    let bootAdmitted := BootTopology.consumeAuthoritativeBootAdmission
      BootTopology.bootAdmissionInitial
      (BootTopology.decodeAndAdmitAuthoritativeAcpiTopology rootTags rootCopy
        tableCopies executingId)
    let final := BootTopology.runRuntime bootAdmitted.business operations
    snapshot.processors.filter (fun candidate => candidate.enabled) = [processor] ∧
      processor.apicId = snapshot.bspId ∧
      snapshot.executingId = snapshot.bspId ∧
      bootAdmitted.latched = none ∧
      final.singleCoreAdmitted = true ∧
      final.apStartIssued = false := by
  obtain ⟨hsingleton, hbsp, hexecuting⟩ :=
    BootTopology.accepted_implies_single_enabled_bsp snapshot processor haccepted
  have hauthoritative :
      BootTopology.decodeAndAdmitAuthoritativeAcpiTopology rootTags rootCopy
        tableCopies executingId =
      .ok (.accepted processor) := by
    unfold BootTopology.decodeAndAdmitAuthoritativeAcpiTopology
    rw [hdecoded]
    exact congrArg Except.ok haccepted
  have hboot :
      (BootTopology.consumeAuthoritativeBootAdmission BootTopology.bootAdmissionInitial
        (BootTopology.decodeAndAdmitAuthoritativeAcpiTopology rootTags rootCopy
          tableCopies executingId)).latched = none := by
    simp [hauthoritative, BootTopology.consumeAuthoritativeBootAdmission,
      BootTopology.bootAdmissionInitial,
      BootTopology.consumeAdmission, BootTopology.admissionInitial]
  have hadmitted :
      (BootTopology.consumeAuthoritativeBootAdmission BootTopology.bootAdmissionInitial
        (BootTopology.decodeAndAdmitAuthoritativeAcpiTopology rootTags rootCopy
          tableCopies executingId)).business.singleCoreAdmitted = true := by
    simp [hauthoritative, BootTopology.consumeAuthoritativeBootAdmission,
      BootTopology.bootAdmissionInitial,
      BootTopology.consumeAdmission, BootTopology.admissionInitial]
  have hnotStarted :
      (BootTopology.consumeAuthoritativeBootAdmission BootTopology.bootAdmissionInitial
        (BootTopology.decodeAndAdmitAuthoritativeAcpiTopology rootTags rootCopy
          tableCopies executingId)).business.apStartIssued = false := by
    simp [hauthoritative, BootTopology.consumeAuthoritativeBootAdmission,
      BootTopology.bootAdmissionInitial,
      BootTopology.consumeAdmission, BootTopology.admissionInitial]
  exact ⟨hsingleton, hbsp, hexecuting, hboot,
    BootTopology.run_runtime_preserves_single_core_admission _ operations hadmitted,
    BootTopology.run_runtime_cannot_publish_ap_start _ operations hnotStarted⟩

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

/-- SC-COMPOSITE-INFLIGHT-REVOCATION: an accepted transitive revocation
through the public composite gate reaches authority that is still in flight.
Every sealed descendant of the revoked lineage root loses its envelope, its
pending record, and its IPC mailbox entry in the same step that clears the
installed descendants; afterwards no retained sealed record and no installed
slot descends from that root; and the derivation history and identity frontier
are unchanged, so the canceled generation can never be reissued.  The concrete
#175 trace `CompositeDispatcher.inFlightRevocationCanonicalEdges` exercises
this contract end to end, including the typed empty receipt and the distinct
replacement generation. -/
theorem composite_subtree_revocation_reaches_in_flight_authority
    state authoritySlot victim victimSlot next target published
    (hmode : state.execution.mode = .running)
    (haccepted : Capability.revokeSubtreeRuntimeSafe state.capabilities
      state.execution.core.context.currentSubject authoritySlot victim victimSlot =
        { state := next, result := .accepted })
    (hlookup : Capability.lookup state.capabilities victim victimSlot = .found target)
    (hpublished : published =
      (FailStop.gate state (.capabilityRevokeSubtree authoritySlot victim victimSlot)).state) :
    (∀ endpoint transfer, state.transfers.pending endpoint = some transfer →
      CapabilityTransfer.descendsFromRoot state.transfers.capabilities target.identity
        transfer = true →
      published.transfers.pending endpoint = none ∧
        published.transfers.mailbox endpoint = none ∧
        published.ipc.endpoints.mailbox endpoint = none) ∧
    (∀ endpoint transfer, published.transfers.pending endpoint = some transfer →
      CapabilityTransfer.descendsFromRoot state.transfers.capabilities target.identity
        transfer = false) ∧
    (∀ subject slot capability,
      published.capabilities.slots subject slot = some capability →
        Capability.descendsFrom state.capabilities capability.identity target.identity
          state.capabilities.nextIdentity = false) ∧
    published.capabilities.derivations = state.capabilities.derivations ∧
    published.capabilities.nextIdentity = state.capabilities.nextIdentity := by
  obtain ⟨hpendingMonotone, hslotsMonotone⟩ :=
    FailStop.gate_capabilityRevokeSubtree_accepted_authority_monotone state authoritySlot
      victim victimSlot next target published hmode haccepted hlookup hpublished
  obtain ⟨hderivations, hnextIdentity⟩ :=
    FailStop.gate_capabilityRevokeSubtree_accepted_retains_history state authoritySlot
      victim victimSlot next published hmode haccepted hpublished
  refine ⟨?_, hpendingMonotone, hslotsMonotone, hderivations, hnextIdentity⟩
  intro endpoint transfer hpending hdescendant
  exact FailStop.gate_capabilityRevokeSubtree_accepted_cancels_sealed_descendants state
    authoritySlot victim victimSlot next target endpoint transfer published hmode haccepted
    hlookup hpublished hpending hdescendant

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
    (∀ handleWord word0 word1 receiver,
      (FailStop.blockingGate state (.send handleWord word0 word1)).result =
        .completed (.send (.woke receiver)) →
      ∃ saved, saved.owner = receiver ∧
        (FailStop.dispatchBlockingSend state handleWord word0 word1).restored = some saved ∧
        ResumablePreemption.validContext
          (FailStop.blockingGate state (.send handleWord word0 word1)).state.resumable saved) ∧
    (∀ subject saved,
      FailStop.BlockingRuntimeWellFormed state →
      (FailStop.blockingGate state (.cancel subject)).result =
        .completed (.cancel (.cancelled saved)) →
      FailStop.BlockingRuntimeWellFormed
        (FailStop.blockingGate state (.cancel subject)).state) ∧
    (∀ subject cancelled,
      (FailStop.blockingGate state (.cancel subject)).result =
        .completed (.cancel (.cancelled cancelled)) →
      ∃ saved, saved.owner = cancelled ∧
        (FailStop.dispatchBlockingCancel state subject).restored = some saved ∧
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

/-- SC-COMPOSITE-OBSERVER-ISOLATION: over the authoritative composite state and
`authoritativeGate`, (1) every operation classified silent for an observer
leaves its view (authority row, named objects, IPC observations, owned spaces
and mappings, and the public scheduler choice) unchanged, and (2) finite runs
from low-equivalent states with equal observer event projections end
low-equivalent.  Given the preserved `AuthoritativeRuntimeWellFormed`
invariant, (3) the coherent families (`protect`, `createSubject`, blocking
send/receive/cancel away from the observer) are also silent and (4) the
trace theorem holds with them silent.  For the scheduled observer, (5) its
own operations in `ownStepConsistent` are step consistent and (6) those in
`ownOutputConsistent` are output consistent, and (7) the two compose: a run
of its operations in both families returns equal results and ends
low-equivalent.  (8) The two excluded channels are real: the global
capability-identity counter breaks step consistency and a delegation's
destination breaks output consistency.

Extensions (`CompositeLocalRespect`, `CompositeOwnSteps`, `CompositeChannels`):
(9) scheduler operations that keep the scheduled subject, transfers on
endpoints the observer does not name, interrupts that contain no scheduled
subject, failed resumable switches, and drains of other subjects are also
silent, and (10) the trace theorem holds with them silent.  With the identity
counter a declared public input (`OwnStepCounter`), (11) step consistency
extends to the observer's delegation into its own row, its transfer offers,
creation of any subject, and every scheduler operation except
`terminateCurrent`; (12) output consistency extends to transfer offer and
receipt, subtree revocation of its own slot, creation and termination of the
observer itself, `scheduleNext`, and `terminateCurrent`; (13) with the ready queue public as well, to
`scheduleYield`, `scheduleTick`, and `scheduleRemove`; (14) transfer receipt is
step consistent given agreement on the carried object; (15) deferred drains are
step consistent and the observer's own drain is output consistent; and (16) the
extended families compose.  (17) Every remaining exclusion with a counterexample
is a real channel: creation, termination, and queue admission of another
subject reveal its liveness and issuance; termination of another subject
cancels the observer's pending offers; delegation to and revocation of another
subject's slot reveal its occupancy, with the counters equal; and without the
public counter, transfer offers are step inconsistent.

(18) Given `AuthoritativeRuntimeWellFormed` of both states, the observer's own
termination, `terminateCurrent`, and interrupts are step consistent, and
interrupts and NMIs are output consistent.  (19) The kernel evaluates, on the
canonical sample boot plan (which compiles), the channels that need another
subject to run: subtree revocation of the observer's own or another subject's
capability depends on a hidden derivation.  The replies of the observer's
timer switch, blocking send, and wait cancellation used to carry another
subject's saved registers (the adversarial record, evaluated on the same
pairs); they now name a subject only and agree on those pairs, and (20) the
subject a switch reply names is the scheduled subject of the post-state, part
of every observer's view.

(21) Over the subject-facing gate `FailStop.subjectGate`, which refuses a
scheduled subject's request that names another subject (delegation into,
direct or subtree revocation of, creation, termination and queue admission
of, wait cancellation and deferred drain of another subject) with one fixed
result and no effect: local respect also treats another subject's refused
request as silent, finite-trace noninterference holds, the observer's
cross-subject requests are step and output consistent without any further
premise, every family above carries over, and on the `#542` pairs the
cross-subject channels are closed.

(22) **The full statement.**  The observer's full view adds the authority
its row implies (`CompositeFullView`): the lineage of every capability it
holds, and for every sealed transfer pending on an object it names, that
transfer's lineage, the carried object's view, and the lineage of the transfer
pending on the carried object.  The subject gate also refuses receipt of a
transfer whose carried object has a transfer of its own pending.  Then, with
the identity counter and the scheduler's bookkeeping public and both states
runtime-well-formed (`CompositeFullIsolation.FullStep`): every request the
scheduled observer makes through the subject gate is step consistent on the
full view, and output consistent except that a user return may differ by
halting (the termination channel); another subject's request silent on the
full view leaves it unchanged, and finite traces with equal projections end
fully low-equivalent; and the subtree-revocation pair of (19) is not fully
low-equivalent: the derivation it depended on is in the full view. -/
theorem composite_observer_isolation (observer : Nat) :
    (∀ state operation, CompositeObservation.isSilent observer state operation = true →
      CompositeObservation.LowEquiv observer
        (FailStop.authoritativeGate state operation).state state) ∧
    (∀ left right leftOperations rightOperations,
      CompositeObservation.LowEquiv observer left right →
      CompositeObservation.projection observer left leftOperations =
        CompositeObservation.projection observer right rightOperations →
      CompositeObservation.LowEquiv observer
        (CompositeObservation.run observer left leftOperations).1
        (CompositeObservation.run observer right rightOperations).1) ∧
    (∀ state operation, FailStop.AuthoritativeRuntimeWellFormed state →
      CompositeUnwinding.isSilentCoherent observer state operation = true →
      CompositeObservation.LowEquiv observer
        (FailStop.authoritativeGate state operation).state state) ∧
    (∀ left right leftOperations rightOperations,
      FailStop.AuthoritativeRuntimeWellFormed left →
      FailStop.AuthoritativeRuntimeWellFormed right →
      CompositeObservation.LowEquiv observer left right →
      CompositeUnwinding.projectionCoherent observer left leftOperations =
        CompositeUnwinding.projectionCoherent observer right rightOperations →
      CompositeObservation.LowEquiv observer
        (CompositeUnwinding.runCoherent observer left leftOperations).1
        (CompositeUnwinding.runCoherent observer right rightOperations).1) ∧
    (∀ left right operation, CompositeUnwinding.OwnStep observer left right →
      CompositeUnwinding.ownStepConsistent observer operation = true →
      CompositeObservation.LowEquiv observer
        (FailStop.authoritativeGate left (.ordinary operation)).state
        (FailStop.authoritativeGate right (.ordinary operation)).state) ∧
    (∀ left right operation, CompositeUnwinding.OwnStep observer left right →
      CompositeUnwinding.ownOutputConsistent observer operation = true →
      (FailStop.authoritativeGate left (.ordinary operation)).result =
        (FailStop.authoritativeGate right (.ordinary operation)).result) ∧
    (∀ left right operations, CompositeUnwinding.OwnStep observer left right →
      (∀ operation, operation ∈ operations →
        CompositeUnwinding.ownTraceFamily observer operation = true) →
      (CompositeUnwinding.ownRun left operations).2 =
          (CompositeUnwinding.ownRun right operations).2 ∧
        CompositeObservation.LowEquiv observer (CompositeUnwinding.ownRun left operations).1
          (CompositeUnwinding.ownRun right operations).1) ∧
    (∀ plan,
      (CompositeUnwinding.OwnStep 2 (CompositeUnwinding.Channels.seed plan)
          (CompositeUnwinding.Channels.shifted plan) ∧
        ¬ CompositeObservation.LowEquiv 2
          (FailStop.authoritativeGate (CompositeUnwinding.Channels.seed plan)
            (.ordinary CompositeUnwinding.Channels.delegateToSelf)).state
          (FailStop.authoritativeGate (CompositeUnwinding.Channels.shifted plan)
            (.ordinary CompositeUnwinding.Channels.delegateToSelf)).state) ∧
      (FailStop.authoritativeGate (CompositeUnwinding.Channels.seed plan)
          (.ordinary CompositeUnwinding.Channels.delegateToOther)).result ≠
        (FailStop.authoritativeGate (CompositeUnwinding.Channels.shifted plan)
          (.ordinary CompositeUnwinding.Channels.delegateToOther)).result) ∧
    (∀ state operation, FailStop.AuthoritativeRuntimeWellFormed state →
      CompositeLocalRespect.isSilentExtended observer state operation = true →
      CompositeObservation.LowEquiv observer
        (FailStop.authoritativeGate state operation).state state) ∧
    (∀ left right leftOperations rightOperations,
      FailStop.AuthoritativeRuntimeWellFormed left →
      FailStop.AuthoritativeRuntimeWellFormed right →
      CompositeObservation.LowEquiv observer left right →
      CompositeLocalRespect.projectionExtended observer left leftOperations =
        CompositeLocalRespect.projectionExtended observer right rightOperations →
      CompositeObservation.LowEquiv observer
        (CompositeLocalRespect.runExtended observer left leftOperations).1
        (CompositeLocalRespect.runExtended observer right rightOperations).1) ∧
    (∀ left right operation, CompositeOwnSteps.OwnStepCounter observer left right →
      CompositeOwnSteps.ownStepConsistentCounter observer operation = true →
      CompositeObservation.LowEquiv observer
        (FailStop.authoritativeGate left (.ordinary operation)).state
        (FailStop.authoritativeGate right (.ordinary operation)).state) ∧
    (∀ left right operation, CompositeOwnSteps.OwnStepCounter observer left right →
      CompositeOwnSteps.ownOutputConsistentCounter observer operation = true →
      (FailStop.authoritativeGate left (.ordinary operation)).result =
        (FailStop.authoritativeGate right (.ordinary operation)).result) ∧
    (∀ left right operation, CompositeUnwinding.OwnStep observer left right →
      CompositeOwnSteps.SchedulerPublic left right →
      CompositeOwnSteps.schedulerOutputConsistent operation = true →
      (FailStop.authoritativeGate left (.ordinary operation)).result =
        (FailStop.authoritativeGate right (.ordinary operation)).result) ∧
    (∀ left right endpointWord destinationSlot, CompositeUnwinding.OwnStep observer left right →
      CompositeOwnSteps.CarriedAgree observer left right →
      CompositeObservation.LowEquiv observer
        (FailStop.authoritativeGate left
          (.ordinary (.transferAccept endpointWord destinationSlot))).state
        (FailStop.authoritativeGate right
          (.ordinary (.transferAccept endpointWord destinationSlot))).state) ∧
    (∀ left right subject, CompositeUnwinding.OwnStep observer left right →
      FailStop.AuthoritativeRuntimeWellFormed left →
      FailStop.AuthoritativeRuntimeWellFormed right →
      CompositeObservation.LowEquiv observer
          (FailStop.authoritativeGate left (.drainDeferred subject)).state
          (FailStop.authoritativeGate right (.drainDeferred subject)).state ∧
        (FailStop.authoritativeGate left (.drainDeferred observer)).result =
          (FailStop.authoritativeGate right (.drainDeferred observer)).result) ∧
    (∀ left right operations, CompositeOwnSteps.OwnStepCounter observer left right →
      (∀ operation, operation ∈ operations →
        CompositeOwnSteps.ownTraceFamilyCounter observer operation = true) →
      (CompositeUnwinding.ownRun left operations).2 =
          (CompositeUnwinding.ownRun right operations).2 ∧
        CompositeObservation.LowEquiv observer (CompositeUnwinding.ownRun left operations).1
          (CompositeUnwinding.ownRun right operations).1) ∧
    (∀ plan,
      (CompositeOwnSteps.OwnStepCounter 2 (CompositeChannels.seed plan)
          (CompositeChannels.created plan) ∧
        CompositeChannels.reply (CompositeChannels.seed plan) CompositeChannels.createThree ≠
          CompositeChannels.reply (CompositeChannels.created plan)
            CompositeChannels.createThree ∧
        CompositeChannels.reply (CompositeChannels.seed plan) (.terminateSubject 3) ≠
          CompositeChannels.reply (CompositeChannels.created plan) (.terminateSubject 3) ∧
        CompositeChannels.reply (CompositeChannels.seed plan) (.scheduleAdd 3) ≠
          CompositeChannels.reply (CompositeChannels.created plan) (.scheduleAdd 3)) ∧
      (CompositeOwnSteps.OwnStepCounter 2 (CompositeChannels.offered plan)
          (CompositeChannels.offeredCreated plan) ∧
        ¬ CompositeObservation.LowEquiv 2
          (CompositeChannels.step (CompositeChannels.offered plan) (.terminateSubject 3))
          (CompositeChannels.step (CompositeChannels.offeredCreated plan)
            (.terminateSubject 3))) ∧
      (CompositeOwnSteps.OwnStepCounter 2 (CompositeChannels.toSlotThree plan)
          (CompositeChannels.toSlotTwo plan) ∧
        CompositeChannels.reply (CompositeChannels.toSlotThree plan)
            CompositeUnwinding.Channels.delegateToOther ≠
          CompositeChannels.reply (CompositeChannels.toSlotTwo plan)
            CompositeUnwinding.Channels.delegateToOther ∧
        CompositeChannels.reply (CompositeChannels.toSlotThree plan)
            (.capabilityRevoke 0 1 2) ≠
          CompositeChannels.reply (CompositeChannels.toSlotTwo plan)
            (.capabilityRevoke 0 1 2) ∧
        CompositeChannels.reply (CompositeChannels.toSlotThree plan)
            (.capabilityRevokeSubtree 0 1 2) ≠
          CompositeChannels.reply (CompositeChannels.toSlotTwo plan)
            (.capabilityRevokeSubtree 0 1 2)) ∧
      (CompositeUnwinding.OwnStep 2 (CompositeChannels.seed plan)
          (CompositeUnwinding.Channels.shifted plan) ∧
        (CompositeChannels.seed plan).capabilities.nextIdentity ≠
          (CompositeUnwinding.Channels.shifted plan).capabilities.nextIdentity ∧
        ¬ CompositeObservation.LowEquiv 2
          (CompositeChannels.step (CompositeChannels.seed plan) CompositeChannels.offerMemory)
          (CompositeChannels.step (CompositeUnwinding.Channels.shifted plan)
            CompositeChannels.offerMemory))) ∧
    (∀ left right, CompositeUnwinding.OwnStep observer left right →
      FailStop.AuthoritativeRuntimeWellFormed left →
      FailStop.AuthoritativeRuntimeWellFormed right →
      CompositeObservation.LowEquiv observer
          (FailStop.authoritativeGate left (.ordinary (.terminateSubject observer))).state
          (FailStop.authoritativeGate right (.ordinary (.terminateSubject observer))).state ∧
        CompositeObservation.LowEquiv observer
          (FailStop.authoritativeGate left (.ordinary .terminateCurrent)).state
          (FailStop.authoritativeGate right (.ordinary .terminateCurrent)).state ∧
        (∀ frame,
          CompositeObservation.LowEquiv observer
              (FailStop.authoritativeGate left (.ordinary (.interrupt frame))).state
              (FailStop.authoritativeGate right (.ordinary (.interrupt frame))).state ∧
            (FailStop.authoritativeGate left (.ordinary (.interrupt frame))).result =
              (FailStop.authoritativeGate right (.ordinary (.interrupt frame))).result) ∧
        (∀ raw context,
          (FailStop.authoritativeGate left (.ordinary (.nmi raw context))).result =
            (FailStop.authoritativeGate right (.ordinary (.nmi raw context))).result)) ∧
    (∃ plan, BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan) ∧
    (∀ plan, BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan →
      (CompositeOwnSteps.OwnStepCounter 2
          (CompositeSwitchedChannels.runFrom plan CompositeSwitchedChannels.leftTrace)
          (CompositeSwitchedChannels.runFrom plan CompositeSwitchedChannels.rightTrace) ∧
        ¬ CompositeObservation.LowEquiv 2
          (CompositeChannels.step
            (CompositeSwitchedChannels.runFrom plan CompositeSwitchedChannels.leftTrace)
            CompositeSwitchedChannels.ownSubtree)
          (CompositeChannels.step
            (CompositeSwitchedChannels.runFrom plan CompositeSwitchedChannels.rightTrace)
            CompositeSwitchedChannels.ownSubtree) ∧
        ¬ CompositeObservation.LowEquiv 2
          (CompositeChannels.step
            (CompositeSwitchedChannels.runFrom plan CompositeSwitchedChannels.leftTrace)
            CompositeSwitchedChannels.otherSubtree)
          (CompositeChannels.step
            (CompositeSwitchedChannels.runFrom plan CompositeSwitchedChannels.rightTrace)
            CompositeSwitchedChannels.otherSubtree)) ∧
      (CompositeOwnSteps.OwnStepCounter 2
          (CompositeSwitchedChannels.runFrom plan CompositeSwitchedChannels.preemptLeftTrace)
          (CompositeSwitchedChannels.runFrom plan CompositeSwitchedChannels.preemptRightTrace) ∧
        CompositeRegisterChannels.legacyResume
            (CompositeSwitchedChannels.runFrom plan CompositeSwitchedChannels.preemptLeftTrace)
            CompositeSwitchedChannels.preempt ≠
          CompositeRegisterChannels.legacyResume
            (CompositeSwitchedChannels.runFrom plan CompositeSwitchedChannels.preemptRightTrace)
            CompositeSwitchedChannels.preempt ∧
        CompositeOwnSteps.OwnStepCounter 2
          (CompositeSwitchedChannels.runFrom plan CompositeSwitchedChannels.blockedLeftTrace)
          (CompositeSwitchedChannels.runFrom plan CompositeSwitchedChannels.blockedRightTrace) ∧
        CompositeRegisterChannels.legacySend
            (CompositeSwitchedChannels.runFrom plan CompositeSwitchedChannels.blockedLeftTrace)
            CompositeChannels.endpointWord 5 6 ≠
          CompositeRegisterChannels.legacySend
            (CompositeSwitchedChannels.runFrom plan CompositeSwitchedChannels.blockedRightTrace)
            CompositeChannels.endpointWord 5 6 ∧
        CompositeRegisterChannels.legacyCancel
            (CompositeSwitchedChannels.runFrom plan CompositeSwitchedChannels.blockedLeftTrace) 1 ≠
          CompositeRegisterChannels.legacyCancel
            (CompositeSwitchedChannels.runFrom plan CompositeSwitchedChannels.blockedRightTrace)
            1) ∧
      (CompositeChannels.reply
            (CompositeSwitchedChannels.runFrom plan CompositeSwitchedChannels.preemptLeftTrace)
            CompositeSwitchedChannels.preempt =
          CompositeChannels.reply
            (CompositeSwitchedChannels.runFrom plan CompositeSwitchedChannels.preemptRightTrace)
            CompositeSwitchedChannels.preempt ∧
        (FailStop.authoritativeGate
            (CompositeSwitchedChannels.runFrom plan CompositeSwitchedChannels.blockedLeftTrace)
            CompositeSwitchedChannels.blockingSend).result =
          (FailStop.authoritativeGate
            (CompositeSwitchedChannels.runFrom plan CompositeSwitchedChannels.blockedRightTrace)
            CompositeSwitchedChannels.blockingSend).result ∧
        (FailStop.authoritativeGate
            (CompositeSwitchedChannels.runFrom plan CompositeSwitchedChannels.blockedLeftTrace)
            CompositeSwitchedChannels.blockingCancel).result =
          (FailStop.authoritativeGate
            (CompositeSwitchedChannels.runFrom plan CompositeSwitchedChannels.blockedRightTrace)
            CompositeSwitchedChannels.blockingCancel).result)) ∧
    (∀ state frame registers next,
      (FailStop.authoritativeGate state (.ordinary (.resumePreempt frame registers))).result =
        .completed (.ordinary (.resume (some next) none)) →
      (FailStop.authoritativeGate state
        (.ordinary (.resumePreempt frame registers))).state.lifecycle.current = some next) ∧
    (∀ state operation, FailStop.AuthoritativeRuntimeWellFormed state →
      CompositeSubjectGate.isSilentSubject observer state operation = true →
      CompositeObservation.LowEquiv observer (FailStop.subjectGate state operation).state state) ∧
    (∀ left right leftOperations rightOperations,
      FailStop.AuthoritativeRuntimeWellFormed left →
      FailStop.AuthoritativeRuntimeWellFormed right →
      CompositeObservation.LowEquiv observer left right →
      CompositeSubjectGate.projection observer left leftOperations =
        CompositeSubjectGate.projection observer right rightOperations →
      CompositeObservation.LowEquiv observer
        (CompositeSubjectGate.run observer left leftOperations).1
        (CompositeSubjectGate.run observer right rightOperations).1) ∧
    (∀ left right operation, CompositeOwnSteps.OwnStepCounter observer left right →
      FailStop.AuthoritativeRuntimeWellFormed left →
      FailStop.AuthoritativeRuntimeWellFormed right →
      CompositeSubjectGate.ownStepSubject observer operation = true →
      CompositeObservation.LowEquiv observer (FailStop.subjectGate left operation).state
        (FailStop.subjectGate right operation).state) ∧
    (∀ left right operation, CompositeOwnSteps.OwnStepCounter observer left right →
      FailStop.AuthoritativeRuntimeWellFormed left →
      FailStop.AuthoritativeRuntimeWellFormed right →
      CompositeSubjectGate.ownOutputSubject observer operation = true →
      (FailStop.subjectGate left operation).result =
        (FailStop.subjectGate right operation).result) ∧
    (∀ left right operation, CompositeUnwinding.OwnStep observer left right →
      CompositeSubjectGate.crossTarget observer operation = true →
      (FailStop.subjectGate left operation).state = left ∧
        (FailStop.subjectGate right operation).state = right ∧
        (FailStop.subjectGate left operation).result =
          (FailStop.subjectGate right operation).result) ∧
    (∀ plan,
      CompositeSubjectGate.subjectReply (CompositeChannels.seed plan)
          CompositeChannels.createThree =
        CompositeSubjectGate.subjectReply (CompositeChannels.created plan)
          CompositeChannels.createThree ∧
      CompositeSubjectGate.subjectReply (CompositeChannels.seed plan) (.terminateSubject 3) =
        CompositeSubjectGate.subjectReply (CompositeChannels.created plan)
          (.terminateSubject 3) ∧
      CompositeSubjectGate.subjectReply (CompositeChannels.seed plan) (.scheduleAdd 3) =
        CompositeSubjectGate.subjectReply (CompositeChannels.created plan) (.scheduleAdd 3) ∧
      CompositeObservation.LowEquiv 2
        (CompositeSubjectGate.subjectStep (CompositeChannels.offered plan)
          (.terminateSubject 3))
        (CompositeSubjectGate.subjectStep (CompositeChannels.offeredCreated plan)
          (.terminateSubject 3)) ∧
      CompositeSubjectGate.subjectReply (CompositeChannels.toSlotThree plan)
          CompositeUnwinding.Channels.delegateToOther =
        CompositeSubjectGate.subjectReply (CompositeChannels.toSlotTwo plan)
          CompositeUnwinding.Channels.delegateToOther ∧
      CompositeSubjectGate.subjectReply (CompositeChannels.toSlotThree plan)
          (.capabilityRevoke 0 1 2) =
        CompositeSubjectGate.subjectReply (CompositeChannels.toSlotTwo plan)
          (.capabilityRevoke 0 1 2) ∧
      CompositeSubjectGate.subjectReply (CompositeChannels.toSlotThree plan)
          (.capabilityRevokeSubtree 0 1 2) =
        CompositeSubjectGate.subjectReply (CompositeChannels.toSlotTwo plan)
          (.capabilityRevokeSubtree 0 1 2)) ∧
    (∀ plan, BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan →
      CompositeObservation.LowEquiv 2
        (CompositeSubjectGate.subjectStep
          (CompositeSwitchedChannels.runFrom plan CompositeSwitchedChannels.leftTrace)
          CompositeSwitchedChannels.otherSubtree)
        (CompositeSubjectGate.subjectStep
          (CompositeSwitchedChannels.runFrom plan CompositeSwitchedChannels.rightTrace)
          CompositeSwitchedChannels.otherSubtree)) ∧
    (∀ left right operation, CompositeFullIsolation.FullStep observer left right →
      CompositeFullView.FullLowEquiv observer (FailStop.subjectGate left operation).state
          (FailStop.subjectGate right operation).state ∧
        ((∀ request, operation = .ordinary (.userReturn request) →
            CompositeOwnSwitch.Continues (FailStop.subjectGate left operation).state ∧
              CompositeOwnSwitch.Continues (FailStop.subjectGate right operation).state) →
          (FailStop.subjectGate left operation).result =
            (FailStop.subjectGate right operation).result)) ∧
    (∀ state operation, FailStop.AuthoritativeRuntimeWellFormed state →
      CompositeFullTrace.isSilentFull observer state operation = true →
      CompositeFullView.FullLowEquiv observer (FailStop.subjectGate state operation).state
        state) ∧
    (∀ left right leftOperations rightOperations,
      FailStop.AuthoritativeRuntimeWellFormed left →
      FailStop.AuthoritativeRuntimeWellFormed right →
      CompositeFullView.FullLowEquiv observer left right →
      CompositeFullTrace.projection observer left leftOperations =
        CompositeFullTrace.projection observer right rightOperations →
      CompositeFullView.FullLowEquiv observer
        (CompositeFullTrace.run observer left leftOperations).1
        (CompositeFullTrace.run observer right rightOperations).1) ∧
    (∀ plan, BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan →
      ¬ CompositeFullView.FullLowEquiv 2
        (CompositeSwitchedChannels.runFrom plan CompositeSwitchedChannels.leftTrace)
        (CompositeSwitchedChannels.runFrom plan CompositeSwitchedChannels.rightTrace)) := by
  refine ⟨fun state operation hsilent =>
      CompositeObservation.authoritativeGate_silent_observe observer state operation hsilent,
    fun left right leftOperations rightOperations hlow hevents =>
      CompositeObservation.finite_trace_lowEquiv observer left right leftOperations
        rightOperations hlow hevents,
    fun state operation hstate hsilent =>
      CompositeUnwinding.authoritativeGate_silentCoherent_observe observer state operation
        hstate hsilent,
    fun left right leftOperations rightOperations hleft hright hlow hevents =>
      CompositeUnwinding.finite_trace_lowEquiv_coherent observer left right leftOperations
        rightOperations hleft hright hlow hevents,
    fun left right operation h hfamily =>
      CompositeUnwinding.own_step_consistent h operation hfamily,
    fun left right operation h hfamily =>
      CompositeUnwinding.own_output_consistent h operation hfamily,
    fun left right operations h hfamily =>
      CompositeUnwinding.own_run_noninterference h operations hfamily,
    fun plan =>
      ⟨CompositeUnwinding.Channels.identity_counter_step_inconsistent plan,
        (CompositeUnwinding.Channels.copy_destination_output_inconsistent plan).2⟩,
    fun state operation hstate hsilent =>
      CompositeLocalRespect.authoritativeGate_silentExtended_observe observer state operation
        hstate hsilent,
    fun left right leftOperations rightOperations hleft hright hlow hevents =>
      CompositeLocalRespect.finite_trace_lowEquiv_extended observer left right leftOperations
        rightOperations hleft hright hlow hevents,
    fun left right operation h hfamily =>
      CompositeOwnSteps.own_step_consistent_counter h operation hfamily,
    fun left right operation h hfamily =>
      CompositeOwnSteps.own_output_consistent_counter h operation hfamily,
    fun left right operation h hpublic hfamily =>
      CompositeOwnSteps.own_output_consistent_scheduler h hpublic operation hfamily,
    fun left right endpointWord destinationSlot h hcarried =>
      CompositeOwnSteps.own_step_accept_gate h hcarried endpointWord destinationSlot,
    fun left right subject h hleft hright =>
      ⟨CompositeLocalRespect.own_step_drain h hleft hright subject,
        CompositeLocalRespect.own_output_drain_self h hleft hright⟩,
    fun left right operations h hfamily =>
      CompositeOwnSteps.own_run_noninterference_counter h operations hfamily,
    fun plan =>
      ⟨⟨CompositeChannels.seed_created plan,
          (CompositeChannels.create_output_inconsistent plan).2,
          (CompositeChannels.terminate_output_inconsistent plan).2,
          (CompositeChannels.scheduleAdd_output_inconsistent plan).2⟩,
        CompositeChannels.terminate_step_inconsistent plan,
        ⟨CompositeChannels.slotThree_slotTwo plan,
          (CompositeChannels.copy_destination_output_inconsistent_counter plan).2,
          (CompositeChannels.revoke_other_output_inconsistent plan).2,
          (CompositeChannels.revokeSubtree_other_output_inconsistent plan).2⟩,
        CompositeChannels.offer_counter_step_inconsistent plan⟩,
    fun left right h hleft hright =>
      ⟨CompositeOwnTermination.own_step_terminate_self h hleft hright,
        CompositeOwnTermination.own_step_terminateCurrent h hleft hright,
        fun frame => ⟨CompositeOwnTermination.own_step_interrupt h hleft hright frame,
          CompositeOwnTermination.own_output_interrupt h frame⟩,
        fun raw context => CompositeOwnTermination.own_output_nmi h raw context⟩,
    CompositeSwitchedChannels.sample_plan_exists,
    fun plan hplan =>
      ⟨⟨CompositeSwitchedChannels.derivation_pair plan hplan,
          (CompositeSwitchedChannels.revokeSubtree_own_step_inconsistent plan hplan).2,
          (CompositeSwitchedChannels.revokeSubtree_other_step_inconsistent plan hplan).2⟩,
        CompositeRegisterChannels.legacy_replies_leaked plan hplan,
        CompositeRegisterChannels.register_channel_closed_on_pairs plan hplan⟩,
    fun state frame registers next hreply =>
      CompositeRegisterChannels.resume_reply_names_scheduled state frame registers next hreply,
    fun state operation hstate hsilent =>
      CompositeSubjectGate.subjectGate_silent_observe observer state operation hstate hsilent,
    fun left right leftOperations rightOperations hleft hright hlow hevents =>
      CompositeSubjectGate.finite_trace_lowEquiv_subject observer left right leftOperations
        rightOperations hleft hright hlow hevents,
    fun left right operation h hleft hright hfamily =>
      CompositeSubjectGate.own_step_consistent_subject h hleft hright operation hfamily,
    fun left right operation h hleft hright hfamily =>
      CompositeSubjectGate.own_output_consistent_subject h hleft hright operation hfamily,
    fun left right operation h hcross =>
      CompositeSubjectGate.own_cross_stutter h operation hcross,
    fun plan => CompositeSubjectGate.cross_subject_channels_closed plan,
    fun plan hplan => CompositeSubjectGate.revokeSubtree_other_closed plan hplan,
    fun left right operation h =>
      ⟨CompositeFullIsolation.full_step h operation,
        CompositeFullIsolation.full_output h operation⟩,
    fun state operation hstate hsilent =>
      CompositeFullTrace.subjectGate_silent_full observer state operation hstate hsilent,
    fun left right leftOperations rightOperations hleft hright hlow hevents =>
      CompositeFullTrace.finite_trace_full observer left right leftOperations rightOperations
        hleft hright hlow hevents,
    fun plan hplan => CompositeFullChannels.revokeSubtree_own_closed plan hplan⟩

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

/-- SC-DEVICE-PROGRAM-STATIC-CONFINEMENT: a device program accepted by the
static checker, run by the reference simulator on any device model from any
registers and scratch, requests no MMIO, configuration or bus-address effect
outside its policy. -/
theorem device_program_static_confinement {σ : Type} (π : Wifi.Bytecode.Policy)
    (p : Wifi.Bytecode.Program) (hp : DeviceProgramConfinement.admissible p π = true)
    (d : Wifi.Sim.Device σ) (s0 : σ) (fuel : Nat)
    (init : Wifi.Sim.Machine (σ × Bool) → Wifi.Sim.Machine (σ × Bool))
    (hinit : ∀ m, (init m).dev = m.dev) :
    (Wifi.Sim.run p (DeviceProgramConfinement.guard π d) (s0, false) fuel init).2.dev.2 =
      false :=
  DeviceProgramConfinement.run_confined π p hp d s0 fuel init hinit

/-- SC-DEVICE-PROGRAM-DECLARED-CONFINEMENT: any program whose image declares a
policy (target window inside the policy window) is confined to it by the
simulator's dynamic policy checks alone. -/
theorem device_program_declared_confinement {σ : Type} (π : Wifi.Bytecode.Policy)
    (p : Wifi.Bytecode.Program) (hpol : p.policy = some π)
    (hwin : p.effTarget.windowBytes.toNat ≤ π.window.toNat)
    (d : Wifi.Sim.Device σ) (s0 : σ) (fuel : Nat)
    (init : Wifi.Sim.Machine (σ × Bool) → Wifi.Sim.Machine (σ × Bool))
    (hinit : ∀ m, (init m).dev = m.dev) :
    (Wifi.Sim.run p (DeviceProgramConfinement.guard π d) (s0, false) fuel init).2.dev.2 =
      false :=
  DeviceProgramConfinement.run_declared_confined π p hpol hwin d s0 fuel init hinit

/-- SC-DEVICE-PROGRAM-DESCRIPTOR-POINTERS: an admissible device program, run
by the reference simulator from zeroed scratch on any device model whose bus
address of scratch is fixed, leaves every field of its policy's descriptor
map (for xHCI: DCBAA and scratchpad-array entries, the ERST entry,
input-context dequeue pointers and TRB parameters) holding zero or a bus
address inside scratch, in every reachable state. -/
theorem device_program_descriptor_pointers {σ : Type} (π : Wifi.Bytecode.Policy)
    (p : Wifi.Bytecode.Program) (hp : DeviceProgramConfinement.admissible p π = true)
    (d : Wifi.Sim.Device σ) (base : UInt32) (hphys : ∀ s, (d.phys s 0).1 = base)
    (s0 : σ) (fuel : Nat) :
    Wifi.Sim.descOk π base (Wifi.Sim.run p d s0 fuel).2.mem = true :=
  DeviceProgramConfinement.run_admissible_descriptors π p hp d base hphys s0 fuel

/-- SC-DEVICE-CAPABILITY-CONFINEMENT: in the device-capability kernel
service, no sequence of capability operations, grants, binds, invocations and
revocations makes any device act outside its policy, and only an invocation by
a current holder of a device's capability changes that device. -/
theorem device_capability_confinement {σ : Type}
    (models : Nat → Wifi.Sim.Device σ) (ts : List DeviceCapability.Transition)
    (sys : DeviceCapability.System σ) (hinv : DeviceCapability.Inv sys) :
    DeviceCapability.Inv (DeviceCapability.run models sys ts) ∧
      ∀ t k, (DeviceCapability.step models sys t).1.devState k ≠ sys.devState k →
        ∃ subject fuel, t = .invoke subject fuel ∧ sys.deviceCaps subject = some ⟨k⟩ :=
  ⟨DeviceCapability.run_inv models ts sys hinv,
    fun t k h => DeviceCapability.device_state_changes_only_by_holder models sys t k h⟩

/-- SC-IPC-EVENT-STREAM: from any state where a receiver waits for and a
sender holds authority over one endpoint (`CycleReady`), the blocking IPC
delivers every sequence of payloads exactly and in order, one exchange per
payload, and returns to the starting state. -/
theorem ipc_event_stream {s : BlockingIPC.State} {rc sc : Capability.Capability}
    (h : BlockingIPC.CycleReady s rc sc) (payloads : List BlockingIPC.Payload) :
    BlockingIPC.keyStream s payloads =
      (s, payloads.map fun p => .delivered (BlockingIPC.bootEnvelope p)) :=
  BlockingIPC.keyStream_delivers h payloads

/-- SC-NOTIFY-REPLY-NO-AMPLIFICATION: notifications, calls, replies, reply
copies and terminations never change the capability state, and a reply
capability appears only through `call`, naming exactly that caller at its
current generation. -/
theorem notify_reply_no_amplification (sys : NotifyReply.System)
    (t : NotifyReply.Transition) (hcap : ∀ op, t ≠ .cap op) :
    (NotifyReply.step sys t).1.caps = sys.caps ∧
      ∀ server r rc, (NotifyReply.step sys t).1.replies server r = some rc →
        sys.replies server r ≠ some rc →
        ∃ slot, t = .call rc.caller slot ∧ rc.callerGeneration = sys.generation rc.caller :=
  ⟨NotifyReply.non_cap_step_caps sys t hcap,
    fun server r rc hnew hold => NotifyReply.reply_created_only_by_call sys t server r rc hnew hold⟩

/-- SC-NOTIFY-REPLY-NO-STALE-REUSE: a reply whose caller terminated or moved
to a new generation is rejected and changes nothing. -/
theorem notify_reply_no_stale_reuse (sys : NotifyReply.System) (server : Capability.SubjectId)
    (r : Nat) (rc : NotifyReply.ReplyCap) (word : UInt64)
    (hreply : sys.replies server r = some rc)
    (hstale : sys.alive rc.caller = false ∨ sys.generation rc.caller ≠ rc.callerGeneration) :
    NotifyReply.step sys (.reply server r word) = (sys, .rejected .staleCaller) :=
  NotifyReply.stale_reply_rejected sys server r rc word hreply hstale

/-- SC-NOTIFY-REPLY-SINGLE-USE: an accepted reply consumes the reply
capability; a second reply through it is rejected and changes nothing, and a
reply capability is never handed to another subject. -/
theorem notify_reply_single_use (sys : NotifyReply.System) (server : Capability.SubjectId)
    (r : Nat) (word word' : UInt64)
    (h : (NotifyReply.step sys (.reply server r word)).2 = .accepted) :
    NotifyReply.step (NotifyReply.step sys (.reply server r word)).1 (.reply server r word') =
        ((NotifyReply.step sys (.reply server r word)).1, .rejected .noReply) ∧
      ∀ destination, NotifyReply.step sys (.copyReply server r destination) =
        (sys, .rejected .notCopyable) :=
  ⟨NotifyReply.reply_single_use sys server r word word' h,
    fun destination => NotifyReply.copyReply_rejected sys server r destination⟩

/-- SC-NOTIFY-REPLY-BUDGET: a transition changes another subject's reply
slots only when it is a call on that subject's endpoint or that subject's own
reply, and a call to an exhausted reply pool is a typed rejection without
effect. -/
theorem notify_reply_budget (sys : NotifyReply.System) (t : NotifyReply.Transition)
    (other : Capability.SubjectId)
    (hchanged : (NotifyReply.step sys t).1.replies other ≠ sys.replies other) :
    (∃ client slot capability, t = .call client slot ∧
        Capability.authorizeKind sys.caps client slot .endpoint = .ok capability ∧
        sys.endpointServer capability.object = some other) ∨
      (∃ r word, t = .reply other r word) :=
  NotifyReply.replies_change_only_at_server sys t other hchanged

/-- SC-BOOT-TRANSITION-AGREEMENT: the Lean adapter `bootTransition` computes the
model's encoded result on every encoded model state. A Lean-level statement
only; it says nothing about generated C. -/
theorem boot_transition_agreement (state : KernelTransition.State) (command : UInt64) :
    KernelTransition.bootTransition (KernelTransition.encodeState state) command =
      KernelTransition.encodeResult
        (KernelTransition.transition state (KernelTransition.decodeCommand command)).result :=
  KernelTransition.bootTransition_agrees state command

/-- SC-BOOT-TRANSITION-REFINEMENT: the C function `leanos_boot_transition`, as
emitted by the pinned toolchain (the AST the build's drift check pins) and
interpreted by the `Refinement.CSubset` semantics, refines `transition` under
the encodings. ADR 0023 records the trusted subset meaning, extractor and
calling convention. -/
theorem boot_transition_refinement (state : KernelTransition.State) (command : UInt64) :
    Refinement.CSubset.call Refinement.BootTransitionC.bootTransitionC
        [KernelTransition.encodeState state, command] =
      some (KernelTransition.encodeResult
        (KernelTransition.transition state (KernelTransition.decodeCommand command)).result) :=
  Refinement.BootTransitionC.bootTransitionC_refines_transition state command

/-- SC-SPAWN-SYSCALL-REFINEMENT: the C function `leanos_spawn_syscall`, as
emitted by the pinned toolchain (with its five emitted helpers) and
interpreted by the `Refinement.CSubset` semantics, computes the Lean witness
`spawnSyscall` on every six words, given a dispatcher that answers with
`CompositeDispatcher.dispatch`; its answer is a refusal or the reply of exactly
one edge of the spawn table at the presented token. ADR 0029 records what
stays trusted. -/
theorem spawn_syscall_refinement (ext : Refinement.CSubset.Ext)
    (spec : Refinement.SpawnSyscallC.DispatchSpec ext) (state actor number rbx rcx rdx : UInt64) :
    Refinement.CSubset.callWith (Refinement.SpawnSyscallC.helpers ext)
        Refinement.SpawnSyscallC.spawnSyscallC [state, actor, number, rbx, rcx, rdx] =
      some (SpawnSyscall.spawnSyscall state actor number rbx rcx rdx) ∧
    (SpawnSyscall.spawnSyscall state actor number rbx rcx rdx ∈ SpawnSyscall.refusals ∨
      ∃ edge ∈ SpawnBoundary.edges, SpawnBoundary.encodeState edge.state = state ∧
        edge.words = SpawnSyscall.syscallWords number rbx rcx rdx ∧
        actor = SpawnSyscall.stateActor state ∧
        SpawnSyscall.spawnSyscall state actor number rbx rcx rdx =
          SpawnBoundary.replyWord edge.next edge.status) := by
  refine ⟨Refinement.SpawnSyscallC.spawnSyscallC_refines ext spec state actor number rbx rcx rdx,
    ?_⟩
  rcases SpawnSyscall.spawnSyscall_cases state actor number rbx rcx rdx with
    refused | ⟨edge, member, token, words, sameActor, _, _, reply⟩
  · exact Or.inl refused
  · exact Or.inr ⟨edge, member, token, words, sameActor, reply⟩

/-- SC-SPAWN-SYSCALL-VALUE-REFINEMENT: the C function
`leanos_spawn_syscall_value`, as emitted by the pinned toolchain and
interpreted by the `Refinement.CSubset` semantics, calling the emitted
`leanos_spawn_syscall`, computes the Lean witness `spawnSyscallValue` on
every six words, given a dispatcher that answers with
`CompositeDispatcher.dispatch` and `dispatchValue`. -/
theorem spawn_syscall_value_refinement (ext : Refinement.CSubset.Ext)
    (spec : Refinement.SpawnSyscallC.DispatchSpec ext) (state actor number rbx rcx rdx : UInt64) :
    Refinement.CSubset.callWith (Refinement.SpawnSyscallC.link ext)
        Refinement.SpawnSyscallC.spawnSyscallValueC [state, actor, number, rbx, rcx, rdx] =
      some (SpawnSyscall.spawnSyscallValue state actor number rbx rcx rdx) :=
  Refinement.SpawnSyscallC.spawnSyscallValueC_refines ext spec state actor number rbx rcx rdx

/-- SC-LOADER-SOURCE-REFINEMENT: the C function `leanos_loader_source`, as
emitted by the pinned toolchain and interpreted by the `Refinement.CSubset`
semantics, computes the Lean witness on every five words, and on words below
`2^62` the model's range and placement test. -/
theorem loader_source_refinement :
    (∀ source start stop fileOffset span : UInt64,
      Refinement.CSubset.call Refinement.ChildLoaderC.loaderSourceC
          [source, start, stop, fileOffset, span] =
        some (ChildLoader.loaderSource source start stop fileOffset span)) ∧
    (∀ source start stop fileOffset span : Nat, source < 2 ^ 62 → start < 2 ^ 62 →
      stop < 2 ^ 62 → fileOffset < 2 ^ 62 → span < 2 ^ 62 →
      Refinement.CSubset.call Refinement.ChildLoaderC.loaderSourceC
          [UInt64.ofNat source, UInt64.ofNat start, UInt64.ofNat stop, UInt64.ofNat fileOffset,
            UInt64.ofNat span] =
        some (if !(decide (start ≤ source) && decide (source + span ≤ stop)) then 5
          else if source ≠ start + fileOffset then 6 else 0)) := by
  refine ⟨Refinement.ChildLoaderC.loaderSourceC_refines, ?_⟩
  intro source start stop fileOffset span h1 h2 h3 h4 h5
  rw [Refinement.ChildLoaderC.loaderSourceC_refines,
    ChildLoader.loaderSource_agrees source start stop fileOffset span h1 h2 h3 h4 h5]

/-- SC-LOADER-DECIDE-REFINEMENT: the C functions `leanos_loader_decide` and
`leanos_loader_source`, as emitted by the pinned toolchain and interpreted by
the `Refinement.CSubset` semantics, answer a start on every state, and a load
on every state whose words are small, with exactly the encoded reply of
`ChildLoader.step`. -/
theorem loader_decide_refinement (state : ChildLoader.State) (control : UInt64) :
    (∀ sourceCode pages frames used : UInt64,
      Refinement.CSubset.call Refinement.ChildLoaderC.loaderDecideC
          [2, ChildLoader.flagsWord state (.start control), sourceCode, pages, frames, used] =
        some (ChildLoader.encodeReply false (ChildLoader.step state (.start control)).2)) ∧
    (∀ index source : Nat, ChildLoader.Small state → source < 2 ^ 62 →
      ((match state.plan[index]? with
          | some s => Refinement.CSubset.call Refinement.ChildLoaderC.loaderSourceC
              [UInt64.ofNat source, UInt64.ofNat state.start, UInt64.ofNat state.stop,
                UInt64.ofNat s.fileOffset,
                UInt64.ofNat (ChildLoader.pageCount s * ElfAdmission.pageBytes)]
          | none => some 0).bind fun sourceCode =>
        Refinement.CSubset.call Refinement.ChildLoaderC.loaderDecideC
          [1, ChildLoader.flagsWord state (.load control index source), sourceCode,
            UInt64.ofNat ((state.plan[index]?.map ChildLoader.pageCount).getD 0),
            UInt64.ofNat ((state.child.map (fun c : ChildLoader.Child => c.frames)).getD 0),
            UInt64.ofNat state.used]) =
        some (ChildLoader.encodeReply
          (ChildLoader.requestWritable state (.load control index source))
          (ChildLoader.step state (.load control index source)).2)) :=
  ⟨Refinement.ChildLoaderC.loaderC_refines_start state control,
    fun index source small sourceSmall =>
      Refinement.ChildLoaderC.loaderC_refines_load state control index source small sourceSmall⟩

/-- SC-FRAME-COPY-REFINEMENT: the C function `leanos_frame_copy_check`, as
emitted by the pinned toolchain (with its emitted helper) and interpreted by
the `Refinement.CSubset` semantics, computes the Lean witness on every six
words, so it accepts the network subject's fetch or send exactly when the
model's `fetchOk` or `sendOk` does and refuses every other subject. -/
theorem frame_copy_check_refinement (ext : Refinement.CSubset.Ext) :
    (∀ subject request addr len base limit : UInt64,
      Refinement.CSubset.callWith (Refinement.NetworkSubjectC.link ext)
          Refinement.NetworkSubjectC.frameCopyCheckC [subject, request, addr, len, base, limit] =
        some (NetworkSubject.frameCopyCheck subject request addr len base limit)) ∧
    (∀ (w : NetworkSubject.Window) (s : NetworkSubject.State) (addr base limit : UInt64),
      w = ⟨base.toNat, limit.toNat⟩ → s.rx.length < 2 ^ 64 →
      (Refinement.CSubset.callWith (Refinement.NetworkSubjectC.link ext)
          Refinement.NetworkSubjectC.frameCopyCheckC
          [3, NetworkSubject.fetchRequest s.rxPending, addr, s.rx.length.toUInt64, base, limit] =
          some 0 ↔ NetworkSubject.fetchOk w s NetworkSubject.network addr.toNat = true)) ∧
    (∀ (w : NetworkSubject.Window) (s : NetworkSubject.State) (addr len base limit : UInt64),
      w = ⟨base.toNat, limit.toNat⟩ →
      (Refinement.CSubset.callWith (Refinement.NetworkSubjectC.link ext)
          Refinement.NetworkSubjectC.frameCopyCheckC
          [3, NetworkSubject.sendRequest s.txPending, addr, len, base, limit] = some 0 ↔
        NetworkSubject.sendOk w s NetworkSubject.network addr.toNat len.toNat = true)) ∧
    (∀ subject request addr len base limit : UInt64, subject ≠ 3 →
      Refinement.CSubset.callWith (Refinement.NetworkSubjectC.link ext)
          Refinement.NetworkSubjectC.frameCopyCheckC [subject, request, addr, len, base, limit] =
        some 1) :=
  ⟨Refinement.NetworkSubjectC.frameCopyCheckC_refines ext,
    fun w s addr base limit hw hlen =>
      Refinement.NetworkSubjectC.frameCopyCheckC_fetch ext w s addr base limit hw hlen,
    fun w s addr len base limit hw =>
      Refinement.NetworkSubjectC.frameCopyCheckC_send ext w s addr len base limit hw,
    fun subject request addr len base limit h =>
      Refinement.NetworkSubjectC.frameCopyCheckC_nonholder ext subject request addr len base limit h⟩

/-- SC-FRAME-PORT-REFINEMENT: the C function `leanos_frame_port_check`, as
emitted by the pinned toolchain and interpreted by the `Refinement.CSubset`
semantics, computes the Lean witness on every six words, so it admits a copy
only from a port holder for a window labelled its own and served by the
endpoint, and refuses every subject holding no port. -/
theorem frame_port_check_refinement :
    (∀ subject req addr len base limit : UInt64,
      Refinement.CSubset.call Refinement.DhcpSubjectC.framePortCheckC
          [subject, req, addr, len, base, limit] =
        some (DhcpSubject.framePortCheck subject req addr len base limit)) ∧
    (∀ subject req addr len base limit : UInt64,
      Refinement.CSubset.call Refinement.DhcpSubjectC.framePortCheckC
          [subject, req, addr, len, base, limit] = some 0 →
      (subject = 2 ∨ subject = 3) ∧ (req >>> 24) &&& 0xff = subject ∧
        (req >>> 16) &&& 0xff = subject ∧
        NetworkSubject.Window.covers ⟨base.toNat, limit.toNat⟩ addr.toNat len.toNat = true) ∧
    (∀ subject req addr len base limit : UInt64, subject ≠ 2 → subject ≠ 3 →
      Refinement.CSubset.call Refinement.DhcpSubjectC.framePortCheckC
          [subject, req, addr, len, base, limit] = some 1) :=
  ⟨Refinement.DhcpSubjectC.framePortCheckC_refines,
    Refinement.DhcpSubjectC.framePortCheckC_own_window,
    Refinement.DhcpSubjectC.framePortCheckC_nonholder⟩
/-- SC-CONSOLE-INTEGRITY: a subject holding neither the console capability nor
an endpoint capability that reaches the console server cannot change the
console trace: two scripts that differ only in its actions produce equal
console output. -/
theorem console_integrity (auth : ConsoleServer.Authority) (x : ConsoleServer.Subject)
    (hx : ConsoleServer.Unprivileged auth x) (s : ConsoleServer.State)
    (first second : List (ConsoleServer.Subject × ConsoleServer.Op))
    (hsame : ConsoleServer.erase x first = ConsoleServer.erase x second) :
    (ConsoleServer.run auth s first).1.output = (ConsoleServer.run auth s second).1.output :=
  ConsoleServer.console_integrity_pair auth x hx s first second hsame

/-- SC-CONSOLE-CONFIDENTIALITY: such a subject observes one refusal per action
of its own, so its observations do not depend on console input. -/
theorem console_confidentiality (auth : ConsoleServer.Authority) (x : ConsoleServer.Subject)
    (hx : ConsoleServer.Unprivileged auth x) (s : ConsoleServer.State)
    (hs : ConsoleServer.NoQueuedFrom x s) (input : List Nat)
    (script : List (ConsoleServer.Subject × ConsoleServer.Op)) :
    ConsoleServer.observations x (ConsoleServer.run auth s script).2 =
      ConsoleServer.observations x (ConsoleServer.run auth { s with input := input } script).2 :=
  ConsoleServer.console_confidentiality auth x hx s hs input script

/-- SC-DIRECTORY-NO-AMPLIFICATION: when an endpoint directory resolves a name
with a policy that offers at most send, every authority any subject has
afterwards either existed before, or is the client's send right over an
endpoint on which the directory itself held send and grant; and a resolved
name delivers, in the client's slot, a capability for the same endpoint the
directory holds under that name, with rights a subset of both the directory's
rights and send-only. -/
theorem endpoint_directory_no_amplification (offered : Capability.Rights)
    (hoffered : EndpointDirectory.AttenuatesToSend offered) (st : Capability.State)
    (d : EndpointDirectory.Directory) (client : Capability.SubjectId)
    (clientSlot : Capability.SlotId) (name : EndpointDirectory.Name) :
    (∀ candidate object right,
      Capability.HasAuthority
          (EndpointDirectory.resolveWith offered st d client clientSlot name).1
          candidate object right →
        Capability.HasAuthority st candidate object right ∨
          (candidate = client ∧ right = .send ∧
            Capability.HasAuthority st d.subject object .send ∧
            Capability.HasAuthority st d.subject object .grant)) ∧
    (∀ slot,
      (EndpointDirectory.resolveWith offered st d client clientSlot name).2 = .resolved slot →
        ∃ heldSlot held delivered,
          EndpointDirectory.slotOf d name = some heldSlot ∧
          st.slots d.subject heldSlot = some held ∧
          (EndpointDirectory.resolveWith offered st d client clientSlot name).1.slots
            client clientSlot = some delivered ∧
          delivered.object = held.object ∧ held.kind = .endpoint ∧
          Capability.rightsSubset delivered.rights held.rights = true ∧
          Capability.rightsSubset delivered.rights EndpointDirectory.sendOnly = true) :=
  ⟨fun candidate object right hauthority =>
    EndpointDirectory.resolve_no_amplification offered hoffered st d client clientSlot name
      candidate object right hauthority,
   fun slot hresolved => by
    obtain ⟨_, heldSlot, held, delivered, hslot, hheld, hdelivered, hobject, _, hkind, _,
        hsend, hsubset, _⟩ :=
      EndpointDirectory.resolve_resolved_held offered hoffered st d client clientSlot name slot
        hresolved
    exact ⟨heldSlot, held, delivered, hslot, hheld, hdelivered, hobject, hkind, hsubset,
      hsend⟩⟩

/-- SC-DIRECTORY-MISS: an unregistered name is the typed miss `unregistered`
with the capability state unchanged, and every miss transfers nothing. -/
theorem endpoint_directory_miss_transfers_nothing (offered : Capability.Rights)
    (st : Capability.State) (d : EndpointDirectory.Directory)
    (client : Capability.SubjectId) (clientSlot : Capability.SlotId)
    (name : EndpointDirectory.Name) :
    (EndpointDirectory.slotOf d name = none →
      EndpointDirectory.resolveWith offered st d client clientSlot name =
        (st, .miss .unregistered)) ∧
    (∀ m, (EndpointDirectory.resolveWith offered st d client clientSlot name).2 = .miss m →
      (EndpointDirectory.resolveWith offered st d client clientSlot name).1 = st) :=
  ⟨EndpointDirectory.resolve_unregistered offered st d client clientSlot name,
   fun m h => EndpointDirectory.resolve_miss_unchanged offered st d client clientSlot name m h⟩

/-- SC-FAULT-HANDLER-DEFAULT: with no fault handler bound, a fault is handled
exactly as before: the system's core state and action are those of
`FaultDispatch.dispatch` (containment, idle, rejection, or fail-stop halt), and
the same holds for every fault of another class or from another subject when
a handler is bound. -/
theorem fault_handler_default (sys : FaultHandler.System) (entry : InterruptEntry.Result)
    (hunbound : sys.binding = none ∨ FaultHandler.boundFor sys.binding entry = none) :
    (FaultHandler.fault sys entry).1.core = (FaultDispatch.dispatch sys.core entry).state ∧
      (FaultHandler.fault sys entry).2 =
        .default (FaultDispatch.dispatch sys.core entry).action := by
  rcases hunbound with hnone | hclass
  · rw [FaultHandler.unbound_is_default sys entry hnone]
    exact ⟨rfl, rfl⟩
  · rw [FaultHandler.unbound_class_is_default sys entry hclass]
    exact ⟨rfl, rfl⟩

/-- SC-FAULT-HANDLER-DELIVERY: a bound fault is delivered only to the bound
handler and only as the typed record built from the normalized frame (class,
vector, faulting subject, saved RIP, error word); the faulting subject, which
was the live, runnable current subject, is suspended (not runnable, not
current, not queued); every other subject's inbox is unchanged; and the
capability state is unchanged (no amplification).  The handler's terminate
retires exactly that subject with the default cleanup, so it never resumes,
and cleanup gives no holder a capability slot it lacked.  Only the bound
handler ever holds a fault record. -/
theorem fault_handler_delivery (sys : FaultHandler.System) (entry : InterruptEntry.Result)
    (handler : Capability.SubjectId) (record : FaultHandler.FaultRecord)
    (h : (FaultHandler.fault sys entry).2 = .delivered handler record) :
    (∃ b frame reason,
      sys.binding = some b ∧ handler = b.handler ∧ entry = .accepted frame ∧
      InterruptEntry.containedReason? frame.vector = some reason ∧ reason = b.reason ∧
      record = FaultHandler.recordOf reason frame ∧ record.faulting = b.faulting ∧
      b.handler ≠ b.faulting ∧
      sys.core.scheduler.lifecycle.current = some b.faulting ∧
      sys.core.scheduler.lifecycle.runnable b.faulting = true ∧
      (FaultHandler.fault sys entry).1.inbox b.handler = some record ∧
      (∀ s, s ≠ b.handler → (FaultHandler.fault sys entry).1.inbox s = sys.inbox s) ∧
      (FaultHandler.fault sys entry).1.core.scheduler.lifecycle.runnable b.faulting = false ∧
      (FaultHandler.fault sys entry).1.core.scheduler.lifecycle.current = none ∧
      b.faulting ∉ (FaultHandler.fault sys entry).1.core.scheduler.ready ∧
      (FaultHandler.fault sys entry).1.core.scheduler.lifecycle.capabilities =
        sys.core.scheduler.lifecycle.capabilities) ∧
    (∀ next : FaultHandler.System, next.binding = sys.binding →
      ∀ subject faulting,
        (FaultHandler.reply next subject .terminate).2 = .terminated faulting →
        (FaultHandler.reply next subject .terminate).1.core.scheduler.lifecycle.capabilities.subjects
            faulting = false ∧
          faulting ∉ (FaultHandler.reply next subject .terminate).1.core.scheduler.ready ∧
          ResumablePreemption.contextFor
            (FaultHandler.reply next subject .terminate).1.core.contexts faulting = none ∧
          (∀ holder slot capability,
            (FaultHandler.reply next subject .terminate).1.core.scheduler.lifecycle.capabilities.slots
                holder slot = some capability →
              next.core.scheduler.lifecycle.capabilities.slots holder slot = some capability)) ∧
    (∀ (start : FaultHandler.System) (op : FaultHandler.Op), FaultHandler.InboxBound start →
      FaultHandler.InboxBound (FaultHandler.step start op).1) := by
  refine ⟨?_, ?_, fun start op hinv => FaultHandler.step_preserves_inboxBound start op hinv⟩
  · obtain ⟨b, frame, reason, hb, hh, he, hr, hre, hrec, hf, hd, hc, _, hrun, hs, hin, hother,
        hnr, hcur, hready, hcaps, _, _⟩ :=
      FaultHandler.delivered_exact sys entry handler record h
    exact ⟨b, frame, reason, hb, hh, he, hr, hre, hrec, hf, hd, hc, hrun, hin, hother, hnr,
      hcur, hready, hcaps⟩
  · intro next _ subject faulting hterm
    obtain ⟨b, _, _, _, _, _, _, hdead, hready, _, hcontext⟩ :=
      FaultHandler.reply_terminates next subject .terminate faulting hterm
    exact ⟨hdead, hready, hcontext,
      fun holder slot capability hslot =>
        FaultHandler.reply_no_amplification next subject .terminate holder slot capability hslot⟩

/-- SC-FRAME-SERVER-BUDGET: with allocation policy in a ring-3 frame server,
no client ever holds more pool frames than its budget capability allows,
whatever the server decides and whatever any client writes; and no step gives
anyone more authority: the server, its pool and its pool rights never change,
no budget ever grows, and every grant is of a pool frame with rights inside the
pool rights. -/
theorem frame_server_budget (sys : FrameServer.System) (op : FrameServer.Op)
    (hinv : FrameServer.Invariant sys) :
    FrameServer.Invariant (FrameServer.step sys op) ∧
      (∀ client, FrameServer.usage (FrameServer.step sys op) client ≤
        (FrameServer.step sys op).limit client) ∧
      (FrameServer.step sys op).server = sys.server ∧
      (FrameServer.step sys op).pool = sys.pool ∧
      (FrameServer.step sys op).poolRights = sys.poolRights ∧
      (∀ client, (FrameServer.step sys op).limit client ≤ sys.limit client) ∧
      FrameServer.Confined (FrameServer.step sys op) := by
  obtain ⟨hserver, hpool, hrights, hlimit, hconf⟩ := FrameServer.no_amplification sys op hinv
  exact ⟨FrameServer.step_preserves_invariant sys op hinv,
    FrameServer.budget_respected sys op hinv, hserver, hpool, hrights, hlimit, hconf⟩

/-- SC-FRAME-SERVER-SCRUB: a frame the server grants is completely scrubbed
before the client can see it, whatever it held (in particular a frame released
or revoked from another client, whose bytes release leaves in place); revoking
a client's budget capability retires every frame it held; and in every
invariant state a client reading a held frame it has not written reads zero. -/
theorem frame_server_scrub (sys : FrameServer.System) (caller client : Capability.SubjectId)
    (frame : FrameAllocator.FrameId) (rights : UInt64) :
    ((FrameServer.decide sys caller (.grant client frame rights)).2 = .granted client frame →
      (∀ offset, offset < FrameScrub.frameBytes →
        (FrameServer.decide sys caller (.grant client frame rights)).1.bytes frame offset =
          FrameScrub.initialByte) ∧
      (rights &&& FrameServer.readBit ≠ 0 → ∀ offset, offset < FrameScrub.frameBytes →
        FrameServer.read (FrameServer.decide sys caller (.grant client frame rights)).1
          client frame offset = some FrameScrub.initialByte)) ∧
    (FrameServer.decide sys caller (.reclaim client frame)).1.bytes = sys.bytes ∧
    (FrameServer.decide sys caller (.revoke client)).1.bytes = sys.bytes ∧
    ((FrameServer.decide sys caller (.revoke client)).2 = .revoked client →
      (FrameServer.decide sys caller (.revoke client)).1.limit client = 0 ∧
      ∀ held, FrameServer.holds (FrameServer.decide sys caller (.revoke client)).1 client held =
        false) ∧
    (FrameServer.Invariant sys → ∀ reader held offset g value,
      sys.grant held = some g → sys.written held = false → offset < FrameScrub.frameBytes →
      FrameServer.read sys reader held offset = some value → value = FrameScrub.initialByte) := by
  refine ⟨fun h => ⟨?_, fun hread offset hoffset =>
      FrameServer.grant_publishes_scrubbed sys caller client frame rights h hread offset hoffset⟩,
    (FrameServer.release_preserves_bytes sys caller client frame).1,
    (FrameServer.release_preserves_bytes sys caller client frame).2,
    FrameServer.revoke_retires sys caller client,
    fun hinv reader held offset g value hg hw hoffset hread =>
      FrameServer.read_unwritten_zero sys hinv reader held offset g hg hw hoffset value hread⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hbytes⟩ :=
    FrameServer.granted_exact sys caller client frame rights client frame h
  exact hbytes

/-- SC-FRAME-SERVER-CHECK: the kernel's role is reduced to checking the
server's decisions.  Every decision is either refused without effect or
applied exactly as the server named it (the kernel chooses no client, frame,
rights or reason); a decision from any subject but the server is refused; an
accepted grant names a free pool frame, rights inside the pool rights and a
client below its limit; a typed refusal is true; the honest server policy is
never overridden; and the boot witness `frameServerCheck` answers exactly the
model's encoded reply. -/
theorem frame_server_kernel_checks (sys : FrameServer.System) (caller : Capability.SubjectId)
    (d : FrameServer.Decision) :
    ((∃ reason, FrameServer.check sys caller d = some reason ∧
        FrameServer.decide sys caller d = (sys, .rejected reason)) ∨
      (FrameServer.check sys caller d = none ∧
        FrameServer.decide sys caller d = (FrameServer.effect sys d, FrameServer.replyOf d))) ∧
    (caller ≠ sys.server → FrameServer.decide sys caller d = (sys, .rejected .notServer)) ∧
    (∀ client frame rights, d = .grant client frame rights →
      (FrameServer.decide sys caller d).2 = .granted client frame →
      caller = sys.server ∧ frame ∈ sys.pool ∧ sys.grant frame = none ∧
        FrameServer.rightsSubset rights sys.poolRights = true ∧
        FrameServer.usage sys client < sys.limit client) ∧
    (∀ client reason, d = .refuse client reason →
      (FrameServer.decide sys caller d).2 = .refused client reason →
      (reason = .budgetExhausted → sys.limit client ≤ FrameServer.usage sys client) ∧
      (reason = .poolExhausted → FrameServer.hasFree sys = false)) ∧
    (sys.poolRights ≠ 0 → ∀ client,
      FrameServer.check sys sys.server (FrameServer.serverPolicy sys client) = none) ∧
    (FrameServer.usage sys d.client < 2 ^ 64 → sys.limit d.client < 2 ^ 64 →
      FrameServer.frameServerCheck (FrameServer.opWord d) (FrameServer.decisionView sys d)
          (UInt64.ofNat (FrameServer.usage sys d.client)) (UInt64.ofNat (sys.limit d.client))
          (FrameServer.requestedWord d) sys.poolRights =
        FrameServer.encodeReply (FrameServer.decide sys sys.server d).2) := by
  refine ⟨FrameServer.kernel_only_checks sys caller d,
    FrameServer.decide_not_server sys caller d, ?_, ?_,
    fun hrights client => FrameServer.serverPolicy_accepted sys client hrights,
    FrameServer.frameServerCheck_agrees sys d⟩
  · intro client frame rights hd h
    subst hd
    obtain ⟨_, _, hs, hp, hfree, hr, hu, _⟩ :=
      FrameServer.granted_exact sys caller client frame rights client frame h
    exact ⟨hs, hp, hfree, hr, hu⟩
  · intro client reason hd h
    subst hd
    obtain ⟨_, _, _, hb, hp⟩ := FrameServer.refused_truthful sys caller client reason client reason h
    exact ⟨hb, hp⟩

/-- SC-DEVICE-CONSOLE-SEPARATION: in the composed console and device system
under the keyboard-echo authority, a change to the console trace is an action
of the console server, and a change to a device's state is an invocation by
the keyboard client `a`; the device holder and the console holder are
different subjects. -/
theorem device_console_separation {σ : Type} (models : Nat → Wifi.Sim.Device σ)
    (c : KeyboardEcho.Composed σ)
    (hcaps : c.device.deviceCaps = KeyboardEcho.bootDeviceCaps) (action : KeyboardEcho.Action) :
    ((KeyboardEcho.cstep models ConsoleServer.bootAuthority c action).console.output ≠
        c.console.output → ∃ op, action = .console .server op) ∧
      (∀ k, (KeyboardEcho.cstep models ConsoleServer.bootAuthority c action).device.devState k ≠
        c.device.devState k →
          ∃ fuel, action = .device (.invoke (KeyboardEcho.subjectId .a) fuel)) :=
  KeyboardEcho.boot_causes_distinct models c hcaps action

/-- SC-NETWORK-SUBJECT-CONFINEMENT: frames cross between the WiFi driver
subject and the ring-3 network subject only through the frame endpoint. A
fetch or send by any subject other than the network subject is refused
without effect; across any run, memory a subject did not store to itself
changes only inside the network subject's own window (the kernel copies no
frame byte anywhere else, the driver subject included); the transmit slot
changes only by an accepted send from the network subject, carrying exactly
bytes of its window, or by the driver program taking it; the generated
witness refuses every other subject; and the network subject, never granted
a device capability, cannot cause any device effect. -/
theorem network_subject_confinement {σ : Type} (models : Nat → Wifi.Sim.Device σ) :
    (∀ (w : NetworkSubject.Window) (s : NetworkSubject.State) (who : Nat),
      who ≠ NetworkSubject.network →
        (∀ addr, NetworkSubject.step w s (.fetch who addr) = (s, .refused)) ∧
        (∀ addr len, NetworkSubject.step w s (.send who addr len) = (s, .refused))) ∧
    (∀ (w : NetworkSubject.Window) (s : NetworkSubject.State) (ops : List NetworkSubject.Op)
        (x a : Nat),
      (∀ op ∈ ops, ∀ addr bytes, op ≠ .write x addr bytes) →
      ¬(x = NetworkSubject.network ∧ w.contains a) →
      (NetworkSubject.run w s ops).mem x a = s.mem x a) ∧
    (∀ (w : NetworkSubject.Window) (s : NetworkSubject.State) (op : NetworkSubject.Op),
      (NetworkSubject.step w s op).1.tx ≠ s.tx →
        op = .transmit ∨
        ∃ addr len, op = .send NetworkSubject.network addr len ∧ w.covers addr len = true ∧
          (NetworkSubject.step w s op).1.tx =
            NetworkSubject.readBytes (s.mem NetworkSubject.network) addr len) ∧
    (∀ subject request addr len base limit : UInt64, subject ≠ 3 →
      NetworkSubject.frameCopyCheck subject request addr len base limit = 1) ∧
    (∀ (sys : DeviceCapability.System σ), sys.deviceCaps = KeyboardEcho.bootDeviceCaps →
      ∀ ts : List DeviceCapability.Transition,
        (∀ d, DeviceCapability.Transition.grant NetworkSubject.network d ∉ ts) →
        (∀ program, DeviceCapability.step models (DeviceCapability.run models sys ts)
            (.bind NetworkSubject.network program) =
              (DeviceCapability.run models sys ts, .denied)) ∧
        (∀ fuel, DeviceCapability.step models (DeviceCapability.run models sys ts)
            (.invoke NetworkSubject.network fuel) =
              (DeviceCapability.run models sys ts, .denied))) :=
  ⟨NetworkSubject.nonholder_refused, NetworkSubject.run_mem_outside_window,
   NetworkSubject.step_tx_changed, NetworkSubject.frameCopyCheck_nonholder,
   fun sys hcaps ts hg => NetworkSubject.network_no_device_effects models sys hcaps ts hg⟩

/-- SC-DHCP-SUBJECT-SEPARATION: the DHCP client is a ring-3 subject of its
own, separate from the echo subject and from the driver. A fetch or send by
a subject holding no frame port, the driver included, is refused without
effect, and so is one by the port holder the endpoint does not serve; across
any run, memory a subject did not store to itself changes only inside that
subject's own window; the echo subject's lease changes only by the DHCP
subject's hand-off, the endpoint serves the echo subject only once it holds
that lease, and the responder answers only frames that ask for the leased
address; the generated port witness admits only a port holder, only for a
window labelled its own, and refuses every other subject; and neither the
DHCP subject nor the echo subject, never granted a device capability, can
cause any device effect. -/
theorem dhcp_subject_separation {σ : Type} (models : Nat → Wifi.Sim.Device σ) :
    (∀ (p : DhcpSubject.Ports) (s : DhcpSubject.State) (who : Nat),
      who ≠ DhcpSubject.dhcp → who ≠ DhcpSubject.echo →
        (∀ addr, DhcpSubject.step p s (.fetch who addr) = (s, .refused)) ∧
        (∀ addr len, DhcpSubject.step p s (.send who addr len) = (s, .refused))) ∧
    (∀ (p : DhcpSubject.Ports) (s : DhcpSubject.State) (who : Nat), who ≠ s.route →
        (∀ addr, DhcpSubject.step p s (.fetch who addr) = (s, .refused)) ∧
        (∀ addr len, DhcpSubject.step p s (.send who addr len) = (s, .refused))) ∧
    (∀ (p : DhcpSubject.Ports) (s : DhcpSubject.State) (ops : List DhcpSubject.Op) (x a : Nat),
      (∀ op ∈ ops, ∀ addr bytes, op ≠ .write x addr bytes) →
      ¬ DhcpSubject.inOwnWindow p x a →
      (DhcpSubject.run p s ops).mem x a = s.mem x a) ∧
    (∀ (p : DhcpSubject.Ports) (s : DhcpSubject.State) (op : DhcpSubject.Op),
      (DhcpSubject.step p s op).1.lease ≠ s.lease →
        ∃ mac ip, op = .handoff DhcpSubject.dhcp mac ip ∧ s.route = DhcpSubject.dhcp ∧
          (DhcpSubject.step p s op).1.lease = some (mac, ip)) ∧
    (∀ (p : DhcpSubject.Ports) (mem : Nat → Nat → UInt8) (ops : List DhcpSubject.Op),
      (DhcpSubject.run p (DhcpSubject.State.boot mem) ops).route = DhcpSubject.echo →
        ∃ mac ip, (DhcpSubject.run p (DhcpSubject.State.boot mem) ops).lease = some (mac, ip) ∧
          ∀ f r, Net.Echo.replyFrame f mac ip = some r → DhcpSubject.askedFor f = ip) ∧
    (∀ subject req addr len base limit : UInt64,
      DhcpSubject.framePortCheck subject req addr len base limit = 0 →
        (subject = 2 ∨ subject = 3) ∧ (req >>> 24) &&& 0xff = subject ∧
          (req >>> 16) &&& 0xff = subject ∧
          NetworkSubject.Window.covers ⟨base.toNat, limit.toNat⟩ addr.toNat len.toNat = true) ∧
    (∀ subject req addr len base limit : UInt64, subject ≠ 2 → subject ≠ 3 →
      DhcpSubject.framePortCheck subject req addr len base limit = 1) ∧
    (∀ (sys : DeviceCapability.System σ), sys.deviceCaps = KeyboardEcho.bootDeviceCaps →
      ∀ ts : List DeviceCapability.Transition,
        (∀ d, DeviceCapability.Transition.grant DhcpSubject.dhcp d ∉ ts) →
        (∀ program, DeviceCapability.step models (DeviceCapability.run models sys ts)
            (.bind DhcpSubject.dhcp program) =
              (DeviceCapability.run models sys ts, .denied)) ∧
        (∀ fuel, DeviceCapability.step models (DeviceCapability.run models sys ts)
            (.invoke DhcpSubject.dhcp fuel) =
              (DeviceCapability.run models sys ts, .denied))) ∧
    (∀ (sys : DeviceCapability.System σ), sys.deviceCaps = KeyboardEcho.bootDeviceCaps →
      ∀ ts : List DeviceCapability.Transition,
        (∀ d, DeviceCapability.Transition.grant DhcpSubject.echo d ∉ ts) →
        (∀ program, DeviceCapability.step models (DeviceCapability.run models sys ts)
            (.bind DhcpSubject.echo program) =
              (DeviceCapability.run models sys ts, .denied)) ∧
        (∀ fuel, DeviceCapability.step models (DeviceCapability.run models sys ts)
            (.invoke DhcpSubject.echo fuel) =
              (DeviceCapability.run models sys ts, .denied))) :=
  ⟨DhcpSubject.nonholder_refused, DhcpSubject.unrouted_refused,
   DhcpSubject.run_mem_outside_windows, DhcpSubject.step_lease_changed,
   DhcpSubject.echo_answers_only_lease, DhcpSubject.framePortCheck_own_window,
   DhcpSubject.framePortCheck_nonholder,
   fun sys hcaps ts hg => DhcpSubject.dhcp_no_device_effects models sys hcaps ts hg,
   fun sys hcaps ts hg => DhcpSubject.echo_no_device_effects models sys hcaps ts hg⟩

/-- SC-WIFI-GROUP-KEY-ROTATION: the BCM43224 driver keeps a session across
the access point's group-key rotation without accepting replays. No frame
lowers the EAPOL replay counter, and across any run the counters answered
with group message 2 strictly increase, so a group message is answered at
most once; an answered message 1 installs exactly its GTK, key id (1–3,
never the TK's 0) and Key RSC, leaving the TK alone; after the rotation a
frame under the new key id and key with a packet number above the Key RSC
is delivered, while a frame under the previous key id, under stale material
for the new key id, or with a packet number at or below its key's floor is
dropped without changing anything; and a delivered frame's packet number
exceeds its key's floor and becomes the new floor. -/
theorem wifi_group_key_rotation :
    (∀ (s : GtkRekey.State) (fs : List GtkRekey.Frame),
      s.replay ≤ (GtkRekey.run s fs).1.replay ∧
        (GtkRekey.msg2s (GtkRekey.run s fs).2).Pairwise (· < ·)) ∧
    (∀ (s : GtkRekey.State) (f : GtkRekey.Frame) (r : Nat),
      (GtkRekey.step s f).2 = .msg2 r →
        ∃ m, f.body = .groupMsg1 m ∧ r = m.replay ∧ m.micOk = true ∧ m.unwrapOk = true ∧
          (m.keyId = 1 ∨ m.keyId = 2 ∨ m.keyId = 3) ∧
          (GtkRekey.step s f).1.gtkId = m.keyId ∧ (GtkRekey.step s f).1.gtk = m.gtk ∧
          (GtkRekey.step s f).1.pnGtk = m.rsc ∧ (GtkRekey.step s f).1.tk = s.tk) ∧
    (∀ (s : GtkRekey.State) (f g : GtkRekey.Frame) (r : Nat) (m : GtkRekey.GroupMsg1) (p : Nat),
      (GtkRekey.step s f).2 = .msg2 r → f.body = .groupMsg1 m →
        g.keyId = m.keyId → g.key = m.gtk → m.rsc < g.pn → g.body = .data p →
          (GtkRekey.step (GtkRekey.step s f).1 g).2 = .deliver p) ∧
    (∀ (s : GtkRekey.State) (f g : GtkRekey.Frame) (r : Nat) (m : GtkRekey.GroupMsg1),
      (GtkRekey.step s f).2 = .msg2 r → f.body = .groupMsg1 m →
        g.keyId ≠ 0 → g.keyId ≠ m.keyId →
          GtkRekey.step (GtkRekey.step s f).1 g = ((GtkRekey.step s f).1, .drop .unknownKey)) ∧
    (∀ (s : GtkRekey.State) (f g : GtkRekey.Frame) (r : Nat) (m : GtkRekey.GroupMsg1),
      (GtkRekey.step s f).2 = .msg2 r → f.body = .groupMsg1 m →
        g.keyId = m.keyId → g.key ≠ m.gtk →
          GtkRekey.step (GtkRekey.step s f).1 g = ((GtkRekey.step s f).1, .drop .mic)) ∧
    (∀ (s : GtkRekey.State) (g : GtkRekey.Frame),
      GtkRekey.keyFor s g.keyId = some g.key → g.pn ≤ GtkRekey.lastPn s g.keyId →
        GtkRekey.step s g = (s, .drop .replayedPn)) ∧
    (∀ (s : GtkRekey.State) (f : GtkRekey.Frame) (p : Nat),
      (GtkRekey.step s f).2 = .deliver p →
        GtkRekey.lastPn s f.keyId < f.pn ∧ GtkRekey.lastPn (GtkRekey.step s f).1 f.keyId = f.pn) :=
  ⟨fun s fs => ⟨GtkRekey.run_replay_mono s fs, GtkRekey.run_msg2_sorted s fs⟩,
   GtkRekey.msg2_installs, GtkRekey.delivered_after_rekey, GtkRekey.stale_id_dropped,
   GtkRekey.stale_material_dropped, GtkRekey.replayed_pn_dropped,
   fun s f p h => ⟨(GtkRekey.deliver_pn s f p h).2.2.1, (GtkRekey.deliver_pn s f p h).2.2.2⟩⟩

/-- SC-TIMER-CAPABILITY: the PIT alarm is armed only by an accepted arm from
the timer-capability holder with a count in `1 .. 65535`; an arm from any
other subject is refused without effect; the expiry interrupt is delivered
only to the holder and touches nothing but the alarm and the holder's expiry
notification (no authority, server state, client wake, tick count or
preemption deadline); no other subject ever has pending expiry bits; and no
operation, the server's included, changes the kernel's preemption deadline,
so the programmed count is never later than it. -/
theorem timer_capability_confinement :
    (∀ (sys : TimerServer.System) (op : TimerServer.Op) (count : Nat),
      (TimerServer.step sys op).1.pit.alarm = some count →
        sys.pit.alarm = some count ∨
          ∃ actor, op = .arm actor count ∧ sys.auth.timerHolder = some actor ∧
            TimerServer.InBound count = true) ∧
    (∀ (sys : TimerServer.System) (actor : TimerServer.SubjectId) (count : Nat),
      sys.auth.timerHolder ≠ some actor →
        TimerServer.step sys (.arm actor count) = (sys, .refused .noTimerCapability)) ∧
    (∀ (sys : TimerServer.System) (holder : TimerServer.SubjectId),
      (TimerServer.step sys .expire).2 = .delivered holder →
        sys.auth.timerHolder = some holder) ∧
    (∀ sys : TimerServer.System,
      let next := (TimerServer.step sys .expire).1
      next.auth = sys.auth ∧ next.pit.preemption = sys.pit.preemption ∧
        next.server.queue = sys.server.queue ∧
        next.server.outstanding = sys.server.outstanding ∧
        next.wakes = sys.wakes ∧ next.ticks = sys.ticks ∧
        (∀ s, sys.auth.timerHolder ≠ some s → next.expiries s = sys.expiries s)) ∧
    (∀ (sys : TimerServer.System) (op : TimerServer.Op), TimerServer.ExpiryBound sys →
      TimerServer.ExpiryBound (TimerServer.step sys op).1) ∧
    (∀ (sys : TimerServer.System) (op : TimerServer.Op),
      (TimerServer.step sys op).1.pit.preemption = sys.pit.preemption) ∧
    (∀ (pit : TimerServer.Pit) (p : Nat), pit.preemption = some p →
      ∃ q, pit.programmed = some q ∧ q ≤ p) :=
  ⟨TimerServer.alarm_set_only_by_holder, TimerServer.arm_non_holder_unchanged,
   fun sys holder h => (TimerServer.expire_delivered_to_holder sys holder h).1,
   TimerServer.expire_footprint, TimerServer.step_preserves_expiryBound,
   TimerServer.preemption_unchanged, TimerServer.programmed_le_preemption⟩

/-- SC-TIMER-SERVER-POLICY: a request from a subject without the endpoint to
the timer server is refused without effect, so every queued alarm (the only
thing the server arms) belongs to an endpoint holder; a request outside the
bound or over the client's quota is refused without effect; no client's
outstanding alarm count ever exceeds the quota; and a client's wake bits rise
only when the timer-capability holder collects an expiry for that client's
alarm. -/
theorem timer_server_alarm_policy :
    (∀ (sys : TimerServer.System) (client : TimerServer.SubjectId) (count : Nat),
      sys.auth.reachesServer client = false →
        TimerServer.step sys (.request client count) = (sys, .refused .noEndpoint)) ∧
    (∀ (sys : TimerServer.System) (op : TimerServer.Op), TimerServer.QueueFromSenders sys →
      TimerServer.QueueFromSenders (TimerServer.step sys op).1) ∧
    (∀ (sys : TimerServer.System) (client : TimerServer.SubjectId) (count : Nat),
      TimerServer.InBound count = false →
        (TimerServer.step sys (.request client count)).1 = sys) ∧
    (∀ (sys : TimerServer.System) (client : TimerServer.SubjectId) (count : Nat),
      sys.auth.reachesServer client = true → TimerServer.InBound count = true →
        sys.server.quota ≤ sys.server.outstanding client →
          TimerServer.step sys (.request client count) = (sys, .refused .quotaExceeded)) ∧
    (∀ (sys : TimerServer.System) (op : TimerServer.Op), TimerServer.WithinQuota sys →
      TimerServer.WithinQuota (TimerServer.step sys op).1) ∧
    (∀ (sys : TimerServer.System) (op : TimerServer.Op) (client : TimerServer.SubjectId),
      sys.wakes client < (TimerServer.step sys op).1.wakes client →
        ∃ actor count rest, op = .collect actor ∧ sys.auth.timerHolder = some actor ∧
          sys.expiries actor ≠ 0 ∧ sys.server.queue = (client, count) :: rest) :=
  ⟨TimerServer.request_without_endpoint_unchanged,
   TimerServer.step_preserves_queueFromSenders,
   fun sys client count h => (TimerServer.request_out_of_bound_unchanged sys client count h).1,
   TimerServer.request_over_quota_refused,
   TimerServer.step_preserves_withinQuota,
   TimerServer.wake_only_by_holder⟩

/-- SC-SPAWN-SYSCALL: the ring-3 spawn syscall's generated witness either
refuses before any gate, keeping the kernel's token, or answers exactly one
edge of the generated spawn table at the presented token.  That edge's words
are the syscall's canonical command words, which decode to a public child or
memory command (never a kernel command); the actor is the current subject of
the latch on the complete state the token names; the step is exactly
`childGate` or `memoryGate` there, whose post-state the successor token names;
and a rejected step keeps the token and the complete pre-state. -/
theorem spawn_syscall_refines_gate (plan : BootPageTablePlan.Plan)
    (compiled : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan)
    (state actor number rbx rcx rdx : UInt64) :
    (SpawnSyscall.spawnSyscall state actor number rbx rcx rdx ∈ SpawnSyscall.refusals ∧
        SpawnSyscall.nextToken state (SpawnSyscall.spawnSyscall state actor number rbx rcx rdx) =
          state) ∨
      ∃ edge ∈ SpawnBoundary.edges, SpawnBoundary.encodeState edge.state = state ∧
        SpawnBoundary.decodeFamily (SpawnSyscall.syscallWords number rbx rcx rdx) =
          .ok edge.command ∧
        SpawnSyscall.isSyscallCommand edge.command = true ∧
        actor = UInt64.ofNat (FailStop.spawnParent (SpawnBoundary.stateOf plan edge.state)) ∧
        SpawnBoundary.familyStep (SpawnBoundary.stateOf plan edge.state) edge.command =
          { state := SpawnBoundary.stateOf plan edge.next, status := edge.status,
            value := edge.value } ∧
        SpawnSyscall.nextToken state (SpawnSyscall.spawnSyscall state actor number rbx rcx rdx) =
          SpawnBoundary.encodeState edge.next ∧
        (edge.status ≠ 0x01 → edge.next = edge.state ∧
          (SpawnBoundary.familyStep (SpawnBoundary.stateOf plan edge.state) edge.command).state =
            SpawnBoundary.stateOf plan edge.state) := by
  rcases SpawnSyscall.spawnSyscall_cases state actor number rbx rcx rdx with
    refused | ⟨edge, member, token, words, sameActor, _, _, reply⟩
  · left
    refine ⟨refused, ?_⟩
    simp only [SpawnSyscall.refusals, List.mem_cons, List.not_mem_nil, or_false] at refused
    simp only [SpawnSyscall.nextToken]
    rcases refused with h | h | h | h | h <;> rw [h] <;> simp [SpawnSyscall.isEdgeReply]
  · right
    obtain ⟨decoded, isSyscall, current, step, next, _⟩ :=
      SpawnSyscall.spawnSyscall_refines plan compiled state actor number rbx rcx rdx edge member
        token words reply sameActor
    exact ⟨edge, member, token, decoded, isSyscall, current, step, next,
      SpawnBoundary.rejected_edge_unchanged plan compiled edge member⟩

/-- SC-SPAWN-STALE-CHILD: a parent's control word for a child it terminated
stays stale after the parent spawns a new child, including into the same
child-table slot.  Both a frame grant and a termination through the old word
are rejected with a typed control error and leave the complete composite
state unchanged. -/
theorem spawn_stale_child_control (state : FailStop.CompositeState) (word : UInt64)
    (child returned : Nat) (accounting : FailStop.ChildAccountingWellFormed state)
    (terminated : (FailStop.terminateChild state word).result = .terminated child returned)
    (request : FailStop.SpawnRequest) (frames : Nat) :
    let respawned :=
      (FailStop.childGate (FailStop.terminateChild state word).state (.spawn request)).state
    FailStop.spawnParent respawned = FailStop.spawnParent state →
    (∃ reason, (FailStop.grantFrames respawned word frames).result =
        .framesRejected (.control reason)) ∧
      (FailStop.grantFrames respawned word frames).state = respawned ∧
      (∃ reason, (FailStop.terminateChild respawned word).result = .terminateRejected reason) ∧
      (FailStop.terminateChild respawned word).state = respawned :=
  FailStop.stale_control_after_respawn state word child returned accounting terminated request
    frames

/-- SC-LOADER-EXACT: the loader model keeps the child's pages exactly the
pages of its loaded admitted segments, from the empty state and across every
request; and when the child is started, every segment of the admitted plan is
loaded and the child's pages are exactly the plan's pages, each matching its
one segment's permissions (copied when writable, in place otherwise). -/
theorem loader_exact_admitted_segments :
    (∀ state : ChildLoader.State, ChildLoader.Exact (ChildLoader.rollback state)) ∧
    (∀ (state : ChildLoader.State) (request : ChildLoader.Request), ChildLoader.Exact state →
      ChildLoader.Exact (ChildLoader.step state request).1) ∧
    (∀ (state : ChildLoader.State) (control : UInt64), ChildLoader.PlanLayout state.plan →
      ChildLoader.Exact state →
      (ChildLoader.step state (.start control)).2 = .started →
      (ChildLoader.step state (.start control)).1.started = true ∧
      (∀ page leaf, (ChildLoader.step state (.start control)).1.leaves page = some leaf →
        ∃ segment ∈ state.plan, ChildLoader.inSegment segment page = true ∧
          ChildLoader.Matches segment leaf) ∧
      (∀ segment ∈ state.plan, ∀ page, ChildLoader.inSegment segment page = true →
        ∃ leaf, (ChildLoader.step state (.start control)).1.leaves page = some leaf ∧
          ChildLoader.Matches segment leaf)) := by
  refine ⟨ChildLoader.exact_rollback, fun state request exact =>
    ChildLoader.step_preserves_exact state request exact, ?_⟩
  intro state control layout exact started
  obtain ⟨isStarted, both⟩ := ChildLoader.started_exact state control exact started
  refine ⟨isStarted, fun page leaf found => (both page).1 leaf found, ?_⟩
  intro segment member page inside
  exact ChildLoader.started_exact_unique state control layout exact started page segment member
    inside

/-- SC-LOADER-RESERVED-RANGE: whatever the loader asks, every page the model
maps in place lies inside the loader's read authority (the reserved range),
and every copy uses a frame given to the child; a load whose claimed source
is not inside the read authority is rejected and rolls the spawn back. -/
theorem loader_reserved_range_only :
    (∀ state : ChildLoader.State, ChildLoader.Inside (ChildLoader.rollback state)) ∧
    (∀ (state : ChildLoader.State) (request : ChildLoader.Request), ChildLoader.Inside state →
      ChildLoader.Inside (ChildLoader.step state request).1) ∧
    (∀ (state : ChildLoader.State) (child : ChildLoader.Child) (control : UInt64)
        (index source : Nat) (segment : ElfAdmission.Segment),
      ChildLoader.liveChild state control = some child → state.plan[index]? = some segment →
      state.loaded index = false →
      (source < state.start ∨ state.stop < source + ChildLoader.pageCount segment * ElfAdmission.pageBytes) →
      ChildLoader.step state (.load control index source) =
        (ChildLoader.rollback state, .rolledBack .outsideAuthority)) :=
  ⟨ChildLoader.inside_rollback, fun state request inside =>
    ChildLoader.step_preserves_inside state request inside,
   ChildLoader.load_outside_authority_rejected⟩

/-- SC-LOADER-ROLLBACK: every rejection of a request naming the child being
loaded discards that child entirely (no child, no pages, nothing loaded, no
frame used); a request naming no such child changes nothing; and the boot
witnesses answer exactly the model's encoded reply for every request whose
words are small. -/
theorem loader_failure_rolls_back :
    (∀ (state : ChildLoader.State) (request : ChildLoader.Request) (reason : ChildLoader.Rejection),
      (ChildLoader.step state request).2 = .rolledBack reason →
      (ChildLoader.step state request).1 = ChildLoader.rollback state ∧
        (ChildLoader.step state request).1.child = none ∧
        (∀ page, (ChildLoader.step state request).1.leaves page = none) ∧
        (ChildLoader.step state request).1.used = 0) ∧
    (∀ (state : ChildLoader.State) (request : ChildLoader.Request) (reason : ChildLoader.Rejection),
      (ChildLoader.step state request).2 = .refused reason →
      (ChildLoader.step state request).1 = state) ∧
    (∀ (state : ChildLoader.State) (control : UInt64) (sourceCode pages frames used : UInt64),
      ChildLoader.loaderDecide 2 (ChildLoader.flagsWord state (.start control)) sourceCode pages
          frames used =
        ChildLoader.encodeReply false (ChildLoader.step state (.start control)).2) := by
  refine ⟨fun state request reason rejected => ?_, ChildLoader.refused_unchanged,
    ChildLoader.loader_witness_agrees_start⟩
  have rolled := ChildLoader.rejection_rolls_back state request reason rejected
  obtain ⟨child, leaves, _, used⟩ := ChildLoader.rollback_empty state
  rw [rolled]
  exact ⟨rfl, child, leaves, used⟩

/-- SC-LOADER-JOINT-ROLLBACK: from a composite state satisfying the
invariants under the running latch and a loader with no child, spawn a child
through the gate, grant it frames, and run loader requests; when a request
rolls the loader back, the paired steps (the loader's rollback and the
composite termination of the child the request names) leave the loader
exactly as before the spawn and the composite state restored against the
state before the spawn: live subjects, every capability slot, runnable set,
current subject, ownership records, frame commitments, allocator, bindings,
frame contents, child tables and spawn authority, with the child's spawn
records cleared and only never-reused histories advanced. -/
theorem loader_joint_rollback_restores :
    ∀ (pre : FailStop.CompositeState) (idle : ChildLoader.State)
      (request : FailStop.SpawnRequest) (grants : List Nat)
      (requests : List ChildLoader.Request) (last : ChildLoader.Request)
      (child addressSpace : Nat) (control : UInt64) (reason : ChildLoader.Rejection),
      pre.execution.mode = .running → FailStop.ResourceRuntimeWellFormed pre →
      FailStop.ChildAccountingWellFormed pre → ChildLoader.rollback idle = idle →
      (FailStop.childGate pre (.spawn request)).result =
        .completed (.spawned child addressSpace control) →
      (ChildLoaderJoint.loaderStep (ChildLoaderJoint.runLoader (ChildLoaderJoint.grantSteps
        (ChildLoaderJoint.spawnStep ⟨pre, idle⟩ request) control grants) requests) last).2 =
          .rolledBack reason →
      (ChildLoaderJoint.loaderStep (ChildLoaderJoint.runLoader (ChildLoaderJoint.grantSteps
        (ChildLoaderJoint.spawnStep ⟨pre, idle⟩ request) control grants) requests) last).1.loader =
          idle ∧
      FailStop.SpawnRestored pre
        (ChildLoaderJoint.loaderStep (ChildLoaderJoint.runLoader (ChildLoaderJoint.grantSteps
          (ChildLoaderJoint.spawnStep ⟨pre, idle⟩ request) control grants) requests)
          last).1.composite child :=
  fun pre idle request grants requests last child addressSpace control reason running holds
    accounting noChild spawned rolledBack =>
  ChildLoaderJoint.joint_rollback_restores pre idle request grants requests last child
    addressSpace control reason running holds accounting noChild spawned rolledBack

/-- SC-LOADER-CONTENTS: from a loader with no child, every run of requests
keeps the child's pages exact, inside the reserved range and the child's
frames, and holding their segments' bytes; and when `start` succeeds, every
address of a writable segment's page-rounded memory image reads, through the
child's pages, the admitted file byte below the segment's file size and zero
from there to the segment's page-rounded end. -/
theorem loader_copied_contents :
    (∀ (state : ChildLoader.State) (requests : List ChildLoader.Request),
      ChildLoader.Exact (ChildLoader.runRequests (ChildLoader.rollback state) requests) ∧
        ChildLoader.Inside (ChildLoader.runRequests (ChildLoader.rollback state) requests) ∧
        ChildLoader.Contents (ChildLoader.runRequests (ChildLoader.rollback state) requests)) ∧
    (∀ (state : ChildLoader.State) (control : UInt64), ChildLoader.PlanLayout state.plan →
      ChildLoader.Exact state → ChildLoader.Contents state →
      (ChildLoader.step state (.start control)).2 = .started →
      ∀ segment ∈ state.plan, segment.writable = true → ∀ address,
        segment.vaddr ≤ address → address < segment.pageEnd →
        (address < segment.vaddr + segment.fileBytes →
          ChildLoader.childByte (ChildLoader.step state (.start control)).1 address =
            some (state.file (segment.fileOffset + (address - segment.vaddr)))) ∧
        (segment.vaddr + segment.fileBytes ≤ address →
          ChildLoader.childByte (ChildLoader.step state (.start control)).1 address =
            some 0)) :=
  ⟨ChildLoader.runRequests_invariants,
   fun state control layout exact contents started segment member writable address low high =>
    ChildLoader.started_writable_bytes state control layout exact contents started segment member
      writable address low high⟩

/-- SC-LOADER-CHILD-SEND: the started child's send (syscall 8 through its
slot-`0` endpoint) is a composite step that keeps the combined runtime and
resource invariant, the child accounting invariant and the spawn-tree
invariant (so it is a step of `child_resource_trace`); an accepted send
writes only the mailbox of the endpoint the child's slot-`0` capability
names and changes no other projection; and after a spawn through the gate,
frame grants and loader requests that leave the child started, the started
child is the spawned child, its slot-`0` capability is the copy of the
parent's endpoint with exactly the requested rights, and an accepted send
reaches only that endpoint. -/
theorem loader_child_send_confined :
    (∀ (state : FailStop.CompositeState) (child : Nat) (word : UInt64),
      FailStop.ResourceRuntimeWellFormed state → FailStop.ChildAccountingWellFormed state →
      FailStop.SpawnTreeWellFormed state →
      FailStop.ResourceRuntimeWellFormed (FailStop.childSend state child word).state ∧
        FailStop.ChildAccountingWellFormed (FailStop.childSend state child word).state ∧
        FailStop.SpawnTreeWellFormed (FailStop.childSend state child word).state) ∧
    (∀ (state : FailStop.CompositeState) (child : Nat) (word : UInt64),
      FailStop.RuntimeWellFormed state → (FailStop.childSend state child word).result = .sent →
      ∃ capability, state.capabilities.slots child FailStop.childEndpointSlot = some capability ∧
        capability.kind = .endpoint ∧ capability.rights.send = true ∧
        (∀ object, object ≠ capability.object →
          (FailStop.childSend state child word).state.ipc.endpoints.mailbox object =
            state.ipc.endpoints.mailbox object) ∧
        (FailStop.childSend state child word).state.ipc.endpoints.capabilities =
          state.ipc.endpoints.capabilities ∧
        { (FailStop.childSend state child word).state with
            ipc := state.ipc, transfers := state.transfers } = state) ∧
    (∀ (pre : FailStop.CompositeState) (idle : ChildLoader.State)
      (request : FailStop.SpawnRequest) (grants : List Nat)
      (requests : List ChildLoader.Request) (child addressSpace : Nat) (control word : UInt64),
      pre.execution.mode = .running → FailStop.ResourceRuntimeWellFormed pre →
      FailStop.ChildAccountingWellFormed pre →
      (FailStop.childGate pre (.spawn request)).result =
        .completed (.spawned child addressSpace control) →
      (∃ loading, (ChildLoaderJoint.runLoader (ChildLoaderJoint.grantSteps
        (ChildLoaderJoint.spawnStep ⟨pre, idle⟩ request) control grants)
          requests).loader.child = some loading) →
      (ChildLoaderJoint.runLoader (ChildLoaderJoint.grantSteps
        (ChildLoaderJoint.spawnStep ⟨pre, idle⟩ request) control grants)
          requests).loader.started = true →
      let ran := ChildLoaderJoint.runLoader (ChildLoaderJoint.grantSteps
        (ChildLoaderJoint.spawnStep ⟨pre, idle⟩ request) control grants) requests
      ChildLoaderJoint.startedChild ran = some child ∧
        ((ChildLoaderJoint.childSendStep ran word).2 = .sent →
          ∃ slot endpoint,
            pre.capabilities.slots (FailStop.spawnParent pre) slot = some endpoint ∧
            endpoint.kind = .endpoint ∧
            ran.composite.capabilities.slots child FailStop.childEndpointSlot =
              some ⟨endpoint.object, .endpoint, request.rights,
                pre.capabilities.nextIdentity + 1, some endpoint.identity⟩ ∧
            (ChildLoaderJoint.childSendStep ran word).1.composite.ipc.endpoints.mailbox
                endpoint.object =
              some { endpoint := endpoint.object, sender := child,
                     payload := FailStop.childSendPayload word } ∧
            (∀ object, object ≠ endpoint.object →
              (ChildLoaderJoint.childSendStep ran word).1.composite.ipc.endpoints.mailbox
                  object =
                ran.composite.ipc.endpoints.mailbox object) ∧
            { (ChildLoaderJoint.childSendStep ran word).1.composite with
                ipc := ran.composite.ipc, transfers := ran.composite.transfers } =
              ran.composite)) :=
  ⟨fun state child word holds accounting tree =>
    FailStop.childSend_preserves state child word holds accounting tree,
   fun state child word holds sent => FailStop.childSend_confined state child word holds sent,
   fun pre idle request grants requests child addressSpace control word running holds
    accounting spawned loaded started =>
    ChildLoaderJoint.joint_child_send_confined pre idle request grants requests child
      addressSpace control word running holds accounting spawned loaded started⟩

/-- SC-TIMING-REFUSAL-BUDGET: the subject gate's refusal of a cross-subject
request is decided by the boot witness `leanos_cross_subject_refusal` from the
latch mode, the scheduled subject and the named subject alone, exactly as
`CompositeState.refusesCrossSubject` decides it; two states that agree on the
mode and the scheduled subject refuse the same request with the same fixed
result and no effect, and replies padded to a budget leave at the same cycle
whenever their work fits it, and never before it (ADR 0028). -/
theorem timing_refusal_fixed_budget :
    (∀ (state : FailStop.CompositeState) (operation : FailStop.AuthoritativeOperation),
      TimingBudget.Encodable state.lifecycle.current →
      TimingBudget.Encodable operation.target →
      TimingChannels.crossSubjectRefusal (TimingBudget.modeWord state.execution.mode)
          (TimingBudget.subjectWord state.lifecycle.current)
          (TimingBudget.subjectWord operation.target) =
        if state.refusesCrossSubject operation then TimingChannels.refusedWord
        else TimingChannels.passWord) ∧
    (∀ (left right : FailStop.CompositeState) (operation : FailStop.AuthoritativeOperation)
      (start budget leftWork rightWork : Nat),
      left.execution.mode = right.execution.mode →
      left.lifecycle.current = right.lifecycle.current →
      left.refusesCrossSubject operation = true →
      leftWork ≤ budget → rightWork ≤ budget →
      FailStop.subjectGate left operation = { state := left, result := .crossSubjectRefused } ∧
        FailStop.subjectGate right operation =
          { state := right, result := .crossSubjectRefused } ∧
        TimingBudget.departure start leftWork budget =
          TimingBudget.departure start rightWork budget) ∧
    (∀ start work budget : Nat, start + budget ≤ TimingBudget.departure start work budget) :=
  ⟨TimingBudget.crossSubjectRefusal_agrees,
   fun _ _ _ _ _ _ _ hmode hcurrent hrefused hleft hright =>
     TimingBudget.refusal_fixed_budget hmode hcurrent hrefused hleft hright,
   TimingBudget.departure_not_early⟩

/-- SC-TIMING-NO-USER-CLOCK: every CR4 the validated user return accepts has
CR4.TSD set and CR4.PCE clear, so under the architectural reading of RDTSC,
RDTSCP and RDPMC each of them faults at CPL3; a CR4 without TSD is refused
(ADR 0028). -/
theorem timing_no_user_clock :
    (∀ cr4 : UInt64, TimingBudget.userReturnClockControls cr4 = true →
      TimingBudget.userCounterFaults cr4 3 = true) ∧
    (∀ cr4 : UInt64, cr4 &&& TimingBudget.tsdBit = 0 →
      TimingBudget.userReturnClockControls cr4 = false) :=
  ⟨TimingBudget.clock_controls_deny_user_counters, TimingBudget.clock_controls_require_tsd⟩

end LeanOS.SecurityClaims
