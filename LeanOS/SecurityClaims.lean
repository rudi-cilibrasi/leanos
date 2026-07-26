import LeanOS.BootInterruptPhase
import LeanOS.BoundedLifecycle
import LeanOS.KernelTransition
import LeanOS.Capability
import LeanOS.FrameAllocator
import LeanOS.FrameBudget
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
import LeanOS.DirectPortIO
import LeanOS.DirectPortContainment
import LeanOS.UserFaultContainmentVocabulary
import LeanOS.StaleTranslation

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

private def returnWitnessLifecycle : SubjectLifecycle.State :=
  { capabilities :=
      { subjects := fun subject => subject = 1
        objects := fun object => object = 100 || object = 101
        kinds := fun object => if object = 100 || object = 101 then some .memory else none
        slots := fun _ _ => none }
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
      Interrupt.WellFormed, SubjectLifecycle.WellFormed]
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
    issued := fun object => object = 100 || object = 101 }

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
  { execution := returnWitnessBase
    scheduler
    preemption := { scheduler, timerArmed := false, acceptedTicks := 1 }
    virtualMemory := returnWitnessVirtualMemory
    ipc := { virtualMemory := returnWitnessVirtualMemory, endpoints := returnWitnessEndpoints }
    capabilities := returnWitnessLifecycle.capabilities
    lifecycle := returnWitnessLifecycle }

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

private def returnWitnessSyscallContext : Syscall.TrustedContext :=
  { caller := 1, activeAddressSpace := 1 }

private def returnWitnessSyscallCall : Syscall.UntrustedCall :=
  { number := 99, arg0 := 0, arg1 := 0, arg2 := 0 }

set_option maxRecDepth 100000 in
/-- Concrete typed composite trace: syscall entry clears old authority, the
syscall body installs its final lifecycle/context and reselects, and the
following return is accepted without changing the composite state. -/
theorem user_return_composite_entry_witness :
    let entered := (FailStop.gate returnWitnessComposite
      (.interrupt returnWitnessSyscallFrame)).state
    let called := (FailStop.gate entered
      (.syscall returnWitnessSyscallContext returnWitnessSyscallCall)).state
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
