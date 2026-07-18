import LeanOS.KernelTransition
import LeanOS.Capability
import LeanOS.FrameAllocator
import LeanOS.FrameBudget
import LeanOS.X86PageTable
import LeanOS.Syscall
import LeanOS.FailStop
import LeanOS.InterruptEntry
import LeanOS.ExtendedState
import LeanOS.ScheduledObservation

/-! # Stable security-claim contract

Each theorem independently restates one advertised proposition. Changes to an
implementation theorem's assumptions or conclusion therefore require an
explicit change here and in `docs/security-claims.md`.
-/
namespace LeanOS.SecurityClaims

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
