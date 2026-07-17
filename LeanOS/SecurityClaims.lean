import LeanOS.KernelTransition
import LeanOS.Capability
import LeanOS.FrameAllocator
import LeanOS.X86PageTable
import LeanOS.Syscall
import LeanOS.FailStop
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
      attested.hardware.flagsAllowed = true ∧
      attested.flags.reservedAllowed = true ∧
      attested.flags.interruptEnable = true ∧
      attested.flags.direction = false ∧
      attested.flags.alignmentCheck = false ∧
      attested.flags.nestedTask = false ∧
      attested.flags.virtual8086 = false ∧
      attested.flags.ioPrivilegeLevel = 0 ∧
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

/-- SC-USER-RETURN-FAILSTOP: a rejected outgoing return atomically latches a
typed terminal record, freezes every composite subsystem, and absorbs all
later operations. -/
theorem user_return_rejection_failstop state request reason proposals
    (hmode : state.execution.mode = .running)
    (hrejected : Interrupt.validateUserReturn
      (FailStop.authoritativeReturnRequest state.execution request) = .rejected reason) :
    let record : FailStop.HaltRecord :=
      { reason := .invalidUserReturn request.purpose reason
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
    hmode hrejected

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
