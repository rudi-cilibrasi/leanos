import LeanOS.SubjectLifecycle

/-!
# Interrupt and exception transition model

This is a total, sequential model of the first interrupt boundary.  Hardware
frame construction is trusted; general-purpose registers are kept separate so
they cannot supply the vector, origin, subject, address space, or return mode.
-/
namespace LeanOS.Interrupt

set_option linter.unusedSimpArgs false

open LeanOS

abbrev SubjectId := Capability.SubjectId
abbrev AddressSpaceId := VirtualMapping.AddressSpaceId

inductive Privilege where | kernel | user
  deriving DecidableEq, Repr

inductive Vector where | pageFault | timer | syscall
  deriving DecidableEq, Repr

def decodeVector : Nat → Option Vector
  | 14 => some .pageFault
  | 32 => some .timer
  | 128 => some .syscall
  | _ => none

/-- Fields established by the trusted hardware/assembly entry boundary. -/
structure HardwareFrame where
  vector : Nat
  errorCode : UInt64
  savedPrivilege : Privilege
  instructionPointer : UInt64
  stackPointer : UInt64
  codeSelector : UInt64
  stackSelector : UInt64
  flags : UInt64
  canonicalInstructionPointer : Bool
  canonicalStackPointer : Bool
  flagsAllowed : Bool
  deriving DecidableEq, Repr

/-- Values controlled by the interrupted subject, never used as trusted context. -/
structure AttackerRegisters where
  accumulator : UInt64
  base : UInt64
  count : UInt64
  data : UInt64
  deriving DecidableEq, Repr

structure Trap where
  hardware : HardwareFrame
  registers : AttackerRegisters
  deriving DecidableEq, Repr

structure TrustedContext where
  currentSubject : SubjectId
  activeAddressSpace : AddressSpaceId
  kernelStack : UInt64
  entryActive : Bool
  deriving DecidableEq, Repr

structure State where
  lifecycle : SubjectLifecycle.State
  context : TrustedContext

def WellFormed (state : State) : Prop := SubjectLifecycle.WellFormed state.lifecycle

inductive FatalReason where | kernelFault | unsupportedVector | nestedEntry
  deriving DecidableEq, Repr

inductive RejectReason where | malformedReturn | wrongOrigin
  deriving DecidableEq, Repr

inductive Action where
  | contained (subject : SubjectId)
  | timer
  | resume
  | rejected (reason : RejectReason)
  | fatal (reason : FatalReason)
  deriving DecidableEq, Repr

structure Outcome where
  state : State
  action : Action

def validUserReturn (frame : HardwareFrame) : Bool :=
  frame.savedPrivilege = .user && frame.codeSelector = 0x1b &&
    frame.stackSelector = 0x23 && frame.canonicalInstructionPointer &&
    frame.canonicalStackPointer && frame.flagsAllowed

/-! ## Authoritative outgoing user-return validation

This transition deliberately returns the request it accepted.  The accepted
value is therefore an attestation of the complete immutable frame/context
tuple, rather than a Boolean that could accidentally be reused for a different
mutable frame.  Machine code consuming the attestation remains a refinement
boundary.
-/

inductive ReturnPurpose where
  | initialDispatch | syscallResume | schedulerRestore | containedFaultResume
  | diagnosticKernelRecovery
  deriving DecidableEq, Repr

inductive ExecutionMode where | running | halted
  deriving DecidableEq, Repr

structure UserRegion where
  first : UInt64
  pastLast : UInt64
  deriving DecidableEq, Repr

def UserRegion.contains (region : UserRegion) (address : UInt64) : Bool :=
  region.first ≤ address && address < region.pastLast

/-- Decoded architectural flag policy supplied beside the raw frame.  The
machine adapter must establish that these bits agree with `hardware.flags`. -/
structure ReturnFlags where
  interruptEnable : Bool
  direction : Bool
  alignmentCheck : Bool
  nestedTask : Bool
  virtual8086 : Bool
  ioPrivilegeLevel : UInt64
  reservedAllowed : Bool
  deriving DecidableEq, Repr

structure UserReturnRequest where
  hardware : HardwareFrame
  purpose : ReturnPurpose
  frameSubject : SubjectId
  frameAddressSpace : AddressSpaceId
  frameCr3 : UInt64
  expectedSubject : SubjectId
  expectedAddressSpace : AddressSpaceId
  expectedCr3 : UInt64
  executionMode : ExecutionMode
  lifecycle : SubjectLifecycle.State
  codeRegion : UserRegion
  stackRegion : UserRegion
  flags : ReturnFlags

inductive ReturnRejectReason where
  | wrongPurpose | fatalMode | wrongOrigin | wrongSelector | noncanonical
  | forbiddenFlags | staleSubject | wrongAddressSpace | wrongCr3
  | instructionOutsideSubject | stackOutsideSubject
  deriving DecidableEq, Repr

inductive UserReturnValidation where
  | accepted (attested : UserReturnRequest)
  | rejected (reason : ReturnRejectReason)

def validateUserReturn (request : UserReturnRequest) : UserReturnValidation :=
  if request.purpose = .diagnosticKernelRecovery then .rejected .wrongPurpose
  else if request.executionMode != .running then .rejected .fatalMode
  else if request.hardware.savedPrivilege != .user then .rejected .wrongOrigin
  else if request.hardware.codeSelector != 0x1b || request.hardware.stackSelector != 0x23 then
    .rejected .wrongSelector
  else if !request.hardware.canonicalInstructionPointer ||
      !request.hardware.canonicalStackPointer then .rejected .noncanonical
  else if !request.hardware.flagsAllowed || !request.flags.reservedAllowed ||
      !request.flags.interruptEnable || request.flags.direction ||
      request.flags.alignmentCheck || request.flags.nestedTask ||
      request.flags.virtual8086 || request.flags.ioPrivilegeLevel != 0 then
    .rejected .forbiddenFlags
  else if request.lifecycle.capabilities.subjects request.expectedSubject != true ||
      request.lifecycle.runnable request.expectedSubject != true ||
      request.lifecycle.current != some request.expectedSubject ||
      request.frameSubject != request.expectedSubject then .rejected .staleSubject
  else if request.lifecycle.addressOwner request.expectedAddressSpace !=
      some request.expectedSubject ||
      request.frameAddressSpace != request.expectedAddressSpace then
    .rejected .wrongAddressSpace
  else if request.frameCr3 != request.expectedCr3 then .rejected .wrongCr3
  else if !request.codeRegion.contains request.hardware.instructionPointer then
    .rejected .instructionOutsideSubject
  else if !request.stackRegion.contains request.hardware.stackPointer then
    .rejected .stackOutsideSubject
  else .accepted request

theorem accepted_attests_exact_request request attested
    (haccepted : validateUserReturn request = .accepted attested) :
    attested = request := by
  unfold validateUserReturn at haccepted
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> simp_all

theorem accepted_user_return_context_confined request attested
    (haccepted : validateUserReturn request = .accepted attested) :
    attested.hardware.savedPrivilege = .user ∧
      attested.hardware.codeSelector = 0x1b ∧
      attested.hardware.stackSelector = 0x23 ∧
      attested.hardware.canonicalInstructionPointer = true ∧
      attested.hardware.canonicalStackPointer = true ∧
      attested.flags.interruptEnable = true ∧
      attested.flags.direction = false ∧
      attested.flags.alignmentCheck = false ∧
      attested.flags.nestedTask = false ∧
      attested.flags.virtual8086 = false ∧
      attested.flags.ioPrivilegeLevel = 0 ∧
      attested.executionMode = .running ∧
      attested.lifecycle.current = some attested.expectedSubject ∧
      attested.lifecycle.runnable attested.expectedSubject = true ∧
      attested.frameSubject = attested.expectedSubject ∧
      attested.lifecycle.addressOwner attested.expectedAddressSpace =
        some attested.expectedSubject ∧
      attested.frameAddressSpace = attested.expectedAddressSpace ∧
      attested.frameCr3 = attested.expectedCr3 := by
  have hattested : attested = request :=
    accepted_attests_exact_request request attested haccepted
  rw [hattested] at haccepted ⊢
  unfold validateUserReturn at haccepted
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> simp_all

theorem diagnostic_recovery_never_authorizes_user_return request
    (hpurpose : request.purpose = .diagnosticKernelRecovery) :
    validateUserReturn request = .rejected .wrongPurpose := by
  simp [validateUserReturn, hpurpose]

def dispatchHardware (state : State) (frame : HardwareFrame) : Outcome :=
  if state.context.entryActive then { state, action := .fatal .nestedEntry }
  else match decodeVector frame.vector with
    | none => { state, action := .fatal .unsupportedVector }
    | some .pageFault =>
        match frame.savedPrivilege with
        | .kernel => { state, action := .fatal .kernelFault }
        | .user =>
            let subject := state.context.currentSubject
            { state := { state with lifecycle :=
                SubjectLifecycle.terminateState state.lifecycle subject }
              action := .contained subject }
    | some .timer => { state, action := .timer }
    | some .syscall =>
        match frame.savedPrivilege with
        | .kernel => { state, action := .rejected .wrongOrigin }
        | .user =>
            if validUserReturn frame then { state, action := .resume }
            else { state, action := .rejected .malformedReturn }

/-- Register contents are deliberately erased before trusted classification. -/
def dispatch (state : State) (trap : Trap) : Outcome :=
  dispatchHardware state trap.hardware

theorem decodeVector_deterministic raw first second
    (hfirst : decodeVector raw = some first) (hsecond : decodeVector raw = some second) :
    first = second := by
  rw [hfirst] at hsecond
  exact Option.some.inj hsecond

theorem attacker_registers_cannot_change_dispatch state frame first second :
    dispatch state { hardware := frame, registers := first } =
      dispatch state { hardware := frame, registers := second } := by
  rfl

theorem dispatchHardware_preserves_trusted_context state frame :
    (dispatchHardware state frame).state.context = state.context := by
  unfold dispatchHardware
  by_cases hentry : state.context.entryActive
  · simp [hentry]
  · simp only [hentry, Bool.false_eq_true, ↓reduceIte]
    cases hvector : decodeVector frame.vector with
    | none => simp [hvector]
    | some vector =>
      cases vector with
      | pageFault => cases frame.savedPrivilege <;> simp [hvector]
      | timer => simp [hvector]
      | syscall =>
        cases frame.savedPrivilege
        · simp [hvector]
        · simp only [hvector]
          by_cases hvalid : validUserReturn frame = true <;> simp [hvalid]

theorem attacker_registers_cannot_change_trusted_context state frame registers :
    (dispatch state { hardware := frame, registers }).state.context = state.context := by
  exact dispatchHardware_preserves_trusted_context state frame

theorem dispatch_preserves_invariant_or_fatal state trap (hstate : WellFormed state) :
    WellFormed (dispatch state trap).state ∨
      ∃ reason, (dispatch state trap).action = .fatal reason := by
  unfold dispatch dispatchHardware
  split
  · exact Or.inr ⟨.nestedEntry, rfl⟩
  · cases hvector : decodeVector trap.hardware.vector with
    | none => simp [hvector]
    | some vector =>
      cases vector with
      | pageFault =>
        cases trap.hardware.savedPrivilege with
        | kernel => exact Or.inr ⟨.kernelFault, by simp [hvector]⟩
        | user =>
          simp [hvector]
          exact SubjectLifecycle.terminateState_preserves_wellFormed
            state.lifecycle state.context.currentSubject hstate
      | timer => simpa [hvector] using hstate
      | syscall =>
        cases trap.hardware.savedPrivilege
        · simp [hvector, hstate]
        · cases hreturn : validUserReturn trap.hardware <;> simp [hvector, hreturn, hstate]

theorem user_page_fault_contained state frame
    (hnested : state.context.entryActive = false)
    (hvector : frame.vector = 14) (horigin : frame.savedPrivilege = .user) :
    (dispatchHardware state frame).action = .contained state.context.currentSubject := by
  simp [dispatchHardware, hnested, hvector, decodeVector, horigin]

theorem kernel_page_fault_is_fatal state frame
    (hnested : state.context.entryActive = false)
    (hvector : frame.vector = 14) (horigin : frame.savedPrivilege = .kernel) :
    (dispatchHardware state frame).action = .fatal .kernelFault := by
  simp [dispatchHardware, hnested, hvector, decodeVector, horigin]

theorem unsupported_vector_is_fatal state frame
    (hnested : state.context.entryActive = false)
    (hvector : decodeVector frame.vector = none) :
    (dispatchHardware state frame).action = .fatal .unsupportedVector := by
  simp [dispatchHardware, hnested, hvector]

theorem timer_preserves_state state frame
    (hnested : state.context.entryActive = false)
    (hvector : frame.vector = 32) :
    dispatchHardware state frame = { state, action := .timer } := by
  simp [dispatchHardware, hnested, hvector, decodeVector]

theorem kernel_syscall_has_wrong_origin state frame
    (hnested : state.context.entryActive = false)
    (hvector : frame.vector = 128) (horigin : frame.savedPrivilege = .kernel) :
    (dispatchHardware state frame).action = .rejected .wrongOrigin := by
  simp [dispatchHardware, hnested, hvector, decodeVector, horigin]

theorem contained_fault_terminates_only_current_memory state frame object owner physicalFrame
    (hnested : state.context.entryActive = false)
    (hvector : frame.vector = 14) (horigin : frame.savedPrivilege = .user)
    (hmemory : state.lifecycle.ownedMemory object = some (owner, physicalFrame))
    (hunrelated : owner ≠ state.context.currentSubject) :
    (dispatchHardware state frame).state.lifecycle.ownedMemory object =
      some (owner, physicalFrame) := by
  simp [dispatchHardware, hnested, hvector, decodeVector, horigin]
  exact SubjectLifecycle.unrelated_memory_unchanged state.lifecycle
    state.context.currentSubject object owner physicalFrame hmemory hunrelated

theorem contained_fault_preserves_unrelated_authority state frame holder slot capability
    (hnested : state.context.entryActive = false)
    (hvector : frame.vector = 14) (horigin : frame.savedPrivilege = .user)
    (hholder : holder ≠ state.context.currentSubject)
    (hslot : state.lifecycle.capabilities.slots holder slot = some capability)
    (hmemory : (state.lifecycle.ownedMemory capability.object).any
      (fun owner => owner.1 = state.context.currentSubject) = false)
    (hendpoint : state.lifecycle.endpointOwner capability.object ≠
      some state.context.currentSubject) :
    (dispatchHardware state frame).state.lifecycle.capabilities.slots holder slot =
      some capability := by
  simp [dispatchHardware, hnested, hvector, decodeVector, horigin,
    SubjectLifecycle.terminateState, SubjectLifecycle.terminatedCapabilities,
    hholder, hslot, hmemory, hendpoint]

theorem contained_fault_preserves_unrelated_mapping state frame addressSpace page owner
    (hnested : state.context.entryActive = false)
    (hvector : frame.vector = 14) (horigin : frame.savedPrivilege = .user)
    (howner : state.lifecycle.addressOwner addressSpace = some owner)
    (hunrelated : owner ≠ state.context.currentSubject) :
    (dispatchHardware state frame).state.lifecycle.mapping addressSpace page =
      state.lifecycle.mapping addressSpace page := by
  simp [dispatchHardware, hnested, hvector, decodeVector, horigin,
    SubjectLifecycle.terminateState, howner, hunrelated]

theorem contained_fault_preserves_unrelated_frame state frame physicalFrame owner
    (hnested : state.context.entryActive = false)
    (hvector : frame.vector = 14) (horigin : frame.savedPrivilege = .user)
    (howner : state.lifecycle.frameOwner physicalFrame = some owner)
    (hunrelated : owner ≠ state.context.currentSubject) :
    (dispatchHardware state frame).state.lifecycle.frameOwner physicalFrame = some owner ∧
    (dispatchHardware state frame).state.lifecycle.freeFrame physicalFrame =
      state.lifecycle.freeFrame physicalFrame := by
  simp [dispatchHardware, hnested, hvector, decodeVector, horigin,
    SubjectLifecycle.terminateState, howner, hunrelated]

theorem contained_fault_preserves_unrelated_endpoint state frame object owner
    (hnested : state.context.entryActive = false)
    (hvector : frame.vector = 14) (horigin : frame.savedPrivilege = .user)
    (howner : state.lifecycle.endpointOwner object = some owner)
    (hunrelated : owner ≠ state.context.currentSubject) :
    (dispatchHardware state frame).state.lifecycle.endpointOwner object = some owner ∧
    (dispatchHardware state frame).state.lifecycle.mailbox object =
      match state.lifecycle.mailbox object with
      | some message =>
          if message.sender = state.context.currentSubject then none else some message
      | none => none := by
  simp [dispatchHardware, hnested, hvector, decodeVector, horigin,
    SubjectLifecycle.terminateState, howner, hunrelated]
  rfl

theorem malformed_return_cannot_resume state frame
    (hmalformed : validUserReturn frame = false) :
    (dispatchHardware state frame).action ≠ .resume := by
  unfold dispatchHardware
  split <;> simp
  next =>
    cases hvector : decodeVector frame.vector with
    | none => simp [hvector]
    | some vector =>
      cases vector with
      | pageFault => cases frame.savedPrivilege <;> simp [hvector]
      | timer => simp [hvector]
      | syscall => cases frame.savedPrivilege <;> simp [hvector, hmalformed]

theorem resume_requires_safe_user_frame state frame
    (hresume : (dispatchHardware state frame).action = .resume) :
    validUserReturn frame = true ∧
      frame.savedPrivilege = .user ∧ frame.codeSelector = 0x1b ∧
      frame.stackSelector = 0x23 ∧ frame.canonicalInstructionPointer = true ∧
      frame.canonicalStackPointer = true ∧ frame.flagsAllowed = true := by
  unfold dispatchHardware at hresume
  split at hresume <;> simp_all
  next =>
    cases hvector : decodeVector frame.vector with
    | none => simp [hvector] at hresume
    | some vector =>
      cases vector with
      | pageFault =>
        cases hprivilege : frame.savedPrivilege <;> simp [hvector, hprivilege] at hresume
      | timer => simp [hvector] at hresume
      | syscall =>
        by_cases hkernel : frame.savedPrivilege = .kernel
        · simp [hvector, hkernel] at hresume
        · have horigin : frame.savedPrivilege = .user := by
            have hcases : frame.savedPrivilege = .kernel ∨
                frame.savedPrivilege = .user := by
              cases frame.savedPrivilege
              · exact Or.inl rfl
              · exact Or.inr rfl
            exact hcases.resolve_left hkernel
          by_cases hvalid : validUserReturn frame = true
          · have hfields := hvalid
            simp [validUserReturn, horigin] at hfields
            exact ⟨hvalid, horigin, hfields.1.1.1.1, hfields.1.1.1.2,
              hfields.1.1.2, hfields.1.2, hfields.2⟩
          · simp [hvector, horigin, hvalid] at hresume

theorem resume_preserves_trusted_subject state frame
    (_hresume : (dispatchHardware state frame).action = .resume) :
    (dispatchHardware state frame).state.context.currentSubject =
      state.context.currentSubject := by
  exact congrArg (fun context => context.currentSubject)
    (dispatchHardware_preserves_trusted_context state frame)

theorem fatal_cannot_resume_as_other_subject state frame reason
    (hfatal : (dispatchHardware state frame).action = .fatal reason) :
    (dispatchHardware state frame).action ≠ .resume := by
  rw [hfatal]
  simp

private def registers : AttackerRegisters := ⟨1, 2, 3, 4⟩
private def frame (vector : Nat) (origin : Privilege) : HardwareFrame :=
  { vector, errorCode := 0, savedPrivilege := origin,
    instructionPointer := 0x400000, stackPointer := 0x500000,
    codeSelector := 0x1b, stackSelector := 0x23, flags := 2,
    canonicalInstructionPointer := true, canonicalStackPointer := true,
    flagsAllowed := true }
private def context : TrustedContext := ⟨1, 11, 0x800000, false⟩
private def modelState (lifecycle : SubjectLifecycle.State) : State := ⟨lifecycle, context⟩

example (lifecycle : SubjectLifecycle.State) :
    (dispatch (modelState lifecycle) ⟨frame 14 .user, registers⟩).action = .contained 1 := by
  simp [dispatch, dispatchHardware, modelState, context, frame, decodeVector]
example (lifecycle : SubjectLifecycle.State) :
    (dispatch (modelState lifecycle) ⟨frame 14 .kernel, registers⟩).action =
      .fatal .kernelFault := by simp [dispatch, dispatchHardware, modelState, context, frame, decodeVector]
example (lifecycle : SubjectLifecycle.State) :
    (dispatch (modelState lifecycle) ⟨frame 77 .user, registers⟩).action =
      .fatal .unsupportedVector := by simp [dispatch, dispatchHardware, modelState, context, frame, decodeVector]
example (lifecycle : SubjectLifecycle.State) :
    (dispatch (modelState lifecycle) ⟨frame 32 .user, registers⟩).action = .timer := by
  simp [dispatch, dispatchHardware, modelState, context, frame, decodeVector]
example (lifecycle : SubjectLifecycle.State) :
    (dispatch (modelState lifecycle) ⟨frame 128 .user, registers⟩).action = .resume := by
  simp [dispatch, dispatchHardware, modelState, context, frame, decodeVector, validUserReturn]
example (lifecycle : SubjectLifecycle.State) :
    (dispatch (modelState lifecycle) ⟨frame 128 .kernel, registers⟩).action =
      .rejected .wrongOrigin := by
  simp [dispatch, dispatchHardware, modelState, context, frame, decodeVector]
example (lifecycle : SubjectLifecycle.State) :
    let malformed := { frame 128 .user with codeSelector := 0x8 }
    (dispatch (modelState lifecycle) ⟨malformed, registers⟩).action =
      .rejected .malformedReturn := by
  simp [dispatch, dispatchHardware, modelState, context, frame, decodeVector, validUserReturn]
example (lifecycle : SubjectLifecycle.State) :
    let malformed := { frame 128 .user with flagsAllowed := false }
    (dispatch (modelState lifecycle) ⟨malformed, registers⟩).action =
      .rejected .malformedReturn := by
  simp [dispatch, dispatchHardware, modelState, context, frame, decodeVector, validUserReturn]
example (lifecycle : SubjectLifecycle.State) :
    let nested := { modelState lifecycle with context := { context with entryActive := true } }
    (dispatch nested ⟨frame 32 .user, registers⟩).action = .fatal .nestedEntry := by
  simp [dispatch, dispatchHardware, modelState, context, frame]

end LeanOS.Interrupt
