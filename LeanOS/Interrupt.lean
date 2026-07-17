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
  | syscall
  | rejected (reason : RejectReason)
  | fatal (reason : FatalReason)
  deriving DecidableEq, Repr

structure Outcome where
  state : State
  action : Action

/-- Structural predicate for saved user frames used by the preemption model.
It is not an authorization to leave the kernel; outgoing returns use
`validateUserReturn`. -/
def validSavedUserFrame (frame : HardwareFrame) : Bool :=
  frame.savedPrivilege = .user && frame.codeSelector = 0x23 &&
    frame.stackSelector = 0x1b && frame.canonicalInstructionPointer &&
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

/-- A saved stack pointer may name the first byte beyond the mapped stack: it
is an empty-stack cursor, not a memory access.  Actual stack memory remains the
half-open interval recognized by `contains`. -/
def UserRegion.containsStackPointer (region : UserRegion) (address : UInt64) : Bool :=
  region.first ≤ address && address ≤ region.pastLast

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
  else if request.hardware.codeSelector != 0x23 || request.hardware.stackSelector != 0x1b then
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
  else if !request.stackRegion.containsStackPointer request.hardware.stackPointer then
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

/-! ## Fixed-width differential-oracle adapter

The oracle uses one synthetic live subject and address space so five scalar
words can exercise the complete return policy without exposing function-valued
model state at the ABI.  `mode` selects a kernel-owned purpose or one controlled
context corruption; the remaining words are the outgoing machine fields.
-/

private def oracleCanonical (address : UInt64) : Bool :=
  let high := address / 0x800000000000
  high = 0 || high = 0x1ffff

private def oracleFlag (flags divisor : UInt64) : Bool :=
  flags / divisor % 2 = 1

private def oracleFlagsAllowed (flags : UInt64) : Bool :=
  let arithmetic :=
    (if oracleFlag flags 0x1 then 0x1 else 0) +
    (if oracleFlag flags 0x4 then 0x4 else 0) +
    (if oracleFlag flags 0x10 then 0x10 else 0) +
    (if oracleFlag flags 0x40 then 0x40 else 0) +
    (if oracleFlag flags 0x80 then 0x80 else 0) +
    (if oracleFlag flags 0x800 then 0x800 else 0)
  flags = 0x202 + arithmetic

private def oracleLifecycle (mode : UInt64) : SubjectLifecycle.State :=
  { capabilities :=
      { subjects := fun subject => subject = 1 && mode != 8
        objects := fun _ => false
        kinds := fun _ => none
        slots := fun _ _ => none }
    issuedSubjects := fun subject => subject = 1
    ownedMemory := fun _ => none
    addressOwner := fun addressSpace =>
      if addressSpace = 11 && mode != 9 then some 1 else none
    mapping := fun _ _ => none
    endpointOwner := fun _ => none
    mailbox := fun _ => none
    frameOwner := fun _ => none
    freeFrame := fun _ => true
    runnable := fun subject => subject = 1 && mode != 8
    current := if mode = 8 then none else some 1 }

private def oraclePurpose (mode : UInt64) : ReturnPurpose :=
  if mode = 2 then .syscallResume
  else if mode = 3 then .schedulerRestore
  else if mode = 1 || (6 ≤ mode && mode ≤ 13) then .initialDispatch
  else .diagnosticKernelRecovery

private def oracleRequest (mode rip rsp selectors flags : UInt64) : UserReturnRequest :=
  { hardware :=
      { vector := 0
        errorCode := 0
        savedPrivilege := if mode = 7 then .kernel else .user
        instructionPointer := rip
        stackPointer := rsp
        codeSelector := selectors % 0x10000
        stackSelector := selectors / 0x10000
        flags
        canonicalInstructionPointer := oracleCanonical rip
        canonicalStackPointer := oracleCanonical rsp
        flagsAllowed := oracleFlagsAllowed flags }
    purpose := oraclePurpose mode
    frameSubject := if mode = 11 then 2 else 1
    frameAddressSpace := if mode = 12 then 12 else 11
    frameCr3 := if mode = 10 then 0x2000 else 0x1000
    expectedSubject := 1
    expectedAddressSpace := 11
    expectedCr3 := 0x1000
    executionMode := if mode = 6 then .halted else .running
    lifecycle := oracleLifecycle mode
    codeRegion := ⟨0x400000, 0x401000⟩
    stackRegion := ⟨0x500000, 0x501000⟩
    flags :=
      { interruptEnable := oracleFlag flags 0x200
        direction := oracleFlag flags 0x400
        alignmentCheck := oracleFlag flags 0x40000
        nestedTask := oracleFlag flags 0x4000
        virtual8086 := oracleFlag flags 0x20000
        ioPrivilegeLevel := flags / 0x1000 % 4
        reservedAllowed := oracleFlagsAllowed flags } }

/-- Consumption checks the field taken from the accepted attestation, rather
than re-reading a mutable outgoing frame. -/
def consumeValidatedInstructionPointer (request : UserReturnRequest)
    (consumedInstructionPointer : UInt64) : Bool :=
  match validateUserReturn request with
  | .accepted attested => attested.hardware.instructionPointer = consumedInstructionPointer
  | .rejected _ => false

private def oracleModelAccepts (request : UserReturnRequest) : Bool :=
  match validateUserReturn request with
  | .accepted _ => true
  | .rejected _ => false

private theorem oracleModelAccepts_iff (request : UserReturnRequest) :
    oracleModelAccepts request = true ↔
      validateUserReturn request = .accepted request := by
  constructor
  · intro haccepts
    unfold oracleModelAccepts at haccepts
    cases hvalidation : validateUserReturn request with
    | rejected reason => simp [hvalidation] at haccepts
    | accepted attested =>
        have hattested := accepted_attests_exact_request request attested hvalidation
        subst attested
        rfl
  · intro hvalidation
    simp [oracleModelAccepts, hvalidation]

/-- Allocation-free spelling of the same bounded request predicate, suitable
for the freestanding generated-code ABI. -/
private def oracleScalarAccepts (mode rip rsp selectors flags : UInt64) : Bool :=
  if !(mode = 1 || mode = 2 || mode = 3 || (6 ≤ mode && mode ≤ 13)) then false
  else if mode = 6 then false
  else if mode = 7 then false
  else if selectors % 0x10000 != 0x23 || selectors / 0x10000 != 0x1b then false
  else if !oracleCanonical rip || !oracleCanonical rsp then false
  else if !oracleFlagsAllowed flags || !oracleFlag flags 0x200 ||
      oracleFlag flags 0x400 || oracleFlag flags 0x40000 ||
      oracleFlag flags 0x4000 || oracleFlag flags 0x20000 ||
      flags / 0x1000 % 4 != 0 then false
  else if mode = 8 || mode = 11 then false
  else if mode = 9 || mode = 12 then false
  else if mode = 10 then false
  else if !(0x400000 ≤ rip && rip < 0x401000) then false
  else if !(0x500000 ≤ rsp && rsp ≤ 0x501000) then false
  else true

/-- Bounded generated-code adapter for shared Lean/host/boot differential
replay. Modes 1--3 are the boot-supported purposes; modes 6--12 inject one
policy failure; mode 13 validates a good request and then attempts to consume a
mutated RIP. Every other mode is total-to-rejection. -/
@[export leanos_user_return_demo]
def userReturnDemo (mode rip rsp selectors flags : UInt64) : UInt64 :=
  if mode = 13 then 0
  else if oracleScalarAccepts mode rip rsp selectors flags then 1 else 0

/-- Model-derived expectation used to generate the shared corpus.  This is
kept separate from the allocation-free exported adapter so hosted and boot
replay compare two independently evaluated paths. -/
def userReturnModelExpected (mode rip rsp selectors flags : UInt64) : UInt64 :=
  let request := oracleRequest mode rip rsp selectors flags
  if mode = 13 then
    if consumeValidatedInstructionPointer request (rip + 1) then 1 else 0
  else if oracleModelAccepts request then 1 else 0

theorem userReturnDemo_accepts_reviewed_purposes :
    userReturnDemo 1 0x400100 0x500ff8 0x1b0023 0x202 = 1 ∧
    userReturnDemo 2 0x400100 0x500ff8 0x1b0023 0x202 = 1 ∧
    userReturnDemo 3 0x400100 0x500ff8 0x1b0023 0x202 = 1 ∧
    oracleModelAccepts (oracleRequest 1 0x400100 0x500ff8 0x1b0023 0x202) ∧
    oracleModelAccepts (oracleRequest 2 0x400100 0x500ff8 0x1b0023 0x202) ∧
    oracleModelAccepts (oracleRequest 3 0x400100 0x500ff8 0x1b0023 0x202) := by
  native_decide

theorem userReturnDemo_rejects_mutated_consumption :
    userReturnDemo 13 0x400100 0x500ff8 0x1b0023 0x202 = 0 ∧
    consumeValidatedInstructionPointer
      (oracleRequest 13 0x400100 0x500ff8 0x1b0023 0x202) 0x400101 = false := by
  native_decide

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
        | .user => { state, action := .syscall }

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
        cases frame.savedPrivilege <;> simp [hvector]

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
        cases trap.hardware.savedPrivilege <;> simp [hvector, hstate]

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

theorem syscall_entry_requires_user_origin state frame
    (hsyscall : (dispatchHardware state frame).action = .syscall) :
    frame.savedPrivilege = .user := by
  unfold dispatchHardware at hsyscall
  split at hsyscall <;> simp_all
  next =>
    cases hvector : decodeVector frame.vector with
    | none => simp [hvector] at hsyscall
    | some vector =>
      cases vector with
      | pageFault => cases hprivilege : frame.savedPrivilege <;>
          simp [hvector, hprivilege] at hsyscall
      | timer => simp [hvector] at hsyscall
      | syscall =>
          cases hprivilege : frame.savedPrivilege with
          | kernel => simp [hvector, hprivilege] at hsyscall
          | user => rfl

theorem syscall_preserves_trusted_subject state frame
    (_hsyscall : (dispatchHardware state frame).action = .syscall) :
    (dispatchHardware state frame).state.context.currentSubject =
      state.context.currentSubject := by
  exact congrArg (fun context => context.currentSubject)
    (dispatchHardware_preserves_trusted_context state frame)

theorem fatal_cannot_be_syscall state frame reason
    (hfatal : (dispatchHardware state frame).action = .fatal reason) :
    (dispatchHardware state frame).action ≠ .syscall := by
  rw [hfatal]
  simp

private def registers : AttackerRegisters := ⟨1, 2, 3, 4⟩
private def frame (vector : Nat) (origin : Privilege) : HardwareFrame :=
  { vector, errorCode := 0, savedPrivilege := origin,
    instructionPointer := 0x400000, stackPointer := 0x500000,
    codeSelector := 0x23, stackSelector := 0x1b, flags := 2,
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
    (dispatch (modelState lifecycle) ⟨frame 128 .user, registers⟩).action = .syscall := by
  simp [dispatch, dispatchHardware, modelState, context, frame, decodeVector]
example (lifecycle : SubjectLifecycle.State) :
    (dispatch (modelState lifecycle) ⟨frame 128 .kernel, registers⟩).action =
      .rejected .wrongOrigin := by
  simp [dispatch, dispatchHardware, modelState, context, frame, decodeVector]
example (lifecycle : SubjectLifecycle.State) :
    let malformed := { frame 128 .user with codeSelector := 0x8 }
    (dispatch (modelState lifecycle) ⟨malformed, registers⟩).action = .syscall := by
  simp [dispatch, dispatchHardware, modelState, context, frame, decodeVector]
example (lifecycle : SubjectLifecycle.State) :
    let malformed := { frame 128 .user with flagsAllowed := false }
    (dispatch (modelState lifecycle) ⟨malformed, registers⟩).action = .syscall := by
  simp [dispatch, dispatchHardware, modelState, context, frame, decodeVector]
example (lifecycle : SubjectLifecycle.State) :
    let nested := { modelState lifecycle with context := { context with entryActive := true } }
    (dispatch nested ⟨frame 32 .user, registers⟩).action = .fatal .nestedEntry := by
  simp [dispatch, dispatchHardware, modelState, context, frame]

end LeanOS.Interrupt
