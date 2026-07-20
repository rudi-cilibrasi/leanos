import LeanOS.ExtendedState
import LeanOS.FailStop

/-!
# Fail-closed fast privilege-entry control

This finite Phase 2 model makes the manifest-backed `int 0x80` gate the only
authorized user-to-kernel system-call mechanism.  It models the selected CPU
contract, the relevant fast-entry MSRs, kernel-owned initialization/read-back,
normalized denial events, and a wrapper around the authoritative composite
operation gate.  CPUID/MSR reads and writes, instruction and exception
semantics, assembly, generated code, and the final binary remain trusted or
tested boundaries rather than theorem claims.
-/
namespace LeanOS.PrivilegeEntryControl

abbrev SubjectId := Nat
abbrev AddressSpaceId := Nat
abbrev Cr3 := Nat

inductive Vendor where
  | intel | amd | unsupported
  deriving BEq, DecidableEq, Repr

inductive Mode where
  | protected32 | long64 | compatibility
  deriving BEq, DecidableEq, Repr

/-- Finite CPUID/vendor projection used by this policy.  The concrete machine
adapter must populate it from the selected CPU before the first user return. -/
structure CpuContract where
  vendor : Vendor
  mode : Mode
  syscallExposed : Bool
  sysenterExposed : Bool
  deriving BEq, DecidableEq, Repr

/-- The pinned Phase 2 contract.  `amd` names the vendor string exposed by the
reviewed QEMU `-cpu max` configuration; it is not a statement about all AMD
processors. -/
def selectedCpu : CpuContract :=
  { vendor := .amd, mode := .long64, syscallExposed := true,
    sysenterExposed := true }

/-- Complete modeled projection of EFER and the fast-entry target MSRs.  The
reserved portions of the physical registers are outside this finite model and
must be checked by the machine adapter's masks. -/
structure MsrState where
  eferLme : Bool
  eferLma : Bool
  eferNxe : Bool
  eferSce : Bool
  star : UInt64
  lstar : UInt64
  cstar : UInt64
  sfmask : UInt64
  sysenterCs : UInt64
  sysenterEsp : UInt64
  sysenterEip : UInt64
  deriving BEq, DecidableEq, Repr

/-- Fail-closed recipe: preserve the required long-mode/NX state, clear SCE,
and clear every unused fast-entry target.  Zero SYSENTER_CS is the modeled
denial configuration; the other zero targets prevent stale inherited values
from being mistaken for reviewed state. -/
def deniedMsrs : MsrState :=
  { eferLme := true, eferLma := true, eferNxe := true, eferSce := false
    star := 0, lstar := 0, cstar := 0, sfmask := 0
    sysenterCs := 0, sysenterEsp := 0, sysenterEip := 0 }

/-- `writesComplete` and `readbackMatches` distinguish kernel-produced state
from coincidental firmware/reset values. -/
structure BootEvidence where
  writesComplete : Bool
  readbackMatches : Bool
  deriving BEq, DecidableEq, Repr

structure ControlState where
  cpu : CpuContract
  msrs : MsrState
  boot : BootEvidence
  extendedFeatures : ExtendedState.Features
  extendedControls : ExtendedState.ControlState
  int80ManifestPresent : Bool
  deriving BEq, DecidableEq, Repr

def reviewedExtendedFeatures : ExtendedState.Features :=
  { x87 := true, mmx := true, sse := true, sse2 := true,
    xsave := true, avx := true }

def acceptedControl : ControlState :=
  { cpu := selectedCpu
    msrs := deniedMsrs
    boot := { writesComplete := true, readbackMatches := true }
    extendedFeatures := reviewedExtendedFeatures
    extendedControls := ExtendedState.deniedControls
    int80ManifestPresent := true }

/-- One coherent CPU-control snapshot composes the fast-entry contract with
the completed extended-state denial contract instead of creating competing
boot policies. -/
def Accepted (control : ControlState) : Prop :=
  control.cpu = selectedCpu ∧
    control.msrs = deniedMsrs ∧
    control.boot.writesComplete = true ∧
    control.boot.readbackMatches = true ∧
    control.int80ManifestPresent = true ∧
    ExtendedState.Denied control.extendedFeatures control.extendedControls

def validate (control : ControlState) : Bool :=
  decide (control.cpu = selectedCpu) &&
    decide (control.msrs = deniedMsrs) &&
    control.boot.writesComplete && control.boot.readbackMatches &&
    control.int80ManifestPresent &&
    ExtendedState.validatePolicy control.extendedFeatures control.extendedControls

theorem validate_accepted_iff control :
    validate control = true ↔ Accepted control := by
  simp [validate, Accepted, ExtendedState.validatePolicy_accepted_iff, and_assoc]

theorem validate_total control : ∃ result, validate control = result := ⟨_, rfl⟩

theorem validate_deterministic control first second
    (hfirst : validate control = first) (hsecond : validate control = second) :
    first = second := by
  rw [← hfirst, hsecond]

inductive Mechanism where
  | int80 | syscall | sysenter
  deriving BEq, DecidableEq, Repr

/-- Mechanism enablement is a finite authorization view, not an instruction
semantics theorem. -/
def enabled (control : ControlState) : Mechanism → Bool
  | .int80 => control.int80ManifestPresent
  | .syscall => control.cpu.syscallExposed && control.msrs.eferSce
  | .sysenter => control.cpu.sysenterExposed &&
      control.cpu.mode != .long64 && control.msrs.sysenterCs != 0

/-- Every accepted state authorizes exactly the reviewed manifest entry among
the modeled system-call mechanisms. -/
theorem accepted_exactly_int80 control (haccepted : Accepted control) mechanism :
    enabled control mechanism = decide (mechanism = .int80) := by
  rcases haccepted with ⟨hcpu, hmsrs, _, _, hmanifest, _⟩
  cases mechanism <;>
    simp [enabled, hcpu, hmsrs, hmanifest, selectedCpu, deniedMsrs]

inductive Origin where
  | user | kernel
  deriving BEq, DecidableEq, Repr

inductive StackIdentity where
  | ordinaryEntry | userOwned | otherKernel
  deriving BEq, DecidableEq, Repr

def expectedVector (cpu : CpuContract) : Mechanism → Nat
  | .syscall => 6
  | .sysenter => if cpu.vendor = .amd && cpu.mode = .long64 then 6 else 13
  | .int80 => 128

structure State where
  control : ControlState
  currentSubject : SubjectId
  activeAddressSpace : AddressSpaceId
  activeCr3 : Cr3
  addressOwner : AddressSpaceId → Option SubjectId
  addressCr3 : AddressSpaceId → Option Cr3
  halted : Bool := false

def ContextBound (state : State) : Prop :=
  state.addressOwner state.activeAddressSpace = some state.currentSubject ∧
    state.addressCr3 state.activeAddressSpace = some state.activeCr3

/-- The entry normalizer supplies these fields from hardware plus protected
kernel context.  Opcode bytes and saved registers are intentionally absent. -/
structure DenialEvent where
  mechanism : Mechanism
  vector : Nat
  errorCode : UInt64
  origin : Origin
  normalizedSubject : SubjectId
  normalizedAddressSpace : AddressSpaceId
  normalizedCr3 : Cr3
  stackIdentity : StackIdentity
  reachedAlternateTarget : Bool
  liveControl : ControlState
  deriving Repr

structure AttackerPayload where
  words : List UInt64
  deriving DecidableEq, Repr

inductive FatalReason where
  | policyMismatch | liveControlMismatch | ordinaryMechanism
  | unexpectedVector | unexpectedError | kernelAttempt
  | staleContext | untrustedStack | alternateTargetReached
  deriving DecidableEq, Repr

inductive Result where
  | denied (subject : SubjectId)
  | returnAllowed (subject : SubjectId)
  | fatal (reason : FatalReason)
  | alreadyFatal
  deriving DecidableEq, Repr

structure Outcome where
  state : State
  result : Result

def fatal (state : State) (reason : FatalReason) : Outcome :=
  { state := { state with halted := true }, result := .fatal reason }

/-- Total denial classifier.  Containment is possible only after the disabled
instruction has reached its reviewed #UD/#GP gate without executing an
alternate CPL0 target or consuming a non-kernel entry stack. -/
def classify (state : State) (event : DenialEvent) : Outcome :=
  if state.halted then { state, result := .alreadyFatal }
  else if !validate state.control then fatal state .policyMismatch
  else if decide (event.liveControl ≠ state.control) then fatal state .liveControlMismatch
  else if event.mechanism = .int80 then fatal state .ordinaryMechanism
  else if event.vector != expectedVector state.control.cpu event.mechanism then
    fatal state .unexpectedVector
  else if event.errorCode != 0 then fatal state .unexpectedError
  else if event.origin = .kernel then fatal state .kernelAttempt
  else if event.reachedAlternateTarget then fatal state .alternateTargetReached
  else if decide (event.stackIdentity ≠ .ordinaryEntry) then fatal state .untrustedStack
  else if event.normalizedSubject != state.currentSubject ||
      event.normalizedAddressSpace != state.activeAddressSpace ||
      event.normalizedCr3 != state.activeCr3 ||
      state.addressOwner state.activeAddressSpace != some state.currentSubject ||
      state.addressCr3 state.activeAddressSpace != some state.activeCr3 then
    fatal state .staleContext
  else { state, result := .denied state.currentSubject }

def classifyWithPayload (state : State) (event : DenialEvent)
    (_payload : AttackerPayload) : Outcome := classify state event

theorem attacker_payload_erasure state event left right :
    classifyWithPayload state event left = classifyWithPayload state event right := rfl

theorem classify_total state event : ∃ outcome, classify state event = outcome := ⟨_, rfl⟩

theorem classify_deterministic state event first second
    (hfirst : classify state event = first)
    (hsecond : classify state event = second) : first = second := by
  rw [← hfirst, hsecond]

/-- A contained alternate-instruction denial names only the authoritative
current subject and requires the exact recorded/live policy and entry binding. -/
theorem denied_subject_confined state event subject
    (h : (classify state event).result = .denied subject) :
    subject = state.currentSubject ∧
      Accepted state.control ∧
      event.liveControl = state.control ∧
      event.mechanism ≠ .int80 ∧
      event.vector = expectedVector state.control.cpu event.mechanism ∧
      event.errorCode = 0 ∧
      event.origin = .user ∧
      event.reachedAlternateTarget = false ∧
      event.stackIdentity = .ordinaryEntry ∧
      event.normalizedSubject = state.currentSubject ∧
      event.normalizedAddressSpace = state.activeAddressSpace ∧
      event.normalizedCr3 = state.activeCr3 ∧
      ContextBound state := by
  unfold classify at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i hpolicy
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h
  simp only [Bool.not_eq_true] at hpolicy
  have hvalid : validate state.control = true := by
    cases hv : validate state.control <;> simp_all
  have haccepted := (validate_accepted_iff state.control).mp hvalid
  cases horigin : event.origin
  · simp_all [ContextBound]
  · simp_all

theorem kernel_attempt_never_contained state event subject
    (horigin : event.origin = .kernel) :
    (classify state event).result ≠ .denied subject := by
  intro h
  have confined := denied_subject_confined state event subject h
  simp_all

theorem alternate_target_never_contained state event subject
    (hreached : event.reachedAlternateTarget = true) :
    (classify state event).result ≠ .denied subject := by
  intro h
  have confined := denied_subject_confined state event subject h
  simp_all

theorem user_stack_never_contained state event subject
    (hstack : event.stackIdentity = .userOwned) :
    (classify state event).result ≠ .denied subject := by
  intro h
  have confined := denied_subject_confined state event subject h
  simp_all

theorem already_fatal_absorbing state event (hhalted : state.halted = true) :
    classify state event = { state, result := .alreadyFatal } := by
  simp [classify, hhalted]

/-- The sole outbound user-return authorization also depends on the exact
kernel-produced and freshly read-back entry-control state. -/
def armUserReturn (state : State) (liveControl : ControlState) : Outcome :=
  if state.halted then { state, result := .alreadyFatal }
  else if !validate state.control then fatal state .policyMismatch
  else if decide (liveControl ≠ state.control) then fatal state .liveControlMismatch
  else if state.addressOwner state.activeAddressSpace != some state.currentSubject ||
      state.addressCr3 state.activeAddressSpace != some state.activeCr3 then
    fatal state .staleContext
  else { state, result := .returnAllowed state.currentSubject }

theorem return_allowed_requires_single_entry state live subject
    (h : (armUserReturn state live).result = .returnAllowed subject) :
    subject = state.currentSubject ∧ Accepted state.control ∧
      live = state.control ∧ ContextBound state := by
  unfold armUserReturn at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i hpolicy
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h
  simp only [Bool.not_eq_true] at hpolicy
  have hvalid : validate state.control = true := by
    cases hv : validate state.control <;> simp_all
  exact ⟨rfl, (validate_accepted_iff _).mp hvalid, by simp_all,
    by simp_all [ContextBound]⟩

/-! ## Authoritative composite-operation preservation -/

structure CompositeRuntimeState where
  control : ControlState
  liveControl : ControlState
  composite : FailStop.CompositeState
  policyHalted : Bool := false

def CompositePolicyInvariant (state : CompositeRuntimeState) : Prop :=
  Accepted state.control ∧ state.liveControl = state.control

inductive CompositeGateResult where
  | published (result : FailStop.GateResult)
  | fatal (reason : FatalReason)
  | alreadyFatal
  deriving DecidableEq, Repr

structure CompositeGateOutcome where
  state : CompositeRuntimeState
  result : CompositeGateResult

private def haltComposite (state : CompositeRuntimeState)
    (reason : FatalReason) : CompositeGateOutcome :=
  { state := { state with policyHalted := true }, result := .fatal reason }

/-- Fast-entry control state is not part of any operation payload.  Every
interrupt, return, syscall, preemption, IPC, capability, mapping, lifecycle,
and scheduler step crosses this prefix before `FailStop.gate`. -/
def compositeGate (state : CompositeRuntimeState)
    (operation : FailStop.Operation) : CompositeGateOutcome :=
  if state.policyHalted then { state, result := .alreadyFatal }
  else if !validate state.control then haltComposite state .policyMismatch
  else if decide (state.liveControl ≠ state.control) then
    haltComposite state .liveControlMismatch
  else
    let outcome := FailStop.gate state.composite operation
    { state := { state with composite := outcome.state }
      result := .published outcome.result }

theorem compositeGate_published_requires_single_entry state operation result
    (h : (compositeGate state operation).result = .published result) :
    CompositePolicyInvariant state := by
  unfold compositeGate at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i hpolicy
  split at h <;> try contradiction
  simp only [Bool.not_eq_true] at hpolicy
  have hvalid : validate state.control = true := by
    cases hv : validate state.control <;> simp_all
  exact ⟨(validate_accepted_iff _).mp hvalid, by simp_all⟩

theorem accepted_composite_user_return_requires_single_entry state request
    (h : (compositeGate state (.userReturn request)).result =
      .published (.completed (.userReturn .accepted))) :
    CompositePolicyInvariant state :=
  compositeGate_published_requires_single_entry state (.userReturn request)
    (.completed (.userReturn .accepted)) h

theorem compositeGate_preserves_policy state operation
    (hinvariant : CompositePolicyInvariant state) :
    CompositePolicyInvariant (compositeGate state operation).state := by
  simp only [compositeGate]
  split <;> try exact hinvariant
  split <;> simp_all [haltComposite, CompositePolicyInvariant]

def runComposite (state : CompositeRuntimeState) :
    List FailStop.Operation → CompositeRuntimeState
  | [] => state
  | operation :: rest =>
    let outcome := compositeGate state operation
    match outcome.result with
    | .published _ => runComposite outcome.state rest
    | .fatal _ | .alreadyFatal => outcome.state

theorem runComposite_preserves_policy state operations
    (hinvariant : CompositePolicyInvariant state) :
    CompositePolicyInvariant (runComposite state operations) := by
  induction operations generalizing state with
  | nil => exact hinvariant
  | cons operation rest ih =>
      simp only [runComposite]
      generalize houtcome : compositeGate state operation = outcome
      cases outcome with
      | mk next result =>
          have hnext : CompositePolicyInvariant next := by
            have preserved := compositeGate_preserves_policy state operation hinvariant
            rw [houtcome] at preserved
            exact preserved
          cases result
          · exact ih next hnext
          · exact hnext
          · exact hnext

/-! ## Fixed-width generated boundary

The six-word adapter below is the finite evidence boundary used by the hosted
and boot oracle.  `cpuCode` selects the reviewed CPUID projection, while
`controlCode` selects the canonical read-back or one deliberately corrupted
field.  The remaining words select a validation/return/denial event and its
normalized vector, subject, and CR3 binding.  These scalar decoders are test
images of kernel-owned snapshots; they do not prove CPUID, MSR, or exception
semantics.
-/

def canonicalCpuCode : UInt64 := 1
def canonicalControlCode : UInt64 := 0

private def controlCpu (code : UInt64) : CpuContract :=
  if code = canonicalCpuCode then selectedCpu
  else if code = 2 then { selectedCpu with vendor := .intel }
  else if code = 3 then { selectedCpu with vendor := .unsupported }
  else if code = 4 then { selectedCpu with mode := .protected32 }
  else if code = 5 then { selectedCpu with mode := .compatibility }
  else if code = 6 then { selectedCpu with syscallExposed := false }
  else if code = 7 then { selectedCpu with sysenterExposed := false }
  else { selectedCpu with vendor := .unsupported }

private def controlMsrs (code : UInt64) : MsrState :=
  if code = 1 then { deniedMsrs with eferSce := true }
  else if code = 2 then { deniedMsrs with star := 0x8 }
  else if code = 3 then { deniedMsrs with lstar := 0x400000 }
  else if code = 4 then { deniedMsrs with cstar := 0x400000 }
  else if code = 5 then { deniedMsrs with sfmask := 0x200 }
  else if code = 6 then { deniedMsrs with sysenterCs := 0x8 }
  else if code = 7 then { deniedMsrs with sysenterEsp := 0x800000 }
  else if code = 8 then { deniedMsrs with sysenterEip := 0x400000 }
  else deniedMsrs

private def controlImage (cpuCode controlCode : UInt64) : ControlState :=
  { acceptedControl with
    cpu := controlCpu cpuCode
    msrs := controlMsrs controlCode
    boot :=
      { writesComplete := controlCode != 9
        readbackMatches := controlCode != 10 }
    int80ManifestPresent := controlCode != 11
    extendedControls := if controlCode = 12 then
      { ExtendedState.deniedControls with cr0Ts := false }
      else ExtendedState.deniedControls }

private def adapterState (cpuCode controlCode eventCode : UInt64) : State :=
  { control := controlImage cpuCode controlCode
    currentSubject := 1
    activeAddressSpace := 1
    activeCr3 := 1
    addressOwner := fun space => if space = 1 then some 1 else none
    addressCr3 := fun space => if space = 1 then some 1 else none
    halted := eventCode = 7 }

private def adapterEvent (state : State) (eventCode vector normalizedSubject
    normalizedCr3 : UInt64) : DenialEvent :=
  let mechanism := if eventCode = 3 || eventCode = 5 then .sysenter
    else if eventCode = 6 then .int80 else .syscall
  { mechanism
    vector := vector.toNat
    errorCode := if eventCode = 11 then 1 else 0
    origin := if eventCode = 4 || eventCode = 5 then .kernel else .user
    normalizedSubject := normalizedSubject.toNat
    normalizedAddressSpace := normalizedSubject.toNat
    normalizedCr3 := normalizedCr3.toNat
    stackIdentity := if eventCode = 10 then .userOwned else .ordinaryEntry
    reachedAlternateTarget := eventCode = 9
    liveControl := if eventCode = 8 then
      { state.control with msrs := { state.control.msrs with eferSce := true } }
      else state.control }

private def fatalReasonCode : FatalReason → UInt64
  | .policyMismatch => 1
  | .liveControlMismatch => 2
  | .ordinaryMechanism => 3
  | .unexpectedVector => 4
  | .unexpectedError => 5
  | .kernelAttempt => 6
  | .staleContext => 7
  | .untrustedStack => 8
  | .alternateTargetReached => 9

private def encodeAdapterOutcome (outcome : Outcome) : UInt64 :=
  match outcome.result with
  | .denied subject => 0xd000 + UInt64.ofNat subject
  | .returnAllowed subject => 0xa000 + UInt64.ofNat subject
  | .fatal reason => 0xf000 + fatalReasonCode reason
  | .alreadyFatal => 0xff00

/-- Model-facing expectation used to derive every shared-corpus result.  This
rich decoder deliberately remains separate from the exported scalar endpoint:
it constructs the authoritative structures and function-valued context maps
against which the finite corpus checks the generated boundary. -/
def controlModelExpected (cpuCode controlCode eventCode vector normalizedSubject
    normalizedCr3 : UInt64) : UInt64 :=
  let state := adapterState cpuCode controlCode eventCode
  if eventCode = 0 then if validate state.control then 1 else 0
  else if eventCode = 1 then encodeAdapterOutcome (armUserReturn state state.control)
  else encodeAdapterOutcome <| classify state <|
    adapterEvent state eventCode vector normalizedSubject normalizedCr3

/-- Allocation-free image of `validate (controlImage cpuCode controlCode)`.
Codes above the named mutation range select the unmodified control image, just
as `controlImage` does. -/
private def scalarControlAccepted (cpuCode controlCode : UInt64) : Bool :=
  cpuCode = canonicalCpuCode &&
    (controlCode = canonicalControlCode || 12 < controlCode)

/-- Allocation-free scalar decoder for hosted and freestanding linking.

The ordering mirrors `armUserReturn` and `classify`: an already-fatal state is
absorbing, policy/live-control failures precede event validation, and context
binding is checked last.  It uses only fixed-width comparisons and arithmetic;
the rich model above owns structure construction and supplies independent
finite-corpus expectations. -/
def controlScalar (cpuCode controlCode eventCode vector normalizedSubject
    normalizedCr3 : UInt64) : UInt64 :=
  if eventCode = 0 then
    if scalarControlAccepted cpuCode controlCode then 1 else 0
  else if eventCode = 1 then
    if scalarControlAccepted cpuCode controlCode then 0xa001 else 0xf001
  else if eventCode = 7 then 0xff00
  else if !scalarControlAccepted cpuCode controlCode then 0xf001
  else if eventCode = 8 then 0xf002
  else if eventCode = 6 then 0xf003
  else if vector != 6 then 0xf004
  else if eventCode = 11 then 0xf005
  else if eventCode = 4 || eventCode = 5 then 0xf006
  else if eventCode = 9 then 0xf009
  else if eventCode = 10 then 0xf008
  else if normalizedSubject != 1 || normalizedCr3 != 1 then 0xf007
  else 0xd001

@[export leanos_privilege_entry_control_demo]
def controlDemo (cpuCode controlCode eventCode vector normalizedSubject
    normalizedCr3 : UInt64) : UInt64 :=
  controlScalar cpuCode controlCode eventCode vector normalizedSubject normalizedCr3

theorem controlDemo_refines_scalar_all_inputs cpuCode controlCode eventCode vector
    normalizedSubject normalizedCr3 :
    controlDemo cpuCode controlCode eventCode vector normalizedSubject normalizedCr3 =
      controlScalar cpuCode controlCode eventCode vector normalizedSubject normalizedCr3 := rfl

theorem canonical_control_adapter_accepts :
    controlDemo canonicalCpuCode canonicalControlCode 0 0 0 0 = 1 := by
  native_decide

theorem contained_syscall_adapter_binds_authoritative_subject :
    controlDemo canonicalCpuCode canonicalControlCode 2 6 1 1 = 0xd001 := by
  native_decide

theorem contained_sysenter_adapter_binds_authoritative_subject :
    controlDemo canonicalCpuCode canonicalControlCode 3 6 1 1 = 0xd001 := by
  native_decide

/-- The completed lifecycle/context cleanup contract applies to the subject
selected by the confinement theorem; it cannot leave that subject live,
queued, current, or resumable. -/
theorem denial_cleanup_cannot_resume machine faulting :
    let cleaned := ResumablePreemption.cleanupSubject machine faulting
    cleaned.scheduler.lifecycle.capabilities.subjects faulting = false ∧
      faulting ∉ cleaned.scheduler.ready ∧
      cleaned.scheduler.lifecycle.current ≠ some faulting ∧
      ResumablePreemption.contextFor cleaned.contexts faulting = none := by
  exact ExtendedState.denial_cleanup_cannot_resume machine faulting

example : validate acceptedControl = true := by native_decide

example : enabled acceptedControl .int80 = true ∧
    enabled acceptedControl .syscall = false ∧
    enabled acceptedControl .sysenter = false := by native_decide

example : validate { acceptedControl with msrs :=
    { deniedMsrs with eferSce := true } } = false := by native_decide

example : validate { acceptedControl with msrs :=
    { deniedMsrs with lstar := 0x400000 } } = false := by native_decide

example : validate { acceptedControl with msrs :=
    { deniedMsrs with sysenterCs := 0x08 } } = false := by native_decide

example : validate { acceptedControl with boot :=
    { writesComplete := false, readbackMatches := true } } = false := by native_decide

end LeanOS.PrivilegeEntryControl
