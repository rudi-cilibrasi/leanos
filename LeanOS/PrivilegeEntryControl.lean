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
    (h : (compositeGate state (.userReturn request)).result = .published .accepted) :
    CompositePolicyInvariant state :=
  compositeGate_published_requires_single_entry state (.userReturn request) .accepted h

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
