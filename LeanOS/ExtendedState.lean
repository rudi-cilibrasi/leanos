/-!
# Fail-closed user extended-state policy

This finite model denies x87, MMX, SSE/SSE2, and AVX to user subjects until
LeanOS has per-subject extended-state ownership.  CPUID/control-register reads,
instruction decoding, exception delivery, assembly, and the final binary are
trusted or tested boundaries, not theorem claims.
-/
namespace LeanOS.ExtendedState

abbrev SubjectId := Nat
abbrev AddressSpaceId := Nat

/-- The bounded CPUID projection relevant to the Phase 2 denial policy. -/
structure Features where
  x87 : Bool
  mmx : Bool
  sse : Bool
  sse2 : Bool
  xsave : Bool
  avx : Bool
  deriving BEq, DecidableEq, Repr

/-- Reject feature combinations that cannot describe the modeled dependency
chain.  This is a validation rule for the finite model, not a CPUID theorem. -/
def coherentFeatures (features : Features) : Bool :=
  (!features.sse2 || features.sse) &&
    (!features.avx || (features.xsave && features.sse))

/-- Exact live control-state snapshot.  `xcr0 = none` records that OSXSAVE is
clear, so the policy neither reads nor assigns meaning to XCR0. -/
structure ControlState where
  cr0Em : Bool
  cr0Mp : Bool
  cr0Ts : Bool
  cr4Osfxsr : Bool
  cr4Osxmmexcpt : Bool
  cr4Osxsave : Bool
  xcr0 : Option UInt64
  deriving BEq, DecidableEq, Repr

/-- Phase 2 denial contract: x87/MMX are trapped with EM/TS, legacy SIMD is
not OS-enabled, and XSAVE/AVX state is not OS-enabled. -/
def deniedControls : ControlState :=
  { cr0Em := true
    cr0Mp := true
    cr0Ts := true
    cr4Osfxsr := false
    cr4Osxmmexcpt := false
    cr4Osxsave := false
    xcr0 := none }

def Denied (features : Features) (controls : ControlState) : Prop :=
  coherentFeatures features = true ∧ controls = deniedControls

def validatePolicy (features : Features) (controls : ControlState) : Bool :=
  coherentFeatures features && decide (controls = deniedControls)

theorem validatePolicy_accepted_iff features controls :
    validatePolicy features controls = true ↔ Denied features controls := by
  simp [validatePolicy, Denied]

theorem validatePolicy_total features controls :
    ∃ accepted, validatePolicy features controls = accepted := by
  exact ⟨_, rfl⟩

theorem validatePolicy_deterministic features controls first second
    (hfirst : validatePolicy features controls = first)
    (hsecond : validatePolicy features controls = second) : first = second := by
  rw [← hfirst, hsecond]

inductive InstructionClass where
  | x87 | mmx | sse | sse2 | avx
  deriving BEq, DecidableEq, Repr

/-- Expected reviewed denial vector for one representative instruction.
Unavailable instruction families and families deliberately left OS-disabled
use #UD (6); available x87/MMX use the #NM (7) denial path. -/
def expectedVector (features : Features) : InstructionClass → Nat
  | .x87 => if features.x87 then 7 else 6
  | .mmx => if features.mmx then 7 else 6
  | .sse | .sse2 | .avx => 6

inductive Origin where | user | kernel
  deriving BEq, DecidableEq, Repr

/-- Kernel-owned identity and the live policy snapshot are authoritative. -/
structure State where
  features : Features
  controls : ControlState
  currentSubject : SubjectId
  activeAddressSpace : AddressSpaceId
  addressOwner : AddressSpaceId → Option SubjectId
  halted : Bool := false

def ContextBound (state : State) : Prop :=
  state.addressOwner state.activeAddressSpace = some state.currentSubject

/-- The normalized event carries bindings for stale-entry detection.  It does
not choose the subject that will be denied. -/
structure Event where
  instruction : InstructionClass
  vector : Nat
  origin : Origin
  normalizedSubject : SubjectId
  normalizedAddressSpace : AddressSpaceId
  deriving DecidableEq, Repr

/-- Explicitly attacker-controlled words are erased by `classifyWithPayload`. -/
structure AttackerPayload where
  words : List UInt64
  deriving DecidableEq, Repr

inductive FatalReason where
  | policyMismatch | unexpectedVector | kernelAttempt | staleContext
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

/-- Total typed classification.  Only a user event with the exact expected
vector, accepted live policy, and authoritative context binding is contained.
This first checkpoint does not perform lifecycle cleanup; issue #101 owns that
composition. -/
def classify (state : State) (event : Event) : Outcome :=
  if state.halted then { state, result := .alreadyFatal }
  else if !validatePolicy state.features state.controls then
    fatal state .policyMismatch
  else if event.vector != expectedVector state.features event.instruction then
    fatal state .unexpectedVector
  else if event.origin = .kernel then
    fatal state .kernelAttempt
  else if event.normalizedSubject != state.currentSubject ||
      event.normalizedAddressSpace != state.activeAddressSpace ||
      state.addressOwner state.activeAddressSpace != some state.currentSubject then
    fatal state .staleContext
  else
    { state, result := .denied state.currentSubject }

def classifyWithPayload (state : State) (event : Event)
    (_payload : AttackerPayload) : Outcome :=
  classify state event

theorem attacker_payload_erasure state event left right :
    classifyWithPayload state event left = classifyWithPayload state event right := by
  rfl

theorem classify_total state event : ∃ outcome, classify state event = outcome := by
  exact ⟨_, rfl⟩

theorem classify_deterministic state event first second
    (hfirst : classify state event = first)
    (hsecond : classify state event = second) : first = second := by
  rw [← hfirst, hsecond]

/-- A contained denial can name only the authoritative current subject and is
possible only under the exact accepted denial policy and live context. -/
theorem denied_subject_confined state event subject
    (h : (classify state event).result = .denied subject) :
    subject = state.currentSubject ∧
      Denied state.features state.controls ∧
      event.origin = .user ∧
      event.normalizedSubject = state.currentSubject ∧
      event.normalizedAddressSpace = state.activeAddressSpace ∧
      ContextBound state := by
  unfold classify at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i hpolicy
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i hkernel
  split at h <;> try contradiction
  cases h
  simp only [Bool.not_eq_true] at hpolicy
  have haccepted : validatePolicy state.features state.controls = true := by
    cases hv : validatePolicy state.features state.controls <;> simp_all
  have hdenied := (validatePolicy_accepted_iff state.features state.controls).mp haccepted
  have horigin : event.origin = .user := by
    cases horigin : event.origin
    · rfl
    · exact (hkernel horigin).elim
  simp_all [ContextBound]

theorem kernel_attempt_never_contained state event subject
    (horigin : event.origin = .kernel) :
    (classify state event).result ≠ .denied subject := by
  intro h
  have confined := denied_subject_confined state event subject h
  simp_all

theorem policy_mismatch_never_contained state event subject
    (hpolicy : validatePolicy state.features state.controls = false) :
    (classify state event).result ≠ .denied subject := by
  intro h
  have confined := denied_subject_confined state event subject h
  have accepted := (validatePolicy_accepted_iff state.features state.controls).mpr confined.2.1
  simp_all

theorem already_fatal_absorbing state event (hhalted : state.halted = true) :
    classify state event = { state, result := .alreadyFatal } := by
  simp [classify, hhalted]

/-- The common user-return gate may arm only while the exact denial policy and
authoritative address-space binding remain live. -/
def armUserReturn (state : State) : Outcome :=
  if state.halted then { state, result := .alreadyFatal }
  else if !validatePolicy state.features state.controls then
    fatal state .policyMismatch
  else if state.addressOwner state.activeAddressSpace != some state.currentSubject then
    fatal state .staleContext
  else { state, result := .returnAllowed state.currentSubject }

theorem return_allowed_requires_denial state subject
    (h : (armUserReturn state).result = .returnAllowed subject) :
    subject = state.currentSubject ∧ Denied state.features state.controls ∧ ContextBound state := by
  unfold armUserReturn at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i hpolicy
  split at h <;> try contradiction
  cases h
  simp only [Bool.not_eq_true] at hpolicy
  have haccepted : validatePolicy state.features state.controls = true := by
    cases hv : validatePolicy state.features state.controls <;> simp_all
  exact ⟨rfl, (validatePolicy_accepted_iff _ _).mp haccepted, by simp_all [ContextBound]⟩

/-! Executable non-vacuity and adversarial cases for the finite model. -/

def reviewedFeatures : Features :=
  { x87 := true, mmx := true, sse := true, sse2 := true, xsave := true, avx := true }

def reviewedState : State :=
  { features := reviewedFeatures
    controls := deniedControls
    currentSubject := 1
    activeAddressSpace := 1
    addressOwner := fun addressSpace => if addressSpace = 1 then some 1 else none }

def userX87 : Event :=
  { instruction := .x87, vector := 7, origin := .user
    normalizedSubject := 1, normalizedAddressSpace := 1 }

example : validatePolicy reviewedFeatures deniedControls = true := by native_decide
example : (classify reviewedState userX87).result = .denied 1 := by native_decide
example : (classify reviewedState { userX87 with vector := 6 }).result =
    .fatal .unexpectedVector := by native_decide
example : (classify reviewedState { userX87 with origin := .kernel }).result =
    .fatal .kernelAttempt := by native_decide
example : (classify reviewedState { userX87 with normalizedSubject := 2 }).result =
    .fatal .staleContext := by native_decide
example : validatePolicy reviewedFeatures { deniedControls with cr0Ts := false } = false := by
  native_decide
example : (armUserReturn { reviewedState with
    controls := { deniedControls with cr4Osxsave := true } }).result =
      .fatal .policyMismatch := by native_decide
example : coherentFeatures { reviewedFeatures with xsave := false } = false := by native_decide

end LeanOS.ExtendedState
