import LeanOS.ResumablePreemption
import LeanOS.FailStop

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
  | missingCurrent | dispatchInvariant
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
Lifecycle cleanup and peer dispatch are composed below through the authoritative
resumable-preemption state. -/
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

/-! ## Global composite-runtime policy

The denial controls wrap the authoritative `FailStop.gate`; they are not an
operation payload and cannot be rewritten by a syscall, timer, IPC, mapping,
capability, lifecycle, scheduler, or return operation.  A mismatch is latched
before the underlying composite gate runs, leaving its complete pre-state
untouched. -/

structure CompositeRuntimeState where
  features : Features
  controls : ControlState
  composite : FailStop.CompositeState
  policyHalted : Bool := false

def CompositePolicyInvariant (state : CompositeRuntimeState) : Prop :=
  Denied state.features state.controls

inductive CompositeGateResult where
  | published (result : FailStop.GateResult)
  | fatal (reason : FatalReason)
  | alreadyFatal
  deriving DecidableEq, Repr

structure CompositeGateOutcome where
  state : CompositeRuntimeState
  result : CompositeGateResult

private def haltCompositePolicy (state : CompositeRuntimeState)
    (reason : FatalReason) : CompositeGateOutcome :=
  { state := { state with policyHalted := true }, result := .fatal reason }

/-- Every authoritative composite operation first validates the live denial
controls.  The operation vocabulary is exactly `FailStop.Operation`, so this
single gate covers interrupt, return, syscall, preemption, IPC, capability,
mapping, lifecycle, and scheduler transitions. -/
def compositeGate (state : CompositeRuntimeState)
    (operation : FailStop.Operation) : CompositeGateOutcome :=
  if state.policyHalted then { state, result := .alreadyFatal }
  else if !validatePolicy state.features state.controls then
    haltCompositePolicy state .policyMismatch
  else
    let outcome := FailStop.gate state.composite operation
    { state := { state with composite := outcome.state }
      result := .published outcome.result }

theorem compositeGate_total state operation :
    ∃ outcome, compositeGate state operation = outcome := ⟨_, rfl⟩

theorem compositeGate_deterministic state operation first second
    (hfirst : compositeGate state operation = first)
    (hsecond : compositeGate state operation = second) : first = second := by
  rw [← hfirst, hsecond]

/-- A live policy mismatch exposes no partial subsystem transition. -/
theorem compositeGate_policy_mismatch_atomic state operation
    (hlive : state.policyHalted = false)
    (hmismatch : validatePolicy state.features state.controls = false) :
    compositeGate state operation =
      { state := { state with policyHalted := true }
        result := .fatal .policyMismatch } := by
  simp [compositeGate, hlive, hmismatch, haltCompositePolicy]

/-- Any nonfatal publication, including an accepted user return, implies the
exact denied feature/control predicate. -/
theorem compositeGate_published_requires_denial state operation result
    (hpublished : (compositeGate state operation).result = .published result) :
    CompositePolicyInvariant state := by
  unfold compositeGate at hpublished
  split at hpublished <;> try contradiction
  split at hpublished <;> try contradiction
  rename_i hpolicy
  simp only [Bool.not_eq_true] at hpolicy
  have haccepted : validatePolicy state.features state.controls = true := by
    cases hv : validatePolicy state.features state.controls <;> simp_all
  exact (validatePolicy_accepted_iff _ _).mp haccepted

theorem accepted_composite_user_return_requires_denial state request
    (haccepted : (compositeGate state (.userReturn request)).result =
      .published .accepted) :
    CompositePolicyInvariant state := by
  exact compositeGate_published_requires_denial state (.userReturn request) .accepted haccepted

/-- Once established, the global policy predicate is invariant under every
modeled composite operation; the wrapper changes only the composite projection
or the absorbing policy latch. -/
theorem compositeGate_preserves_policy state operation
    (hinvariant : CompositePolicyInvariant state) :
    CompositePolicyInvariant (compositeGate state operation).state := by
  simp only [compositeGate]
  split <;> try exact hinvariant
  split <;> simp_all [haltCompositePolicy, CompositePolicyInvariant]

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
    have hnext : CompositePolicyInvariant outcome.state := by
      rw [← houtcome]
      exact compositeGate_preserves_policy state operation hinvariant
    cases outcome.result <;> simp_all

/-! ## Authoritative cleanup and peer dispatch

The runtime composition does not introduce another lifecycle, ready queue, or
context bank.  It derives the classifier's trusted identity from
`ResumablePreemption.State`, applies its existing whole-subject cleanup, and
uses the existing scheduler head plus owned saved context for dispatch. -/

structure RuntimeState where
  features : Features
  controls : ControlState
  machine : ResumablePreemption.State

inductive DispatchResult where
  | dispatched (faulting : SubjectId) (restored : ResumablePreemption.Context)
  | idle (faulting : SubjectId)
  | fatal (reason : FatalReason)
  | alreadyFatal
  deriving DecidableEq, Repr

structure DispatchOutcome where
  state : RuntimeState
  result : DispatchResult

private def haltRuntime (state : RuntimeState) (reason : FatalReason) : DispatchOutcome :=
  { state := { state with machine := { state.machine with halted := true } }
    result := .fatal reason }

private def classifierState (state : RuntimeState) (current active : Nat) : State :=
  { features := state.features
    controls := state.controls
    currentSubject := current
    activeAddressSpace := active
    addressOwner := state.machine.scheduler.lifecycle.addressOwner }

/-- A normalized denial is one atomic cleanup-and-dispatch transition.  Every
failure before publication halts the original runtime state; no partially
cleaned state is exposed.  Empty survivor selection is a typed idle result. -/
private def dispatchDeniedCandidate (state : RuntimeState) (event : Event) : DispatchOutcome :=
  if state.machine.halted then { state, result := .alreadyFatal }
  else match state.machine.scheduler.lifecycle.current, state.machine.translations.active with
    | some current, some active =>
      match (classify (classifierState state current active) event).result with
      | .denied faulting =>
        let cleaned := ResumablePreemption.cleanupSubject state.machine faulting
        let selected := Scheduler.selectNext cleaned.scheduler
        match selected.result with
        | .rejected _ => haltRuntime state .dispatchInvariant
        | .accepted none =>
          { state := { state with machine := cleaned }, result := .idle faulting }
        | .accepted (some context) =>
          match ResumablePreemption.contextFor cleaned.contexts context.currentSubject with
          | none => haltRuntime state .dispatchInvariant
          | some restored =>
            if restored.owner != context.currentSubject ||
                restored.addressSpace != context.activeAddressSpace ||
                Interrupt.validSavedUserFrame restored.frame != true ||
                selected.state.lifecycle.capabilities.subjects restored.owner != true ||
                selected.state.lifecycle.runnable restored.owner != true ||
                selected.state.lifecycle.addressOwner restored.addressSpace != some restored.owner ||
                cleaned.translations.virtual.owner restored.addressSpace != some restored.owner then
              haltRuntime state .dispatchInvariant
            else
              { state := { state with machine := { cleaned with
                  scheduler := selected.state
                  contexts := ResumablePreemption.eraseContext cleaned.contexts restored.owner
                  translations := TLB.switch cleaned.translations restored.addressSpace } }
                result := .dispatched faulting restored }
      | .fatal reason => haltRuntime state reason
      | .alreadyFatal => { state, result := .alreadyFatal }
      | .returnAllowed _ => haltRuntime state .dispatchInvariant
    | _, _ => haltRuntime state .missingCurrent

/-- Fatal publication is centralized here so every rejected candidate exposes
the untouched pre-state plus only the absorbing halt latch. -/
def dispatchDenied (state : RuntimeState) (event : Event) : DispatchOutcome :=
  let candidate := dispatchDeniedCandidate state event
  match candidate.result with
  | .fatal reason => haltRuntime state reason
  | _ => candidate

theorem dispatchDenied_total state event :
    ∃ outcome, dispatchDenied state event = outcome := ⟨_, rfl⟩

theorem dispatchDenied_deterministic state event first second
    (hfirst : dispatchDenied state event = first)
    (hsecond : dispatchDenied state event = second) : first = second := by
  rw [← hfirst, hsecond]

/-- The authoritative cleanup primitive cannot retain any live, queued,
current, or resumable reference to the faulting subject.  `dispatchDenied`
publishes exactly this state before either idle or peer selection. -/
theorem denial_cleanup_cannot_resume machine faulting :
    let cleaned := ResumablePreemption.cleanupSubject machine faulting
    cleaned.scheduler.lifecycle.capabilities.subjects faulting = false ∧
      faulting ∉ cleaned.scheduler.ready ∧
      cleaned.scheduler.lifecycle.current ≠ some faulting ∧
      ResumablePreemption.contextFor cleaned.contexts faulting = none := by
  exact ⟨ResumablePreemption.cleanup_terminates_subject machine faulting,
    (ResumablePreemption.cleanup_removes_scheduler_membership machine faulting).1,
    (ResumablePreemption.cleanup_removes_scheduler_membership machine faulting).2,
    ResumablePreemption.cleanup_removes_context machine faulting⟩

/-- The restored tuple is selected only from the post-cleanup scheduler head
and its kernel-owned context bank entry. -/
theorem dispatched_peer_is_scheduler_selected state event faulting restored
    (h : (dispatchDenied state event).result = .dispatched faulting restored) :
    let cleaned := ResumablePreemption.cleanupSubject state.machine faulting
    ∃ selected,
      (Scheduler.selectNext cleaned.scheduler).result = .accepted (some selected) ∧
      ResumablePreemption.contextFor cleaned.contexts selected.currentSubject = some restored ∧
      restored.owner = selected.currentSubject ∧
      restored.addressSpace = selected.activeAddressSpace := by
  have hcandidate : (dispatchDeniedCandidate state event).result =
      .dispatched faulting restored := by
    unfold dispatchDenied at h
    generalize hc : dispatchDeniedCandidate state event = candidate at h
    cases candidate with
    | mk next result => cases result <;> simp_all [haltRuntime]
  simp only [dispatchDeniedCandidate] at hcandidate
  split at hcandidate <;> try contradiction
  next =>
    split at hcandidate <;> try contradiction
    next current active hcurrent hactive =>
      split at hcandidate <;> try contradiction
      next deniedSubject hclassified =>
        split at hcandidate <;> try contradiction
        next selected hselected =>
          split at hcandidate <;> try contradiction
          next destination hdestination =>
            split at hcandidate <;> try contradiction
            cases hcandidate
            exact ⟨selected, hselected, hdestination, by simp_all, by simp_all⟩

/-- Fatal classification or dispatch inconsistency never exposes a partial
cleanup; only the absorbing halt latch changes. -/
theorem dispatchDenied_fatal_atomic state event reason
    (h : (dispatchDenied state event).result = .fatal reason) :
    (dispatchDenied state event).state =
      { state with machine := { state.machine with halted := true } } := by
  unfold dispatchDenied at h ⊢
  generalize hc : dispatchDeniedCandidate state event = candidate
  cases candidate with
  | mk next result =>
    cases result <;> simp_all [haltRuntime]

/-! ## Fixed-width generated boundary

The adapter encodes the bounded runtime decision used by the C entry endpoint:
zero is fatal, one is idle after cleanup, and `0x100 + subject` is the exact
kernel-selected peer.  The leading policy word is derived from the live CPUID
and CR0/CR4 snapshot: only one means that the global denial wrapper may publish.
`mode` injects one reviewed policy/runtime corruption; the vector and normalized
bindings remain explicit inputs. -/

def denialDispatchModel (mode vector current active normalized : UInt64) : UInt64 :=
  if mode = 1 then 0
  else if (mode = 6 && vector != 6) || (mode != 6 && vector != 7) then 0
  else if mode = 2 then 0
  else if normalized != current || active != current then 0
  else if mode = 3 then 0
  else if mode = 4 then 1
  else 0x100 + (if current = 1 then 2 else 1)

/-- Scalar image of the global policy prefix.  This is deliberately separate
from the cleanup decision so the generated endpoint cannot publish a peer when
its live policy snapshot is stale or already fatal. -/
def denialMachineGateModel (policy mode vector current active normalized : UInt64) : UInt64 :=
  if policy = 1 then denialDispatchModel mode vector current active normalized else 0

/-- Encode the model-level global wrapper latch and live validator into the
single fixed-width word consumed by the generated machine gate. -/
def compositePolicyCode (state : CompositeRuntimeState) : UInt64 :=
  if state.policyHalted then 2
  else if validatePolicy state.features state.controls then 1
  else 0

/-- All-input refinement of the generated scalar policy prefix to the global
wrapper's exact latch/validator order.  The underlying cleanup scalar remains
the finite tested boundary documented above. -/
theorem denialMachineGate_refines_composite_policy_all_inputs
    (state : CompositeRuntimeState) mode vector current active normalized :
    denialMachineGateModel (compositePolicyCode state) mode vector current active normalized =
      if state.policyHalted then 0
      else if validatePolicy state.features state.controls then
        denialDispatchModel mode vector current active normalized
      else 0 := by
  cases hhalted : state.policyHalted <;>
    cases hpolicy : validatePolicy state.features state.controls <;>
    simp [denialMachineGateModel, compositePolicyCode, hhalted, hpolicy]

theorem denialMachineGate_policy_mismatch_fails_closed
    policy mode vector current active normalized
    (hpolicy : policy ≠ 1) :
    denialMachineGateModel policy mode vector current active normalized = 0 := by
  simp [denialMachineGateModel, hpolicy]

theorem denialMachineGate_live_policy_publishes_exact_dispatch
    mode vector current active normalized :
    denialMachineGateModel 1 mode vector current active normalized =
      denialDispatchModel mode vector current active normalized := by
  simp [denialMachineGateModel]

@[export leanos_extended_state_denial_demo]
def denialDispatchDemo (policy mode vector current active normalized : UInt64) : UInt64 :=
  denialMachineGateModel policy mode vector current active normalized

theorem denialDispatchDemo_refines_machine_gate_all_inputs
    policy mode vector current active normalized :
    denialDispatchDemo policy mode vector current active normalized =
      denialMachineGateModel policy mode vector current active normalized := rfl

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
