import LeanOS.FailStop.ReadSets
import LeanOS.FailStop.AuthoritativeTraces
import LeanOS.BoundedLifecycle
import LeanOS.FrameBudget

/-!
# Fail-stop composite: lifecycle issuers, frame budgets, and frame contents

Issue #499 and gate item 1 of ADR 0010 (#473) ask for the never-reused
lifetime issuers of `BoundedLifecycle` and the per-subject frame budgets of
`FrameBudget` to live in `FailStop.CompositeState`, so that a later spawn
(#489) is one composite transition.  `CompositeState` now carries three more
projections:

- `issuers`: the subject and object `LifetimeIssuer`s of
  `BoundedLifecycle.Runtime`.
- `frameBudgets`: the fixed boot-admitted frame commitment of
  `FrameBudget.State`.
- `scrub`: the frame contents and lifetime write flags of `FrameScrub.State`.

The budgets and contents carry no memory of their own.  Each subsystem state is
reached from the composite by one projection (`lifecycleRuntime`,
`budgetState`, `scrubState`) that reads the composite's own lifecycle and
virtual-memory projections, so there is still one physical-ownership model.

No ordinary, blocking, deferred-drain, or invalidation operation reads or
writes the new projections (`AuthoritativeOperation.footprint_untouched_resources`,
`InvalidationOperation.footprint_untouched_resources`), so every existing
frame, read-set, and preservation proof is unchanged.  Their invariants are
`ProjectionInvariant`s collected in `resourceInvariants`; a transition whose
write set misses a conjunct's support keeps it by the frame rule.

The issued lifecycle family `LifecycleOperation` is the first operation that
draws from the issuers.  `LifecycleOperation.createSubject` takes no identity
word: it issues the subject counter's current value, runs the composite
`createSubject` transition with exactly that identity, and commits the
advanced counter only together with an accepted creation.  It refines
`BoundedLifecycle.createSubject` on the issuers, the lifecycle, and the typed
result (`issueSubject_refines`).
-/
namespace LeanOS.FailStop

open LeanOS
open LeanOS.CompositeFootprint (Projection Footprint)
open LeanOS.LifetimeIssuer (Issuer IssueResult)
set_option linter.unusedSimpArgs false

/-! ## Subsystem views reached by one projection -/

/-- `BoundedLifecycle.Runtime` as a view of the composite: both issuers, the
composite lifecycle and virtual memory, and the composite endpoint mailboxes. -/
def CompositeState.lifecycleRuntime (state : CompositeState) : BoundedLifecycle.Runtime :=
  { subjectIssuer := state.issuers.subject
    objectIssuer := state.issuers.object
    lifecycle := state.lifecycle
    virtualMemory := state.virtualMemory
    mailbox := state.ipc.endpoints.mailbox
    sendHistory := state.ipc.endpoints.sendHistory }

/-- `FrameBudget.State` as a view of the composite: the commitment projection
over the composite memory and subject history. -/
def CompositeState.budgetState (state : CompositeState) : FrameBudget.State :=
  { memory := state.virtualMemory.memory
    issuedSubjects := state.lifecycle.issuedSubjects
    commitment := state.frameBudgets.commitment }

/-- `FrameScrub.State` as a view of the composite: the contents projection
over the composite memory. -/
def CompositeState.scrubState (state : CompositeState) : FrameScrub.State :=
  { memory := state.virtualMemory.memory
    bytes := state.scrub.bytes
    written := state.scrub.written }

/-! ## Resource invariants by projection -/

/-- Both issuer counters stay inside the bounded identity domain. -/
def issuersInvariant : ProjectionInvariant where
  support := [.issuers]
  holds state :=
    state.issuers.subject.next ≤ LifetimeIssuer.identityReserved ∧
      state.issuers.object.next ≤ LifetimeIssuer.identityReserved
  dependsOn := by projection_depends_on

/-- The issuers bound the issued histories: every subject identity the
lifecycle has ever issued, and every object identity in either object
history, is positive and strictly below its counter.  The next identity of
each issuer is therefore fresh. -/
def issuerAgreementInvariant : ProjectionInvariant where
  support := [.issuers, .lifecycle, .virtualMemory]
  holds state :=
    (∀ subject, state.lifecycle.issuedSubjects subject = true →
      0 < subject ∧ subject < state.issuers.subject.next) ∧
    (∀ object, BoundedLifecycle.issuedObject state.lifecycleRuntime object = true →
      0 < object ∧ object < state.issuers.object.next)
  dependsOn := by projection_depends_on

/-- Every committed frame is a modeled, unreserved frame of the composite
allocator and is committed to an issued subject.  This is the commitment
conjunct of `FrameBudget.WellFormed` over the composite memory. -/
def budgetAgreementInvariant : ProjectionInvariant where
  support := [.frameBudgets, .lifecycle, .virtualMemory]
  holds state :=
    ∀ frame subject, state.frameBudgets.commitment frame = some subject →
      frame ∈ state.virtualMemory.memory.allocator.frames ∧
        ¬FrameAllocator.IsReserved state.virtualMemory.memory.allocator frame ∧
        state.lifecycle.issuedSubjects subject = true
  dependsOn := by projection_depends_on

/-- `FrameScrub.ScrubInvariant` over the composite memory: every bound
lifetime its owner has not yet written owns its frame, and that frame holds
only initial bytes. -/
def scrubInvariant : ProjectionInvariant where
  support := [.scrub, .virtualMemory]
  holds state := FrameScrub.ScrubInvariant state.scrubState
  dependsOn := by projection_depends_on

/-- The resource conjuncts added by the issuer, budget, and contents
projections. -/
def resourceInvariants : List ProjectionInvariant :=
  [issuersInvariant, issuerAgreementInvariant, budgetAgreementInvariant, scrubInvariant]

/-- The resource invariant: every conjunct of `resourceInvariants`. -/
def ResourceWellFormed (state : CompositeState) : Prop :=
  ProjectionInvariant.All resourceInvariants state

/-- The resource invariant unfolded into its four conjuncts. -/
theorem resourceWellFormed_iff (state : CompositeState) :
    ResourceWellFormed state ↔
      issuersInvariant.holds state ∧ issuerAgreementInvariant.holds state ∧
        budgetAgreementInvariant.holds state ∧ scrubInvariant.holds state := by
  simp only [ResourceWellFormed, ProjectionInvariant.All, resourceInvariants,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]

/-- **Resource lifting.**  A framed transition preserves the resource
invariant once every resource conjunct whose support it writes is proved. -/
theorem resourceWellFormed_preserved_of_frames {footprint : Footprint}
    {before after : CompositeState}
    (frames : CompositeState.Frames footprint before after)
    (holds : ResourceWellFormed before)
    (touched : ∀ invariant, invariant ∈ resourceInvariants →
      invariant.untouchedBy footprint = false → invariant.holds after) :
    ResourceWellFormed after :=
  ProjectionInvariant.All.preserved_of_frames frames holds touched

/-- A transition that writes no projection read by a resource conjunct keeps
the resource invariant by the frame rule alone. -/
theorem resourceWellFormed_preserved_of_untouched {footprint : Footprint}
    {before after : CompositeState}
    (frames : CompositeState.Frames footprint before after)
    (untouched : ∀ projection, projection ∈ [Projection.issuers, .frameBudgets, .scrub,
      .lifecycle, .virtualMemory] → footprint.writes projection = false)
    (holds : ResourceWellFormed before) :
    ResourceWellFormed after := by
  refine resourceWellFormed_preserved_of_frames frames holds ?_
  intro invariant member touched
  have clean : invariant.untouchedBy footprint = true := by
    simp only [resourceInvariants, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      simp [ProjectionInvariant.untouchedBy, issuersInvariant, issuerAgreementInvariant,
        budgetAgreementInvariant, scrubInvariant, untouched]
  rw [clean] at touched
  contradiction

/-- The combined invariant: the authoritative runtime invariant and the
resource conjuncts. -/
def ResourceRuntimeWellFormed (state : CompositeState) : Prop :=
  AuthoritativeRuntimeWellFormed state ∧ ResourceWellFormed state

/-- The combined invariant is exactly one list of supported conjuncts. -/
theorem resourceRuntimeWellFormed_iff_all (state : CompositeState) :
    ResourceRuntimeWellFormed state ↔
      ProjectionInvariant.All (authoritativeInvariants ++ resourceInvariants) state := by
  rw [ProjectionInvariant.all_append, ← authoritativeRuntimeWellFormed_iff_all]
  rfl

/-! ## No existing operation touches the new projections -/

/-- No ordinary operation reads or writes the issuer, budget, or contents
projections. -/
theorem Operation.footprint_unread_resources (operation : Operation) :
    operation.footprint.reads .issuers = false ∧
      operation.footprint.reads .frameBudgets = false ∧
      operation.footprint.reads .scrub = false := by
  cases operation <;> simp only [Operation.footprint] <;> decide

/-- No authoritative operation (ordinary, blocking, or deferred drain) reads or
writes the issuer, budget, or contents projections. -/
theorem AuthoritativeOperation.footprint_unread_resources
    (operation : AuthoritativeOperation) :
    operation.footprint.reads .issuers = false ∧
      operation.footprint.reads .frameBudgets = false ∧
      operation.footprint.reads .scrub = false := by
  cases operation with
  | ordinary operation => exact Operation.footprint_unread_resources operation
  | blocking operation =>
      cases operation <;>
        simp only [AuthoritativeOperation.footprint, CompositeBlockingOperation.footprint] <;>
        decide
  | drainDeferred _ => simp only [AuthoritativeOperation.footprint]; decide

/-- No invalidation-publication entry point reads or writes the issuer,
budget, or contents projections. -/
theorem InvalidationOperation.footprint_unread_resources
    (operation : InvalidationOperation) :
    operation.footprint.reads .issuers = false ∧
      operation.footprint.reads .frameBudgets = false ∧
      operation.footprint.reads .scrub = false := by
  cases operation <;> simp only [InvalidationOperation.footprint] <;> decide

private theorem untouched_of_unread {footprint : Footprint} {projection : Projection}
    (unread : footprint.reads projection = false) :
    CompositeFootprint.Untouched footprint projection :=
  footprint.unread_is_untouched projection unread

/-- Every authoritative gate step keeps the issuers, the budget commitment,
and the frame contents literally. -/
theorem authoritativeGate_resources (state : CompositeState)
    (operation : AuthoritativeOperation) :
    (authoritativeGate state operation).state.issuers = state.issuers ∧
      (authoritativeGate state operation).state.frameBudgets = state.frameBudgets ∧
      (authoritativeGate state operation).state.scrub = state.scrub := by
  have unread := AuthoritativeOperation.footprint_unread_resources operation
  exact ⟨authoritativeGate_frames state operation .issuers (untouched_of_unread unread.1),
    authoritativeGate_frames state operation .frameBudgets (untouched_of_unread unread.2.1),
    authoritativeGate_frames state operation .scrub (untouched_of_unread unread.2.2)⟩

/-- Every invalidation-publication entry point keeps the issuers, the budget
commitment, and the frame contents literally. -/
theorem InvalidationOperation.apply_resources (state : CompositeState)
    (operation : InvalidationOperation) :
    (operation.apply state).state.issuers = state.issuers ∧
      (operation.apply state).state.frameBudgets = state.frameBudgets ∧
      (operation.apply state).state.scrub = state.scrub := by
  have unread := InvalidationOperation.footprint_unread_resources operation
  exact ⟨InvalidationOperation.apply_frames state operation .issuers
      (untouched_of_unread unread.1),
    InvalidationOperation.apply_frames state operation .frameBudgets
      (untouched_of_unread unread.2.1),
    InvalidationOperation.apply_frames state operation .scrub (untouched_of_unread unread.2.2)⟩

/-- An authoritative operation that writes neither the lifecycle nor the
virtual-memory projection keeps the resource invariant by the frame rule.
The condition is a closed computation on the declared footprint. -/
def AuthoritativeOperation.resourceFramed (operation : AuthoritativeOperation) : Bool :=
  !operation.footprint.writes .lifecycle && !operation.footprint.writes .virtualMemory

theorem authoritativeGate_preserves_resourceWellFormed_of_framed (state : CompositeState)
    (operation : AuthoritativeOperation)
    (framed : operation.resourceFramed = true) (holds : ResourceWellFormed state) :
    ResourceWellFormed (authoritativeGate state operation).state := by
  have unread := AuthoritativeOperation.footprint_unread_resources operation
  simp only [AuthoritativeOperation.resourceFramed, Bool.and_eq_true, Bool.not_eq_true'] at framed
  refine resourceWellFormed_preserved_of_untouched (authoritativeGate_frames state operation)
    ?_ holds
  intro projection member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact untouched_of_unread unread.1
  · exact untouched_of_unread unread.2.1
  · exact untouched_of_unread unread.2.2
  · exact framed.1
  · exact framed.2

/-- The ordinary operations framed away from the resource conjuncts: IPC, NMI,
return selection and return, queue admission, and restart. -/
theorem resourceFramed_ordinary :
    (∀ call, (AuthoritativeOperation.ordinary (.ipc call)).resourceFramed = true) ∧
    (∀ raw context,
      (AuthoritativeOperation.ordinary (.nmi raw context)).resourceFramed = true) ∧
    (∀ purpose,
      (AuthoritativeOperation.ordinary (.selectUserReturn purpose)).resourceFramed = true) ∧
    (∀ request,
      (AuthoritativeOperation.ordinary (.userReturn request)).resourceFramed = true) ∧
    (∀ subject,
      (AuthoritativeOperation.ordinary (.scheduleAdd subject)).resourceFramed = true) ∧
    (AuthoritativeOperation.ordinary .restart).resourceFramed = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    simp only [AuthoritativeOperation.resourceFramed, AuthoritativeOperation.footprint,
      Operation.footprint] <;> decide

/-- Every invalidation-publication entry point except
`acknowledgeCurrentUnmap` keeps the resource invariant by the frame rule. -/
theorem InvalidationOperation.apply_preserves_resourceWellFormed (state : CompositeState)
    (operation : InvalidationOperation)
    (notCurrentUnmap : ∀ ack, operation ≠ .acknowledgeCurrentUnmap ack)
    (holds : ResourceWellFormed state) :
    ResourceWellFormed (operation.apply state).state := by
  refine resourceWellFormed_preserved_of_untouched
    (InvalidationOperation.apply_frames state operation) ?_ holds
  intro projection member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  cases operation
  case acknowledgeCurrentUnmap ack => exact absurd rfl (notCurrentUnmap ack)
  all_goals
    rcases member with rfl | rfl | rfl | rfl | rfl <;>
      simp only [InvalidationOperation.footprint] <;> decide

/-! ## The boot runtime -/

/-- The boot runtime satisfies every resource conjunct: nothing is issued,
nothing is committed, and nothing is bound. -/
theorem bootRuntime_resourceWellFormed plan :
    ResourceWellFormed (bootRuntime plan) := by
  rw [resourceWellFormed_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [issuersInvariant, bootRuntime]
    decide
  · simp [issuerAgreementInvariant, bootRuntime, bootLifecycle, bootVirtualMemory, bootMemory,
      BoundedLifecycle.issuedObject, CompositeState.lifecycleRuntime]
  · simp [budgetAgreementInvariant, bootRuntime]
  · simp [scrubInvariant, FrameScrub.ScrubInvariant, CompositeState.scrubState, bootRuntime,
      bootVirtualMemory, bootMemory]

/-- The boot runtime satisfies the combined invariant once its compiled plan
is accepted. -/
theorem bootRuntime_resourceRuntimeWellFormed input plan
    (compiled : BootPageTablePlan.compile input = .ok plan) :
    ResourceRuntimeWellFormed (bootRuntime plan) :=
  ⟨(bootRuntime_deferredBlockingRuntimeWellFormed input plan compiled).authoritative
      InvalidationPublication.initial_wellFormed,
    bootRuntime_resourceWellFormed plan⟩

/-! ## Issued subject creation through the composite -/

/-- The issued lifecycle operations.  None of them carries an identity word:
identities are drawn from the composite issuers. -/
inductive LifecycleOperation where
  /-- Create the next subject lifetime. -/
  | createSubject
  deriving DecidableEq, Repr

/-- The state and typed creation result of one issued operation. -/
structure IssuedOutcome where
  state : CompositeState
  result : BoundedLifecycle.CreationResult SubjectLifecycle.CreateError

/-- Issue the subject counter's current value and create exactly that
subject through the composite `createSubject` transition.  The advanced
counter is committed only together with an accepted creation; exhaustion and
rejection leave the whole composite unchanged. -/
def issueSubject (state : CompositeState) : IssuedOutcome :=
  match LifetimeIssuer.issue state.issuers.subject with
  | .exhausted => { state, result := .exhausted }
  | .issued identity issuer =>
      match (SubjectLifecycle.create state.lifecycle identity).result with
      | .rejected reason => { state, result := .rejected reason }
      | .accepted =>
          { state := { applyOperation state (.createSubject identity) with
              issuers := { state.issuers with subject := issuer } }
            result := .issued identity }

/-- Run one issued lifecycle operation. -/
def LifecycleOperation.apply (state : CompositeState) : LifecycleOperation → IssuedOutcome
  | .createSubject => issueSubject state

/-- Public result of the issued lifecycle gate. -/
inductive LifecycleGateResult where
  | completed (result : BoundedLifecycle.CreationResult SubjectLifecycle.CreateError)
  | rejectedBusy
  | rejectedHalted (record : HaltRecord)
  deriving DecidableEq, Repr

structure LifecycleGateOutcome where
  state : CompositeState
  result : LifecycleGateResult

/-- The issued lifecycle family runs only under the running latch, like every
ordinary operation: a busy or halted latch rejects without touching an
issuer. -/
def lifecycleGate (state : CompositeState) (operation : LifecycleOperation) :
    LifecycleGateOutcome :=
  match state.execution.mode with
  | .running =>
      { state := (operation.apply state).state
        result := .completed (operation.apply state).result }
  | .handling _ => { state, result := .rejectedBusy }
  | .halted record => { state, result := .rejectedHalted record }

/-- The declared footprint of each issued operation: subject creation reads
and writes the subject issuer and every projection the composite
`createSubject` publication writes. -/
def LifecycleOperation.footprint : LifecycleOperation → Footprint
  | .createSubject => .ofLists [] (publicationProjections ++ [.issuers])

/-- The accepted branch of `issueSubject`, unfolded. -/
theorem issueSubject_accepted_state (state : CompositeState) (identity : Nat)
    (issuer : Issuer .subject)
    (issued : LifetimeIssuer.issue state.issuers.subject = .issued identity issuer)
    (accepted : (SubjectLifecycle.create state.lifecycle identity).result = .accepted) :
    (issueSubject state).state =
        { installCreatedSubject state identity with
          issuers := { state.issuers with subject := issuer } } ∧
      (issueSubject state).result = .issued identity := by
  simp [issueSubject, issued, accepted, applyOperation]

/-- **Atomic exhaustion.**  An exhausted subject issuer leaves the whole
composite, including both issuers, unchanged. -/
theorem issueSubject_exhausted_unchanged (state : CompositeState)
    (exhausted : (issueSubject state).result = .exhausted) :
    (issueSubject state).state = state := by
  unfold issueSubject at exhausted ⊢
  split at exhausted <;> try rfl
  split at exhausted <;> simp_all

/-- **Atomic rejection.**  A rejected creation leaves the whole composite,
including both issuers, unchanged. -/
theorem issueSubject_rejected_unchanged (state : CompositeState) reason
    (rejected : (issueSubject state).result = .rejected reason) :
    (issueSubject state).state = state := by
  unfold issueSubject at rejected ⊢
  split at rejected <;> try rfl
  split at rejected <;> simp_all

/-- Exhaustion is decided exactly by the subject issuer. -/
theorem issueSubject_exhausted_iff (state : CompositeState) :
    (issueSubject state).result = .exhausted ↔
      LifetimeIssuer.exhausted state.issuers.subject = true := by
  constructor
  · intro result
    cases exhausted : LifetimeIssuer.exhausted state.issuers.subject with
    | true => rfl
    | false =>
        have issued : LifetimeIssuer.issue state.issuers.subject =
            .issued state.issuers.subject.next { next := state.issuers.subject.next + 1 } := by
          simp [LifetimeIssuer.issue, exhausted]
        cases created : (SubjectLifecycle.create state.lifecycle
            state.issuers.subject.next).result <;>
          simp [issueSubject, issued, created] at result
  · intro exhausted
    simp [issueSubject, LifetimeIssuer.issue, exhausted]

/-- An issued subject identity is the pre-state counter, is representable,
advances the counter by exactly one, leaves the object issuer unchanged, and
installs exactly the composite `createSubject` transition for that
identity. -/
theorem issueSubject_issued (state : CompositeState) (identity : Nat)
    (result : (issueSubject state).result = .issued identity) :
    identity = state.issuers.subject.next ∧
      LifetimeIssuer.Representable identity ∧
      (SubjectLifecycle.create state.lifecycle identity).result = .accepted ∧
      (issueSubject state).state =
        { applyOperation state (.createSubject identity) with
          issuers := { state.issuers with
            subject := { next := state.issuers.subject.next + 1 } } } := by
  cases issued : LifetimeIssuer.issue state.issuers.subject with
  | exhausted => simp [issueSubject, issued] at result
  | issued fresh issuer =>
      obtain ⟨hfresh, hnext, _, _⟩ := LifetimeIssuer.issued_facts issued
      obtain ⟨representable, _⟩ := LifetimeIssuer.issued_representable issued
      cases created : (SubjectLifecycle.create state.lifecycle fresh).result with
      | rejected reason => simp [issueSubject, issued, created] at result
      | accepted =>
          have same : fresh = identity := by
            simpa [issueSubject, issued, created] using result
          subst same
          have issuerEq : issuer = { next := state.issuers.subject.next + 1 } := by
            cases issuer
            simp_all
          subst issuerEq
          refine ⟨hfresh, representable, created, ?_⟩
          simp [issueSubject, issued, created]

/-- **Total issuance.**  Under the issuer agreement and the lifecycle
invariant a live subject issuer always issues exactly its next identity: the
fresh identity can never be rejected as already issued or already live. -/
theorem issueSubject_total (state : CompositeState)
    (agreement : issuerAgreementInvariant.holds state)
    (lifecycle : SubjectLifecycle.WellFormed state.lifecycle)
    (live : LifetimeIssuer.exhausted state.issuers.subject = false) :
    (issueSubject state).result = .issued state.issuers.subject.next := by
  have issued : LifetimeIssuer.issue state.issuers.subject =
      .issued state.issuers.subject.next { next := state.issuers.subject.next + 1 } := by
    simp [LifetimeIssuer.issue, live]
  have unissued : state.lifecycle.issuedSubjects state.issuers.subject.next = false := by
    cases h : state.lifecycle.issuedSubjects state.issuers.subject.next with
    | false => rfl
    | true => exact absurd (agreement.1 _ h).2 (Nat.lt_irrefl _)
  have dead : state.lifecycle.capabilities.subjects state.issuers.subject.next = false := by
    cases h : state.lifecycle.capabilities.subjects state.issuers.subject.next with
    | false => rfl
    | true =>
        have := lifecycle.1 _ h
        rw [unissued] at this
        contradiction
  simp [issueSubject, issued, SubjectLifecycle.create, unissued, dead]

/-- **Refinement of `BoundedLifecycle.createSubject`.**  Composite issued
creation returns the same typed result as the standalone bounded lifecycle
runtime and agrees with it on both issuers, the lifecycle, and the endpoint
mailboxes.  The composite additionally republishes the new capability
registry into its virtual-memory view, as every composite capability
publication does. -/
theorem issueSubject_refines (state : CompositeState)
    (coherent : state.virtualMemory.memory.capabilities = state.lifecycle.capabilities) :
    let bounded := BoundedLifecycle.createSubject state.lifecycleRuntime
    let composite := issueSubject state
    composite.result = bounded.result ∧
      composite.state.lifecycleRuntime =
        { bounded.runtime with
          virtualMemory := { state.virtualMemory with
            memory := { state.virtualMemory.memory with
              capabilities := bounded.runtime.lifecycle.capabilities } } } := by
  intro bounded composite
  cases issued : LifetimeIssuer.issue state.issuers.subject with
  | exhausted =>
      simp [bounded, composite, issueSubject, BoundedLifecycle.createSubject,
        CompositeState.lifecycleRuntime, issued, ← coherent]
  | issued identity issuer =>
      cases created : (SubjectLifecycle.create state.lifecycle identity).result with
      | rejected reason =>
          simp [bounded, composite, issueSubject, BoundedLifecycle.createSubject,
            CompositeState.lifecycleRuntime, issued, created, ← coherent]
      | accepted =>
          simp [bounded, composite, issueSubject, BoundedLifecycle.createSubject,
            CompositeState.lifecycleRuntime, issued, created, applyOperation,
            installCreatedSubject]

/-- An accepted issued identity was never issued and is not live before the
step, and is issued and live after it. -/
theorem issueSubject_fresh (state : CompositeState) (identity : Nat)
    (result : (issueSubject state).result = .issued identity) :
    state.lifecycle.issuedSubjects identity = false ∧
      state.lifecycle.capabilities.subjects identity = false ∧
      (issueSubject state).state.lifecycle.issuedSubjects identity = true ∧
      (issueSubject state).state.lifecycle.capabilities.subjects identity = true := by
  obtain ⟨_, _, created, eq⟩ := issueSubject_issued state identity result
  obtain ⟨issuedMap, subjectsMap⟩ :=
    BoundedLifecycle.subject_create_accepted_registry state.lifecycle identity created
  have before : state.lifecycle.capabilities.subjects identity = false ∧
      state.lifecycle.issuedSubjects identity = false := by
    simp only [SubjectLifecycle.create] at created
    split at created
    · simp [SubjectLifecycle.reject] at created
    · split at created
      · simp [SubjectLifecycle.reject] at created
      · constructor <;> simp_all
  rw [eq]
  simp only [applyOperation, created, installCreatedSubject]
  refine ⟨before.2, before.1, ?_, ?_⟩
  · rw [issuedMap]; simp [SubjectLifecycle.setBool]
  · rw [subjectsMap]; simp [SubjectLifecycle.setBool]

/-! ## Frame rule and read sets of the issued family -/

/-- **Frame rule.**  Issued subject creation changes nothing outside its
declared write set, on every outcome. -/
theorem issueSubject_frames (state : CompositeState) :
    CompositeState.Frames LifecycleOperation.createSubject.footprint state
      (issueSubject state).state := by
  cases issued : LifetimeIssuer.issue state.issuers.subject with
  | exhausted =>
      simp only [issueSubject, issued]
      exact CompositeState.frames_of_eq _ rfl
  | issued identity issuer =>
      cases created : (SubjectLifecycle.create state.lifecycle identity).result with
      | rejected reason =>
          simp only [issueSubject, issued, created]
          exact CompositeState.frames_of_eq _ rfl
      | accepted =>
          rw [(issueSubject_accepted_state state identity issuer issued created).1]
          simp only [LifecycleOperation.footprint]
          composite_frame

/-- The frame rule holds for every outcome of the issued lifecycle gate,
including busy and halted rejections. -/
theorem lifecycleGate_frames (state : CompositeState) (operation : LifecycleOperation) :
    CompositeState.Frames operation.footprint state (lifecycleGate state operation).state := by
  cases operation
  cases hmode : state.execution.mode <;>
    simp only [lifecycleGate, hmode, LifecycleOperation.apply] <;>
    first
      | exact issueSubject_frames state
      | exact CompositeState.frames_of_eq _ rfl

/-- **Read independence.**  Two states that agree on the declared reads of
issued subject creation produce the same typed result and post-states that
agree on its declared writes. -/
theorem issueSubject_reads (left right : CompositeState)
    (agree : CompositeState.AgreeOn LifecycleOperation.createSubject.footprint.reads
      left right) :
    (issueSubject left).result = (issueSubject right).result ∧
      CompositeState.AgreeOn LifecycleOperation.createSubject.footprint.writes
        (issueSubject left).state (issueSubject right).state := by
  have sameIssuers : left.issuers = right.issuers := agree .issuers (by decide)
  have sameLifecycle : left.lifecycle = right.lifecycle := agree .lifecycle (by decide)
  have inner : ∀ identity, CompositeState.AgreeOn
      (Operation.createSubject identity).footprint.writes
      (applyOperation left (.createSubject identity))
      (applyOperation right (.createSubject identity)) := by
    intro identity
    apply applyOperation_reads
    apply agree.mono
    intro projection read
    revert read
    cases projection <;> simp only [Operation.footprint, LifecycleOperation.footprint] <;>
      decide
  cases issued : LifetimeIssuer.issue right.issuers.subject with
  | exhausted =>
      simp only [issueSubject, sameIssuers, issued]
      exact ⟨by first | rfl | trivial, agree.writes_of_reads⟩
  | issued identity issuer =>
      cases created : (SubjectLifecycle.create right.lifecycle identity).result with
      | rejected reason =>
          simp only [issueSubject, sameIssuers, sameLifecycle, issued, created]
          exact ⟨by first | rfl | trivial, agree.writes_of_reads⟩
      | accepted =>
          simp only [issueSubject, sameIssuers, sameLifecycle, issued, created]
          refine ⟨by first | rfl | trivial, ?_⟩
          intro projection written
          have framed := inner identity projection
          cases projection <;>
            first
              | rfl
              | exact absurd written (by decide)
              | exact framed (by simp only [Operation.footprint]; decide)

/-- Read independence of the issued lifecycle gate.  The gate also reads the
latch mode, which is part of the declared `execution` read. -/
theorem lifecycleGate_reads (left right : CompositeState) (operation : LifecycleOperation)
    (agree : CompositeState.AgreeOn operation.footprint.reads left right) :
    (lifecycleGate left operation).result = (lifecycleGate right operation).result ∧
      CompositeState.AgreeOn operation.footprint.writes
        (lifecycleGate left operation).state (lifecycleGate right operation).state := by
  cases operation
  have sameExecution : left.execution = right.execution := agree .execution (by decide)
  obtain ⟨result, written⟩ := issueSubject_reads left right agree
  simp only [lifecycleGate, LifecycleOperation.apply, sameExecution]
  split
  · exact ⟨by rw [result], written⟩
  · exact ⟨by first | rfl | trivial, agree.writes_of_reads⟩
  · exact ⟨by first | rfl | trivial, agree.writes_of_reads⟩

/-! ## Invariant preservation -/

/-- Changing only the issuers keeps the authoritative runtime invariant: no
authoritative conjunct reads them. -/
theorem AuthoritativeRuntimeWellFormed.withIssuers {state : CompositeState}
    (holds : AuthoritativeRuntimeWellFormed state) (issuers : LifecycleIssuers) :
    AuthoritativeRuntimeWellFormed { state with issuers } :=
  ⟨holds.left, holds.right, holds.publication⟩

/-- Issued subject creation keeps the authoritative runtime invariant under
the running latch: an accepted step is exactly the composite `createSubject`
transition plus the issuer advance. -/
theorem issueSubject_preserves_authoritativeRuntimeWellFormed (state : CompositeState)
    (running : state.execution.mode = .running)
    (holds : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed (issueSubject state).state := by
  cases result : (issueSubject state).result with
  | exhausted => rw [issueSubject_exhausted_unchanged state result]; exact holds
  | rejected reason => rw [issueSubject_rejected_unchanged state reason result]; exact holds
  | issued identity =>
      obtain ⟨_, _, _, eq⟩ := issueSubject_issued state identity result
      rw [eq]
      have created :=
        authoritativeGate_createSubject_preserves_authoritativeRuntimeWellFormed
          state identity holds
      rw [authoritativeGate_ordinary_state] at created
      simp only [gate, running] at created
      exact created.withIssuers _

/-- Issued subject creation keeps every resource conjunct.  Only the subject
issuer and the subject history change: the new identity is the old counter,
which the advanced counter now bounds, and the object histories, frame
allocator, bindings, commitment, and contents are untouched. -/
theorem issueSubject_preserves_resourceWellFormed (state : CompositeState)
    (holds : ResourceWellFormed state) :
    ResourceWellFormed (issueSubject state).state := by
  cases result : (issueSubject state).result with
  | exhausted => rw [issueSubject_exhausted_unchanged state result]; exact holds
  | rejected reason => rw [issueSubject_rejected_unchanged state reason result]; exact holds
  | issued identity =>
      obtain ⟨hidentity, representable, created, eq⟩ :=
        issueSubject_issued state identity result
      obtain ⟨issuedMap, _⟩ :=
        BoundedLifecycle.subject_create_accepted_registry state.lifecycle identity created
      rw [resourceWellFormed_iff] at holds ⊢
      obtain ⟨issuersHold, agreementHold, budgetHold, scrubHold⟩ := holds
      rw [eq]
      simp only [applyOperation, created]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [issuersInvariant, installCreatedSubject] at issuersHold ⊢
        refine ⟨?_, issuersHold.2⟩
        have := representable.2
        omega
      · simp only [issuerAgreementInvariant, installCreatedSubject,
          CompositeState.lifecycleRuntime, BoundedLifecycle.issuedObject]
          at agreementHold ⊢
        refine ⟨?_, agreementHold.2⟩
        intro subject issuedNow
        rw [issuedMap] at issuedNow
        by_cases same : subject = identity
        · subst same
          exact ⟨representable.1, hidentity ▸ Nat.lt_succ_self _⟩
        · simp only [SubjectLifecycle.setBool, same] at issuedNow
          have := agreementHold.1 subject (by simpa using issuedNow)
          exact ⟨this.1, Nat.lt_succ_of_lt this.2⟩
      · simp only [budgetAgreementInvariant, installCreatedSubject] at budgetHold ⊢
        intro frame subject committed
        obtain ⟨member, unreserved, issuedBefore⟩ := budgetHold frame subject committed
        refine ⟨member, unreserved, ?_⟩
        rw [issuedMap]
        simp only [SubjectLifecycle.setBool]
        split <;> simp_all
      · simpa [scrubInvariant, installCreatedSubject, CompositeState.scrubState,
          FrameScrub.ScrubInvariant] using scrubHold

/-- **Issued creation keeps the combined invariant.**  Every step of the
issued lifecycle gate, on every outcome, preserves the authoritative runtime
invariant and every resource conjunct. -/
theorem lifecycleGate_preserves_resourceRuntimeWellFormed (state : CompositeState)
    (operation : LifecycleOperation) (holds : ResourceRuntimeWellFormed state) :
    ResourceRuntimeWellFormed (lifecycleGate state operation).state := by
  cases operation
  cases hmode : state.execution.mode <;> simp only [lifecycleGate, hmode,
    LifecycleOperation.apply]
  all_goals first
    | exact holds
    | exact ⟨issueSubject_preserves_authoritativeRuntimeWellFormed state hmode holds.1,
        issueSubject_preserves_resourceWellFormed state holds.2⟩

/-- Exhaustion and rejection through the issued lifecycle gate leave the
whole composite unchanged, and so do a busy or halted latch. -/
theorem lifecycleGate_unchanged_of_not_issued (state : CompositeState)
    (operation : LifecycleOperation)
    (notIssued : ∀ identity, (lifecycleGate state operation).result ≠ .completed (.issued identity)) :
    (lifecycleGate state operation).state = state := by
  cases operation
  cases hmode : state.execution.mode <;> simp only [lifecycleGate, hmode,
    LifecycleOperation.apply] at notIssued ⊢
  cases result : (issueSubject state).result with
  | exhausted => exact issueSubject_exhausted_unchanged state result
  | rejected reason => exact issueSubject_rejected_unchanged state reason result
  | issued identity => exact absurd (by rw [result]) (notIssued identity)

/-! ## Frame budgets through the composite -/

/-- A subject's frame usage, read from the composite. -/
def CompositeState.budgetUsage (state : CompositeState) (subject : Capability.SubjectId) : Nat :=
  FrameBudget.usage state.budgetState subject

/-- A subject's frame limit: the committed frames of the composite
allocator. -/
def CompositeState.budgetLimit (state : CompositeState) (subject : Capability.SubjectId) : Nat :=
  FrameBudget.limit state.budgetState subject

/-- **Budget conservation, lifted.**  In every composite state each subject's
usage is within its limit, each frame is committed to at most one subject,
and every frame of the composite allocator is in exactly one allocator
class. -/
theorem budget_conservation (state : CompositeState) :
    (∀ subject, state.budgetUsage subject ≤ state.budgetLimit subject) ∧
      (∀ frame left right, state.frameBudgets.commitment frame = some left →
        state.frameBudgets.commitment frame = some right → left = right) ∧
      FrameAllocator.Conserved state.virtualMemory.memory.allocator :=
  ⟨fun subject => FrameBudget.usage_le_limit state.budgetState subject,
    fun frame left right hl hr =>
      FrameBudget.commitments_disjoint state.budgetState frame left right hl hr,
    FrameAllocator.conservation _⟩

/-- Usage and limit read only the commitment and the composite allocator. -/
theorem budget_eq_of_allocator {before after : CompositeState}
    (commitment : after.frameBudgets = before.frameBudgets)
    (allocator : after.virtualMemory.memory.allocator =
      before.virtualMemory.memory.allocator)
    (subject : Capability.SubjectId) :
    after.budgetUsage subject = before.budgetUsage subject ∧
      after.budgetLimit subject = before.budgetLimit subject := by
  simp only [CompositeState.budgetUsage, CompositeState.budgetLimit, FrameBudget.usage,
    FrameBudget.limit, FrameBudget.budgetFrames, CompositeState.budgetState, commitment,
    allocator]
  exact ⟨rfl, rfl⟩

/-- Every authoritative step that does not write the virtual-memory
projection keeps every subject's usage and limit exactly. -/
theorem authoritativeGate_budget_unchanged (state : CompositeState)
    (operation : AuthoritativeOperation)
    (untouched : operation.footprint.writes .virtualMemory = false)
    (subject : Capability.SubjectId) :
    (authoritativeGate state operation).state.budgetUsage subject = state.budgetUsage subject ∧
      (authoritativeGate state operation).state.budgetLimit subject =
        state.budgetLimit subject := by
  have memory : (authoritativeGate state operation).state.virtualMemory =
      state.virtualMemory := authoritativeGate_frames state operation .virtualMemory untouched
  exact budget_eq_of_allocator (authoritativeGate_resources state operation).2.1
    (by rw [memory]) subject

/-- Issued subject creation keeps every subject's usage and limit exactly:
it changes neither the allocator nor the commitment. -/
theorem issueSubject_budget_unchanged (state : CompositeState)
    (subject : Capability.SubjectId) :
    (issueSubject state).state.budgetUsage subject = state.budgetUsage subject ∧
      (issueSubject state).state.budgetLimit subject = state.budgetLimit subject := by
  cases result : (issueSubject state).result with
  | exhausted => rw [issueSubject_exhausted_unchanged state result]; exact ⟨rfl, rfl⟩
  | rejected reason =>
      rw [issueSubject_rejected_unchanged state reason result]; exact ⟨rfl, rfl⟩
  | issued identity =>
      obtain ⟨_, _, created, eq⟩ := issueSubject_issued state identity result
      apply budget_eq_of_allocator
      · rw [eq]; simp [applyOperation, created, installCreatedSubject]
      · rw [eq]; simp [applyOperation, created, installCreatedSubject]

/-- **A created subject starts with a zero frame budget.**  Under the budget
agreement no frame is committed to an identity that was never issued, so the
subject issued by `issueSubject` has limit and usage zero.  This is the
zero-budget clause of the #489 inheritance set. -/
theorem issueSubject_zero_budget (state : CompositeState) (identity : Nat)
    (budget : budgetAgreementInvariant.holds state)
    (result : (issueSubject state).result = .issued identity) :
    (issueSubject state).state.budgetLimit identity = 0 ∧
      (issueSubject state).state.budgetUsage identity = 0 := by
  have unissued := (issueSubject_fresh state identity result).1
  have limit : state.budgetLimit identity = 0 := by
    simp only [CompositeState.budgetLimit, FrameBudget.limit, FrameBudget.budgetFrames,
      CompositeState.budgetState, List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro frame _ committed
    have := (budget frame identity (of_decide_eq_true committed)).2.2
    rw [unissued] at this
    contradiction
  obtain ⟨usage, limitEq⟩ := issueSubject_budget_unchanged state identity
  rw [limitEq, limit]
  refine ⟨rfl, ?_⟩
  have bound := FrameBudget.usage_le_limit (issueSubject state).state.budgetState identity
  have : (issueSubject state).state.budgetLimit identity = 0 := by rw [limitEq, limit]
  simp only [CompositeState.budgetLimit, CompositeState.budgetUsage] at this ⊢
  omega

/-! ## Operations that write lifecycle or memory but keep the histories

Capability delegation, revocation, sealed transfer, and mapping write the
lifecycle and virtual-memory projections, so the frame rule alone does not
discharge the cross-projection resource conjuncts for them.  They change only
capability registries and mappings, never an issued history, the frame
allocator, or an object binding, and that is all the resource conjuncts
read. -/

/-- Two states agree on everything the resource conjuncts read. -/
def ResourceHistoryAgrees (before after : CompositeState) : Prop :=
  after.issuers = before.issuers ∧ after.frameBudgets = before.frameBudgets ∧
    after.scrub = before.scrub ∧
    after.lifecycle.issuedSubjects = before.lifecycle.issuedSubjects ∧
    after.virtualMemory.memory.issued = before.virtualMemory.memory.issued ∧
    after.virtualMemory.issuedAddressSpace = before.virtualMemory.issuedAddressSpace ∧
    after.virtualMemory.memory.allocator = before.virtualMemory.memory.allocator ∧
    after.virtualMemory.memory.binding = before.virtualMemory.memory.binding

theorem ResourceHistoryAgrees.refl (state : CompositeState) :
    ResourceHistoryAgrees state state :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The resource invariant reads only issued histories, the allocator, object
bindings, and its own projections. -/
theorem resourceWellFormed_of_historyAgrees {before after : CompositeState}
    (agrees : ResourceHistoryAgrees before after) (holds : ResourceWellFormed before) :
    ResourceWellFormed after := by
  obtain ⟨issuers, budgets, scrub, subjects, issued, spaces, allocator, binding⟩ := agrees
  rw [resourceWellFormed_iff] at holds ⊢
  obtain ⟨issuersHold, agreementHold, budgetHold, scrubHold⟩ := holds
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [issuersInvariant, issuers] using issuersHold
  · simpa [issuerAgreementInvariant, CompositeState.lifecycleRuntime,
      BoundedLifecycle.issuedObject, issuers, subjects, issued, spaces] using agreementHold
  · simpa [budgetAgreementInvariant, budgets, subjects, allocator] using budgetHold
  · simpa [scrubInvariant, CompositeState.scrubState, FrameScrub.ScrubInvariant, scrub,
      allocator, binding] using scrubHold

theorem VirtualMapping.map_registry (state : VirtualMapping.State) actor slot space page
    permissions :
    (VirtualMapping.map state actor slot space page permissions).state.memory = state.memory ∧
      (VirtualMapping.map state actor slot space page permissions).state.issuedAddressSpace =
        state.issuedAddressSpace := by
  unfold VirtualMapping.map
  repeat' split
  all_goals simp [VirtualMapping.reject, VirtualMapping.setMapping]

theorem VirtualMapping.unmap_registry (state : VirtualMapping.State) actor space page :
    (VirtualMapping.unmap state actor space page).state.memory = state.memory ∧
      (VirtualMapping.unmap state actor space page).state.issuedAddressSpace =
        state.issuedAddressSpace := by
  unfold VirtualMapping.unmap
  repeat' split
  all_goals simp [VirtualMapping.reject, VirtualMapping.setMapping]

/-- The ordinary operations that change only capability registries or
mappings: delegation, revocation, sealed transfer, map, and unmap. -/
def Operation.keepsHistory : Operation → Bool
  | .capabilityCopy .. | .capabilityRevoke .. | .capabilityRevokeSubtree ..
  | .transferOffer .. | .transferAccept .. | .map .. | .unmap _ => true
  | _ => false

theorem applyOperation_historyAgrees (state : CompositeState) (operation : Operation)
    (keeps : operation.keepsHistory = true) :
    ResourceHistoryAgrees state (applyOperation state operation) := by
  cases operation <;> simp only [Operation.keepsHistory] at keeps <;>
    simp only [applyOperation] <;> try contradiction
  all_goals
    repeat' split
    all_goals first
      | exact ResourceHistoryAgrees.refl state
      | (simp [ResourceHistoryAgrees, installCopiedCapabilities, installRevokedSubtree,
          installTransfers, installVirtualMemory, VirtualMapping.map_registry,
          VirtualMapping.unmap_registry]; done)

/-- Every authoritative gate step of a history-keeping ordinary operation
keeps the resource invariant. -/
theorem authoritativeGate_preserves_resourceWellFormed_of_keepsHistory
    (state : CompositeState) (operation : Operation)
    (keeps : operation.keepsHistory = true) (holds : ResourceWellFormed state) :
    ResourceWellFormed (authoritativeGate state (.ordinary operation)).state := by
  rw [authoritativeGate_ordinary_state]
  apply resourceWellFormed_of_historyAgrees _ holds
  cases operation <;> simp only [Operation.keepsHistory] at keeps <;> try contradiction
  all_goals
    cases hmode : state.execution.mode <;> simp only [gate, hmode]
    all_goals first
      | exact ResourceHistoryAgrees.refl state
      | exact applyOperation_historyAgrees state _ rfl

/-! ## Composite traces -/

/-- One composite step: an issued lifecycle operation or an authoritative
operation. -/
inductive CompositeStep where
  | lifecycle (operation : LifecycleOperation)
  | authoritative (operation : AuthoritativeOperation)

def CompositeStep.apply (state : CompositeState) : CompositeStep → CompositeState
  | .lifecycle operation => (lifecycleGate state operation).state
  | .authoritative operation => (authoritativeGate state operation).state

/-- The subject identity a step issues, if any. -/
def CompositeStep.issued (state : CompositeState) : CompositeStep → Option Nat
  | .lifecycle operation =>
      match (lifecycleGate state operation).result with
      | .completed (.issued identity) => some identity
      | _ => none
  | .authoritative _ => none

def runSteps (state : CompositeState) : List CompositeStep → CompositeState
  | [] => state
  | step :: rest => runSteps (step.apply state) rest

/-- The subject identities issued along a trace, in order. -/
def issuedAlong (state : CompositeState) : List CompositeStep → List Nat
  | [] => []
  | step :: rest =>
      (step.issued state).toList ++ issuedAlong (step.apply state) rest

/-- A step either leaves the subject issuer unchanged or issues exactly its
current value and advances it by one; the object issuer never changes. -/
theorem CompositeStep.apply_issuers (state : CompositeState) (step : CompositeStep) :
    (step.apply state).issuers.object = state.issuers.object ∧
      ((step.issued state = none ∧ (step.apply state).issuers = state.issuers) ∨
        (step.issued state = some state.issuers.subject.next ∧
          (step.apply state).issuers.subject.next = state.issuers.subject.next + 1 ∧
          LifetimeIssuer.Representable state.issuers.subject.next)) := by
  cases step with
  | authoritative operation =>
      have same := (authoritativeGate_resources state operation).1
      simp [CompositeStep.apply, CompositeStep.issued, same]
  | lifecycle operation =>
      cases operation
      cases hmode : state.execution.mode <;>
        simp only [CompositeStep.apply, CompositeStep.issued, lifecycleGate, hmode,
          LifecycleOperation.apply]
      case running =>
        cases result : (issueSubject state).result with
        | exhausted =>
            rw [issueSubject_exhausted_unchanged state result]
            exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
        | rejected reason =>
            rw [issueSubject_rejected_unchanged state reason result]
            exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
        | issued identity =>
            obtain ⟨hidentity, representable, _, eq⟩ :=
              issueSubject_issued state identity result
            subst hidentity
            rw [eq]
            exact ⟨rfl, Or.inr ⟨rfl, rfl, representable⟩⟩
      all_goals simp

/-- The subject counter never decreases along a trace. -/
theorem runSteps_subject_monotone (state : CompositeState) (steps : List CompositeStep) :
    state.issuers.subject.next ≤ (runSteps state steps).issuers.subject.next ∧
      (runSteps state steps).issuers.object = state.issuers.object := by
  induction steps generalizing state with
  | nil => exact ⟨Nat.le_refl _, rfl⟩
  | cons step rest ih =>
      obtain ⟨object, change⟩ := step.apply_issuers state
      obtain ⟨later, laterObject⟩ := ih (step.apply state)
      refine ⟨?_, laterObject.trans object⟩
      rcases change with ⟨_, same⟩ | ⟨_, advanced, _⟩
      · rw [same] at later; exact later
      · simp only [runSteps]; omega

/-- **No identity is issued twice.**  Along every composite trace the issued
subject identities strictly increase, each is representable, each is at least
the starting counter, and each is below the final counter.  In particular no
two steps ever issue the same identity, whatever other composite operations
run between them. -/
theorem issuedAlong_strictly_increasing (state : CompositeState) (steps : List CompositeStep) :
    (issuedAlong state steps).Pairwise (· < ·) ∧
      ∀ identity, identity ∈ issuedAlong state steps →
        LifetimeIssuer.Representable identity ∧
          state.issuers.subject.next ≤ identity ∧
          identity < (runSteps state steps).issuers.subject.next := by
  induction steps generalizing state with
  | nil => simp [issuedAlong]
  | cons step rest ih =>
      obtain ⟨pairwise, bounds⟩ := ih (step.apply state)
      obtain ⟨_, change⟩ := step.apply_issuers state
      rcases change with ⟨none, same⟩ | ⟨some, advanced, representable⟩
      · simp only [issuedAlong, none, Option.toList_none, List.nil_append, runSteps]
        refine ⟨pairwise, fun identity member => ?_⟩
        obtain ⟨r, lower, upper⟩ := bounds identity member
        rw [same] at lower
        exact ⟨r, lower, upper⟩
      · simp only [issuedAlong, some, Option.toList_some, List.singleton_append,
          List.pairwise_cons, List.mem_cons, runSteps]
        refine ⟨⟨fun identity member => ?_, pairwise⟩, ?_⟩
        · have := (bounds identity member).2.1
          omega
        · rintro identity (rfl | member)
          · have := (runSteps_subject_monotone (step.apply state) rest).1
            exact ⟨representable, Nat.le_refl _, by omega⟩
          · obtain ⟨r, lower, upper⟩ := bounds identity member
            exact ⟨r, by omega, upper⟩

/-- An exhausted subject issuer stays exhausted and unchanged along every
composite trace. -/
theorem runSteps_exhausted_absorbing (state : CompositeState) (steps : List CompositeStep)
    (exhausted : LifetimeIssuer.exhausted state.issuers.subject = true) :
    (runSteps state steps).issuers = state.issuers ∧ issuedAlong state steps = [] := by
  induction steps generalizing state with
  | nil => exact ⟨rfl, rfl⟩
  | cons step rest ih =>
      obtain ⟨_, change⟩ := step.apply_issuers state
      rcases change with ⟨none, same⟩ | ⟨_, _, representable⟩
      · have stillExhausted : LifetimeIssuer.exhausted (step.apply state).issuers.subject =
            true := by rw [same]; exact exhausted
        obtain ⟨issuers, issued⟩ := ih (step.apply state) stillExhausted
        simp only [runSteps, issuedAlong, none, Option.toList_none, List.nil_append]
        exact ⟨issuers.trans same, issued⟩
      · simp only [LifetimeIssuer.exhausted, Bool.or_eq_true, decide_eq_true_eq] at exhausted
        have := representable.1
        have := representable.2
        omega

/-- A step that keeps the combined invariant from any state satisfying it.
Every issued lifecycle step qualifies
(`lifecycleGate_preserves_resourceRuntimeWellFormed`), and so does every
authoritative step framed away from the resource conjuncts
(`CompositeStep.preserving_of_framed`). -/
def CompositeStep.Preserving (step : CompositeStep) : Prop :=
  ∀ state, ResourceRuntimeWellFormed state → ResourceRuntimeWellFormed (step.apply state)

theorem CompositeStep.preserving_lifecycle (operation : LifecycleOperation) :
    (CompositeStep.lifecycle operation).Preserving :=
  fun state holds => lifecycleGate_preserves_resourceRuntimeWellFormed state operation holds

theorem CompositeStep.preserving_of_framed (operation : AuthoritativeOperation)
    (framed : operation.resourceFramed = true) :
    (CompositeStep.authoritative operation).Preserving :=
  fun state holds =>
    ⟨authoritativeGate_preserves_authoritativeRuntimeWellFormed state operation holds.1,
      authoritativeGate_preserves_resourceWellFormed_of_framed state operation framed holds.2⟩

theorem CompositeStep.preserving_of_keepsHistory (operation : Operation)
    (keeps : operation.keepsHistory = true) :
    (CompositeStep.authoritative (.ordinary operation)).Preserving :=
  fun state holds =>
    ⟨authoritativeGate_preserves_authoritativeRuntimeWellFormed state _ holds.1,
      authoritativeGate_preserves_resourceWellFormed_of_keepsHistory state operation keeps
        holds.2⟩

/-- **Never-reuse through the composite** (`BoundedLifecycle.bounded_identity_no_reuse`
lifted).  Along every composite trace whose steps keep the combined
invariant, starting from a state that satisfies it:

- the combined invariant holds at the end;
- the issued subject identities strictly increase, so none is issued twice;
- every issued identity is above every subject identity in the starting
  lifecycle history, live or terminated, so no issued identity aliases an
  earlier subject;
- an exhausted subject issuer stays exhausted and issues nothing. -/
theorem composite_identity_no_reuse (state : CompositeState) (steps : List CompositeStep)
    (holds : ResourceRuntimeWellFormed state)
    (preserving : ∀ step, step ∈ steps → step.Preserving) :
    ResourceRuntimeWellFormed (runSteps state steps) ∧
      (issuedAlong state steps).Pairwise (· < ·) ∧
      (∀ identity, identity ∈ issuedAlong state steps →
        ∀ earlier, state.lifecycle.issuedSubjects earlier = true → earlier < identity) ∧
      (LifetimeIssuer.exhausted state.issuers.subject = true →
        (runSteps state steps).issuers = state.issuers ∧ issuedAlong state steps = []) := by
  refine ⟨?_, (issuedAlong_strictly_increasing state steps).1, ?_,
    runSteps_exhausted_absorbing state steps⟩
  · induction steps generalizing state with
    | nil => exact holds
    | cons step rest ih =>
        exact ih (step.apply state) (preserving step (List.mem_cons_self ..) state holds)
          (fun later member => preserving later (List.mem_cons_of_mem _ member))
  · intro identity member earlier issuedEarlier
    have agreement := ((resourceWellFormed_iff state).1 holds.2).2.1
    have bound : earlier < state.issuers.subject.next := (agreement.1 earlier issuedEarlier).2
    have := ((issuedAlong_strictly_increasing state steps).2 identity member).2.1
    exact Nat.lt_of_lt_of_le bound this

end LeanOS.FailStop
