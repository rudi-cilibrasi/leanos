import LeanOS.FailStop.DeferredBlocking
import LeanOS.FailStop.ProjectionInvariants

/-!
# Fail-stop composite: the authoritative gate

The authoritative ordinary/blocking gate vocabulary, conditional invalidation
publication, `authoritativeGate` itself, its rejection classification, and
the dormant-cancellation compatibility theorems for the ordinary families.
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

/-! ## Authoritative ordinary/blocking gate

The ordinary gate and the blocking gate were developed independently while
their operation-specific preservation proofs were completed.  The vocabulary
below is their migration boundary: it uses the same `CompositeState`, one
execution latch, and one typed result family.  The successor invariant folds
the complete blocking/deferred classification into the global boundary.
Lower blocking and drain readiness are projections of that invariant.
Operation-local compatibility lemmas remain as proof decomposition, while the
published gate and trace preservation boundaries derive them entirely from the
authoritative pre-invariant. -/

/-- Every currently modeled runtime event admitted by the successor gate. -/
inductive AuthoritativeOperation where
  | ordinary (operation : Operation)
  | blocking (operation : CompositeBlockingOperation)
  | drainDeferred (subject : BlockingIPC.SubjectId)

/-- Operation-specific observation retained by the successor gate. -/
inductive AuthoritativeOperationReply where
  | ordinary (reply : OperationReply)
  | blocking (reply : CompositeBlockingOperationReply)
  | deferredDrain (result : BlockingIPCContext.DrainResult)
  deriving DecidableEq, Repr

inductive AuthoritativeGateResult where
  | completed (reply : AuthoritativeOperationReply)
  | rejectedBusy
  | rejectedHalted (record : HaltRecord)
  deriving DecidableEq, Repr

structure AuthoritativeGateOutcome where
  state : CompositeState
  result : AuthoritativeGateResult

/-- The successor gate's authoritative global invariant includes the complete
blocking/deferred-cancellation classification.  In particular, it carries the
scheduler/mailbox/waiter well-formedness required by blocking transitions and
the retained-context classification required by deferred drains. -/
structure AuthoritativeRuntimeWellFormed (state : CompositeState) : Prop where
  left : RuntimeWellFormed state
  right : state.DeferredCancellationWellFormed
  publication :
    InvalidationPublication.WellFormed state.invalidationPublication

theorem DeferredBlockingRuntimeWellFormed.authoritative {state : CompositeState}
    (hstate : DeferredBlockingRuntimeWellFormed state)
    (hpublication :
      InvalidationPublication.WellFormed state.invalidationPublication) :
    AuthoritativeRuntimeWellFormed state :=
  ⟨hstate.1, hstate.2, hpublication⟩

theorem AuthoritativeRuntimeWellFormed.blocking {state : CompositeState}
    (hstate : AuthoritativeRuntimeWellFormed state) :
    BlockingRuntimeWellFormed state :=
  ⟨hstate.1, hstate.2.1.1⟩

theorem AuthoritativeRuntimeWellFormed.deferred {state : CompositeState}
    (hstate : AuthoritativeRuntimeWellFormed state) :
    DeferredBlockingRuntimeWellFormed state :=
  ⟨hstate.1, hstate.2⟩

/-! ## `AuthoritativeRuntimeWellFormed` by projection -/

/-- The retained-context classification reads only the blocking store, its
saved contexts, the deferred cancellations, and the resumable bank. -/
def deferredCancellationInvariant : ProjectionInvariant where
  support := [.resumable, .blockingIPC, .blockingContexts, .deferredCancels]
  holds := CompositeState.DeferredCancellationWellFormed
  dependsOn := by projection_depends_on

/-- The invalidation-publication protocol invariant reads only its own
projection. -/
def publicationInvariant : ProjectionInvariant where
  support := [.invalidationPublication]
  holds state := InvalidationPublication.WellFormed state.invalidationPublication
  dependsOn := by projection_depends_on

/-- `AuthoritativeRuntimeWellFormed`, one supported conjunct per entry: the
runtime conjuncts followed by the deferred-cancellation and publication
conjuncts. -/
def authoritativeInvariants : List ProjectionInvariant :=
  runtimeInvariants ++ [deferredCancellationInvariant, publicationInvariant]

/-- The per-projection decomposition is exactly the authoritative runtime
invariant. -/
theorem authoritativeRuntimeWellFormed_iff_all (state : CompositeState) :
    AuthoritativeRuntimeWellFormed state ↔
      ProjectionInvariant.All authoritativeInvariants state := by
  rw [authoritativeInvariants, ProjectionInvariant.all_append,
    ← runtimeWellFormed_iff_all]
  simp only [ProjectionInvariant.All, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  constructor
  · intro hstate
    exact ⟨hstate.1, hstate.2, hstate.publication⟩
  · rintro ⟨hruntime, hdeferred, hpublication⟩
    exact ⟨hruntime, hdeferred, hpublication⟩

/-- **Authoritative lifting.**  A framed transition preserves
`AuthoritativeRuntimeWellFormed` once every conjunct whose support it writes
is proved. -/
theorem authoritativeRuntimeWellFormed_preserved_of_frames {footprint : CompositeFootprint.Footprint}
    {before after : CompositeState}
    (frames : CompositeState.Frames footprint before after)
    (holds : AuthoritativeRuntimeWellFormed before)
    (touched : ∀ invariant, invariant ∈ authoritativeInvariants →
      invariant.untouchedBy footprint = false → invariant.holds after) :
    AuthoritativeRuntimeWellFormed after :=
  (authoritativeRuntimeWellFormed_iff_all after).2
    (ProjectionInvariant.All.preserved_of_frames frames
      ((authoritativeRuntimeWellFormed_iff_all before).1 holds) touched)

/-- A transition that writes only the invalidation-publication projection
preserves `AuthoritativeRuntimeWellFormed` once the publication protocol
invariant is re-established; every other conjunct is lifted. -/
theorem authoritativeRuntimeWellFormed_preserved_of_publicationFrames
    {before after : CompositeState}
    (frames : CompositeState.Frames
      (.ofLists [] [.invalidationPublication]) before after)
    (holds : AuthoritativeRuntimeWellFormed before)
    (publication : InvalidationPublication.WellFormed after.invalidationPublication) :
    AuthoritativeRuntimeWellFormed after := by
  refine authoritativeRuntimeWellFormed_preserved_of_frames frames holds ?_
  intro invariant member touched
  simp only [authoritativeInvariants, runtimeInvariants, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals first
    | exact publication
    | exact absurd touched (by decide)

/-- The successor invariant exposes the same proof-carrying PCI quarantine
carried by the sole global runtime invariant. -/
theorem AuthoritativeRuntimeWellFormed.dmaQuarantined {state : CompositeState}
    (hstate : AuthoritativeRuntimeWellFormed state) :
    state.DMAQuarantined :=
  hstate.1.dmaQuarantined

/-! ## Conditional invalidation publication projection -/

/-- Experimental projection relation for composing the standalone publication
protocol with a `CompositeState`.  This is deliberately an explicit premise,
not part of `AuthoritativeRuntimeWellFormed`: `bootRuntime` does not currently
construct it, and the ordinary authoritative gate does not preserve it across
all mapping, cleanup, and root-switch operations.  Consequently the helpers
below are conditional refinement lemmas, not the public global runtime gate. -/
def CompositeState.InvalidationProjectionCoherent
    (state : CompositeState) : Prop :=
  state.invalidationPublication.published = state.resumable.translations

structure InvalidationBoundaryOutcome where
  state : CompositeState
  accepted : Bool
  effect : StaleTranslation.Effect

private def installInvalidationPublication (state : CompositeState)
    (publication : InvalidationPublication.State) : CompositeState :=
  { state with invalidationPublication := publication }

@[simp] private theorem installInvalidationPublication_self
    (state : CompositeState) :
    installInvalidationPublication state state.invalidationPublication = state := by
  cases state
  rfl

private def authoritativePrepareInvalidation (state : CompositeState)
    (kind : InvalidationPublication.TransitionKind)
    (request : StaleTranslation.Request) : InvalidationBoundaryOutcome :=
  let outcome :=
    InvalidationPublication.prepare state.invalidationPublication kind request
  { state := installInvalidationPublication state outcome.state
    accepted := outcome.accepted
    effect := outcome.effect }

/-- Acknowledgement is confined to the operation family named by the trusted
boundary.  Even an otherwise exact ticket/effect pair cannot cross from one
family's completion path into another. -/
private def authoritativeAcknowledgeInvalidation (state : CompositeState)
    (kind : InvalidationPublication.TransitionKind)
    (ack : InvalidationPublication.Acknowledgement) :
    InvalidationBoundaryOutcome :=
  match state.invalidationPublication.pending with
  | some pending =>
      if pending.kind = kind then
        let outcome :=
          InvalidationPublication.acknowledge state.invalidationPublication ack
        { state := installInvalidationPublication state outcome.state
          accepted := outcome.accepted
          effect := outcome.effect }
      else
        { state, accepted := false, effect := .none }
  | none => { state, accepted := false, effect := .none }

def authoritativePrepareUnmap state subject addressSpace page :=
  authoritativePrepareInvalidation state .unmap
    (.unmap subject addressSpace page)

def authoritativePrepareProtect state subject addressSpace page permissions :=
  authoritativePrepareInvalidation state .protect
    (.protect subject addressSpace page permissions)

def authoritativePrepareRelease state subject slot :=
  authoritativePrepareInvalidation state .release (.release subject slot)

def authoritativePrepareDestroy state subject slot :=
  authoritativePrepareInvalidation state .destroy (.destroy subject slot)

def authoritativePrepareSwitch state addressSpace :=
  authoritativePrepareInvalidation state .switch (.switch addressSpace)

def authoritativeAcknowledgeUnmap state ack :=
  authoritativeAcknowledgeInvalidation state .unmap ack

def authoritativeAcknowledgeProtect state ack :=
  authoritativeAcknowledgeInvalidation state .protect ack

def authoritativeAcknowledgeRelease state ack :=
  authoritativeAcknowledgeInvalidation state .release ack

def authoritativeAcknowledgeDestroy state ack :=
  authoritativeAcknowledgeInvalidation state .destroy ack

def authoritativeAcknowledgeSwitch state ack :=
  authoritativeAcknowledgeInvalidation state .switch ack

/-- Conditional current-root unmap preparation derives both authority
identities from the execution latch.  Its only caller-controlled argument is
the virtual page.  Callers claiming agreement with the composite runtime must
separately establish `InvalidationProjectionCoherent`. -/
def authoritativePrepareCurrentUnmap (state : CompositeState) (page : Nat) :=
  authoritativePrepareUnmap state
    state.execution.core.context.currentSubject
    state.execution.core.context.activeAddressSpace page

/-- Install an acknowledged mapping/TLB successor into every authoritative
consumer of those projections, then retain the matching publication protocol
metadata (cleared pending ticket and advanced ticket history). -/
private def installAcknowledgedInvalidation (state : CompositeState)
    (publication : InvalidationPublication.State) : CompositeState :=
  installInvalidationPublication
    (installVirtualMemory state publication.published.virtual
      publication.published)
    publication

/-- The active public-unmap completion path publishes the exact acknowledged
logical successor into the authoritative translation and virtual-memory
projections.  Rejected acknowledgements use the generic literal-stutter path. -/
def authoritativeAcknowledgeCurrentUnmap (state : CompositeState)
    (ack : InvalidationPublication.Acknowledgement) :
    InvalidationBoundaryOutcome :=
  let outcome := authoritativeAcknowledgeUnmap state ack
  if outcome.accepted then
    { state := installAcknowledgedInvalidation state
        outcome.state.invalidationPublication
      accepted := true
      effect := outcome.effect }
  else
    outcome

def authoritativePublishReuse (state : CompositeState) :
    InvalidationBoundaryOutcome :=
  let outcome :=
    InvalidationPublication.publishReuse state.invalidationPublication
  { state := installInvalidationPublication state outcome.state
    accepted := outcome.accepted
    effect := outcome.effect }

/-! ## Invalidation-publication footprints

The conditional invalidation-publication entry points are not
`AuthoritativeOperation` constructors.  `InvalidationOperation` names each of
them so that they declare footprints exactly like the gate families:
preparation, acknowledgement, and reuse write only the publication projection;
the current-root preparation also reads the execution latch; and the active
current-unmap completion republishes the acknowledged mapping successor. -/

/-- Every public invalidation-publication entry point, with its arguments. -/
inductive InvalidationOperation where
  | prepareUnmap (subject : VirtualMapping.SubjectId)
      (addressSpace : VirtualMapping.AddressSpaceId) (page : VirtualMapping.VirtualPage)
  | prepareCurrentUnmap (page : Nat)
  | prepareProtect (subject : VirtualMapping.SubjectId)
      (addressSpace : VirtualMapping.AddressSpaceId) (page : VirtualMapping.VirtualPage)
      (permissions : VirtualMapping.Permissions)
  | prepareRelease (subject : VirtualMapping.SubjectId) (slot : VirtualMapping.SlotId)
  | prepareDestroy (subject : VirtualMapping.SubjectId) (slot : VirtualMapping.SlotId)
  | prepareSwitch (addressSpace : VirtualMapping.AddressSpaceId)
  | acknowledgeUnmap (ack : InvalidationPublication.Acknowledgement)
  | acknowledgeCurrentUnmap (ack : InvalidationPublication.Acknowledgement)
  | acknowledgeProtect (ack : InvalidationPublication.Acknowledgement)
  | acknowledgeRelease (ack : InvalidationPublication.Acknowledgement)
  | acknowledgeDestroy (ack : InvalidationPublication.Acknowledgement)
  | acknowledgeSwitch (ack : InvalidationPublication.Acknowledgement)
  | publishReuse

/-- Run one invalidation-publication entry point. -/
def InvalidationOperation.apply (state : CompositeState) :
    InvalidationOperation → InvalidationBoundaryOutcome
  | .prepareUnmap subject addressSpace page =>
      authoritativePrepareUnmap state subject addressSpace page
  | .prepareCurrentUnmap page => authoritativePrepareCurrentUnmap state page
  | .prepareProtect subject addressSpace page permissions =>
      authoritativePrepareProtect state subject addressSpace page permissions
  | .prepareRelease subject slot => authoritativePrepareRelease state subject slot
  | .prepareDestroy subject slot => authoritativePrepareDestroy state subject slot
  | .prepareSwitch addressSpace => authoritativePrepareSwitch state addressSpace
  | .acknowledgeUnmap ack => authoritativeAcknowledgeUnmap state ack
  | .acknowledgeCurrentUnmap ack => authoritativeAcknowledgeCurrentUnmap state ack
  | .acknowledgeProtect ack => authoritativeAcknowledgeProtect state ack
  | .acknowledgeRelease ack => authoritativeAcknowledgeRelease state ack
  | .acknowledgeDestroy ack => authoritativeAcknowledgeDestroy state ack
  | .acknowledgeSwitch ack => authoritativeAcknowledgeSwitch state ack
  | .publishReuse => authoritativePublishReuse state

/-- The declared footprint of each invalidation-publication entry point. -/
def InvalidationOperation.footprint : InvalidationOperation → CompositeFootprint.Footprint
  | .prepareCurrentUnmap _ => .ofLists [.execution] [.invalidationPublication]
  | .acknowledgeCurrentUnmap _ =>
      .ofLists [] (mappingProjections ++ [.invalidationPublication])
  | .prepareUnmap .. | .prepareProtect .. | .prepareRelease .. | .prepareDestroy ..
  | .prepareSwitch _ | .acknowledgeUnmap _ | .acknowledgeProtect _
  | .acknowledgeRelease _ | .acknowledgeDestroy _ | .acknowledgeSwitch _
  | .publishReuse => .ofLists [] [.invalidationPublication]

private theorem installInvalidationPublication_frames state publication :
    CompositeState.Frames (.ofLists [] [.invalidationPublication]) state
      (installInvalidationPublication state publication) := by
  composite_frame

private theorem authoritativePrepareInvalidation_frames state kind request :
    CompositeState.Frames (.ofLists [] [.invalidationPublication]) state
      (authoritativePrepareInvalidation state kind request).state :=
  installInvalidationPublication_frames _ _

private theorem authoritativeAcknowledgeInvalidation_frames state kind ack :
    CompositeState.Frames (.ofLists [] [.invalidationPublication]) state
      (authoritativeAcknowledgeInvalidation state kind ack).state := by
  unfold authoritativeAcknowledgeInvalidation
  repeat' split
  all_goals first
    | exact CompositeState.frames_of_eq _ rfl
    | exact installInvalidationPublication_frames _ _

private theorem authoritativePublishReuse_frames state :
    CompositeState.Frames (.ofLists [] [.invalidationPublication]) state
      (authoritativePublishReuse state).state :=
  installInvalidationPublication_frames _ _

private theorem installAcknowledgedInvalidation_frames state publication :
    CompositeState.Frames (.ofLists [] (mappingProjections ++ [.invalidationPublication]))
      state (installAcknowledgedInvalidation state publication) :=
  CompositeState.frames_trans _
    ((installVirtualMemory_frames _ _ _).mono (by footprint_within))
    ((installInvalidationPublication_frames _ _).mono (by footprint_within))

/-- **Invalidation frame rule.**  Every projection outside an
invalidation-publication entry point's declared write set is unchanged, on
accepted and rejected outcomes alike. -/
theorem InvalidationOperation.apply_frames (state : CompositeState)
    (operation : InvalidationOperation) :
    CompositeState.Frames operation.footprint state (operation.apply state).state := by
  cases operation with
  | prepareUnmap _ _ _ | prepareProtect _ _ _ _ | prepareRelease _ _ | prepareDestroy _ _
  | prepareSwitch _ => exact authoritativePrepareInvalidation_frames _ _ _
  | prepareCurrentUnmap _ =>
      exact (authoritativePrepareInvalidation_frames _ _ _).mono (by footprint_within)
  | acknowledgeUnmap _ | acknowledgeProtect _ | acknowledgeRelease _ | acknowledgeDestroy _
  | acknowledgeSwitch _ => exact authoritativeAcknowledgeInvalidation_frames _ _ _
  | publishReuse => exact authoritativePublishReuse_frames _
  | acknowledgeCurrentUnmap ack =>
      simp only [InvalidationOperation.apply, InvalidationOperation.footprint,
        authoritativeAcknowledgeCurrentUnmap]
      by_cases accepted : (authoritativeAcknowledgeUnmap state ack).accepted = true
      · simp only [accepted, ↓reduceIte]
        exact installAcknowledgedInvalidation_frames _ _
      · simp only [accepted, ↓reduceIte]
        exact (authoritativeAcknowledgeInvalidation_frames _ _ _).mono (by footprint_within)

/-- No invalidation-publication entry point writes the direct-port or DMA
authority. -/
theorem InvalidationOperation.footprint_untouched_authority
    (operation : InvalidationOperation) :
    CompositeFootprint.Untouched operation.footprint .directPortIO ∧
      CompositeFootprint.Untouched operation.footprint .dmaAccepted ∧
      CompositeFootprint.Untouched operation.footprint .dmaObserved := by
  cases operation <;>
    simp only [CompositeFootprint.Untouched, InvalidationOperation.footprint] <;> decide

private theorem authoritativeAcknowledgeInvalidation_reads (left right : CompositeState)
    kind ack
    (agree : CompositeState.AgreeOn
      (CompositeFootprint.Footprint.ofLists [] [.invalidationPublication]).reads left right) :
    (authoritativeAcknowledgeInvalidation left kind ack).accepted =
        (authoritativeAcknowledgeInvalidation right kind ack).accepted ∧
      (authoritativeAcknowledgeInvalidation left kind ack).effect =
        (authoritativeAcknowledgeInvalidation right kind ack).effect ∧
      CompositeState.AgreeOn
        (CompositeFootprint.Footprint.ofLists [] [.invalidationPublication]).writes
        (authoritativeAcknowledgeInvalidation left kind ack).state
        (authoritativeAcknowledgeInvalidation right kind ack).state := by
  cases left; cases right
  agree_subst agree
  clear agree
  unfold authoritativeAcknowledgeInvalidation
  dsimp only
  repeat' split
  all_goals
    refine ⟨rfl, rfl, ?_⟩
    intro projection written
    cases projection <;> (try exact absurd written Bool.false_ne_true)
    rfl

/-- **Invalidation read independence.**  Two states that agree on an
invalidation-publication entry point's declared reads produce the same
acceptance and machine effect, and post-states that agree on its declared
writes. -/
theorem InvalidationOperation.apply_reads (left right : CompositeState)
    (operation : InvalidationOperation)
    (agree : CompositeState.AgreeOn operation.footprint.reads left right) :
    (operation.apply left).accepted = (operation.apply right).accepted ∧
      (operation.apply left).effect = (operation.apply right).effect ∧
      CompositeState.AgreeOn operation.footprint.writes
        (operation.apply left).state (operation.apply right).state := by
  cases operation
  case acknowledgeCurrentUnmap ack =>
    obtain ⟨accepted, effect, published⟩ :=
      authoritativeAcknowledgeInvalidation_reads left right .unmap ack
        (agree.mono fun projection supported => by
          cases projection <;> first | rfl | exact absurd supported Bool.false_ne_true)
    simp only [InvalidationOperation.apply, authoritativeAcknowledgeCurrentUnmap,
      authoritativeAcknowledgeUnmap]
    by_cases hright :
        (authoritativeAcknowledgeInvalidation right .unmap ack).accepted = true
    · have hleft := accepted.trans hright
      simp only [hleft, hright, ↓reduceIte]
      refine ⟨by trivial, effect, ?_⟩
      have publication := published .invalidationPublication rfl
      simp only [CompositeState.project] at publication
      rw [publication]
      cases left; cases right
      agree_subst agree
      intro projection written
      cases projection <;> (try exact absurd written Bool.false_ne_true)
      all_goals rfl
    · have hleft : ¬ (authoritativeAcknowledgeInvalidation left .unmap ack).accepted = true :=
        fun hleft => hright (accepted.symm.trans hleft)
      simp only [hleft, hright, ↓reduceIte]
      refine ⟨accepted, effect, ?_⟩
      cases left; cases right
      agree_subst agree
      clear agree accepted effect published hright
      intro projection written
      cases projection <;> (try exact absurd written Bool.false_ne_true)
      all_goals
        unfold authoritativeAcknowledgeInvalidation
        dsimp only
        repeat' split
        all_goals rfl
  case acknowledgeUnmap ack | acknowledgeProtect ack | acknowledgeRelease ack
      | acknowledgeDestroy ack | acknowledgeSwitch ack =>
    exact authoritativeAcknowledgeInvalidation_reads _ _ _ _ agree
  all_goals
    cases left; cases right
    agree_subst agree
    clear agree
    refine ⟨rfl, rfl, ?_⟩
    intro projection written
    cases projection <;> (try exact absurd written Bool.false_ne_true)
    all_goals rfl

/-- Every invalidation-publication entry point other than the active
current-unmap completion writes only the publication projection.  It
therefore preserves `RuntimeWellFormed` and the deferred-cancellation
classification by the frame rule alone, without inspecting the protocol. -/
theorem InvalidationOperation.preserves_runtimeWellFormed (state : CompositeState)
    (operation : InvalidationOperation)
    (publicationOnly : ∀ ack, operation ≠ .acknowledgeCurrentUnmap ack)
    (hstate : RuntimeWellFormed state)
    (hdeferred : state.DeferredCancellationWellFormed) :
    RuntimeWellFormed (operation.apply state).state ∧
      (operation.apply state).state.DeferredCancellationWellFormed := by
  have runtime : RuntimeWellFormed (operation.apply state).state := by
    refine runtimeWellFormed_preserved_of_untouched (operation.apply_frames state) ?_ hstate
    intro invariant member
    cases operation
    case acknowledgeCurrentUnmap ack => exact absurd rfl (publicationOnly ack)
    all_goals
      simp only [runtimeInvariants, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl
      all_goals rfl
  have deferred : deferredCancellationInvariant.untouchedBy operation.footprint = true := by
    cases operation
    case acknowledgeCurrentUnmap ack => exact absurd rfl (publicationOnly ack)
    all_goals rfl
  exact ⟨runtime, deferredCancellationInvariant.preserved_of_frames
    (operation.apply_frames state) deferred hdeferred⟩

private theorem authoritativePrepareInvalidation_preserves
    state kind request (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativePrepareInvalidation state kind request).state := by
  refine authoritativeRuntimeWellFormed_preserved_of_publicationFrames
    (authoritativePrepareInvalidation_frames state kind request) hstate ?_
  simpa [authoritativePrepareInvalidation, installInvalidationPublication]
    using InvalidationPublication.prepare_preserves_wellFormed
      state.invalidationPublication kind request hstate.publication

private theorem authoritativeAcknowledgeInvalidation_preserves
    state kind ack (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeAcknowledgeInvalidation state kind ack).state := by
  refine authoritativeRuntimeWellFormed_preserved_of_publicationFrames
    (authoritativeAcknowledgeInvalidation_frames state kind ack) hstate ?_
  cases hpending : state.invalidationPublication.pending with
  | none => simpa [authoritativeAcknowledgeInvalidation, hpending] using hstate.publication
  | some pending =>
      by_cases hkind : pending.kind = kind
      · simp only [authoritativeAcknowledgeInvalidation, hpending, hkind, ite_eq_left]
        simpa [installInvalidationPublication] using
          InvalidationPublication.acknowledge_preserves_wellFormed
            state.invalidationPublication ack hstate.publication
      · simpa [authoritativeAcknowledgeInvalidation, hpending, hkind] using hstate.publication

private theorem authoritativePublishReuse_preserves
    state (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed (authoritativePublishReuse state).state := by
  refine authoritativeRuntimeWellFormed_preserved_of_publicationFrames
    (authoritativePublishReuse_frames state) hstate ?_
  simpa [authoritativePublishReuse, installInvalidationPublication] using
    InvalidationPublication.publishReuse_preserves_wellFormed
      state.invalidationPublication hstate.publication

theorem authoritativePrepareUnmap_preserves_authoritativeRuntimeWellFormed
    state subject addressSpace page
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativePrepareUnmap state subject addressSpace page).state :=
  authoritativePrepareInvalidation_preserves _ _ _ hstate

theorem authoritativePrepareCurrentUnmap_preserves_authoritativeRuntimeWellFormed
    state page (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativePrepareCurrentUnmap state page).state :=
  authoritativePrepareUnmap_preserves_authoritativeRuntimeWellFormed
    state _ _ page hstate

/-- Preparation retains the exact authoritative translation projection; no
mapping or cached entry becomes visible before acknowledgement. -/
theorem authoritativePrepareCurrentUnmap_preserves_projection
    state page (hprojection : state.InvalidationProjectionCoherent) :
    CompositeState.InvalidationProjectionCoherent
      (authoritativePrepareCurrentUnmap state page).state := by
  unfold CompositeState.InvalidationProjectionCoherent
  simpa [authoritativePrepareCurrentUnmap, authoritativePrepareUnmap,
    authoritativePrepareInvalidation, installInvalidationPublication] using
    (InvalidationPublication.prepare_retains_published
      state.invalidationPublication .unmap
      (.unmap state.execution.core.context.currentSubject
        state.execution.core.context.activeAddressSpace page)).trans hprojection

theorem authoritativePrepareProtect_preserves_authoritativeRuntimeWellFormed
    state subject addressSpace page permissions
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativePrepareProtect state subject addressSpace page permissions).state :=
  authoritativePrepareInvalidation_preserves _ _ _ hstate

theorem authoritativePrepareRelease_preserves_authoritativeRuntimeWellFormed
    state subject slot (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativePrepareRelease state subject slot).state :=
  authoritativePrepareInvalidation_preserves _ _ _ hstate

theorem authoritativePrepareDestroy_preserves_authoritativeRuntimeWellFormed
    state subject slot
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativePrepareDestroy state subject slot).state :=
  authoritativePrepareInvalidation_preserves _ _ _ hstate

theorem authoritativePrepareSwitch_preserves_authoritativeRuntimeWellFormed
    state addressSpace (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativePrepareSwitch state addressSpace).state :=
  authoritativePrepareInvalidation_preserves _ _ _ hstate

theorem authoritativeAcknowledgeUnmap_preserves_authoritativeRuntimeWellFormed
    state ack (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeAcknowledgeUnmap state ack).state :=
  authoritativeAcknowledgeInvalidation_preserves _ _ _ hstate

theorem authoritativeAcknowledgeProtect_preserves_authoritativeRuntimeWellFormed
    state ack (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeAcknowledgeProtect state ack).state :=
  authoritativeAcknowledgeInvalidation_preserves _ _ _ hstate

theorem authoritativeAcknowledgeRelease_preserves_authoritativeRuntimeWellFormed
    state ack (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeAcknowledgeRelease state ack).state :=
  authoritativeAcknowledgeInvalidation_preserves _ _ _ hstate

theorem authoritativeAcknowledgeDestroy_preserves_authoritativeRuntimeWellFormed
    state ack (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeAcknowledgeDestroy state ack).state :=
  authoritativeAcknowledgeInvalidation_preserves _ _ _ hstate

theorem authoritativeAcknowledgeSwitch_preserves_authoritativeRuntimeWellFormed
    state ack (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeAcknowledgeSwitch state ack).state :=
  authoritativeAcknowledgeInvalidation_preserves _ _ _ hstate

theorem authoritativePublishReuse_preserves_authoritativeRuntimeWellFormed
    state (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed (authoritativePublishReuse state).state :=
  authoritativePublishReuse_preserves state hstate

/-- Every rejected authoritative preparation is a complete composite-state
stutter and requests no machine effect. -/
private theorem authoritativePrepareInvalidation_rejected_inert
    state kind request
    (hrejected :
      (authoritativePrepareInvalidation state kind request).accepted = false) :
    (authoritativePrepareInvalidation state kind request).state = state ∧
      (authoritativePrepareInvalidation state kind request).effect = .none := by
  have hinert :=
    InvalidationPublication.prepare_rejected_inert
      state.invalidationPublication kind request hrejected
  constructor
  · change installInvalidationPublication state
      (InvalidationPublication.prepare state.invalidationPublication kind request).state =
        state
    rw [hinert.1]
    exact installInvalidationPublication_self state
  · exact hinert.2

/-- Every rejected authoritative acknowledgement, including a missing or
mismatched operation-family completion, preserves the full composite state. -/
private theorem authoritativeAcknowledgeInvalidation_rejected_inert
    state kind ack
    (hrejected :
      (authoritativeAcknowledgeInvalidation state kind ack).accepted = false) :
    (authoritativeAcknowledgeInvalidation state kind ack).state = state ∧
      (authoritativeAcknowledgeInvalidation state kind ack).effect = .none := by
  cases hpending : state.invalidationPublication.pending with
  | none =>
      simp [authoritativeAcknowledgeInvalidation, hpending]
  | some pending =>
      by_cases hkind : pending.kind = kind
      · have hrejected' :
            (InvalidationPublication.acknowledge
              state.invalidationPublication ack).accepted = false := by
          simpa [authoritativeAcknowledgeInvalidation, hpending, hkind] using
            hrejected
        have hinert :=
          InvalidationPublication.acknowledge_rejected_inert
            state.invalidationPublication ack hrejected'
        constructor
        · simp only [authoritativeAcknowledgeInvalidation, hpending, hkind, ite_eq_left]
          rw [hinert.1]
          exact installInvalidationPublication_self state
        · simpa [authoritativeAcknowledgeInvalidation, hpending, hkind] using
            hinert.2
      · simp [authoritativeAcknowledgeInvalidation, hpending, hkind]

private theorem authoritativeAcknowledgeInvalidation_accepted_exact
    state kind ack
    (haccepted :
      (authoritativeAcknowledgeInvalidation state kind ack).accepted = true) :
    ∃ pending,
      state.invalidationPublication.pending = some pending ∧
      pending.kind = kind ∧
      ack.ticket = pending.ticket ∧
      ack.effect = pending.step.effect ∧
      (authoritativeAcknowledgeInvalidation state kind ack).state.invalidationPublication.published = pending.step.state ∧
      (authoritativeAcknowledgeInvalidation state kind ack).state.invalidationPublication.pending = none := by
  cases hpending : state.invalidationPublication.pending with
  | none =>
      simp [authoritativeAcknowledgeInvalidation, hpending] at haccepted
  | some pending =>
      by_cases hkind : pending.kind = kind
      · have haccepted' :
            (InvalidationPublication.acknowledge
              state.invalidationPublication ack).accepted = true := by
          simpa [authoritativeAcknowledgeInvalidation, hpending, hkind] using
            haccepted
        obtain ⟨exactPending, hexactPending, hticket, heffect,
            hpublished, hcleared⟩ :=
          InvalidationPublication.acknowledge_accepted_exact
            state.invalidationPublication ack haccepted'
        have hpendingEq : exactPending = pending := by
          rw [hpending] at hexactPending
          exact (Option.some.inj hexactPending).symm
        subst exactPending
        exact ⟨pending, rfl, hkind, hticket, heffect,
          by simpa [authoritativeAcknowledgeInvalidation, hpending, hkind,
            installInvalidationPublication] using hpublished,
          by simpa [authoritativeAcknowledgeInvalidation, hpending, hkind,
            installInvalidationPublication] using hcleared⟩
      · simp [authoritativeAcknowledgeInvalidation, hpending, hkind] at haccepted

private theorem authoritativePrepareInvalidation_accepted_pending_exact
    state kind request
    (haccepted :
      (authoritativePrepareInvalidation state kind request).accepted = true) :
    ∃ pending,
      (authoritativePrepareInvalidation state kind request).state.invalidationPublication.pending = some pending ∧
      pending.ticket = state.invalidationPublication.nextTicket ∧
      pending.kind = kind ∧
      pending.step =
        StaleTranslation.step state.invalidationPublication.published request ∧
      pending.step.accepted = true ∧
      (authoritativePrepareInvalidation state kind request).effect =
        pending.step.effect ∧
      (authoritativePrepareInvalidation state kind request).state.invalidationPublication.published =
        state.invalidationPublication.published := by
  simpa [authoritativePrepareInvalidation, installInvalidationPublication]
    using InvalidationPublication.prepare_accepted_pending_exact
      state.invalidationPublication kind request haccepted

/-- Accepted unmap preparation is determined and confined to the checked
address-space page, while retaining the published mapping/cache state until
that exact pending step is acknowledged. -/
theorem authoritativePrepareUnmap_accepted_effect_ordered
    state subject addressSpace page
    (haccepted :
      (authoritativePrepareUnmap state subject addressSpace page).accepted = true) :
    (authoritativePrepareUnmap state subject addressSpace page).effect =
        .page addressSpace page ∧
      (authoritativePrepareUnmap state subject addressSpace page).state.invalidationPublication.published =
        state.invalidationPublication.published ∧
      ∃ pending,
        (authoritativePrepareUnmap state subject addressSpace page).state.invalidationPublication.pending = some pending ∧
        pending.ticket = state.invalidationPublication.nextTicket ∧
        pending.kind = .unmap ∧
        pending.step =
          StaleTranslation.step state.invalidationPublication.published
            (.unmap subject addressSpace page) := by
  obtain ⟨pending, hpending, hticket, hkind, hstep, hstepAccepted,
      heffect, hpublished⟩ :=
    authoritativePrepareInvalidation_accepted_pending_exact
      state .unmap (.unmap subject addressSpace page) haccepted
  rw [hstep] at hstepAccepted
  have hdetermined :=
    StaleTranslation.unmap_accepted_effect
      state.invalidationPublication.published subject addressSpace page
        hstepAccepted
  exact ⟨heffect.trans (hstep ▸ hdetermined), hpublished,
    pending, hpending, hticket, hkind, hstep⟩

/-- The current-unmap machine effect is confined to the active authoritative
root and caller-selected page; neither subject nor root is an input. -/
theorem authoritativePrepareCurrentUnmap_accepted_effect_ordered
    state page
    (haccepted :
      (authoritativePrepareCurrentUnmap state page).accepted = true) :
    (authoritativePrepareCurrentUnmap state page).effect =
        .page state.execution.core.context.activeAddressSpace page ∧
      ((authoritativePrepareCurrentUnmap state page).state.invalidationPublication.published) =
        state.invalidationPublication.published := by
  have h := authoritativePrepareUnmap_accepted_effect_ordered state
    state.execution.core.context.currentSubject
    state.execution.core.context.activeAddressSpace page haccepted
  exact ⟨h.1, h.2.1⟩

theorem authoritativePrepareProtect_accepted_effect_ordered
    state subject addressSpace page permissions
    (haccepted :
      (authoritativePrepareProtect state subject addressSpace page permissions).accepted = true) :
    (authoritativePrepareProtect state subject addressSpace page permissions).effect =
        .page addressSpace page ∧
      (authoritativePrepareProtect state subject addressSpace page permissions).state.invalidationPublication.published =
        state.invalidationPublication.published ∧
      ∃ pending,
        (authoritativePrepareProtect state subject addressSpace page permissions).state.invalidationPublication.pending = some pending ∧
        pending.ticket = state.invalidationPublication.nextTicket ∧
        pending.kind = .protect ∧
        pending.step =
          StaleTranslation.step state.invalidationPublication.published
            (.protect subject addressSpace page permissions) := by
  obtain ⟨pending, hpending, hticket, hkind, hstep, hstepAccepted,
      heffect, hpublished⟩ :=
    authoritativePrepareInvalidation_accepted_pending_exact
      state .protect (.protect subject addressSpace page permissions) haccepted
  rw [hstep] at hstepAccepted
  have hdetermined :=
    StaleTranslation.protect_accepted_effect
      state.invalidationPublication.published subject addressSpace page permissions
        hstepAccepted
  exact ⟨heffect.trans (hstep ▸ hdetermined), hpublished,
    pending, hpending, hticket, hkind, hstep⟩

theorem authoritativePrepareRelease_accepted_effect_ordered
    state subject slot
    (haccepted :
      (authoritativePrepareRelease state subject slot).accepted = true) :
    (authoritativePrepareRelease state subject slot).effect = .flush ∧
      (authoritativePrepareRelease state subject slot).state.invalidationPublication.published =
        state.invalidationPublication.published ∧
      ∃ pending,
        (authoritativePrepareRelease state subject slot).state.invalidationPublication.pending = some pending ∧
        pending.ticket = state.invalidationPublication.nextTicket ∧
        pending.kind = .release ∧
        pending.step =
          StaleTranslation.step state.invalidationPublication.published
            (.release subject slot) := by
  obtain ⟨pending, hpending, hticket, hkind, hstep, hstepAccepted,
      heffect, hpublished⟩ :=
    authoritativePrepareInvalidation_accepted_pending_exact
      state .release (.release subject slot) haccepted
  rw [hstep] at hstepAccepted
  have hdetermined :=
    StaleTranslation.release_accepted_effect
      state.invalidationPublication.published subject slot hstepAccepted
  exact ⟨heffect.trans (hstep ▸ hdetermined), hpublished,
    pending, hpending, hticket, hkind, hstep⟩

theorem authoritativePrepareDestroy_accepted_effect_ordered
    state subject slot
    (haccepted :
      (authoritativePrepareDestroy state subject slot).accepted = true) :
    ∃ cap,
      Capability.lookup
          state.invalidationPublication.published.virtual.memory.capabilities
          subject slot = .found cap ∧
      (authoritativePrepareDestroy state subject slot).effect =
        .space cap.object ∧
      (authoritativePrepareDestroy state subject slot).state.invalidationPublication.published =
        state.invalidationPublication.published ∧
      ∃ pending,
        (authoritativePrepareDestroy state subject slot).state.invalidationPublication.pending = some pending ∧
        pending.ticket = state.invalidationPublication.nextTicket ∧
        pending.kind = .destroy ∧
        pending.step =
          StaleTranslation.step state.invalidationPublication.published
            (.destroy subject slot) := by
  obtain ⟨pending, hpending, hticket, hkind, hstep, hstepAccepted,
      heffect, hpublished⟩ :=
    authoritativePrepareInvalidation_accepted_pending_exact
      state .destroy (.destroy subject slot) haccepted
  rw [hstep] at hstepAccepted
  obtain ⟨cap, hlookup, hdetermined⟩ :=
    StaleTranslation.destroy_accepted_effect
      state.invalidationPublication.published subject slot hstepAccepted
  exact ⟨cap, hlookup, heffect.trans (hstep ▸ hdetermined), hpublished,
    pending, hpending, hticket, hkind, hstep⟩

theorem authoritativePrepareSwitch_accepted_effect_ordered
    state addressSpace
    (haccepted :
      (authoritativePrepareSwitch state addressSpace).accepted = true) :
    (authoritativePrepareSwitch state addressSpace).effect = .flush ∧
      (authoritativePrepareSwitch state addressSpace).state.invalidationPublication.published =
        state.invalidationPublication.published ∧
      ∃ pending,
        (authoritativePrepareSwitch state addressSpace).state.invalidationPublication.pending = some pending ∧
        pending.ticket = state.invalidationPublication.nextTicket ∧
        pending.kind = .switch ∧
        pending.step =
          StaleTranslation.step state.invalidationPublication.published
            (.switch addressSpace) := by
  obtain ⟨pending, hpending, hticket, hkind, hstep, hstepAccepted,
      heffect, hpublished⟩ :=
    authoritativePrepareInvalidation_accepted_pending_exact
      state .switch (.switch addressSpace) haccepted
  have hdetermined :=
    (StaleTranslation.switch_effect
      state.invalidationPublication.published addressSpace).2
  exact ⟨heffect.trans (hstep ▸ hdetermined), hpublished,
    pending, hpending, hticket, hkind, hstep⟩

/-- Each operation-family completion publishes only the exact pending
successor, after matching both its fresh ticket and determined effect. -/
theorem authoritativeAcknowledgeUnmap_accepted_exact state ack
    (haccepted : (authoritativeAcknowledgeUnmap state ack).accepted = true) :
    ∃ pending,
      state.invalidationPublication.pending = some pending ∧
      pending.kind = .unmap ∧
      ack.ticket = pending.ticket ∧
      ack.effect = pending.step.effect ∧
      (authoritativeAcknowledgeUnmap state ack).state.invalidationPublication.published = pending.step.state ∧
      (authoritativeAcknowledgeUnmap state ack).state.invalidationPublication.pending = none :=
  authoritativeAcknowledgeInvalidation_accepted_exact _ _ _ haccepted

theorem authoritativeAcknowledgeProtect_accepted_exact state ack
    (haccepted : (authoritativeAcknowledgeProtect state ack).accepted = true) :
    ∃ pending,
      state.invalidationPublication.pending = some pending ∧
      pending.kind = .protect ∧
      ack.ticket = pending.ticket ∧
      ack.effect = pending.step.effect ∧
      (authoritativeAcknowledgeProtect state ack).state.invalidationPublication.published = pending.step.state ∧
      (authoritativeAcknowledgeProtect state ack).state.invalidationPublication.pending = none :=
  authoritativeAcknowledgeInvalidation_accepted_exact _ _ _ haccepted

theorem authoritativeAcknowledgeRelease_accepted_exact state ack
    (haccepted : (authoritativeAcknowledgeRelease state ack).accepted = true) :
    ∃ pending,
      state.invalidationPublication.pending = some pending ∧
      pending.kind = .release ∧
      ack.ticket = pending.ticket ∧
      ack.effect = pending.step.effect ∧
      (authoritativeAcknowledgeRelease state ack).state.invalidationPublication.published = pending.step.state ∧
      (authoritativeAcknowledgeRelease state ack).state.invalidationPublication.pending = none :=
  authoritativeAcknowledgeInvalidation_accepted_exact _ _ _ haccepted

theorem authoritativeAcknowledgeDestroy_accepted_exact state ack
    (haccepted : (authoritativeAcknowledgeDestroy state ack).accepted = true) :
    ∃ pending,
      state.invalidationPublication.pending = some pending ∧
      pending.kind = .destroy ∧
      ack.ticket = pending.ticket ∧
      ack.effect = pending.step.effect ∧
      (authoritativeAcknowledgeDestroy state ack).state.invalidationPublication.published = pending.step.state ∧
      (authoritativeAcknowledgeDestroy state ack).state.invalidationPublication.pending = none :=
  authoritativeAcknowledgeInvalidation_accepted_exact _ _ _ haccepted

theorem authoritativeAcknowledgeSwitch_accepted_exact state ack
    (haccepted : (authoritativeAcknowledgeSwitch state ack).accepted = true) :
    ∃ pending,
      state.invalidationPublication.pending = some pending ∧
      pending.kind = .switch ∧
      ack.ticket = pending.ticket ∧
      ack.effect = pending.step.effect ∧
      (authoritativeAcknowledgeSwitch state ack).state.invalidationPublication.published = pending.step.state ∧
      (authoritativeAcknowledgeSwitch state ack).state.invalidationPublication.pending = none :=
  authoritativeAcknowledgeInvalidation_accepted_exact _ _ _ haccepted

/-- An unmap request for a non-owned address space cannot issue even a page
invalidation: the entire authoritative composite state is unchanged. -/
theorem authoritativePrepareUnmap_wrong_owner_inert
    state subject addressSpace page owner
    (howner :
      state.invalidationPublication.published.virtual.owner addressSpace =
        some owner)
    (hne : owner ≠ subject) :
    (authoritativePrepareUnmap state subject addressSpace page).accepted = false ∧
      (authoritativePrepareUnmap state subject addressSpace page).state = state ∧
      (authoritativePrepareUnmap state subject addressSpace page).effect = .none := by
  cases hpending : state.invalidationPublication.pending with
  | some pending =>
      simp [authoritativePrepareUnmap, authoritativePrepareInvalidation,
        InvalidationPublication.prepare, hpending]
  | none =>
      have hinert :=
        StaleTranslation.unmap_wrong_owner_inert
          state.invalidationPublication.published subject addressSpace page owner
            howner hne
      simp [authoritativePrepareUnmap, authoritativePrepareInvalidation,
        InvalidationPublication.prepare, hpending, hinert.1]

theorem authoritativePrepareProtect_wrong_owner_inert
    state subject addressSpace page permissions owner
    (howner :
      state.invalidationPublication.published.virtual.owner addressSpace =
        some owner)
    (hne : owner ≠ subject) :
    (authoritativePrepareProtect state subject addressSpace page permissions).accepted = false ∧
      (authoritativePrepareProtect state subject addressSpace page permissions).state = state ∧
      (authoritativePrepareProtect state subject addressSpace page permissions).effect = .none := by
  cases hpending : state.invalidationPublication.pending with
  | some pending =>
      simp [authoritativePrepareProtect, authoritativePrepareInvalidation,
        InvalidationPublication.prepare, hpending]
  | none =>
      have hinert :=
        StaleTranslation.protect_wrong_owner_inert
          state.invalidationPublication.published subject addressSpace page
            permissions owner howner hne
      simp [authoritativePrepareProtect, authoritativePrepareInvalidation,
        InvalidationPublication.prepare, hpending, hinert.1]

theorem authoritativePrepareUnmap_rejected_inert state subject addressSpace page
    (hrejected :
      (authoritativePrepareUnmap state subject addressSpace page).accepted = false) :
    (authoritativePrepareUnmap state subject addressSpace page).state = state ∧
      (authoritativePrepareUnmap state subject addressSpace page).effect = .none :=
  authoritativePrepareInvalidation_rejected_inert _ _ _ hrejected

theorem authoritativePrepareCurrentUnmap_rejected_inert state page
    (hrejected :
      (authoritativePrepareCurrentUnmap state page).accepted = false) :
    (authoritativePrepareCurrentUnmap state page).state = state ∧
      (authoritativePrepareCurrentUnmap state page).effect = .none :=
  authoritativePrepareUnmap_rejected_inert _ _ _ _ hrejected

theorem authoritativePrepareProtect_rejected_inert
    state subject addressSpace page permissions
    (hrejected :
      (authoritativePrepareProtect state subject addressSpace page permissions).accepted = false) :
    (authoritativePrepareProtect state subject addressSpace page permissions).state =
        state ∧
      (authoritativePrepareProtect state subject addressSpace page permissions).effect =
        .none :=
  authoritativePrepareInvalidation_rejected_inert _ _ _ hrejected

theorem authoritativePrepareRelease_rejected_inert state subject slot
    (hrejected :
      (authoritativePrepareRelease state subject slot).accepted = false) :
    (authoritativePrepareRelease state subject slot).state = state ∧
      (authoritativePrepareRelease state subject slot).effect = .none :=
  authoritativePrepareInvalidation_rejected_inert _ _ _ hrejected

theorem authoritativePrepareDestroy_rejected_inert state subject slot
    (hrejected :
      (authoritativePrepareDestroy state subject slot).accepted = false) :
    (authoritativePrepareDestroy state subject slot).state = state ∧
      (authoritativePrepareDestroy state subject slot).effect = .none :=
  authoritativePrepareInvalidation_rejected_inert _ _ _ hrejected

theorem authoritativePrepareSwitch_rejected_inert state addressSpace
    (hrejected :
      (authoritativePrepareSwitch state addressSpace).accepted = false) :
    (authoritativePrepareSwitch state addressSpace).state = state ∧
      (authoritativePrepareSwitch state addressSpace).effect = .none :=
  authoritativePrepareInvalidation_rejected_inert _ _ _ hrejected

theorem authoritativeAcknowledgeUnmap_rejected_inert state ack
    (hrejected : (authoritativeAcknowledgeUnmap state ack).accepted = false) :
    (authoritativeAcknowledgeUnmap state ack).state = state ∧
      (authoritativeAcknowledgeUnmap state ack).effect = .none :=
  authoritativeAcknowledgeInvalidation_rejected_inert _ _ _ hrejected

theorem authoritativeAcknowledgeCurrentUnmap_rejected_inert state ack
    (hrejected :
      (authoritativeAcknowledgeCurrentUnmap state ack).accepted = false) :
    (authoritativeAcknowledgeCurrentUnmap state ack).state = state ∧
      (authoritativeAcknowledgeCurrentUnmap state ack).effect = .none := by
  cases haccepted :
      (authoritativeAcknowledgeUnmap state ack).accepted with
  | false =>
      have hinert :=
        authoritativeAcknowledgeUnmap_rejected_inert state ack haccepted
      simpa [authoritativeAcknowledgeCurrentUnmap, haccepted] using hinert
  | true =>
      simp [authoritativeAcknowledgeCurrentUnmap, haccepted] at hrejected

/-- An accepted current-unmap acknowledgement installs one identical state in
the publication protocol, authoritative TLB, and both virtual-memory
consumers. -/
theorem authoritativeAcknowledgeCurrentUnmap_accepted_projects
    state ack
    (haccepted :
      (authoritativeAcknowledgeCurrentUnmap state ack).accepted = true) :
    let next := (authoritativeAcknowledgeCurrentUnmap state ack).state
    next.InvalidationProjectionCoherent ∧
      next.virtualMemory = next.resumable.translations.virtual ∧
      next.ipc.virtualMemory = next.virtualMemory := by
  cases haccepted' :
      (authoritativeAcknowledgeUnmap state ack).accepted with
  | false =>
      simp [authoritativeAcknowledgeCurrentUnmap, haccepted'] at haccepted
  | true =>
      simp [authoritativeAcknowledgeCurrentUnmap, haccepted',
        CompositeState.InvalidationProjectionCoherent,
        installAcknowledgedInvalidation, installInvalidationPublication,
        installVirtualMemory]

theorem authoritativeAcknowledgeProtect_rejected_inert state ack
    (hrejected : (authoritativeAcknowledgeProtect state ack).accepted = false) :
    (authoritativeAcknowledgeProtect state ack).state = state ∧
      (authoritativeAcknowledgeProtect state ack).effect = .none :=
  authoritativeAcknowledgeInvalidation_rejected_inert _ _ _ hrejected

theorem authoritativeAcknowledgeRelease_rejected_inert state ack
    (hrejected : (authoritativeAcknowledgeRelease state ack).accepted = false) :
    (authoritativeAcknowledgeRelease state ack).state = state ∧
      (authoritativeAcknowledgeRelease state ack).effect = .none :=
  authoritativeAcknowledgeInvalidation_rejected_inert _ _ _ hrejected

theorem authoritativeAcknowledgeDestroy_rejected_inert state ack
    (hrejected : (authoritativeAcknowledgeDestroy state ack).accepted = false) :
    (authoritativeAcknowledgeDestroy state ack).state = state ∧
      (authoritativeAcknowledgeDestroy state ack).effect = .none :=
  authoritativeAcknowledgeInvalidation_rejected_inert _ _ _ hrejected

theorem authoritativeAcknowledgeSwitch_rejected_inert state ack
    (hrejected : (authoritativeAcknowledgeSwitch state ack).accepted = false) :
    (authoritativeAcknowledgeSwitch state ack).state = state ∧
      (authoritativeAcknowledgeSwitch state ack).effect = .none :=
  authoritativeAcknowledgeInvalidation_rejected_inert _ _ _ hrejected

/-- No accepted prepare, including release and destruction, changes the
caller-visible logical mapping/cache state before machine acknowledgement. -/
theorem authoritativePrepare_retains_published state kind request :
    (authoritativePrepareInvalidation state kind request).state.invalidationPublication.published =
      state.invalidationPublication.published :=
  InvalidationPublication.prepare_retains_published
    state.invalidationPublication kind request

/-- A pending accepted transition makes reuse publication impossible.  Thus a
released frame cannot become allocatable or mappable through the authoritative
reuse boundary before the exact invalidation acknowledgement. -/
theorem authoritativePrepare_prohibits_reuse_before_ack state kind request
    (haccepted :
      (authoritativePrepareInvalidation state kind request).accepted = true) :
    (authoritativePublishReuse
      (authoritativePrepareInvalidation state kind request).state).accepted =
        false := by
  have hpending :=
    InvalidationPublication.prepare_accepted_fresh_ticket
      state.invalidationPublication kind request haccepted
  rcases hpending with ⟨pending, hpending, _, _⟩
  change (InvalidationPublication.publishReuse
    (InvalidationPublication.prepare state.invalidationPublication kind request).state).accepted =
      false
  simp [InvalidationPublication.publishReuse, hpending]

/-- An acknowledgement routed through the wrong operation-family boundary is
a complete stutter even if its ticket and effect happen to match. -/
theorem authoritativeAcknowledge_wrong_kind_inert state expected ack pending
    (hpending : state.invalidationPublication.pending = some pending)
    (hkind : pending.kind ≠ expected) :
    (authoritativeAcknowledgeInvalidation state expected ack).accepted = false ∧
      (authoritativeAcknowledgeInvalidation state expected ack).state = state ∧
      (authoritativeAcknowledgeInvalidation state expected ack).effect = .none := by
  simp [authoritativeAcknowledgeInvalidation, hpending, hkind]

theorem authoritativeReuse_requires_retirement_ack state
    (haccepted : (authoritativePublishReuse state).accepted = true) :
    state.invalidationPublication.pending = none ∧
      state.invalidationPublication.releaseAcknowledged = true ∧
      state.invalidationPublication.destroyAcknowledged = true := by
  exact InvalidationPublication.reuse_publication_requires_retirement_ack
    state.invalidationPublication haccepted

def applyAuthoritativeOperation (state : CompositeState) :
    AuthoritativeOperation → CompositeState
  | .ordinary operation => applyOperation state operation
  | .blocking operation => applyBlockingOperation state operation
  | .drainDeferred subject => (drainDeferredCancellation state subject).state

def authoritativeOperationReply (state : CompositeState) :
    AuthoritativeOperation → AuthoritativeOperationReply
  | .ordinary operation => .ordinary (operationReply state operation)
  | .blocking operation => .blocking (blockingOperationReply state operation)
  | .drainDeferred subject =>
      .deferredDrain (drainDeferredCancellation state subject).result

/-- One total gate for both operation families.  Neither branch can bypass the
shared busy/halted execution latch. -/
def authoritativeGate (state : CompositeState) (operation : AuthoritativeOperation) :
    AuthoritativeGateOutcome :=
  match operation with
  | .ordinary (.nmi raw context) =>
      match state.execution.mode with
      | .halted record => { state, result := .rejectedHalted record }
      | .running | .handling _ =>
          { state := applyOperation state (.nmi raw context)
            result := .completed (.ordinary (operationReply state (.nmi raw context))) }
  | operation =>
      match state.execution.mode with
      | .running =>
          { state := applyAuthoritativeOperation state operation
            result := .completed (authoritativeOperationReply state operation) }
      | .handling _ => { state, result := .rejectedBusy }
      | .halted record => { state, result := .rejectedHalted record }

@[simp] theorem authoritativeGate_ordinary_state state operation :
    (authoritativeGate state (.ordinary operation)).state =
      (gate state operation).state := by
  cases operation <;> cases hmode : state.execution.mode <;>
    simp [authoritativeGate, gate, applyAuthoritativeOperation, hmode]

@[simp] theorem authoritativeGate_blocking_state state operation :
    (authoritativeGate state (.blocking operation)).state =
      (blockingGate state operation).state := by
  cases hmode : state.execution.mode <;>
    simp [authoritativeGate, blockingGate, applyAuthoritativeOperation, hmode]

@[simp] theorem authoritativeGate_drainDeferred_state state subject :
    (authoritativeGate state (.drainDeferred subject)).state =
      match state.execution.mode with
      | .running => (drainDeferredCancellation state subject).state
      | .handling _ | .halted _ => state := by
  cases hmode : state.execution.mode <;>
    simp [authoritativeGate, applyAuthoritativeOperation, hmode]

/-! ## Authoritative operation footprints

The blocking and deferred-drain families declare footprints exactly like the
ordinary `Operation` family, so the frame rule covers every constructor of
`AuthoritativeOperation`. -/

/-- Projections republished by a blocking IPC transition: the scheduler and
lifecycle views, the resumable bank, and the blocking store with its saved
contexts. -/
def blockingProjections : List CompositeFootprint.Projection :=
  [ .execution, .scheduler, .preemption, .lifecycle, .resumable, .blockingIPC
  , .blockingContexts ]

/-- Projections republished by a deferred-cancellation drain. -/
def drainProjections : List CompositeFootprint.Projection :=
  blockingProjections ++ [.deferredCancels]

theorem publishBlockingIPCContext_frames state blocking :
    CompositeState.Frames (.ofLists [] blockingProjections) state
      (publishBlockingIPCContext state blocking) := by
  composite_frame

theorem publishReleasedBlockingContext_frames state blocking saved next
    (published : publishReleasedBlockingContext state blocking saved = .ok next) :
    CompositeState.Frames (.ofLists [] blockingProjections) state next := by
  unfold publishReleasedBlockingContext at published
  repeat' first | split at published
  all_goals try contradiction
  all_goals injection published with published
  all_goals subst next
  all_goals composite_frame

theorem restoreBlockingPeer_frames state blocking next
    (restored : restoreBlockingPeer state blocking = .ok next) :
    CompositeState.Frames (.ofLists [] blockingProjections) state next := by
  unfold restoreBlockingPeer at restored
  repeat' first | split at restored
  all_goals try contradiction
  all_goals injection restored with restored
  all_goals subst next
  all_goals composite_frame

theorem drainDeferredCancellation_frames state subject :
    CompositeState.Frames (.ofLists [] drainProjections) state
      (drainDeferredCancellation state subject).state := by
  unfold drainDeferredCancellation
  dsimp only
  split
  · exact CompositeState.frames_of_eq _ rfl
  · simp only [publishDeferredDrain]
    composite_frame

/-- Every blocking operation reads and writes only the blocking projections:
handle resolution consults the capability registry carried by the blocking
store's own lifecycle view. -/
def CompositeBlockingOperation.footprint :
    CompositeBlockingOperation → CompositeFootprint.Footprint
  | .receive .. => .ofLists [] blockingProjections
  | .send .. => .ofLists [] blockingProjections
  | .cancel _ => .ofLists [] blockingProjections

/-- The declared footprint of every authoritative constructor. -/
def AuthoritativeOperation.footprint : AuthoritativeOperation → CompositeFootprint.Footprint
  | .ordinary operation => operation.footprint
  | .blocking operation => operation.footprint
  | .drainDeferred _ => .ofLists [] drainProjections

/-- Frame rule for the blocking family. -/
theorem applyBlockingOperation_frames state operation :
    CompositeState.Frames operation.footprint state
      (applyBlockingOperation state operation) := by
  cases operation <;>
    simp only [applyBlockingOperation, CompositeBlockingOperation.footprint,
      dispatchBlockingReceive, dispatchBlockingSend, dispatchBlockingCancel]
  all_goals
    repeat' first | split
    all_goals first
      | exact CompositeState.frames_of_eq _ rfl
      | exact (publishBlockingIPCContext_frames _ _).mono (by footprint_within)
      | exact (restoreBlockingPeer_frames _ _ _ ‹_›).mono (by footprint_within)
      | exact (publishReleasedBlockingContext_frames _ _ _ _ ‹_›).mono
          (by footprint_within)

theorem blockingGate_frames state operation :
    CompositeState.Frames operation.footprint state (blockingGate state operation).state := by
  cases hmode : state.execution.mode <;> simp only [blockingGate, hmode] <;>
    first
      | exact CompositeState.frames_of_eq _ rfl
      | exact applyBlockingOperation_frames _ _

/-- **Authoritative frame rule.**  Every projection outside an authoritative
operation's declared write set survives `applyAuthoritativeOperation`. -/
theorem applyAuthoritativeOperation_frames state operation :
    CompositeState.Frames operation.footprint state
      (applyAuthoritativeOperation state operation) := by
  cases operation with
  | ordinary operation => exact applyOperation_frames state operation
  | blocking operation => exact applyBlockingOperation_frames state operation
  | drainDeferred subject => exact drainDeferredCancellation_frames state subject

/-- The frame rule holds for every outcome of `authoritativeGate`, including
busy and halted stutters. -/
theorem authoritativeGate_frames state operation :
    CompositeState.Frames operation.footprint state (authoritativeGate state operation).state := by
  cases operation with
  | ordinary operation =>
      rw [authoritativeGate_ordinary_state]
      exact gate_frames state operation
  | blocking operation =>
      rw [authoritativeGate_blocking_state]
      exact blockingGate_frames state operation
  | drainDeferred subject =>
      rw [authoritativeGate_drainDeferred_state]
      split
      · exact drainDeferredCancellation_frames state subject
      · exact CompositeState.frames_of_eq _ rfl
      · exact CompositeState.frames_of_eq _ rfl

/-- Direct-port, DMA, and invalidation-publication authority are outside every
authoritative operation's write set. -/
theorem AuthoritativeOperation.footprint_untouched_authority
    (operation : AuthoritativeOperation) :
    CompositeFootprint.Untouched operation.footprint .directPortIO ∧
      CompositeFootprint.Untouched operation.footprint .dmaAccepted ∧
      CompositeFootprint.Untouched operation.footprint .dmaObserved ∧
      CompositeFootprint.Untouched operation.footprint .invalidationPublication := by
  cases operation with
  | ordinary operation => exact Operation.footprint_untouched_authority operation
  | blocking operation =>
      cases operation <;>
        simp only [CompositeFootprint.Untouched, AuthoritativeOperation.footprint,
          CompositeBlockingOperation.footprint] <;> decide
  | drainDeferred subject =>
      simp only [CompositeFootprint.Untouched, AuthoritativeOperation.footprint]
      decide

private theorem drainDeferredCancellation_retains_invalidationPublication
    state subject :
    (drainDeferredCancellation state subject).state.invalidationPublication =
      state.invalidationPublication :=
  drainDeferredCancellation_frames state subject .invalidationPublication
    (by untouched_decide)

/-- Publication well-formedness is lifted through the authoritative frame
rule: no authoritative operation writes the publication projection. -/
private theorem authoritativeGate_preserves_invalidationPublication state operation
    (hpublication :
      InvalidationPublication.WellFormed state.invalidationPublication) :
    InvalidationPublication.WellFormed
      (authoritativeGate state operation).state.invalidationPublication :=
  publicationInvariant.preserved_of_frames (authoritativeGate_frames state operation)
    (by
      have untouched := (AuthoritativeOperation.footprint_untouched_authority operation).2.2.2
      simp only [CompositeFootprint.Untouched] at untouched
      simp [ProjectionInvariant.untouchedBy, publicationInvariant, untouched])
    hpublication

/-- No authoritative ordinary, blocking, or deferred-drain operation can
replace the boot-accepted PCI authority or the current live observation.
Unlike complete global preservation, this structural field law is
unconditional: it does not depend on unfinished operation-compatibility
constructors. -/
@[simp] theorem authoritativeGate_dmaAuthority state operation :
    (authoritativeGate state operation).state.dmaAccepted =
        state.dmaAccepted ∧
      (authoritativeGate state operation).state.dmaObserved =
        state.dmaObserved :=
  ⟨authoritativeGate_frames state operation .dmaAccepted
      (AuthoritativeOperation.footprint_untouched_authority operation).2.1,
    authoritativeGate_frames state operation .dmaObserved
      (AuthoritativeOperation.footprint_untouched_authority operation).2.2.1⟩

/-- Every authoritative constructor preserves the live DMA quarantine
projection without requiring the stronger global compatibility certificate. -/
theorem authoritativeGate_preserves_dmaQuarantined state operation
    (hstate : state.DMAQuarantined) :
    (authoritativeGate state operation).state.DMAQuarantined := by
  obtain ⟨haccepted, hobserved⟩ :=
    authoritativeGate_dmaAuthority state operation
  unfold CompositeState.DMAQuarantined at hstate ⊢
  simpa [haccepted, hobserved] using hstate

/-- The authoritative live observation supplies the same explicit hardware
contract used by the issue-local complete-memory theorem.  Thus a named
present device attempt is a stutter on physical memory, allocator ownership,
page-table frames, kernel-owned frames, kernel state, and every
subject-visible byte without assuming an IOMMU. -/
theorem CompositeState.DMAQuarantined.unownedDevicePreservesCompleteProjection
    {state : CompositeState} (hstate : state.DMAQuarantined)
    (target : DMAQuarantine.BDF)
    (before after : DMAQuarantine.MemoryProjection)
    (hcontract : DMAQuarantine.DeviceContract
      state.dmaObserved target before after)
    (hknown : ∃ function ∈ state.dmaObserved.functions,
      function.bdf = target ∧ function.status = .present) :
    after.physicalMemory = before.physicalMemory ∧
      after.allocatorOwnership = before.allocatorOwnership ∧
      after.pageTableFrames = before.pageTableFrames ∧
      after.kernelOwnedFrames = before.kernelOwnedFrames ∧
      after.kernelState = before.kernelState ∧
      after.subjectVisible = before.subjectVisible := by
  rw [hstate] at hcontract hknown
  apply DMAQuarantine.unowned_device_preserves_complete_projection
    state.dmaAccepted target before after
  · exact hcontract
  · exact hknown

theorem authoritativeGate_deterministic state operation first second
    (hfirst : authoritativeGate state operation = first)
    (hsecond : authoritativeGate state operation = second) : first = second := by
  rw [hfirst] at hsecond
  exact hsecond

/-- Completion fixes either the running latch or the explicit out-of-band NMI
admission, plus the exact typed reply and exact post-state. -/
theorem authoritativeGate_completed_sound state operation reply
    (hcompleted : (authoritativeGate state operation).result = .completed reply) :
    (state.execution.mode = .running ∨
        ∃ raw context, operation = .ordinary (.nmi raw context)) ∧
      reply = authoritativeOperationReply state operation ∧
      (authoritativeGate state operation).state =
        applyAuthoritativeOperation state operation := by
  cases operation with
  | ordinary operation =>
      cases operation <;> cases hmode : state.execution.mode <;>
        simp [authoritativeGate, hmode, applyAuthoritativeOperation,
          authoritativeOperationReply] at hcompleted ⊢ <;>
        exact hcompleted.symm
  | blocking operation =>
      cases hmode : state.execution.mode <;>
        simp [authoritativeGate, hmode, applyAuthoritativeOperation,
          authoritativeOperationReply] at hcompleted ⊢ <;>
        exact hcompleted.symm
  | drainDeferred subject =>
      cases hmode : state.execution.mode <;>
        simp [authoritativeGate, hmode, applyAuthoritativeOperation,
          authoritativeOperationReply] at hcompleted ⊢ <;>
        exact hcompleted.symm

/-- Finite ordinary denials and finite blocking denials share one classifier.
The terminal halted result is intentionally absent. -/
inductive AuthoritativeGateRejection : AuthoritativeGateResult → Prop where
  | busy : AuthoritativeGateRejection .rejectedBusy
  | ordinary {reply} (hrejected : reply.isNonfatalRejection = true) :
      AuthoritativeGateRejection (.completed (.ordinary reply))
  | blocking {reply}
      (hrejected : CompositeBlockingGateRejection (.completed reply)) :
      AuthoritativeGateRejection (.completed (.blocking reply))
  | deferredDrain (reason : BlockingIPCContext.DrainError) :
      AuthoritativeGateRejection
        (.completed (.deferredDrain (.rejected reason)))

theorem AuthoritativeGateRejection.deferredDrain_result {result}
    (h : AuthoritativeGateRejection (.completed (.deferredDrain result))) :
    ∃ reason, result = .rejected reason := by
  cases h with
  | deferredDrain reason => exact ⟨reason, rfl⟩

/-- Every classified nonfatal denial is byte-for-byte atomic across every
projection in the shared composite state. -/
theorem authoritativeGate_rejection_atomic state operation
    (hrejected : AuthoritativeGateRejection
      (authoritativeGate state operation).result) :
    (authoritativeGate state operation).state = state := by
  cases hmode : state.execution.mode with
  | handling active =>
      cases operation with
      | ordinary operation =>
          cases operation <;>
            simp [authoritativeGate, hmode, authoritativeOperationReply,
              OperationReply.isNonfatalRejection] at hrejected ⊢
          all_goals
            cases hrejected with
            | ordinary hreply =>
                simp [operationReply, OperationReply.isNonfatalRejection] at hreply
      | blocking operation => simp [authoritativeGate, hmode]
      | drainDeferred subject => simp [authoritativeGate, hmode]
  | halted record =>
      cases operation with
      | ordinary operation =>
          cases operation <;> simp [authoritativeGate, hmode] at hrejected <;>
            cases hrejected
      | blocking operation =>
          simp [authoritativeGate, hmode] at hrejected
          cases hrejected
      | drainDeferred subject =>
          simp [authoritativeGate, hmode] at hrejected
          cases hrejected
  | running =>
      cases operation with
      | ordinary operation =>
          cases operation with
          | nmi raw context =>
              simp [authoritativeGate, hmode, authoritativeOperationReply,
                operationReply, OperationReply.isNonfatalRejection] at hrejected
              cases hrejected with
              | ordinary hreply =>
                  simp [OperationReply.isNonfatalRejection] at hreply
          | _ =>
              simp only [authoritativeGate, hmode, authoritativeOperationReply] at hrejected
              cases hrejected with
              | ordinary hreply =>
                  rw [authoritativeGate_ordinary_state]
                  exact gate_classified_rejection_global_atomicity state _ hreply
      | blocking operation =>
          simp only [authoritativeGate, hmode, authoritativeOperationReply] at hrejected
          cases hrejected with
          | blocking hreply =>
              have hatomic := blockingGate_rejection_atomic state operation (by
                simpa [blockingGate, hmode] using hreply)
              rw [authoritativeGate_blocking_state]
              exact hatomic
      | drainDeferred subject =>
          have hclassified : AuthoritativeGateRejection
              (.completed (.deferredDrain
                (drainDeferredCancellation state subject).result)) := by
            simpa [authoritativeGate, hmode, authoritativeOperationReply] using hrejected
          obtain ⟨reason, hresult⟩ := hclassified.deferredDrain_result
          simpa [authoritativeGate, hmode, applyAuthoritativeOperation] using
            drainDeferredCancellation_rejected_unchanged
              state subject reason hresult

/-- Atomic denial retains even the strengthened waiter/context invariant. -/
theorem authoritativeGate_rejection_preserves_blockingRuntimeWellFormed
    state operation (hstate : BlockingRuntimeWellFormed state)
    (hrejected : AuthoritativeGateRejection
      (authoritativeGate state operation).result) :
    BlockingRuntimeWellFormed (authoritativeGate state operation).state := by
  rw [authoritativeGate_rejection_atomic state operation hrejected]
  exact hstate

/-- The embedded blocking family keeps the full authoritative waiter/context
invariant through the successor gate for every typed result. -/
theorem authoritativeGate_blocking_preserves_blockingRuntimeWellFormed
    state operation (hstate : BlockingRuntimeWellFormed state) :
    BlockingRuntimeWellFormed
      (authoritativeGate state (.blocking operation)).state := by
  rw [authoritativeGate_blocking_state]
  exact blockingGate_preserves_blockingRuntimeWellFormed state operation hstate

/-- Return selection, completion, and restart cross the successor gate
without weakening the full authoritative blocking invariant. -/
theorem authoritativeGate_blockingStateNeutral_preserves_blockingRuntimeWellFormed
    state operation (hoperation : BlockingStateNeutralOperation operation)
    (hstate : BlockingRuntimeWellFormed state) :
    BlockingRuntimeWellFormed
      (authoritativeGate state (.ordinary operation)).state := by
  rw [authoritativeGate_ordinary_state]
  exact gate_blockingStateNeutral_preserves_blockingRuntimeWellFormed
    state operation hoperation hstate

/-- Control/data-IPC, mapping, syscall, and sealed-offer operations retain the
stronger blocking precondition through the authoritative successor.  A
following block, wake, or cancellation can therefore run without
reconstructing waiter readiness. -/
theorem authoritativeGate_blockingRuntimePreserving_preserves_blockingRuntimeWellFormed
    state operation (hoperation : BlockingRuntimePreservingOperation operation)
    (hstate : BlockingRuntimeWellFormed state) :
    BlockingRuntimeWellFormed
      (authoritativeGate state (.ordinary operation)).state := by
  rw [authoritativeGate_ordinary_state]
  exact gate_blockingRuntimePreserving_preserves_blockingRuntimeWellFormed
    state operation hoperation hstate

/-- One readiness-free mixed slice: any compatible ordinary mutation may be
followed immediately by any authoritative blocking operation while preserving
the complete global/scheduler/mailbox/waiter/context invariant. -/
theorem authoritativeGate_ordinary_then_blocking_preserves_blockingRuntimeWellFormed
    state ordinary blocking
    (hordinary : BlockingRuntimePreservingOperation ordinary)
    (hstate : BlockingRuntimeWellFormed state) :
    BlockingRuntimeWellFormed
      (authoritativeGate
        (authoritativeGate state (.ordinary ordinary)).state
        (.blocking blocking)).state := by
  exact authoritativeGate_blocking_preserves_blockingRuntimeWellFormed
    (authoritativeGate state (.ordinary ordinary)).state blocking
    (authoritativeGate_blockingRuntimePreserving_preserves_blockingRuntimeWellFormed
      state ordinary hordinary hstate)

/-- A state-independent readiness-free mixed-trace language.  Every ordinary
member carries its compositional blocking-preservation proof, while every
authoritative blocking member is admitted directly because the preceding
members retain the complete blocking runtime invariant.  Unlike the finite
compatibility certificate below, this language does not inspect any
intermediate runtime state. -/
inductive ReadinessFreeMixedTrace : List AuthoritativeOperation → Prop where
  | nil : ReadinessFreeMixedTrace []
  | ordinary {operation rest}
      (hoperation : BlockingRuntimePreservingOperation operation)
      (hrest : ReadinessFreeMixedTrace rest) :
      ReadinessFreeMixedTrace (.ordinary operation :: rest)
  | blocking {operation rest}
      (hrest : ReadinessFreeMixedTrace rest) :
      ReadinessFreeMixedTrace (.blocking operation :: rest)

/-- Accepted and fatal return completion both retain the complete blocking
runtime invariant, so a later blocking step needs no reconstructed readiness
witness after crossing the return-control boundary. -/
theorem authoritativeGate_userReturn_preserves_blockingRuntimeWellFormed
    state request (hstate : BlockingRuntimeWellFormed state) :
    BlockingRuntimeWellFormed
      (authoritativeGate state (.ordinary (.userReturn request))).state := by
  exact authoritativeGate_blockingStateNeutral_preserves_blockingRuntimeWellFormed
    state (.userReturn request) (.userReturn request) hstate

/-- Exact local effect laws needed when an operation leaves the dormant
cancellation store in place.  These laws mention only the affected blocking,
scheduler, and resumable projections; they do not assume either the global
runtime invariant or its preservation conclusion. -/
structure DormantCancellationCompatible (before after : CompositeState) : Prop where
  deferredExact : after.deferredCancels = before.deferredCancels
  blockedDeferredDisjoint :
    ∀ subject, (after.blockingContexts subject).isSome = true →
      after.deferredCancels.retained subject = none
  blockedResumableDisjoint :
    ∀ subject saved, after.blockingContexts subject = some saved →
      ResumablePreemption.contextFor after.resumable.contexts subject = none
  retainedQuiescent :
    ∀ subject saved, before.deferredCancels.retained subject = some saved →
      after.blockingIPC.waiterEndpoint subject = none ∧
      after.blockingIPC.scheduler.lifecycle.capabilities.subjects subject = true ∧
      after.blockingIPC.scheduler.lifecycle.runnable subject = false ∧
      after.blockingIPC.scheduler.lifecycle.current ≠ some subject ∧
      subject ∉ after.blockingIPC.scheduler.ready ∧
      Scheduler.ownsAddressSpace after.blockingIPC.scheduler subject = some subject ∧
      ResumablePreemption.contextFor after.resumable.contexts subject = none

/-- Exact preservation of the four projections observed by dormant
cancellation is sufficient to derive its operation-local compatibility law
from the folded authoritative invariant.  This is the reusable constructor
boundary: operation proofs need not reconstruct waiter or retained-context
validity when they leave those stores literally unchanged. -/
theorem dormantCancellationCompatible_of_exact_projections before after
    (hbefore : AuthoritativeRuntimeWellFormed before)
    (hdeferred : after.deferredCancels = before.deferredCancels)
    (hblocked : after.blockingContexts = before.blockingContexts)
    (hipc : after.blockingIPC = before.blockingIPC)
    (hcontexts : after.resumable.contexts = before.resumable.contexts) :
    DormantCancellationCompatible before after := by
  refine ⟨hdeferred, ?_, ?_, ?_⟩
  · intro subject hsome
    rw [hblocked] at hsome
    rw [hdeferred]
    exact hbefore.2.1.2.1 subject hsome
  · intro subject saved hsaved
    rw [hblocked] at hsaved
    rw [hcontexts]
    exact hbefore.2.2.1 subject saved hsaved
  · intro subject saved hretained
    have hretainedBefore :
        before.deferredCancels.retained subject = some saved := by
      exact hretained
    have hvalid := hbefore.2.1.2.2 subject saved hretainedBefore
    rw [hipc, hcontexts]
    exact ⟨hvalid.2.1, hvalid.2.2.1, hvalid.2.2.2.1,
      hvalid.2.2.2.2.1, hvalid.2.2.2.2.2.1,
      hvalid.2.2.2.2.2.2,
      hbefore.2.2.2 subject saved hretainedBefore⟩

/-- Publishing any resumable-switch outcome preserves every dormant
cancellation observation.  Accepted switches rotate only the old current and
ready subjects, while blocked and retained subjects are disjoint from both;
typed rejection and fatal entry leave the scheduler and context bank exact. -/
private theorem installResumableSwitch_dormantCancellationCompatible
    state frame registers
    (hstate : AuthoritativeRuntimeWellFormed state) :
    DormantCancellationCompatible state
      (installResumable state
        (ResumablePreemption.switch state.resumable state.execution.core
          frame registers).state) := by
  rcases hstate.2.1.1 with ⟨hblocking, hagreement⟩
  rcases hblocking with
    ⟨_hscheduler, _hqueues, hwaiters, _hunique, hindex, _hmailbox,
      _hcapabilities⟩
  simp only [CompositeState.blockingIPCContext] at hagreement hwaiters hindex
  have hshared :
      state.resumable.scheduler = state.blockingIPC.scheduler :=
    hstate.1.1.2.2.2.2.2.2.2.1.trans hstate.1.blockingScheduler.symm
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro subject hblocked
    exact hstate.2.1.2.1 subject hblocked
  · intro subject saved hblocked
    change state.blockingContexts subject = some saved at hblocked
    cases hendpoint : state.blockingIPC.waiterEndpoint subject with
    | none =>
        have hprojection := hagreement.1 subject
        simp [CompositeState.blockingIPCContext, hblocked, hendpoint] at hprojection
    | some endpoint =>
        have hvalid :=
          hwaiters endpoint subject ((hindex endpoint subject).mpr hendpoint)
        have hcurrent :
            state.resumable.scheduler.lifecycle.current ≠ some subject := by
          simpa [hshared] using hvalid.2.2.2.2.2.1
        have hready : subject ∉ state.resumable.scheduler.ready := by
          simpa [hshared] using hvalid.2.2.2.2.2.2
        simpa [installResumable] using
          resumeSwitch_preserves_quiescent_context_absence
            state.resumable state.execution.core frame registers subject
            hcurrent hready (hstate.2.2.1 subject saved hblocked)
  · intro subject saved hretained
    have hvalid := hstate.2.1.2.2 subject saved hretained
    simp only [CompositeState.blockingIPCContext] at hvalid
    have hcurrent :
        state.resumable.scheduler.lifecycle.current ≠ some subject := by
      simpa [hshared] using hvalid.2.2.2.2.1
    have hready : subject ∉ state.resumable.scheduler.ready := by
      simpa [hshared] using hvalid.2.2.2.2.2.1
    have hview :=
      resumeSwitch_preserves_quiescent_scheduler_view
        state.resumable state.execution.core frame registers subject
          hcurrent hready
    have hcontext :=
      resumeSwitch_preserves_quiescent_context_absence
        state.resumable state.execution.core frame registers subject
          hcurrent hready (hstate.2.2.2 subject saved hretained)
    simp only [installResumable]
    refine ⟨hvalid.2.1, ?_, ?_, hview.2.2.2.1, hview.2.2.2.2, ?_, hcontext⟩
    · rw [hview.1, hshared]
      exact hvalid.2.2.1
    · rw [hview.2.1, hshared]
      exact hvalid.2.2.2.1
    · simpa [Scheduler.ownsAddressSpace, hview.2.2.1, hshared] using
        hvalid.2.2.2.2.2.2

private theorem dormantCancellationCompatible_preserves
    before after (hbefore : DeferredBlockingRuntimeWellFormed before)
    (hblocking : BlockingRuntimeWellFormed after)
    (hcompatible : DormantCancellationCompatible before after) :
    DeferredBlockingRuntimeWellFormed after := by
  refine ⟨hblocking.1, ?_⟩
  unfold CompositeState.DeferredCancellationWellFormed
  refine ⟨?_, hcompatible.blockedResumableDisjoint, ?_⟩
  · unfold BlockingIPCContext.DeferredWellFormed
    refine ⟨hblocking.2, hcompatible.blockedDeferredDisjoint, ?_⟩
    intro subject saved hretained
    have hretainedBefore : before.deferredCancels.retained subject = some saved := by
      rw [← hcompatible.deferredExact]
      exact hretained
    have hvalid := hbefore.2.1.2.2 subject saved hretainedBefore
    exact ⟨hvalid.1, hcompatible.retainedQuiescent subject saved hretainedBefore |>.1,
      hcompatible.retainedQuiescent subject saved hretainedBefore |>.2.1,
      hcompatible.retainedQuiescent subject saved hretainedBefore |>.2.2.1,
      hcompatible.retainedQuiescent subject saved hretainedBefore |>.2.2.2.1,
      hcompatible.retainedQuiescent subject saved hretainedBefore |>.2.2.2.2.1,
      hcompatible.retainedQuiescent subject saved hretainedBefore |>.2.2.2.2.2.1⟩
  · intro subject saved hretained
    have hretainedBefore : before.deferredCancels.retained subject = some saved := by
      rw [← hcompatible.deferredExact]
      exact hretained
    exact hcompatible.retainedQuiescent subject saved hretainedBefore |>.2.2.2.2.2.2

/-- Independently stated compatibility facts for every public operation.
Contained entry validates identity inside the transition.  Termination, NMI, and
capacity-checked drains have direct preservation proofs.  Scheduler admission
must not target an undrained cancellation.  Operations already proved to
preserve the blocking runtime expose only exact dormant-store effect laws.
Raw scheduler removal additionally exposes the one lower blocking projection
for which it has no unconditional preservation theorem.  No branch assumes
the authoritative invariant of the gate-selected post-state, but most branches
still require the caller to establish laws about that exact post-state. -/
def AuthoritativeOperationCompatible (state : CompositeState) :
    AuthoritativeOperation → Prop
  | .ordinary (.interrupt _) => True
  | .ordinary (.nmi _ _) => True
  | .ordinary (.terminateSubject _) => True
  | .ordinary .terminateCurrent => True
  | .ordinary (.scheduleRemove subject) =>
      BlockingIPCContext.WellFormed
        (authoritativeGate state
          (.ordinary (.scheduleRemove subject))).state.blockingIPCContext ∧
      DormantCancellationCompatible state
        (authoritativeGate state (.ordinary (.scheduleRemove subject))).state
  | .ordinary operation =>
      DormantCancellationCompatible state
        (authoritativeGate state (.ordinary operation)).state
  | .blocking operation =>
      DormantCancellationCompatible state
        (authoritativeGate state (.blocking operation)).state
  | .drainDeferred _ => True

/-- Contained entry has no caller-supplied post-state compatibility law.  Its
sole operation-local premise is the trusted execution/lifecycle identity
binding consumed by atomic cleanup.  Naming this constructor explicitly lets
finite authoritative traces certify an interrupt member without unfolding the
complete compatibility classifier. -/
theorem interrupt_authoritativeOperationCompatible state frame
    : AuthoritativeOperationCompatible state
      (.ordinary (.interrupt frame)) :=
  trivial

/-- Control, data-only IPC, and raw scheduler constructors retain every
projection observed by dormant cancellation.  Their shared public operation
class can therefore discharge the successor-gate compatibility boundary
without a caller-supplied post-state law. -/
theorem blockingStateNeutral_authoritativeOperationCompatible state operation
    (hoperation : BlockingStateNeutralOperation operation)
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeOperationCompatible state (.ordinary operation) := by
  have hdeferred (candidate) (hcandidate : BlockingStateNeutralOperation candidate) :
      (authoritativeGate state (.ordinary candidate)).state.deferredCancels =
        state.deferredCancels := by
    rw [authoritativeGate_ordinary_state]
    cases hcandidate <;> cases hmode : state.execution.mode <;>
      simp only [gate, hmode, applyOperation, selectLiveReturnAuthority, dispatchIPC, installIPC,
        schedulerDispatch, schedulerYield, schedulerTick, Scheduler.reject,
        installScheduler, installLifecycle, synchronizeMemory]
    all_goals
      repeat' first | split
      all_goals rfl
  have hblocked (candidate) (hcandidate : BlockingStateNeutralOperation candidate) :
      (authoritativeGate state (.ordinary candidate)).state.blockingContexts =
        state.blockingContexts := by
    change
      (authoritativeGate state (.ordinary candidate)).state.blockingIPCContext.blocked =
        state.blockingIPCContext.blocked
    rw [authoritativeGate_ordinary_state,
      gate_blockingStateNeutral_preserves_blockingIPCContext state candidate hcandidate]
  have hipc (candidate) (hcandidate : BlockingStateNeutralOperation candidate) :
      (authoritativeGate state (.ordinary candidate)).state.blockingIPC =
        state.blockingIPC := by
    change
      (authoritativeGate state (.ordinary candidate)).state.blockingIPCContext.ipc =
        state.blockingIPCContext.ipc
    rw [authoritativeGate_ordinary_state,
      gate_blockingStateNeutral_preserves_blockingIPCContext state candidate hcandidate]
  have hcontexts (candidate) (hcandidate : BlockingStateNeutralOperation candidate) :
      (authoritativeGate state (.ordinary candidate)).state.resumable.contexts =
        state.resumable.contexts := by
    rw [authoritativeGate_ordinary_state]
    cases hcandidate <;> cases hmode : state.execution.mode <;>
      simp only [gate, hmode, applyOperation, selectLiveReturnAuthority, dispatchIPC, installIPC,
        schedulerDispatch, schedulerYield, schedulerTick, Scheduler.reject,
        installScheduler, installLifecycle, synchronizeMemory]
    all_goals
      repeat' first | split
      all_goals rfl
  cases hoperation <;>
    apply dormantCancellationCompatible_of_exact_projections state _ hstate
  all_goals first
    | exact hdeferred _ (by constructor)
    | exact hblocked _ (by constructor)
    | exact hipc _ (by constructor)
    | exact hcontexts _ (by constructor)

private theorem authoritativeGate_ordinary_preserves_deferredBlockingRuntimeWellFormed
    state operation (hstate : DeferredBlockingRuntimeWellFormed state)
    (hcompatible : AuthoritativeOperationCompatible state (.ordinary operation)) :
    DeferredBlockingRuntimeWellFormed
      (authoritativeGate state (.ordinary operation)).state := by
  have hblocking : BlockingRuntimeWellFormed state := ⟨hstate.1, hstate.2.1.1⟩
  cases operation with
  | interrupt frame =>
      rw [authoritativeGate_ordinary_state]
      exact gate_interrupt_preserves_deferredBlockingRuntimeWellFormed
        state frame hstate
  | nmi raw context =>
      rw [authoritativeGate_ordinary_state]
      exact gate_nmi_preserves_deferredBlockingRuntimeWellFormed
        state raw context hstate
  | terminateSubject subject =>
      rw [authoritativeGate_ordinary_state]
      exact gate_terminateSubject_preserves_deferredBlockingRuntimeWellFormed
        state subject hstate
  | terminateCurrent =>
      rw [authoritativeGate_ordinary_state]
      exact gate_terminateCurrent_preserves_deferredBlockingRuntimeWellFormed
        state hstate
  | scheduleRemove subject =>
      apply dormantCancellationCompatible_preserves state _ hstate
      · refine ⟨?_, hcompatible.1⟩
        rw [authoritativeGate_ordinary_state]
        exact gate_preserves_runtimeWellFormed state (.scheduleRemove subject) hstate.1
      · exact hcompatible.2
  | selectUserReturn purpose =>
      exact dormantCancellationCompatible_preserves state _ hstate
        (authoritativeGate_blockingStateNeutral_preserves_blockingRuntimeWellFormed
          state _ (.selectUserReturn purpose) hblocking) hcompatible
  | userReturn request =>
      exact dormantCancellationCompatible_preserves state _ hstate
        (authoritativeGate_blockingStateNeutral_preserves_blockingRuntimeWellFormed
          state _ (.userReturn request) hblocking) hcompatible
  | ipc call =>
      exact dormantCancellationCompatible_preserves state _ hstate
        (authoritativeGate_blockingStateNeutral_preserves_blockingRuntimeWellFormed
          state _ (.ipc call) hblocking) hcompatible
  | scheduleNext =>
      exact dormantCancellationCompatible_preserves state _ hstate
        (authoritativeGate_blockingStateNeutral_preserves_blockingRuntimeWellFormed
          state _ .scheduleNext hblocking) hcompatible
  | scheduleYield =>
      exact dormantCancellationCompatible_preserves state _ hstate
        (authoritativeGate_blockingStateNeutral_preserves_blockingRuntimeWellFormed
          state _ .scheduleYield hblocking) hcompatible
  | scheduleTick =>
      exact dormantCancellationCompatible_preserves state _ hstate
        (authoritativeGate_blockingStateNeutral_preserves_blockingRuntimeWellFormed
          state _ .scheduleTick hblocking) hcompatible
  | restart =>
      exact dormantCancellationCompatible_preserves state _ hstate
        (authoritativeGate_blockingStateNeutral_preserves_blockingRuntimeWellFormed
          state _ .restart hblocking) hcompatible
  | map slot page permissions =>
      exact dormantCancellationCompatible_preserves state _ hstate
        (authoritativeGate_blockingRuntimePreserving_preserves_blockingRuntimeWellFormed
          state _ (.map slot page permissions) hblocking) hcompatible
  | unmap page =>
      exact dormantCancellationCompatible_preserves state _ hstate
        (authoritativeGate_blockingRuntimePreserving_preserves_blockingRuntimeWellFormed
          state _ (.unmap page) hblocking) hcompatible
  | protect page permissions =>
      exact dormantCancellationCompatible_preserves state _ hstate
        (authoritativeGate_blockingRuntimePreserving_preserves_blockingRuntimeWellFormed
          state _ (.protect page permissions) hblocking) hcompatible
  | syscall call =>
      exact dormantCancellationCompatible_preserves state _ hstate
        (authoritativeGate_blockingRuntimePreserving_preserves_blockingRuntimeWellFormed
          state _ (.syscall call) hblocking) hcompatible
  | resumePreempt frame registers =>
      exact dormantCancellationCompatible_preserves state _ hstate
        (authoritativeGate_blockingRuntimePreserving_preserves_blockingRuntimeWellFormed
          state _ (.resumePreempt frame registers) hblocking) hcompatible
  | transferOffer endpointWord sourceWord sourceKind payload rights =>
      exact dormantCancellationCompatible_preserves state _ hstate
        (authoritativeGate_blockingRuntimePreserving_preserves_blockingRuntimeWellFormed
          state _ (.transferOffer endpointWord sourceWord sourceKind payload rights)
          hblocking) hcompatible
  | transferAccept endpointWord destinationSlot =>
      exact dormantCancellationCompatible_preserves state _ hstate
        (authoritativeGate_blockingRuntimePreserving_preserves_blockingRuntimeWellFormed
          state _ (.transferAccept endpointWord destinationSlot) hblocking) hcompatible
  | capabilityCopy source destination destinationSlot rights =>
      exact dormantCancellationCompatible_preserves state _ hstate
        (authoritativeGate_blockingRuntimePreserving_preserves_blockingRuntimeWellFormed
          state _ (.capabilityCopy source destination destinationSlot rights)
          hblocking) hcompatible
  | capabilityRevoke authoritySlot victim victimSlot =>
      exact dormantCancellationCompatible_preserves state _ hstate
        (authoritativeGate_blockingRuntimePreserving_preserves_blockingRuntimeWellFormed
          state _ (.capabilityRevoke authoritySlot victim victimSlot)
          hblocking) hcompatible
  | capabilityRevokeSubtree authoritySlot victim victimSlot =>
      exact dormantCancellationCompatible_preserves state _ hstate
        (authoritativeGate_blockingRuntimePreserving_preserves_blockingRuntimeWellFormed
          state _ (.capabilityRevokeSubtree authoritySlot victim victimSlot)
          hblocking) hcompatible
  | createSubject subject =>
      exact dormantCancellationCompatible_preserves state _ hstate
        (authoritativeGate_blockingRuntimePreserving_preserves_blockingRuntimeWellFormed
          state _ (.createSubject subject) hblocking) hcompatible
  | scheduleAdd subject =>
      exact dormantCancellationCompatible_preserves state _ hstate
        (authoritativeGate_blockingRuntimePreserving_preserves_blockingRuntimeWellFormed
          state _ (.scheduleAdd subject) hblocking) hcompatible

/-- Ordinary successor operations cross the folded authoritative boundary
when their independently stated operation compatibility premises hold. -/
theorem authoritativeGate_ordinary_preserves_authoritativeRuntimeWellFormed
    state operation (hstate : AuthoritativeRuntimeWellFormed state)
    (hcompatible : AuthoritativeOperationCompatible state (.ordinary operation)) :
    AuthoritativeRuntimeWellFormed
      (authoritativeGate state (.ordinary operation)).state := by
  have hold :=
    authoritativeGate_ordinary_preserves_deferredBlockingRuntimeWellFormed
      state operation hstate.deferred hcompatible
  refine ⟨hold.1, hold.2, ?_⟩
  exact authoritativeGate_preserves_invalidationPublication state
    (.ordinary operation) hstate.publication

/-- Structural readiness consumed by the lower transition proofs.  The
authoritative invariant now implies every branch of this predicate; it is no
longer an external per-state premise of the public contract. -/
def AuthoritativeOperationReady (state : CompositeState) :
    AuthoritativeOperation → Prop
  | .ordinary _ => True
  | .blocking _ => BlockingRuntimeWellFormed state
  | .drainDeferred _ => DeferredBlockingRuntimeWellFormed state

theorem AuthoritativeRuntimeWellFormed.operationReady
    {state : CompositeState} (hstate : AuthoritativeRuntimeWellFormed state)
    (operation : AuthoritativeOperation) :
    AuthoritativeOperationReady state operation := by
  cases operation with
  | ordinary operation => trivial
  | blocking operation => exact hstate.blocking
  | drainDeferred subject => exact hstate.deferred

/-- Every structurally ready successor-gate operation preserves the older
global runtime projection.  Preservation of deferred authority is the
separate public operation contract above. -/
theorem authoritativeGate_preserves_runtimeWellFormed state operation
    (hstate : RuntimeWellFormed state)
    (hready : AuthoritativeOperationReady state operation) :
    RuntimeWellFormed (authoritativeGate state operation).state := by
  cases operation with
  | ordinary operation =>
      rw [authoritativeGate_ordinary_state]
      exact gate_preserves_runtimeWellFormed state operation hstate
  | blocking operation =>
      rw [authoritativeGate_blocking_state]
      exact (blockingGate_preserves_blockingRuntimeWellFormed state operation hready).1
  | drainDeferred subject =>
      cases hmode : state.execution.mode with
      | running =>
          simpa [authoritativeGate, hmode, applyAuthoritativeOperation] using
            (drainDeferredCancellation_preserves_deferredBlockingRuntimeWellFormed
              state subject hready).1
      | handling active => simpa [authoritativeGate, hmode] using hstate
      | halted record => simpa [authoritativeGate, hmode] using hstate

theorem authoritativeGate_preserves_authoritativeRuntimeWellFormed_of_compatible
    state operation (hstate : AuthoritativeRuntimeWellFormed state)
    (hcompatible : AuthoritativeOperationCompatible state operation) :
    AuthoritativeRuntimeWellFormed (authoritativeGate state operation).state := by
  cases operation with
  | ordinary operation =>
      exact authoritativeGate_ordinary_preserves_authoritativeRuntimeWellFormed
        state operation hstate hcompatible
  | blocking operation =>
      have hold := dormantCancellationCompatible_preserves state _ hstate.deferred
          (authoritativeGate_blocking_preserves_blockingRuntimeWellFormed
            state operation hstate.blocking) hcompatible
      refine ⟨hold.1, hold.2, ?_⟩
      exact authoritativeGate_preserves_invalidationPublication state
        (.blocking operation) hstate.publication
  | drainDeferred subject =>
      cases hmode : state.execution.mode with
      | running =>
          rw [show
            (authoritativeGate state (.drainDeferred subject)).state =
              (drainDeferredCancellation state subject).state by
            simp [authoritativeGate, hmode, applyAuthoritativeOperation]]
          have hold :=
            drainDeferredCancellation_preserves_deferredBlockingRuntimeWellFormed
              state subject hstate.deferred
          refine ⟨hold.1, hold.2, ?_⟩
          rw [drainDeferredCancellation_retains_invalidationPublication]
          exact hstate.publication
      | handling active => simpa [authoritativeGate, hmode] using hstate
      | halted record => simpa [authoritativeGate, hmode] using hstate

/-- Resumable preemption derives its dormant-cancellation compatibility from
the folded pre-state alone.  A successful save/restore switch cannot select,
save, or queue a blocked or retained subject; all typed denials are atomic and
fatal entry republishes only the unchanged scheduler/context bank under the
terminal latch. -/
theorem resumePreempt_authoritativeOperationCompatible state frame registers
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeOperationCompatible state
      (.ordinary (.resumePreempt frame registers)) := by
  change DormantCancellationCompatible state
    (authoritativeGate state
      (.ordinary (.resumePreempt frame registers))).state
  cases hmode : state.execution.mode with
  | handling active =>
      simpa [authoritativeGate, hmode] using
        dormantCancellationCompatible_of_exact_projections
          state state hstate rfl rfl rfl rfl
  | halted record =>
      simpa [authoritativeGate, hmode] using
        dormantCancellationCompatible_of_exact_projections
          state state hstate rfl rfl rfl rfl
  | running =>
      have hswitch :=
        installResumableSwitch_dormantCancellationCompatible
          state frame registers hstate
      cases herror : (ResumablePreemption.switch state.resumable
          state.execution.core frame registers).error with
      | none =>
          simpa [authoritativeGate, hmode, applyAuthoritativeOperation,
            applyOperation, herror] using hswitch
      | some reason =>
          cases reason with
          | fatalEntry =>
              cases hhalted : (ResumablePreemption.switch state.resumable
                  state.execution.core frame registers).state.halted with
              | false =>
                  simpa [authoritativeGate, hmode, applyAuthoritativeOperation,
                    applyOperation, herror, hhalted] using
                      dormantCancellationCompatible_of_exact_projections
                        state state hstate rfl rfl rfl rfl
              | true =>
                  simp only [authoritativeGate, hmode, applyAuthoritativeOperation,
                    applyOperation, herror, hhalted]
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · exact hswitch.deferredExact
                  · exact hswitch.blockedDeferredDisjoint
                  · exact hswitch.blockedResumableDisjoint
                  · exact hswitch.retainedQuiescent
          | nonTimer | malformedIncoming | noCurrent | contextMismatch |
              duplicateSave | staleActiveSpace | bankFull | schedulerRejected |
              noDestination | staleDestination =>
                simpa [authoritativeGate, hmode, applyAuthoritativeOperation,
                  applyOperation, herror] using
                    dormantCancellationCompatible_of_exact_projections
                      state state hstate rfl rfl rfl rfl

/-- Every resumable-preemption result unconditionally preserves the complete
folded authoritative invariant.  In particular, callers supply neither a
post-state compatibility law nor a per-state readiness witness. -/
theorem authoritativeGate_resumePreempt_preserves_authoritativeRuntimeWellFormed
    state frame registers (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeGate state
        (.ordinary (.resumePreempt frame registers))).state :=
  authoritativeGate_preserves_authoritativeRuntimeWellFormed_of_compatible state
    (.ordinary (.resumePreempt frame registers)) hstate
    (resumePreempt_authoritativeOperationCompatible
      state frame registers hstate)

/-- Every ordinary constructor in the blocking-state-neutral family now has a
closed successor-gate preservation theorem.  Its compatibility evidence is
derived from exact transition projections, never from the desired post-state
invariant. -/
theorem authoritativeGate_blockingStateNeutral_preserves_authoritativeRuntimeWellFormed
    state operation (hoperation : BlockingStateNeutralOperation operation)
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeGate state (.ordinary operation)).state :=
  authoritativeGate_preserves_authoritativeRuntimeWellFormed_of_compatible state
    (.ordinary operation) hstate
    (blockingStateNeutral_authoritativeOperationCompatible
      state operation hoperation hstate)

/-- Mapping publication changes the blocking scheduler's lifecycle mapping,
but leaves every field observed by dormant cancellation exact. -/
private theorem installVirtualMemory_dormantCancellationCompatible
    state virtualMemory translations
    (hstate : AuthoritativeRuntimeWellFormed state) :
    DormantCancellationCompatible state
      (installVirtualMemory state virtualMemory translations) := by
  refine ⟨rfl, hstate.2.1.2.1, hstate.2.2.1, ?_⟩
  intro subject saved hretained
  have hvalid := hstate.2.1.2.2 subject saved hretained
  simp only [CompositeState.blockingIPCContext] at hvalid
  have hblockingScheduler :
      state.blockingIPC.scheduler = state.scheduler :=
    hstate.1.blockingScheduler
  have hschedulerLifecycle :
      state.scheduler.lifecycle = state.lifecycle :=
    hstate.1.1.2.1
  simpa [installVirtualMemory, Scheduler.ownsAddressSpace_eq_some_iff,
      hblockingScheduler, hschedulerLifecycle] using
    And.intro hvalid.2.1
      (And.intro hvalid.2.2.1
        (And.intro hvalid.2.2.2.1
          (And.intro hvalid.2.2.2.2.1
            (And.intro hvalid.2.2.2.2.2.1
              (And.intro hvalid.2.2.2.2.2.2
                (hstate.2.2.2 subject saved hretained))))))

/-- Raw mapping changes only virtual-memory, translation, and derived mapping
projections.  Every waiter, saved context, retained cancellation, and
resumable context observed by the dormant-cancellation invariant is retained. -/
theorem map_authoritativeOperationCompatible state slot page permissions
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeOperationCompatible state
      (.ordinary (.map slot page permissions)) := by
  change DormantCancellationCompatible state
    (authoritativeGate state
      (.ordinary (.map slot page permissions))).state
  cases hmode : state.execution.mode with
  | handling active =>
      simpa [authoritativeGate, hmode] using
        dormantCancellationCompatible_of_exact_projections
          state state hstate rfl rfl rfl rfl
  | halted record =>
      simpa [authoritativeGate, hmode] using
        dormantCancellationCompatible_of_exact_projections
          state state hstate rfl rfl rfl rfl
  | running =>
      simp only [authoritativeGate, hmode, applyAuthoritativeOperation,
        applyOperation]
      split
      · exact dormantCancellationCompatible_of_exact_projections
          state state hstate rfl rfl rfl rfl
      · exact installVirtualMemory_dormantCancellationCompatible state _ _ hstate

/-- Raw unmapping and its page-local TLB invalidation likewise leave every
projection observed by dormant cancellation exact. -/
theorem unmap_authoritativeOperationCompatible state page
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeOperationCompatible state (.ordinary (.unmap page)) := by
  change DormantCancellationCompatible state
    (authoritativeGate state (.ordinary (.unmap page))).state
  cases hmode : state.execution.mode with
  | handling active =>
      simpa [authoritativeGate, hmode] using
        dormantCancellationCompatible_of_exact_projections
          state state hstate rfl rfl rfl rfl
  | halted record =>
      simpa [authoritativeGate, hmode] using
        dormantCancellationCompatible_of_exact_projections
          state state hstate rfl rfl rfl rfl
  | running =>
      simp only [authoritativeGate, hmode, applyAuthoritativeOperation,
        applyOperation]
      split
      · exact dormantCancellationCompatible_of_exact_projections
          state state hstate rfl rfl rfl rfl
      · exact installVirtualMemory_dormantCancellationCompatible state _ _ hstate

/-- Conditional accepted-unmap refinement for a state whose publication and
runtime projections are already equal.  This theorem does not establish that
`bootRuntime` inhabits the premise or that the ordinary authoritative gate
preserves it across unrelated mapping/lifecycle operations. -/
theorem authoritativeCurrentUnmap_accepted_publication
    state page ack
    (hstate : AuthoritativeRuntimeWellFormed state)
    (hprojection : state.InvalidationProjectionCoherent)
    (hmode : state.execution.mode = .running)
    (hprepared :
      (authoritativePrepareCurrentUnmap state page).accepted = true)
    (hacknowledged :
      (authoritativeAcknowledgeCurrentUnmap
        (authoritativePrepareCurrentUnmap state page).state ack).accepted = true) :
    let prepared := (authoritativePrepareCurrentUnmap state page).state
    let next := (authoritativeAcknowledgeCurrentUnmap prepared ack).state
    prepared.virtualMemory = state.virtualMemory ∧
      prepared.resumable.translations = state.resumable.translations ∧
      AuthoritativeRuntimeWellFormed next ∧
      next.InvalidationProjectionCoherent ∧
      next.virtualMemory = next.resumable.translations.virtual ∧
      next.ipc.virtualMemory = next.virtualMemory := by
  let prepared := (authoritativePrepareCurrentUnmap state page).state
  change (authoritativeAcknowledgeCurrentUnmap prepared ack).accepted = true at hacknowledged
  have hpreparedInvariant :
      AuthoritativeRuntimeWellFormed prepared :=
    authoritativePrepareCurrentUnmap_preserves_authoritativeRuntimeWellFormed
      state page hstate
  obtain ⟨pending, hpending, _hticket, _hkind, hstep, hstepAccepted,
      _heffect, _hpublished⟩ :=
    authoritativePrepareInvalidation_accepted_pending_exact state .unmap
      (.unmap state.execution.core.context.currentSubject
        state.execution.core.context.activeAddressSpace page) hprepared
  have hgenericAck :
      (authoritativeAcknowledgeUnmap prepared ack).accepted = true := by
    cases hgeneric :
        (authoritativeAcknowledgeUnmap prepared ack).accepted with
    | false =>
        have hspecialized :
            (authoritativeAcknowledgeCurrentUnmap prepared ack).accepted =
              false := by
          simp [authoritativeAcknowledgeCurrentUnmap, hgeneric]
        rw [hspecialized] at hacknowledged
        contradiction
    | true => rfl
  obtain ⟨exactPending, hexactPending, _hexactKind, _hackTicket, _hackEffect,
      hpublishedNext, _hcleared⟩ :=
    authoritativeAcknowledgeUnmap_accepted_exact prepared ack hgenericAck
  have hpendingEq : exactPending = pending := by
    change prepared.invalidationPublication.pending = some pending at hpending
    rw [hpending] at hexactPending
    exact (Option.some.inj hexactPending).symm
  subst exactPending
  have hstaleAccepted :
      (StaleTranslation.step state.resumable.translations
        (.unmap state.execution.core.context.currentSubject
          state.execution.core.context.activeAddressSpace page)).accepted = true := by
    rw [← hprojection, ← hstep]
    exact hstepAccepted
  have htlbAccepted :
      (TLB.unmap state.resumable.translations
        state.execution.core.context.currentSubject
        state.execution.core.context.activeAddressSpace page).result =
          .accepted := by
    simp only [StaleTranslation.step] at hstaleAccepted
    split at hstaleAccepted <;> simp_all
  have hvirtualProjection :
      state.resumable.translations.virtual = state.virtualMemory :=
    hstate.1.1.2.2.2.2.2.2.2.2.1
  have hvmAccepted :
      (VirtualMapping.unmap state.virtualMemory
        state.execution.core.context.currentSubject
        state.execution.core.context.activeAddressSpace page).result =
          .accepted := by
    simp only [TLB.unmap] at htlbAccepted
    rw [hvirtualProjection] at htlbAccepted
    split at htlbAccepted <;> simp_all
  have hgate :=
    authoritativeGate_preserves_authoritativeRuntimeWellFormed_of_compatible
      state (.ordinary (.unmap page)) hstate
      (unmap_authoritativeOperationCompatible state page hstate)
  have hpublication :=
    InvalidationPublication.acknowledge_preserves_wellFormed
      prepared.invalidationPublication ack hpreparedInvariant.publication
  let acknowledgedPublication :=
    (authoritativeAcknowledgeUnmap prepared ack).state.invalidationPublication
  have htranslationNext :
      acknowledgedPublication.published =
        (TLB.unmap state.resumable.translations
          state.execution.core.context.currentSubject
          state.execution.core.context.activeAddressSpace page).state := by
    calc
      acknowledgedPublication.published = pending.step.state := hpublishedNext
      _ = (StaleTranslation.step state.invalidationPublication.published
          (.unmap state.execution.core.context.currentSubject
            state.execution.core.context.activeAddressSpace page)).state :=
        congrArg StaleTranslation.Step.state hstep
      _ = (StaleTranslation.step state.resumable.translations
          (.unmap state.execution.core.context.currentSubject
            state.execution.core.context.activeAddressSpace page)).state := by
        rw [hprojection]
      _ = (TLB.unmap state.resumable.translations
          state.execution.core.context.currentSubject
          state.execution.core.context.activeAddressSpace page).state := by
        simp [StaleTranslation.step, htlbAccepted]
  have hprojects :=
    authoritativeAcknowledgeCurrentUnmap_accepted_projects prepared ack
      hacknowledged
  refine ⟨?_, ?_, ?_, hprojects.1, hprojects.2.1, hprojects.2.2⟩
  · rfl
  · rfl
  · refine ⟨?_, ?_, ?_⟩
    · show RuntimeWellFormed
        (authoritativeAcknowledgeCurrentUnmap prepared ack).state
      simp only [authoritativeAcknowledgeCurrentUnmap, hgenericAck, ite_eq_left]
      change RuntimeWellFormed
        (installVirtualMemory prepared acknowledgedPublication.published.virtual
          acknowledgedPublication.published)
      rw [htranslationNext]
      change RuntimeWellFormed
        (installVirtualMemory state
          (TLB.unmap state.resumable.translations
            state.execution.core.context.currentSubject
            state.execution.core.context.activeAddressSpace page).state.virtual
          (TLB.unmap state.resumable.translations
            state.execution.core.context.currentSubject
            state.execution.core.context.activeAddressSpace page).state)
      simpa [authoritativeGate, hmode,
        applyAuthoritativeOperation, applyOperation, TLB.unmap,
        TLB.invalidatePage,
        hvirtualProjection, hvmAccepted] using hgate.1
    · show CompositeState.DeferredCancellationWellFormed
        (authoritativeAcknowledgeCurrentUnmap prepared ack).state
      simp only [authoritativeAcknowledgeCurrentUnmap, hgenericAck, ite_eq_left]
      change (installVirtualMemory prepared
        acknowledgedPublication.published.virtual
          acknowledgedPublication.published).DeferredCancellationWellFormed
      rw [htranslationNext]
      change CompositeState.DeferredCancellationWellFormed
        (installVirtualMemory state
          (TLB.unmap state.resumable.translations
            state.execution.core.context.currentSubject
            state.execution.core.context.activeAddressSpace page).state.virtual
          (TLB.unmap state.resumable.translations
            state.execution.core.context.currentSubject
            state.execution.core.context.activeAddressSpace page).state)
      simpa [authoritativeGate, hmode,
        applyAuthoritativeOperation, applyOperation, TLB.unmap,
        TLB.invalidatePage,
        hvirtualProjection, hvmAccepted] using hgate.2
    · show InvalidationPublication.WellFormed
        ((authoritativeAcknowledgeCurrentUnmap prepared ack).state.invalidationPublication)
      simp only [authoritativeAcknowledgeCurrentUnmap, hgenericAck, ite_eq_left]
      change InvalidationPublication.WellFormed acknowledgedPublication
      simpa [acknowledgedPublication, authoritativeAcknowledgeUnmap,
        authoritativeAcknowledgeInvalidation, installInvalidationPublication,
        hexactPending, _hexactKind] using hpublication

/-- Permission reduction uses the same exact mapping/TLB publisher and leaves
every deferred-cancellation projection literal. -/
theorem protect_authoritativeOperationCompatible state page permissions
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeOperationCompatible state
      (.ordinary (.protect page permissions)) := by
  change DormantCancellationCompatible state
    (authoritativeGate state (.ordinary (.protect page permissions))).state
  cases hmode : state.execution.mode with
  | handling active =>
      simpa [authoritativeGate, hmode] using
        dormantCancellationCompatible_of_exact_projections
          state state hstate rfl rfl rfl rfl
  | halted record =>
      simpa [authoritativeGate, hmode] using
        dormantCancellationCompatible_of_exact_projections
          state state hstate rfl rfl rfl rfl
  | running =>
      simp only [authoritativeGate, hmode, applyAuthoritativeOperation,
        applyOperation]
      split
      · exact dormantCancellationCompatible_of_exact_projections
          state state hstate rfl rfl rfl rfl
      · exact installVirtualMemory_dormantCancellationCompatible state _ _ hstate

/-- Raw mapping has a closed preservation theorem at the folded authoritative
boundary; callers need no post-state compatibility witness. -/
theorem authoritativeGate_map_preserves_authoritativeRuntimeWellFormed
    state slot page permissions
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeGate state
        (.ordinary (.map slot page permissions))).state :=
  authoritativeGate_preserves_authoritativeRuntimeWellFormed_of_compatible state
    (.ordinary (.map slot page permissions)) hstate
    (map_authoritativeOperationCompatible state slot page permissions hstate)

/-- Raw unmapping has the corresponding closed folded-invariant theorem,
including its page-local TLB invalidation. -/
theorem authoritativeGate_unmap_preserves_authoritativeRuntimeWellFormed
    state page (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeGate state (.ordinary (.unmap page))).state :=
  authoritativeGate_preserves_authoritativeRuntimeWellFormed_of_compatible state
    (.ordinary (.unmap page)) hstate
    (unmap_authoritativeOperationCompatible state page hstate)

/-- Raw permission reduction closes the folded global invariant and the exact
page invalidation obligation at the sole authoritative gate. -/
theorem authoritativeGate_protect_preserves_authoritativeRuntimeWellFormed
    state page permissions (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeGate state
        (.ordinary (.protect page permissions))).state :=
  authoritativeGate_preserves_authoritativeRuntimeWellFormed_of_compatible state
    (.ordinary (.protect page permissions)) hstate
    (protect_authoritativeOperationCompatible state page permissions hstate)

/-- Selecting a live return plan changes only execution authority, so it can
be appended to any already-compatible dormant-cancellation mutation. -/
private theorem selectLiveReturnAuthority_dormantCancellationCompatible
    before state purpose
    (hcompatible : DormantCancellationCompatible before state) :
    DormantCancellationCompatible before
      (selectLiveReturnAuthority state purpose) := by
  rw [selectLiveReturnAuthority_eq_execution_update]
  exact
    ⟨hcompatible.deferredExact, hcompatible.blockedDeferredDisjoint,
      hcompatible.blockedResumableDisjoint, hcompatible.retainedQuiescent⟩

/-- The raw syscall family derives caller and active address space from the
execution latch.  Rejections are atomic, access acceptance changes only
return authority, and accepted map/unmap publication reuses the authoritative
virtual-memory compatibility law before selecting that return authority. -/
theorem syscall_authoritativeOperationCompatible state call
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeOperationCompatible state (.ordinary (.syscall call)) := by
  change DormantCancellationCompatible state
    (authoritativeGate state (.ordinary (.syscall call))).state
  cases hmode : state.execution.mode with
  | handling active =>
      simpa [authoritativeGate, hmode] using
        dormantCancellationCompatible_of_exact_projections
          state state hstate rfl rfl rfl rfl
  | halted record =>
      simpa [authoritativeGate, hmode] using
        dormantCancellationCompatible_of_exact_projections
          state state hstate rfl rfl rfl rfl
  | running =>
      simp only [authoritativeGate, hmode, applyAuthoritativeOperation,
        applyOperation]
      cases hreply :
          (Syscall.dispatch state.virtualMemory state.syscallContext call).reply with
      | rejected reason =>
          exact dormantCancellationCompatible_of_exact_projections
            state state hstate rfl rfl rfl rfl
      | accepted =>
          cases hdecode : Syscall.decode call with
          | error reason =>
              simp [Syscall.dispatch, hdecode] at hreply
          | ok operation =>
              cases operation with
              | access page access =>
                  exact
                    selectLiveReturnAuthority_dormantCancellationCompatible
                      state state .syscallResume
                      (dormantCancellationCompatible_of_exact_projections
                        state state hstate rfl rfl rfl rfl)
              | map handleWord page permissions =>
                  exact
                    selectLiveReturnAuthority_dormantCancellationCompatible state
                      (installVirtualMemory state
                        (Syscall.dispatch state.virtualMemory
                          state.syscallContext call).state
                        { state.resumable.translations with
                          virtual :=
                            (Syscall.dispatch state.virtualMemory
                              state.syscallContext call).state })
                      .syscallResume
                      (installVirtualMemory_dormantCancellationCompatible
                        state _ _ hstate)
              | unmap page =>
                  exact
                    selectLiveReturnAuthority_dormantCancellationCompatible state
                      (installVirtualMemory state
                        (Syscall.dispatch state.virtualMemory
                          state.syscallContext call).state
                        (TLB.invalidatePage
                          { state.resumable.translations with
                            virtual :=
                              (Syscall.dispatch state.virtualMemory
                                state.syscallContext call).state }
                          state.execution.core.context.activeAddressSpace page))
                      .syscallResume
                      (installVirtualMemory_dormantCancellationCompatible
                        state _ _ hstate)

/-- Every decoded syscall now has a closed preservation theorem at the folded
authoritative boundary, without a caller-supplied post-state law. -/
theorem authoritativeGate_syscall_preserves_authoritativeRuntimeWellFormed
    state call (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeGate state (.ordinary (.syscall call))).state :=
  authoritativeGate_preserves_authoritativeRuntimeWellFormed_of_compatible state
    (.ordinary (.syscall call)) hstate
    (syscall_authoritativeOperationCompatible state call hstate)

/-- Capability publication changes the blocking scheduler's capability view,
but retains every dormant-cancellation observation.  Registry preservation is
the only non-structural premise needed for retained dead-runner validity. -/
private theorem installCopiedCapabilities_dormantCancellationCompatible
    state capabilities
    (hstate : AuthoritativeRuntimeWellFormed state)
    (hsubjects : capabilities.subjects = state.capabilities.subjects) :
    DormantCancellationCompatible state
      (installCopiedCapabilities state capabilities) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro subject hblocked
    apply hstate.2.1.2.1 subject
    exact hblocked
  · simpa [installCopiedCapabilities] using hstate.2.2.1
  · intro subject saved hretained
    have hvalid := hstate.2.1.2.2 subject saved hretained
    have hcontext := hstate.2.2.2 subject saved hretained
    rcases hstate.1.1 with
      ⟨_, hschedulerLifecycle, _, hcapabilities, _, _, _, _, _, _, _, _, _⟩
    have hbase :
        state.capabilities =
          state.blockingIPC.scheduler.lifecycle.capabilities :=
      hcapabilities.trans
        (congrArg SubjectLifecycle.State.capabilities
          hstate.1.blockingLifecycle.symm)
    have hlive : capabilities.subjects subject = true := by
      rw [hsubjects, hbase]
      exact hvalid.2.2.1
    simpa [installCopiedCapabilities, CompositeState.blockingIPCContext,
        hstate.1.blockingScheduler, hstate.1.blockingLifecycle,
        hschedulerLifecycle, hsubjects, hcapabilities,
        Scheduler.ownsAddressSpace_eq_some_iff] using
      And.intro hvalid.2.1
        (And.intro hlive
          (And.intro hvalid.2.2.2.1
            (And.intro hvalid.2.2.2.2.1
              (And.intro hvalid.2.2.2.2.2.1
                (And.intro hvalid.2.2.2.2.2.2 hcontext)))))

/-- Public capability-publication boundary for a successor whose provenance
and authority obligations have already been checked.  The underlying record
installer remains private so callers cannot unfold a raw publication in place
of discharging this boundary's complete runtime contract. -/
def authoritativePublishCheckedCapabilities (state : CompositeState)
    (capabilities : Capability.State) : CompositeState :=
  installCopiedCapabilities state capabilities

/-- A checked capability successor crosses the folded authoritative boundary
only when it preserves every registry consumed by the runtime, every live slot
comes from the pre-state, and both mapping and blocking-receive authority stay
available.  Deferred-cancellation and invalidation-publication state remain
the exact pre-state projections. -/
theorem authoritativePublishCheckedCapabilities_preserves_authoritativeRuntimeWellFormed
    state next
    (hstate : AuthoritativeRuntimeWellFormed state)
    (hwellFormed : Capability.WellFormed next)
    (hsubjects : next.subjects = state.capabilities.subjects)
    (hobjects : next.objects = state.capabilities.objects)
    (hkinds : next.kinds = state.capabilities.kinds)
    (hnextIdentity : next.nextIdentity = state.capabilities.nextIdentity)
    (hderivations : next.derivations = state.capabilities.derivations)
    (hslots : ∀ subject slot capability,
      next.slots subject slot = some capability →
        state.capabilities.slots subject slot = some capability)
    (hruntimeAuthority : RuntimeAuthorityPreserved state.capabilities next)
    (hreceiveAuthority : ∀ subject endpoint,
      Capability.HasAuthority state.capabilities subject endpoint .receive →
        Capability.HasAuthority next subject endpoint .receive) :
    AuthoritativeRuntimeWellFormed
      (authoritativePublishCheckedCapabilities state next) := by
  have hglobal : RuntimeWellFormed (installCopiedCapabilities state next) :=
    installRevokedCapabilities_preserves_runtimeWellFormed state next hstate.1
      hwellFormed hsubjects hobjects hkinds hnextIdentity hderivations hslots
      hruntimeAuthority
  have hblocking : BlockingRuntimeWellFormed
      (installCopiedCapabilities state next) :=
    installReceiveAuthorityPreservingCapabilities_preserves_blockingRuntimeWellFormed
      state next hstate.blocking hglobal hwellFormed hsubjects hobjects hkinds
      hreceiveAuthority
  have hdeferred : DeferredBlockingRuntimeWellFormed
      (installCopiedCapabilities state next) :=
    dormantCancellationCompatible_preserves state
      (installCopiedCapabilities state next) hstate.deferred hblocking
      (installCopiedCapabilities_dormantCancellationCompatible
        state next hstate hsubjects)
  refine ⟨hdeferred.1, hdeferred.2, ?_⟩
  simpa [authoritativePublishCheckedCapabilities,
    installCopiedCapabilities] using hstate.publication

/-- Publishing a sealed-transfer state has the same dormant-cancellation
boundary as direct capability publication.  Transfer offer/receipt may change
the endpoint mailbox and capability derivation state, but a stable subject
registry keeps every retained dead runner classified by the authoritative
blocking scheduler. -/
private theorem installTransfers_dormantCancellationCompatible
    state transfers
    (hstate : AuthoritativeRuntimeWellFormed state)
    (hsubjects :
      transfers.capabilities.subjects = state.capabilities.subjects) :
    DormantCancellationCompatible state
      (installTransfers state transfers) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro subject hblocked
    apply hstate.2.1.2.1 subject
    exact hblocked
  · simpa [installTransfers] using hstate.2.2.1
  · intro subject saved hretained
    have hvalid := hstate.2.1.2.2 subject saved hretained
    have hcontext := hstate.2.2.2 subject saved hretained
    rcases hstate.1.1 with
      ⟨_, hschedulerLifecycle, _, hcapabilities, _, _, _, _, _, _, _, _, _⟩
    have hlive : transfers.capabilities.subjects subject = true := by
      rw [hsubjects, hcapabilities, ← hstate.1.blockingLifecycle]
      exact hvalid.2.2.1
    simpa [installTransfers, CompositeState.blockingIPCContext,
        hstate.1.blockingScheduler, hstate.1.blockingLifecycle,
        hschedulerLifecycle, hsubjects, hcapabilities,
        Scheduler.ownsAddressSpace_eq_some_iff] using
      And.intro hvalid.2.1
        (And.intro hlive
          (And.intro hvalid.2.2.2.1
            (And.intro hvalid.2.2.2.2.1
              (And.intro hvalid.2.2.2.2.2.1
                (And.intro hvalid.2.2.2.2.2.2 hcontext)))))

/-- A sealed capability offer either rejects atomically or publishes a
transfer state with the exact pre-state subject registry.  The endpoint
mailbox and pending descendant may change, but no retained cancellation can
become live, runnable, current, queued, or resumable as a consequence. -/
theorem transferOffer_authoritativeOperationCompatible state endpointWord
    sourceWord sourceKind payload rights
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeOperationCompatible state
      (.ordinary
        (.transferOffer endpointWord sourceWord sourceKind payload rights)) := by
  change DormantCancellationCompatible state
    (authoritativeGate state
      (.ordinary
        (.transferOffer endpointWord sourceWord sourceKind payload rights))).state
  cases hmode : state.execution.mode with
  | handling active =>
      simpa [authoritativeGate, hmode] using
        dormantCancellationCompatible_of_exact_projections
          state state hstate rfl rfl rfl rfl
  | halted record =>
      simpa [authoritativeGate, hmode] using
        dormantCancellationCompatible_of_exact_projections
          state state hstate rfl rfl rfl rfl
  | running =>
      cases hoffer : CapabilityTransfer.offerWords state.transfers
          state.execution.core.context.currentSubject endpointWord sourceWord
          sourceKind payload rights with
      | mk next result =>
          cases result with
          | rejected reason =>
              simpa [authoritativeGate, hmode, applyAuthoritativeOperation,
                applyOperation, hoffer] using
                dormantCancellationCompatible_of_exact_projections
                  state state hstate rfl rfl rfl rfl
          | accepted =>
              have hregistry :=
                CapabilityTransfer.offerWords_accepted_preserves_authority_registry
                  state.transfers state.execution.core.context.currentSubject
                  endpointWord sourceWord sourceKind payload rights
                  (by simp [hoffer])
              rw [hoffer] at hregistry
              have htransferCapabilities :
                  state.transfers.capabilities = state.capabilities := by
                rcases hstate.1.1 with
                  ⟨_, _, _, hcapabilities, _, _, hipcCapabilities, _, _,
                    htransferEndpoints, _, _, _⟩
                calc
                  state.transfers.capabilities =
                      state.ipc.endpoints.capabilities :=
                    congrArg (fun endpoints => endpoints.capabilities)
                      htransferEndpoints
                  _ = state.lifecycle.capabilities := hipcCapabilities
                  _ = state.capabilities := hcapabilities.symm
              have hsubjects :
                  next.capabilities.subjects =
                    state.capabilities.subjects := by
                exact hregistry.1.trans
                  (congrArg Capability.State.subjects htransferCapabilities)
              simpa [authoritativeGate, hmode, applyAuthoritativeOperation,
                applyOperation, hoffer] using
                installTransfers_dormantCancellationCompatible
                  state next hstate hsubjects

/-- Sealed capability offers have a closed folded-invariant theorem across
the authoritative runtime, including dormant cancellation validity. -/
theorem authoritativeGate_transferOffer_preserves_authoritativeRuntimeWellFormed
    state endpointWord sourceWord sourceKind payload rights
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeGate state
        (.ordinary
          (.transferOffer endpointWord sourceWord sourceKind payload rights))).state :=
  authoritativeGate_preserves_authoritativeRuntimeWellFormed_of_compatible state
    (.ordinary
      (.transferOffer endpointWord sourceWord sourceKind payload rights)) hstate
    (transferOffer_authoritativeOperationCompatible state endpointWord sourceWord
      sourceKind payload rights hstate)

/-- A sealed capability receipt either rejects atomically or publishes a
transfer state with the exact pre-state subject registry.  Delivery may
consume one mailbox and install its checked descendant, but cannot make a
retained cancellation live, runnable, current, queued, or resumable. -/
theorem transferAccept_authoritativeOperationCompatible state endpointWord
    destinationSlot
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeOperationCompatible state
      (.ordinary (.transferAccept endpointWord destinationSlot)) := by
  change DormantCancellationCompatible state
    (authoritativeGate state
      (.ordinary (.transferAccept endpointWord destinationSlot))).state
  cases hmode : state.execution.mode with
  | handling active =>
      simpa [authoritativeGate, hmode] using
        dormantCancellationCompatible_of_exact_projections
          state state hstate rfl rfl rfl rfl
  | halted record =>
      simpa [authoritativeGate, hmode] using
        dormantCancellationCompatible_of_exact_projections
          state state hstate rfl rfl rfl rfl
  | running =>
      cases haccept : CapabilityTransfer.acceptWord state.transfers
          state.execution.core.context.currentSubject endpointWord
          destinationSlot with
      | mk next result deliveredWord =>
          cases result with
          | rejected reason =>
              simpa [authoritativeGate, hmode, applyAuthoritativeOperation,
                applyOperation, haccept] using
                dormantCancellationCompatible_of_exact_projections
                  state state hstate rfl rfl rfl rfl
          | delivered envelope =>
              have hregistry :=
                CapabilityTransfer.acceptWord_delivered_preserves_registry_and_authority
                  state.transfers state.execution.core.context.currentSubject
                  endpointWord destinationSlot envelope (by simp [haccept])
              rw [haccept] at hregistry
              have htransferCapabilities :
                  state.transfers.capabilities = state.capabilities := by
                rcases hstate.1.1 with
                  ⟨_, _, _, hcapabilities, _, _, hipcCapabilities, _, _,
                    htransferEndpoints, _, _, _⟩
                calc
                  state.transfers.capabilities =
                      state.ipc.endpoints.capabilities :=
                    congrArg (fun endpoints => endpoints.capabilities)
                      htransferEndpoints
                  _ = state.lifecycle.capabilities := hipcCapabilities
                  _ = state.capabilities := hcapabilities.symm
              have hsubjects :
                  next.capabilities.subjects =
                    state.capabilities.subjects := by
                exact hregistry.1.trans
                  (congrArg Capability.State.subjects htransferCapabilities)
              simpa [authoritativeGate, hmode, applyAuthoritativeOperation,
                applyOperation, haccept] using
                installTransfers_dormantCancellationCompatible
                  state next hstate hsubjects

/-- Sealed capability receipts have a closed folded-invariant theorem across
the authoritative runtime, including dormant cancellation validity. -/
theorem authoritativeGate_transferAccept_preserves_authoritativeRuntimeWellFormed
    state endpointWord destinationSlot
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeGate state
        (.ordinary (.transferAccept endpointWord destinationSlot))).state :=
  authoritativeGate_preserves_authoritativeRuntimeWellFormed_of_compatible state
    (.ordinary (.transferAccept endpointWord destinationSlot)) hstate
    (transferAccept_authoritativeOperationCompatible state endpointWord
      destinationSlot hstate)

/-- Fresh-subject publication retains the dormant cancellation store, blocked
contexts, and resumable bank exactly.  It only promotes the subject registry
and issuance history; every already-retained subject therefore remains live
while its runnable, current, ready, ownership, and context projections stay
unchanged. -/
private theorem installCreatedSubject_dormantCancellationCompatible
    state subject
    (hstate : AuthoritativeRuntimeWellFormed state) :
    DormantCancellationCompatible state
      (installCreatedSubject state subject) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro candidate hblocked
    apply hstate.2.1.2.1 candidate
    exact hblocked
  · intro candidate saved hblocked
    simpa [installCreatedSubject] using
      hstate.2.2.1 candidate saved hblocked
  · intro candidate saved hretained
    have hvalid := hstate.2.1.2.2 candidate saved hretained
    simp only [CompositeState.blockingIPCContext] at hvalid
    have hcontext := hstate.2.2.2 candidate saved hretained
    have hblockingLifecycle :
        state.blockingIPC.scheduler.lifecycle = state.lifecycle :=
      hstate.1.blockingLifecycle
    have hblockingScheduler :
        state.blockingIPC.scheduler = state.scheduler :=
      hstate.1.blockingScheduler
    have hliveBefore :
        state.lifecycle.capabilities.subjects candidate = true := by
      rw [← hblockingLifecycle]
      exact hvalid.2.2.1
    have hlive :
        (SubjectLifecycle.create state.lifecycle subject).state.capabilities.subjects
          candidate = true :=
      createSubject_preserves_live state.lifecycle subject candidate hliveBefore
    have hrunnable : state.lifecycle.runnable candidate = false := by
      rw [← hblockingLifecycle]
      exact hvalid.2.2.2.1
    have hcurrent : state.lifecycle.current ≠ some candidate := by
      rw [← hblockingLifecycle]
      exact hvalid.2.2.2.2.1
    have hready : candidate ∉ state.scheduler.ready := by
      rw [← hblockingScheduler]
      exact hvalid.2.2.2.2.2.1
    have howner :
        state.lifecycle.addressOwner candidate = some candidate := by
      rw [← hblockingLifecycle]
      simpa [Scheduler.ownsAddressSpace] using hvalid.2.2.2.2.2.2
    simpa [installCreatedSubject, CompositeState.blockingIPCContext,
        Scheduler.ownsAddressSpace] using
      And.intro hvalid.2.1
        (And.intro hlive
          (And.intro hrunnable
            (And.intro hcurrent
              (And.intro hready
                (And.intro howner hcontext)))))

/-- Subject creation either rejects atomically or monotonically publishes one
fresh live identity.  Neither branch can reactivate or attach a dormant
cancellation. -/
theorem createSubject_authoritativeOperationCompatible state subject
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeOperationCompatible state
      (.ordinary (.createSubject subject)) := by
  change DormantCancellationCompatible state
    (authoritativeGate state (.ordinary (.createSubject subject))).state
  cases hmode : state.execution.mode with
  | handling active =>
      simpa [authoritativeGate, hmode] using
        dormantCancellationCompatible_of_exact_projections
          state state hstate rfl rfl rfl rfl
  | halted record =>
      simpa [authoritativeGate, hmode] using
        dormantCancellationCompatible_of_exact_projections
          state state hstate rfl rfl rfl rfl
  | running =>
      cases hcreate : SubjectLifecycle.create state.lifecycle subject with
      | mk next result =>
          cases result with
          | rejected reason =>
              simpa [authoritativeGate, hmode, applyAuthoritativeOperation,
                applyOperation, hcreate] using
                dormantCancellationCompatible_of_exact_projections
                  state state hstate rfl rfl rfl rfl
          | accepted =>
              simpa [authoritativeGate, hmode, applyAuthoritativeOperation,
                applyOperation, hcreate] using
                installCreatedSubject_dormantCancellationCompatible
                  state subject hstate

/-- Fresh-subject publication has a closed folded-invariant theorem across the
authoritative runtime; callers supply only the well-formed pre-state. -/
theorem authoritativeGate_createSubject_preserves_authoritativeRuntimeWellFormed
    state subject (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeGate state
        (.ordinary (.createSubject subject))).state :=
  authoritativeGate_preserves_authoritativeRuntimeWellFormed_of_compatible state
    (.ordinary (.createSubject subject)) hstate
    (createSubject_authoritativeOperationCompatible state subject hstate)

/-- Queue admission changes only the synchronized scheduler projections.
When the admitted identity has no undrained cancellation, every retained
identity is distinct from the appended ready member and therefore remains
quiescent. -/
private theorem installSchedulerAdmission_dormantCancellationCompatible
    state subject context next
    (hstate : AuthoritativeRuntimeWellFormed state)
    (hnotRetained : state.deferredCancels.retained subject = none)
    (haccepted : Scheduler.add state.scheduler subject =
      { state := next, result := .accepted context }) :
    DormantCancellationCompatible state
      (installSchedulerAdmission state next) := by
  obtain ⟨hlifecycle, hready⟩ :=
    schedulerAdd_accepted_projections state.scheduler subject context next haccepted
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro candidate hblocked
    apply hstate.2.1.2.1 candidate
    exact hblocked
  · intro candidate saved hblocked
    simpa [installSchedulerAdmission] using
      hstate.2.2.1 candidate saved hblocked
  · intro candidate saved hretained
    have hvalid := hstate.2.1.2.2 candidate saved hretained
    simp only [CompositeState.blockingIPCContext] at hvalid
    have hcontext := hstate.2.2.2 candidate saved hretained
    have hne : candidate ≠ subject := by
      intro heq
      subst candidate
      rw [hnotRetained] at hretained
      contradiction
    have hblockingScheduler :
        state.blockingIPC.scheduler = state.scheduler :=
      hstate.1.blockingScheduler
    have hreadyBefore : candidate ∉ state.scheduler.ready := by
      rw [← hblockingScheduler]
      exact hvalid.2.2.2.2.2.1
    have hreadyAfter : candidate ∉ next.ready := by
      rw [hready]
      simp [hreadyBefore, hne]
    simpa [installSchedulerAdmission, CompositeState.blockingIPCContext,
        Scheduler.ownsAddressSpace, hlifecycle, hblockingScheduler] using
      And.intro hvalid.2.1
        (And.intro hvalid.2.2.1
          (And.intro hvalid.2.2.2.1
            (And.intro hvalid.2.2.2.2.1
              (And.intro hreadyAfter
                (And.intro hvalid.2.2.2.2.2.2 hcontext)))))

/-- Scheduler admission derives its dormant-cancellation compatibility from
the authoritative pre-state.  The composite transition itself rejects a
candidate awaiting a capacity-checked cancellation drain, so callers no
longer supply that post-state safety condition. -/
theorem scheduleAdd_authoritativeOperationCompatible state subject
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeOperationCompatible state
      (.ordinary (.scheduleAdd subject)) := by
  change DormantCancellationCompatible state
    (authoritativeGate state (.ordinary (.scheduleAdd subject))).state
  cases hmode : state.execution.mode with
  | handling active =>
      simpa [authoritativeGate, hmode] using
        dormantCancellationCompatible_of_exact_projections
          state state hstate rfl rfl rfl rfl
  | halted record =>
      simpa [authoritativeGate, hmode] using
        dormantCancellationCompatible_of_exact_projections
          state state hstate rfl rfl rfl rfl
  | running =>
      cases hadmission : schedulerAdmission state subject with
      | mk next result =>
          cases result with
          | rejected reason =>
              have hnext := schedulerAdmission_rejected_unchanged
                state subject reason (by simp [hadmission])
              simpa [authoritativeGate, hmode, applyAuthoritativeOperation,
                applyOperation, hadmission, hnext] using
                dormantCancellationCompatible_of_exact_projections
                  state state hstate rfl rfl rfl rfl
          | accepted context =>
              obtain ⟨hnotRetained, hadd, _⟩ :=
                schedulerAdmission_accepted_exact
                  state subject context next hadmission
              simpa [authoritativeGate, hmode, applyAuthoritativeOperation,
                applyOperation, hadmission] using
                installSchedulerAdmission_dormantCancellationCompatible
                  state subject context next hstate hnotRetained hadd

/-- Every scheduler-admission result preserves the complete folded
authoritative invariant.  An undrained identity is now a typed, atomic
rejection rather than an external readiness premise. -/
theorem authoritativeGate_scheduleAdd_preserves_authoritativeRuntimeWellFormed
    state subject (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeGate state
        (.ordinary (.scheduleAdd subject))).state :=
  authoritativeGate_preserves_authoritativeRuntimeWellFormed_of_compatible state
    (.ordinary (.scheduleAdd subject)) hstate
    (scheduleAdd_authoritativeOperationCompatible
      state subject hstate)

/-- A retained cancellation cannot be reactivated through scheduler
admission.  The public successor reports the dedicated typed denial and
preserves the complete composite state byte-for-byte. -/
theorem authoritativeGate_scheduleAdd_retained_rejected_atomic
    state subject saved
    (hmode : state.execution.mode = .running)
    (hretained : state.deferredCancels.retained subject = some saved) :
    authoritativeGate state (.ordinary (.scheduleAdd subject)) =
      { state
        result :=
          .completed
            (.ordinary
              (.scheduler (.rejected .undrainedCancellation))) } := by
  simp [authoritativeGate, hmode, applyAuthoritativeOperation,
    authoritativeOperationReply, operationReply, applyOperation,
    schedulerAdmission, hretained, Scheduler.reject]

/-- Resumable-aware scheduler removal cannot invalidate a blocking waiter.
Every waiter is already neither current nor queued, so an accepted raw
removal necessarily targets a different identity and leaves all waiter
authority projections unchanged. -/
private theorem installSchedulerRemoval_blockingIPCContext_wellFormed
    state subject context next
    (hstate : AuthoritativeRuntimeWellFormed state)
    (haccepted : ResumablePreemption.remove state.resumable subject =
      { state := next, result := .accepted context }) :
    BlockingIPCContext.WellFormed
      (installSchedulerRemoval state next).blockingIPCContext := by
  obtain ⟨scheduler, hschedulerRemove, hnext, _hpeer⟩ :=
    ResumablePreemption.remove_accepted_exact state.resumable subject context
      (by simp [haccepted])
  rw [haccepted] at hnext
  change next = ResumablePreemption.removeState
    state.resumable subject scheduler at hnext
  subst next
  rcases hstate.1 with
    ⟨hcoherent, _hexecution, _hlifecycle, _hcapabilities, _hvirtual,
      _hipc, _hschedulerRuntime, _hpreemption, hresumableWellFormed,
      _htransfers, _hhalted, _hlive, hblockingCoherent, _hdevices⟩
  have hshared :
      state.resumable.scheduler = state.blockingIPC.scheduler :=
    hcoherent.2.2.2.2.2.2.2.1.trans hblockingCoherent.1.symm
  have htarget :
      state.resumable.scheduler.lifecycle.current = some subject ∨
        subject ∈ state.resumable.scheduler.ready := by
    simp only [Scheduler.remove] at hschedulerRemove
    split at hschedulerRemove
    · rename_i hselected
      simpa only [Bool.or_eq_true, decide_eq_true_eq] using hselected
    · simp [Scheduler.reject] at hschedulerRemove
  have hschedulerEq : scheduler =
      { state.resumable.scheduler with
        ready := state.resumable.scheduler.ready.filter (· ≠ subject)
        lifecycle := { state.resumable.scheduler.lifecycle with
          runnable := SubjectLifecycle.setBool
            state.resumable.scheduler.lifecycle.runnable subject false
          current := if state.resumable.scheduler.lifecycle.current = some subject
            then none else state.resumable.scheduler.lifecycle.current } } := by
    simp only [Scheduler.remove] at hschedulerRemove
    split at hschedulerRemove
    · simp_all
    · simp_all [Scheduler.reject]
  subst scheduler
  have hresumable :=
    ResumablePreemption.remove_preserves_wellFormed
      state.resumable subject hresumableWellFormed
  rw [haccepted] at hresumable
  rcases hstate.2.1.1 with
    ⟨⟨_hscheduler, hqueues, hwaiters, hunique, hindex, hmailbox,
      hcapabilities⟩, hagreement⟩
  simp only [CompositeState.blockingIPCContext] at hqueues
  simp only [CompositeState.blockingIPCContext] at hwaiters
  simp only [CompositeState.blockingIPCContext] at hunique
  simp only [CompositeState.blockingIPCContext] at hindex
  simp only [CompositeState.blockingIPCContext] at hmailbox
  simp only [CompositeState.blockingIPCContext] at hcapabilities
  simp only [CompositeState.blockingIPCContext] at hagreement
  refine ⟨⟨hresumable.1, hqueues, ?_, hunique, hindex, ?_, ?_⟩, hagreement⟩
  · intro endpoint candidate hmember
    have hvalid := hwaiters endpoint candidate hmember
    simp only [BlockingIPC.authorizedReceive] at hvalid
    rw [← hshared] at hvalid
    have hne : candidate ≠ subject := by
      intro heq
      subst candidate
      exact htarget.elim hvalid.2.2.2.2.2.1 hvalid.2.2.2.2.2.2
    have hne' : subject ≠ candidate := Ne.symm hne
    by_cases hcurrent :
        state.resumable.scheduler.lifecycle.current = some subject
    · simpa [installSchedulerRemoval, ResumablePreemption.removeState,
          CompositeState.blockingIPCContext, BlockingIPC.authorizedReceive,
          SubjectLifecycle.setBool, Scheduler.ownsAddressSpace, hne,
          hne', hcurrent] using hvalid
    · simpa [installSchedulerRemoval, ResumablePreemption.removeState,
          CompositeState.blockingIPCContext, BlockingIPC.authorizedReceive,
          SubjectLifecycle.setBool, Scheduler.ownsAddressSpace, hne,
          hcurrent] using hvalid
  · intro endpoint envelope hstored
    rw [← hshared] at hmailbox
    simpa [installSchedulerRemoval, ResumablePreemption.removeState,
        CompositeState.blockingIPCContext] using hmailbox endpoint envelope hstored
  · simpa [installSchedulerRemoval, ResumablePreemption.removeState,
      CompositeState.blockingIPCContext, hshared] using hcapabilities

/-- Accepted removal only erases the target's resumable context.  A retained
cancellation is already neither current nor queued, so it cannot be that
target; all of its quiescent authority facts and its exact saved context
therefore survive. -/
private theorem installSchedulerRemoval_dormantCancellationCompatible
    state subject context next
    (hstate : AuthoritativeRuntimeWellFormed state)
    (haccepted : ResumablePreemption.remove state.resumable subject =
      { state := next, result := .accepted context }) :
    DormantCancellationCompatible state
      (installSchedulerRemoval state next) := by
  obtain ⟨scheduler, hschedulerRemove, hnext, _hpeer⟩ :=
    ResumablePreemption.remove_accepted_exact state.resumable subject context
      (by simp [haccepted])
  rw [haccepted] at hnext
  change next = ResumablePreemption.removeState
    state.resumable subject scheduler at hnext
  subst next
  have hshared :
      state.resumable.scheduler = state.blockingIPC.scheduler :=
    hstate.1.1.2.2.2.2.2.2.2.1.trans hstate.1.blockingScheduler.symm
  have htarget :
      state.resumable.scheduler.lifecycle.current = some subject ∨
        subject ∈ state.resumable.scheduler.ready := by
    simp only [Scheduler.remove] at hschedulerRemove
    split at hschedulerRemove
    · rename_i hselected
      simpa only [Bool.or_eq_true, decide_eq_true_eq] using hselected
    · simp [Scheduler.reject] at hschedulerRemove
  have hschedulerEq : scheduler =
      { state.resumable.scheduler with
        ready := state.resumable.scheduler.ready.filter (· ≠ subject)
        lifecycle := { state.resumable.scheduler.lifecycle with
          runnable := SubjectLifecycle.setBool
            state.resumable.scheduler.lifecycle.runnable subject false
          current := if state.resumable.scheduler.lifecycle.current = some subject
            then none else state.resumable.scheduler.lifecycle.current } } := by
    simp only [Scheduler.remove] at hschedulerRemove
    split at hschedulerRemove
    · simp_all
    · simp_all [Scheduler.reject]
  subst scheduler
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro candidate hblocked
    apply hstate.2.1.2.1 candidate
    exact hblocked
  · intro candidate saved hblocked
    have hold := hstate.2.2.1 candidate saved hblocked
    by_cases hsame : candidate = subject
    · subst candidate
      simp [installSchedulerRemoval, ResumablePreemption.removeState,
        ResumablePreemption.contextFor_erase_self]
    · simpa [installSchedulerRemoval, ResumablePreemption.removeState,
        ResumablePreemption.contextFor_erase_other, hsame] using hold
  · intro candidate saved hretained
    have hvalid := hstate.2.1.2.2 candidate saved hretained
    simp only [CompositeState.blockingIPCContext] at hvalid
    rw [← hshared] at hvalid
    have hcontext := hstate.2.2.2 candidate saved hretained
    have hne : candidate ≠ subject := by
      intro heq
      subst candidate
      exact htarget.elim hvalid.2.2.2.2.1 hvalid.2.2.2.2.2.1
    have hne' : subject ≠ candidate := Ne.symm hne
    by_cases hcurrent :
        state.resumable.scheduler.lifecycle.current = some subject
    · simpa [installSchedulerRemoval, ResumablePreemption.removeState,
          CompositeState.blockingIPCContext, SubjectLifecycle.setBool,
          Scheduler.ownsAddressSpace, hne, hne', hcurrent,
          ResumablePreemption.contextFor_erase_other] using
        And.intro hvalid.2.1
          (And.intro hvalid.2.2.1
            (And.intro hvalid.2.2.2.1
              (And.intro hvalid.2.2.2.2.1
                (And.intro hvalid.2.2.2.2.2.1
                  (And.intro hvalid.2.2.2.2.2.2 hcontext)))))
    · simpa [installSchedulerRemoval, ResumablePreemption.removeState,
          CompositeState.blockingIPCContext, SubjectLifecycle.setBool,
          Scheduler.ownsAddressSpace, hne, hcurrent,
          ResumablePreemption.contextFor_erase_other] using
        And.intro hvalid.2.1
          (And.intro hvalid.2.2.1
            (And.intro hvalid.2.2.2.1
              (And.intro hvalid.2.2.2.2.1
                (And.intro hvalid.2.2.2.2.2.1
                  (And.intro hvalid.2.2.2.2.2.2 hcontext)))))

/-- Resumable-aware scheduler removal derives both of its formerly external
blocking obligations from the authoritative pre-state.  Rejections and
non-running modes remain byte-for-byte atomic. -/
theorem scheduleRemove_authoritativeOperationCompatible state subject
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeOperationCompatible state
      (.ordinary (.scheduleRemove subject)) := by
  change
    BlockingIPCContext.WellFormed
        (authoritativeGate state
          (.ordinary (.scheduleRemove subject))).state.blockingIPCContext ∧
      DormantCancellationCompatible state
        (authoritativeGate state (.ordinary (.scheduleRemove subject))).state
  cases hmode : state.execution.mode with
  | handling active =>
      refine ⟨?_, ?_⟩
      · simpa [authoritativeGate, hmode] using hstate.2.1.1
      · simpa [authoritativeGate, hmode] using
          dormantCancellationCompatible_of_exact_projections
            state state hstate rfl rfl rfl rfl
  | halted record =>
      refine ⟨?_, ?_⟩
      · simpa [authoritativeGate, hmode] using hstate.2.1.1
      · simpa [authoritativeGate, hmode] using
          dormantCancellationCompatible_of_exact_projections
            state state hstate rfl rfl rfl rfl
  | running =>
      cases hremove : ResumablePreemption.remove state.resumable subject with
      | mk next result =>
          cases result with
          | rejected reason =>
              have hnext := ResumablePreemption.remove_rejected_unchanged
                state.resumable subject reason (by simp [hremove])
              refine ⟨?_, ?_⟩
              · simpa [authoritativeGate, hmode, applyAuthoritativeOperation,
                  applyOperation, hremove, hnext] using hstate.2.1.1
              · simpa [authoritativeGate, hmode, applyAuthoritativeOperation,
                  applyOperation, hremove, hnext] using
                    dormantCancellationCompatible_of_exact_projections
                      state state hstate rfl rfl rfl rfl
          | accepted context =>
              refine ⟨?_, ?_⟩
              · simpa [authoritativeGate, hmode, applyAuthoritativeOperation,
                  applyOperation, hremove] using
                    installSchedulerRemoval_blockingIPCContext_wellFormed
                      state subject context next hstate hremove
              · simpa [authoritativeGate, hmode, applyAuthoritativeOperation,
                  applyOperation, hremove] using
                    installSchedulerRemoval_dormantCancellationCompatible
                      state subject context next hstate hremove

/-- Scheduler removal now has a closed folded-invariant theorem with no
caller-supplied post-state compatibility premise. -/
theorem authoritativeGate_scheduleRemove_preserves_authoritativeRuntimeWellFormed
    state subject (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeGate state
        (.ordinary (.scheduleRemove subject))).state :=
  authoritativeGate_preserves_authoritativeRuntimeWellFormed_of_compatible state
    (.ordinary (.scheduleRemove subject)) hstate
    (scheduleRemove_authoritativeOperationCompatible state subject hstate)

/-- Delegation either rejects atomically or publishes a capability state with
the same live-subject registry, so its dormant cancellation obligations are
derived entirely from the authoritative pre-state. -/
theorem capabilityCopy_authoritativeOperationCompatible state source destination
    destinationSlot rights
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeOperationCompatible state
      (.ordinary (.capabilityCopy source destination destinationSlot rights)) := by
  change DormantCancellationCompatible state
    (authoritativeGate state
      (.ordinary (.capabilityCopy source destination destinationSlot rights))).state
  cases hmode : state.execution.mode with
  | handling active =>
      simpa [authoritativeGate, hmode] using
        dormantCancellationCompatible_of_exact_projections
          state state hstate rfl rfl rfl rfl
  | halted record =>
      simpa [authoritativeGate, hmode] using
        dormantCancellationCompatible_of_exact_projections
          state state hstate rfl rfl rfl rfl
  | running =>
      cases hcopy : Capability.copy state.capabilities
          state.execution.core.context.currentSubject source destination
          destinationSlot rights with
      | mk next result =>
          cases result with
          | rejected reason =>
              simpa [authoritativeGate, hmode, applyAuthoritativeOperation,
                applyOperation, hcopy] using
                dormantCancellationCompatible_of_exact_projections
                  state state hstate rfl rfl rfl rfl
          | accepted =>
              have hregistries := Capability.copy_preserves_registries
                state.capabilities state.execution.core.context.currentSubject
                source destination destinationSlot rights
              rw [hcopy] at hregistries
              simpa [authoritativeGate, hmode, applyAuthoritativeOperation,
                applyOperation, hcopy] using
                installCopiedCapabilities_dormantCancellationCompatible
                  state next hstate hregistries.1

/-- Capability delegation has a closed folded-invariant theorem, including
blocking waiter authority and deferred cancellation validity. -/
theorem authoritativeGate_capabilityCopy_preserves_authoritativeRuntimeWellFormed
    state source destination destinationSlot rights
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeGate state
        (.ordinary
          (.capabilityCopy source destination destinationSlot rights))).state :=
  authoritativeGate_preserves_authoritativeRuntimeWellFormed_of_compatible state
    (.ordinary (.capabilityCopy source destination destinationSlot rights)) hstate
    (capabilityCopy_authoritativeOperationCompatible state source destination
      destinationSlot rights hstate)

/-- Direct revocation either rejects atomically or publishes a capability
state with the same subject registry.  The runtime-safe wrapper's accepted
raw transition supplies the registry law consumed by the common publication
compatibility boundary. -/
theorem capabilityRevoke_authoritativeOperationCompatible state authoritySlot
    victim victimSlot
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeOperationCompatible state
      (.ordinary (.capabilityRevoke authoritySlot victim victimSlot)) := by
  change DormantCancellationCompatible state
    (authoritativeGate state
      (.ordinary (.capabilityRevoke authoritySlot victim victimSlot))).state
  cases hmode : state.execution.mode with
  | handling active =>
      simpa [authoritativeGate, hmode] using
        dormantCancellationCompatible_of_exact_projections
          state state hstate rfl rfl rfl rfl
  | halted record =>
      simpa [authoritativeGate, hmode] using
        dormantCancellationCompatible_of_exact_projections
          state state hstate rfl rfl rfl rfl
  | running =>
      cases hrevoke : Capability.revokeRuntimeSafe state.capabilities
          state.execution.core.context.currentSubject authoritySlot victim
          victimSlot with
      | mk next result =>
          cases result with
          | rejected reason =>
              simpa [authoritativeGate, hmode, applyAuthoritativeOperation,
                applyOperation, hrevoke] using
                dormantCancellationCompatible_of_exact_projections
                  state state hstate rfl rfl rfl rfl
          | accepted =>
              obtain ⟨hraw, _⟩ :=
                Capability.revokeRuntimeSafe_accepted_raw state.capabilities
                  state.execution.core.context.currentSubject authoritySlot
                  victim victimSlot next hrevoke
              have hmetadata := Capability.revoke_preserves_metadata
                state.capabilities state.execution.core.context.currentSubject
                authoritySlot victim victimSlot
              rw [hraw] at hmetadata
              simpa [authoritativeGate, hmode, applyAuthoritativeOperation,
                applyOperation, hrevoke] using
                installCopiedCapabilities_dormantCancellationCompatible
                  state next hstate hmetadata.1

/-- Direct capability revocation has a closed folded-invariant theorem,
including retained blocking-context and deferred-cancellation validity. -/
theorem authoritativeGate_capabilityRevoke_preserves_authoritativeRuntimeWellFormed
    state authoritySlot victim victimSlot
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeGate state
        (.ordinary
          (.capabilityRevoke authoritySlot victim victimSlot))).state :=
  authoritativeGate_preserves_authoritativeRuntimeWellFormed_of_compatible state
    (.ordinary (.capabilityRevoke authoritySlot victim victimSlot)) hstate
    (capabilityRevoke_authoritativeOperationCompatible state authoritySlot
      victim victimSlot hstate)

/-- Transitive revocation has the same dormant-publication boundary as direct
revocation.  Accepted subtree removal retains the subject registry even while
clearing every capability in the selected derivation subtree. -/
theorem capabilityRevokeSubtree_authoritativeOperationCompatible state
    authoritySlot victim victimSlot
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeOperationCompatible state
      (.ordinary (.capabilityRevokeSubtree authoritySlot victim victimSlot)) := by
  change DormantCancellationCompatible state
    (authoritativeGate state
      (.ordinary
        (.capabilityRevokeSubtree authoritySlot victim victimSlot))).state
  cases hmode : state.execution.mode with
  | handling active =>
      simpa [authoritativeGate, hmode] using
        dormantCancellationCompatible_of_exact_projections
          state state hstate rfl rfl rfl rfl
  | halted record =>
      simpa [authoritativeGate, hmode] using
        dormantCancellationCompatible_of_exact_projections
          state state hstate rfl rfl rfl rfl
  | running =>
      cases hrevoke : Capability.revokeSubtreeRuntimeSafe state.capabilities
          state.execution.core.context.currentSubject authoritySlot victim
          victimSlot with
      | mk next result =>
          cases result with
          | rejected reason =>
              simpa [authoritativeGate, hmode, applyAuthoritativeOperation,
                applyOperation, hrevoke] using
                dormantCancellationCompatible_of_exact_projections
                  state state hstate rfl rfl rfl rfl
          | accepted =>
              obtain ⟨hraw, _⟩ :=
                Capability.revokeSubtreeRuntimeSafe_accepted_raw
                  state.capabilities
                  state.execution.core.context.currentSubject authoritySlot
                  victim victimSlot next hrevoke
              have hmetadata := Capability.revokeSubtree_preserves_metadata
                state.capabilities state.execution.core.context.currentSubject
                authoritySlot victim victimSlot
              rw [hraw] at hmetadata
              obtain ⟨target, hlookup, _hclear⟩ :=
                Capability.revokeSubtreeRuntimeSafe_accepted_target
                  state.capabilities state.execution.core.context.currentSubject
                  authoritySlot victim victimSlot next hrevoke
              simpa [authoritativeGate, hmode, applyAuthoritativeOperation,
                applyOperation, hrevoke, hlookup, installRevokedSubtree] using
                installTransfers_dormantCancellationCompatible state
                  (CapabilityTransfer.publishSubtreeRevocation state.transfers
                    target.identity next)
                  hstate (by simpa using hmetadata.1)

/-- Capability-subtree revocation has a closed folded-invariant theorem across
the sole authoritative runtime state. -/
theorem
    authoritativeGate_capabilityRevokeSubtree_preserves_authoritativeRuntimeWellFormed
    state authoritySlot victim victimSlot
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeGate state
        (.ordinary
          (.capabilityRevokeSubtree authoritySlot victim victimSlot))).state :=
  authoritativeGate_preserves_authoritativeRuntimeWellFormed_of_compatible state
    (.ordinary
      (.capabilityRevokeSubtree authoritySlot victim victimSlot)) hstate
    (capabilityRevokeSubtree_authoritativeOperationCompatible state
      authoritySlot victim victimSlot hstate)

end LeanOS.FailStop
