import LeanOS.IOMMU

/-!
# Finite IOMMU translation-cache vocabulary

This module starts the stale-IOMMU-translation model with a bounded cache whose
keys retain every software lifetime needed to distinguish source, assignment,
domain, mapping, and access direction.  It deliberately does not claim VT-d or
QEMU correspondence yet.  Later transition work can require these exact keys
in invalidation tickets before publishing IOMMU mutations or frame reuse.
-/

namespace LeanOS.IOMMU.IOTLB

structure Key where
  source : SourceId
  assignment : AssignmentHandle
  domain : DomainHandle
  mapping : MappingHandle
  iova : IOVA
  direction : Direction
  deriving BEq, DecidableEq, Repr

structure Entry where
  key : Key
  frame : FrameHandle
  permission : Permission
  deriving BEq, DecidableEq, Repr

def capacity : Nat := maxMappings

def lookup (entries : List Entry) (key : Key) : Option Entry :=
  entries.find? fun entry => decide (entry.key = key)

def eraseKey (entries : List Entry) (key : Key) : List Entry :=
  entries.filter fun entry => decide (entry.key ≠ key)

def eraseMapping (entries : List Entry) (mapping : MappingHandle) : List Entry :=
  entries.filter fun entry => decide (entry.key.mapping ≠ mapping)

def eraseAssignment (entries : List Entry)
    (assignment : AssignmentHandle) : List Entry :=
  entries.filter fun entry => decide (entry.key.assignment ≠ assignment)

def insert (entries : List Entry) (entry : Entry) : List Entry :=
  (entry :: eraseKey entries entry.key).take capacity

def Coherent (entries : List Entry) : Prop := entries.length ≤ capacity

theorem erase_mapping_length entries mapping :
    (eraseMapping entries mapping).length ≤ entries.length := by
  exact List.length_filter_le _ _

theorem erase_assignment_length entries assignment :
    (eraseAssignment entries assignment).length ≤ entries.length := by
  exact List.length_filter_le _ _

theorem insert_coherent entries entry : Coherent (insert entries entry) := by
  simp [Coherent, insert, Nat.min_le_left]

theorem erase_mapping_absent entries mapping key
    (hkey : key.mapping = mapping) :
    lookup (eraseMapping entries mapping) key = none := by
  simp only [lookup, List.find?_eq_none, eraseMapping, List.mem_filter]
  intro entry hentry hfound
  have hne := of_decide_eq_true hentry.2
  have heq := of_decide_eq_true hfound
  exact hne (congrArg Key.mapping heq |>.trans hkey)

theorem erase_assignment_absent entries assignment key
    (hkey : key.assignment = assignment) :
    lookup (eraseAssignment entries assignment) key = none := by
  simp only [lookup, List.find?_eq_none, eraseAssignment, List.mem_filter]
  intro entry hentry hfound
  have hne := of_decide_eq_true hentry.2
  have heq := of_decide_eq_true hfound
  exact hne (congrArg Key.assignment heq |>.trans hkey)

theorem erase_key_absent entries key :
    lookup (eraseKey entries key) key = none := by
  simp only [lookup, List.find?_eq_none, eraseKey, List.mem_filter]
  intro entry hentry hfound
  have hne := of_decide_eq_true hentry.2
  have heq := of_decide_eq_true hfound
  exact hne heq

theorem erase_mapping_preserves_coherent entries mapping
    (hcoherent : Coherent entries) : Coherent (eraseMapping entries mapping) := by
  exact Nat.le_trans (erase_mapping_length entries mapping) hcoherent

theorem erase_assignment_preserves_coherent entries assignment
    (hcoherent : Coherent entries) : Coherent (eraseAssignment entries assignment) := by
  exact Nat.le_trans (erase_assignment_length entries assignment) hcoherent

/-! ## Exact invalidation publication

The cache operation alone is not a completion witness.  This small publication
protocol keeps the caller-visible cache unchanged while one exact invalidation
is pending, and publishes the invalidated successor only after a completion
names both the freshly issued ticket and its full lifetime-bearing scope.
-/

structure AssignmentScope where
  source : SourceId
  assignment : AssignmentHandle
  domain : DomainHandle
  deriving BEq, DecidableEq, Repr

structure MappingScope where
  source : SourceId
  assignment : AssignmentHandle
  domain : DomainHandle
  mapping : MappingHandle
  deriving BEq, DecidableEq, Repr

inductive InvalidationScope where
  | mapping (key : Key)
  | mappingSet (scope : MappingScope)
  | assignment (scope : AssignmentScope)
  deriving BEq, DecidableEq, Repr

def eraseMappingScope (entries : List Entry)
    (scope : MappingScope) : List Entry :=
  entries.filter fun entry => decide
    (entry.key.source ≠ scope.source ∨
      entry.key.assignment ≠ scope.assignment ∨
      entry.key.domain ≠ scope.domain ∨
      entry.key.mapping ≠ scope.mapping)

def eraseAssignmentScope (entries : List Entry)
    (scope : AssignmentScope) : List Entry :=
  entries.filter fun entry => decide
    (entry.key.source ≠ scope.source ∨
      entry.key.assignment ≠ scope.assignment ∨
      entry.key.domain ≠ scope.domain)

def invalidate (entries : List Entry) : InvalidationScope → List Entry
  | .mapping key => eraseKey entries key
  | .mappingSet scope => eraseMappingScope entries scope
  | .assignment scope => eraseAssignmentScope entries scope

theorem erase_mapping_scope_absent entries scope key
    (hsource : key.source = scope.source)
    (hassignment : key.assignment = scope.assignment)
    (hdomain : key.domain = scope.domain)
    (hmapping : key.mapping = scope.mapping) :
    lookup (eraseMappingScope entries scope) key = none := by
  simp only [lookup, List.find?_eq_none, eraseMappingScope, List.mem_filter]
  intro entry hentry hfound
  have houtside := of_decide_eq_true hentry.2
  have heq := of_decide_eq_true hfound
  rcases houtside with hne | hne | hne | hne
  · exact hne (congrArg Key.source heq |>.trans hsource)
  · exact hne (congrArg Key.assignment heq |>.trans hassignment)
  · exact hne (congrArg Key.domain heq |>.trans hdomain)
  · exact hne (congrArg Key.mapping heq |>.trans hmapping)

theorem erase_assignment_scope_absent entries scope key
    (hsource : key.source = scope.source)
    (hassignment : key.assignment = scope.assignment)
    (hdomain : key.domain = scope.domain) :
    lookup (eraseAssignmentScope entries scope) key = none := by
  simp only [lookup, List.find?_eq_none, eraseAssignmentScope, List.mem_filter]
  intro entry hentry hfound
  have houtside := of_decide_eq_true hentry.2
  have heq := of_decide_eq_true hfound
  rcases houtside with hne | hne | hne
  · exact hne (congrArg Key.source heq |>.trans hsource)
  · exact hne (congrArg Key.assignment heq |>.trans hassignment)
  · exact hne (congrArg Key.domain heq |>.trans hdomain)

theorem invalidate_mapping_absent entries key :
    lookup (invalidate entries (.mapping key)) key = none := by
  exact erase_key_absent entries key

theorem invalidate_mapping_set_absent entries scope key
    (hsource : key.source = scope.source)
    (hassignment : key.assignment = scope.assignment)
    (hdomain : key.domain = scope.domain)
    (hmapping : key.mapping = scope.mapping) :
    lookup (invalidate entries (.mappingSet scope)) key = none := by
  exact erase_mapping_scope_absent entries scope key hsource hassignment hdomain hmapping

theorem invalidate_assignment_absent entries scope key
    (hsource : key.source = scope.source)
    (hassignment : key.assignment = scope.assignment)
    (hdomain : key.domain = scope.domain) :
    lookup (invalidate entries (.assignment scope)) key = none := by
  exact erase_assignment_scope_absent entries scope key hsource hassignment hdomain

structure PendingInvalidation where
  ticket : Nat
  scope : InvalidationScope
  before : List Entry
  after : List Entry
  deriving DecidableEq, Repr

structure PublicationState where
  published : List Entry
  pending : Option PendingInvalidation
  nextTicket : Nat
  deriving DecidableEq, Repr

structure Completion where
  ticket : Nat
  scope : InvalidationScope
  deriving DecidableEq, Repr

structure PublicationOutcome where
  state : PublicationState
  accepted : Bool
  deriving DecidableEq, Repr

/-- A no-op scope is rejected: a ticket represents an accepted cache
transition, not a caller-selected fence request. -/
def prepareInvalidation (state : PublicationState)
    (scope : InvalidationScope) : PublicationOutcome :=
  match state.pending with
  | some _ => { state, accepted := false }
  | none =>
      let after := invalidate state.published scope
      if after = state.published then
        { state, accepted := false }
      else
        { state := { state with
            pending := some {
              ticket := state.nextTicket
              scope
              before := state.published
              after }
            nextTicket := state.nextTicket + 1 }
          accepted := true }

/-- Completion cannot be acknowledged until the exact ticket, source/domain/
mapping lifetimes, IOVA, direction, and retained pre-state all agree. -/
def acknowledgeInvalidation (state : PublicationState)
    (completion : Completion) : PublicationOutcome :=
  match state.pending with
  | none => { state, accepted := false }
  | some pending =>
      if completion.ticket = pending.ticket ∧
          completion.scope = pending.scope ∧
          pending.before = state.published then
        { state := {
            published := pending.after
            pending := none
            nextTicket := state.nextTicket }
          accepted := true }
      else
        { state, accepted := false }

theorem prepare_retains_published state scope :
    (prepareInvalidation state scope).state.published = state.published := by
  cases hpending : state.pending with
  | some pending => simp [prepareInvalidation, hpending]
  | none =>
      by_cases hchanged : invalidate state.published scope = state.published
      <;> simp [prepareInvalidation, hpending, hchanged]

theorem prepare_accepted_pending_exact state scope
    (haccepted : (prepareInvalidation state scope).accepted = true) :
    ∃ pending,
      (prepareInvalidation state scope).state.pending = some pending ∧
      pending.ticket = state.nextTicket ∧
      pending.scope = scope ∧
      pending.before = state.published ∧
      pending.after = invalidate state.published scope := by
  cases hpending : state.pending with
  | some pending => simp [prepareInvalidation, hpending] at haccepted
  | none =>
      by_cases hchanged : invalidate state.published scope = state.published
      · simp [prepareInvalidation, hpending, hchanged] at haccepted
      · simp [prepareInvalidation, hpending, hchanged]

theorem acknowledge_wrong_ticket_inert state completion pending
    (hpending : state.pending = some pending)
    (hticket : completion.ticket ≠ pending.ticket) :
    (acknowledgeInvalidation state completion).accepted = false ∧
      (acknowledgeInvalidation state completion).state = state := by
  simp [acknowledgeInvalidation, hpending, hticket]

theorem acknowledge_wrong_scope_inert state completion pending
    (hpending : state.pending = some pending)
    (hscope : completion.scope ≠ pending.scope) :
    (acknowledgeInvalidation state completion).accepted = false ∧
      (acknowledgeInvalidation state completion).state = state := by
  simp [acknowledgeInvalidation, hpending, hscope]

theorem acknowledge_accepted_exact state completion
    (haccepted : (acknowledgeInvalidation state completion).accepted = true) :
    ∃ pending,
      state.pending = some pending ∧
      completion.ticket = pending.ticket ∧
      completion.scope = pending.scope ∧
      pending.before = state.published ∧
      (acknowledgeInvalidation state completion).state.published = pending.after ∧
      (acknowledgeInvalidation state completion).state.pending = none := by
  unfold acknowledgeInvalidation at haccepted
  split at haccepted
  · simp_all
  next pending hpending =>
    split at haccepted
    next hexact =>
      refine ⟨pending, hpending, hexact.1, hexact.2.1, hexact.2.2, ?_, ?_⟩
      · simp [acknowledgeInvalidation, hpending, hexact]
      · simp [acknowledgeInvalidation, hpending, hexact]
    next => simp_all

def exampleKey : Key := {
  source := 1
  assignment := ⟨1, 2⟩
  domain := ⟨1, 3⟩
  mapping := ⟨4, 5⟩
  iova := 0x1000
  direction := .read }

def exampleEntry : Entry := {
  key := exampleKey
  frame := ⟨6, 7⟩
  permission := readOnly }

def exampleInitial : PublicationState := {
  published := [exampleEntry]
  pending := none
  nextTicket := 9 }

def examplePrepared : PublicationState :=
  (prepareInvalidation exampleInitial (.mapping exampleKey)).state

def exampleAcknowledged : PublicationState :=
  (acknowledgeInvalidation examplePrepared {
    ticket := 9, scope := .mapping exampleKey }).state

/-- The finite witness makes the ordering non-vacuous: preparation retains the
live translation, a stale ticket is inert, and only the exact completion
publishes its absence. -/
theorem exact_ticket_orders_invalidation :
    (prepareInvalidation exampleInitial (.mapping exampleKey)).accepted = true ∧
      lookup examplePrepared.published exampleKey = some exampleEntry ∧
      (acknowledgeInvalidation examplePrepared {
        ticket := 8, scope := .mapping exampleKey }).accepted = false ∧
      (acknowledgeInvalidation examplePrepared {
        ticket := 8, scope := .mapping exampleKey }).state = examplePrepared ∧
      (acknowledgeInvalidation examplePrepared {
        ticket := 9, scope := .assignment {
          source := 1, assignment := ⟨1, 2⟩, domain := ⟨1, 3⟩ } }).accepted = false ∧
      (acknowledgeInvalidation examplePrepared {
        ticket := 9, scope := .mapping exampleKey }).accepted = true ∧
      lookup exampleAcknowledged.published exampleKey = none := by
  native_decide

/-! ## Authoritative frame-release gate

The static IOMMU model already rejects its control-only `releaseFrame` while
an authoritative mapping names the frame.  The atomic kernel/scrub release
path also needs the cache half of that condition: it must not retire or scrub
a frame while either the published IOTLB or an in-flight invalidation can
still name the old frame lifetime.  This wrapper derives the exact frame from
the authoritative capability binding; callers do not supply it.
-/

def entriesNameFrame (entries : List Entry) (frame : FrameHandle) : Bool :=
  entries.any (·.frame == frame)

def pendingNamesFrame (pending : PendingInvalidation)
    (frame : FrameHandle) : Bool :=
  entriesNameFrame pending.before frame || entriesNameFrame pending.after frame

structure AuthoritativeCacheState where
  authoritative : AuthoritativeExtension
  cache : PublicationState

inductive FrameReleaseGuard where
  | allowed
  | missingAuthority
  | invalidationPending
  | mappingLive
  | cachedTranslationLive
  deriving BEq, DecidableEq, Repr

/-- Resolve the release target through the same authoritative capability and
object-to-frame binding consumed by `gatedMemoryByKernel`. -/
def resolveReleaseFrame (state : AuthoritativeCacheState)
    (subject : FrameScrub.SubjectId) (slot : FrameScrub.SlotId) :
    Option FrameHandle :=
  match LeanOS.Capability.lookup
      state.authoritative.scrub.memory.capabilities subject slot with
  | .found capability =>
      state.authoritative.iommu.core.frameAuthority capability.object
  | .invalidSubject | .staleSlot => none

/-- Pending invalidation is checked first.  Even if the logical mapping has
already been removed, its retained pre-state remains device-reachable until
the exact completion publishes the invalidated cache. -/
def guardExactFrameRelease (state : AuthoritativeCacheState)
    (frame : FrameHandle) : FrameReleaseGuard :=
  match state.cache.pending with
  | some pending =>
      if pendingNamesFrame pending frame then .invalidationPending
      else if state.authoritative.iommu.core.mappings.any (·.frame == frame) then
        .mappingLive
      else if entriesNameFrame state.cache.published frame then
        .cachedTranslationLive
      else .allowed
  | none =>
      if state.authoritative.iommu.core.mappings.any (·.frame == frame) then
        .mappingLive
      else if entriesNameFrame state.cache.published frame then
        .cachedTranslationLive
      else .allowed

def guardFrameRelease (state : AuthoritativeCacheState)
    (subject : FrameScrub.SubjectId) (slot : FrameScrub.SlotId) :
    FrameReleaseGuard :=
  match resolveReleaseFrame state subject slot with
  | none => .missingAuthority
  | some frame => guardExactFrameRelease state frame

theorem pending_invalidation_blocks_exact_frame_release state frame pending
    (hpending : state.cache.pending = some pending)
    (hnames : pendingNamesFrame pending frame = true) :
    guardExactFrameRelease state frame = .invalidationPending := by
  simp [guardExactFrameRelease, hpending, hnames]

theorem live_mapping_blocks_exact_frame_release state frame
    (hpending : state.cache.pending = none)
    (hmapping :
      state.authoritative.iommu.core.mappings.any (·.frame == frame) = true) :
    guardExactFrameRelease state frame = .mappingLive := by
  simp [guardExactFrameRelease, hpending, hmapping]

theorem published_translation_blocks_exact_frame_release state frame
    (hpending : state.cache.pending = none)
    (hmapping :
      state.authoritative.iommu.core.mappings.any (·.frame == frame) = false)
    (hcache : entriesNameFrame state.cache.published frame = true) :
    guardExactFrameRelease state frame = .cachedTranslationLive := by
  simp [guardExactFrameRelease, hpending, hmapping, hcache]

theorem exact_frame_release_allowed_only_after_cleanup state frame
    (hpending : state.cache.pending = none)
    (hmapping :
      state.authoritative.iommu.core.mappings.any (·.frame == frame) = false)
    (hcache : entriesNameFrame state.cache.published frame = false) :
    guardExactFrameRelease state frame = .allowed := by
  simp [guardExactFrameRelease, hpending, hmapping, hcache]

/-! ## Cache-aware authoritative memory publication

`gatedMemoryByKernel` is the authoritative release/scrub boundary, but its
IOMMU projection does not contain the separately published IOTLB state.  This
wrapper makes that missing projection explicit and checks it before delegating
a release.  Rejection retains both projections; accepted non-release
operations and an eligible release retain the cache while publishing only the
authoritative successor returned by the existing gate.
-/

inductive CachedMemoryReject where
  | authoritative (reason : AuthoritativeMemoryReject)
  | missingAuthority
  | invalidationPending
  | mappingLive
  | cachedTranslationLive
  deriving DecidableEq, Repr

inductive CachedMemoryOutcome (before : AuthoritativeCacheState) where
  | accepted (after : AuthoritativeCacheState)
      (invariant : after.authoritative.Invariant)
      (reply : AuthoritativeMemoryReply)
  | rejected (reason : CachedMemoryReject)

def CachedMemoryOutcome.state {before : AuthoritativeCacheState} :
    CachedMemoryOutcome before → AuthoritativeCacheState
  | .accepted after _ _ => after
  | .rejected _ => before

def CachedMemoryOutcome.reason {before : AuthoritativeCacheState} :
    CachedMemoryOutcome before → Option CachedMemoryReject
  | .accepted _ _ _ => none
  | .rejected reason => some reason

def CachedMemoryOutcome.isAccepted {before : AuthoritativeCacheState} :
    CachedMemoryOutcome before → Bool
  | .accepted _ _ _ => true
  | .rejected _ => false

private def liftMemoryOutcome (before : AuthoritativeCacheState) :
    AuthoritativeMemoryOutcome before.authoritative → CachedMemoryOutcome before
  | .accepted after hinvariant reply =>
      .accepted { authoritative := after, cache := before.cache } hinvariant reply
  | .rejected reason => .rejected (.authoritative reason)

/-- Release cannot enter the authoritative lifecycle gate until logical
mappings, published translations, and exact pending invalidations have all
stopped naming the old frame lifetime. -/
noncomputable def gatedCachedMemoryByKernel (state : AuthoritativeCacheState)
    (hstate : state.authoritative.Invariant)
    (operation : AuthoritativeMemoryOperation) : CachedMemoryOutcome state :=
  match operation with
  | .release subject slot =>
      match guardFrameRelease state subject slot with
      | .allowed =>
          liftMemoryOutcome state
            (gatedMemoryByKernel state.authoritative hstate operation)
      | .missingAuthority => .rejected .missingAuthority
      | .invalidationPending => .rejected .invalidationPending
      | .mappingLive => .rejected .mappingLive
      | .cachedTranslationLive => .rejected .cachedTranslationLive
  | operation =>
      liftMemoryOutcome state
        (gatedMemoryByKernel state.authoritative hstate operation)

theorem cached_release_guard_rejection_stutters state hstate subject slot reason
    (hguard : guardFrameRelease state subject slot = reason)
    (hblocked : reason ≠ .allowed) :
    (gatedCachedMemoryByKernel state hstate (.release subject slot)).state = state := by
  cases reason <;>
    simp_all [gatedCachedMemoryByKernel, CachedMemoryOutcome.state]

theorem cached_release_pending_rejected state hstate subject slot
    (hguard : guardFrameRelease state subject slot = .invalidationPending) :
    (gatedCachedMemoryByKernel state hstate (.release subject slot)).reason =
      some .invalidationPending := by
  simp [gatedCachedMemoryByKernel, hguard, CachedMemoryOutcome.reason]

theorem cached_release_accepted_requires_guard_allowed state hstate subject slot
    (haccepted :
      (gatedCachedMemoryByKernel state hstate
        (.release subject slot)).isAccepted = true) :
    guardFrameRelease state subject slot = .allowed := by
  cases hguard : guardFrameRelease state subject slot <;>
    simp_all [gatedCachedMemoryByKernel, CachedMemoryOutcome.isAccepted,
      liftMemoryOutcome]

/-- An accepted cache-aware release is tied to a frame resolved from the
authoritative subject/slot capability, and that exact frame has passed the
IOTLB-aware release guard.  This prevents later machine call-order evidence
from replacing capability resolution with a caller-supplied frame number. -/
theorem cached_release_accepted_resolves_guarded_frame state hstate subject slot
    (haccepted :
      (gatedCachedMemoryByKernel state hstate
        (.release subject slot)).isAccepted = true) :
    ∃ frame,
      resolveReleaseFrame state subject slot = some frame ∧
        guardExactFrameRelease state frame = .allowed := by
  have hguard := cached_release_accepted_requires_guard_allowed
    state hstate subject slot haccepted
  unfold guardFrameRelease at hguard
  split at hguard
  · cases hguard
  · rename_i frame hresolve
    exact ⟨frame, hresolve, hguard⟩

theorem cached_release_allowed_delegates state hstate subject slot
    (hguard : guardFrameRelease state subject slot = .allowed) :
    (gatedCachedMemoryByKernel state hstate
        (.release subject slot)).state.authoritative =
        (gatedMemoryByKernel state.authoritative hstate
          (.release subject slot)).state ∧
      (gatedCachedMemoryByKernel state hstate
        (.release subject slot)).state.cache = state.cache := by
  cases hmemory : gatedMemoryByKernel state.authoritative hstate
      (.release subject slot) <;>
    simp [gatedCachedMemoryByKernel, hguard, liftMemoryOutcome, hmemory,
      CachedMemoryOutcome.state, AuthoritativeMemoryOutcome.state]

/-- An exact-frame cleanup result reaches the actual subject/slot memory
release boundary only through authoritative capability resolution.  Once that
resolution names the same frame, the cache-aware gate delegates to the
existing release/scrub transition and retains the published cache. -/
theorem exact_frame_release_allowed_delegates state hstate subject slot frame
    (hresolve : resolveReleaseFrame state subject slot = some frame)
    (hexact : guardExactFrameRelease state frame = .allowed) :
    (gatedCachedMemoryByKernel state hstate
        (.release subject slot)).state.authoritative =
        (gatedMemoryByKernel state.authoritative hstate
          (.release subject slot)).state ∧
      (gatedCachedMemoryByKernel state hstate
        (.release subject slot)).state.cache = state.cache := by
  apply cached_release_allowed_delegates
  simp [guardFrameRelease, hresolve, hexact]

/-! ## Coupled logical-transition publication

Accepted unmap, permission-reduction, and assignment-teardown operations must
not publish their logical successor before the corresponding exact IOTLB
completion.  The pending record below retains the checked successor returned
by `gatedByKernel`; callers supply neither that successor nor its scope.
While a record is pending, preparation stutters, so the completion's ticket
and scope remain bound to one authoritative pre-state and one logical step.
-/

structure PendingControl where
  ticket : Nat
  scope : InvalidationScope
  logicalAfter : AuthoritativeExtension
  cacheBefore : List Entry
  cacheAfter : List Entry
  reply : AcceptedReply

structure ControlPublicationState where
  authoritative : AuthoritativeExtension
  cache : List Entry
  pending : Option PendingControl
  nextTicket : Nat

structure ControlPublicationOutcome where
  state : ControlPublicationState
  accepted : Bool

def mappingScopeFor (state : AuthoritativeExtension)
    (handle : MappingHandle) : Option MappingScope := do
  let mapping ← findMapping state.iommu.core handle
  let assignment ← findAssignment state.iommu.core mapping.assignment
  pure {
    source := assignment.source
    assignment := mapping.assignment
    domain := mapping.domain
    mapping := mapping.handle }

def assignmentScopeFor (state : AuthoritativeExtension)
    (handle : AssignmentHandle) : Option AssignmentScope := do
  let assignment ← findAssignment state.iommu.core handle
  pure {
    source := assignment.source
    assignment := assignment.handle
    domain := assignment.domain }

/-- Derive the invalidation solely from the authoritative pre-state and the
accepted operation identity.  Mapping attenuation invalidates the complete
old mapping lifetime, including both access directions and every cached IOVA
in its bounded range. -/
def requiredControlScope (state : AuthoritativeExtension) :
    Operation → Option InvalidationScope
  | .unmap handle => .mappingSet <$> mappingScopeFor state handle
  | .attenuate request => .mappingSet <$> mappingScopeFor state request.mapping
  | .teardown handle => .assignment <$> assignmentScopeFor state handle
  | _ => none

noncomputable def prepareControlPublication
    (state : ControlPublicationState)
    (hstate : state.authoritative.Invariant)
    (operation : Operation) : ControlPublicationOutcome :=
  match state.pending with
  | some _ => { state, accepted := false }
  | none =>
      match requiredControlScope state.authoritative operation with
      | none => { state, accepted := false }
      | some scope =>
          match gatedByKernel state.authoritative hstate operation with
          | .rejected _ => { state, accepted := false }
          | .accepted logicalAfter _ reply =>
              let pending : PendingControl := {
                ticket := state.nextTicket
                scope
                logicalAfter
                cacheBefore := state.cache
                cacheAfter := invalidate state.cache scope
                reply }
              { state := { state with
                  pending := some pending
                  nextTicket := state.nextTicket + 1 }
                accepted := true }

def acknowledgeControlPublication (state : ControlPublicationState)
    (completion : Completion) : ControlPublicationOutcome :=
  match state.pending with
  | none => { state, accepted := false }
  | some pending =>
      if completion.ticket = pending.ticket ∧
          completion.scope = pending.scope ∧
          pending.cacheBefore = state.cache then
        { state := {
            authoritative := pending.logicalAfter
            cache := pending.cacheAfter
            pending := none
            nextTicket := state.nextTicket }
          accepted := true }
      else
        { state, accepted := false }

theorem prepare_control_retains_publications state hstate operation :
    let prepared := prepareControlPublication state hstate operation
    prepared.state.authoritative = state.authoritative ∧
      prepared.state.cache = state.cache := by
  simp only [prepareControlPublication]
  split
  · simp
  · split
    · simp
    · split <;> simp

theorem prepare_control_accepted_binds_exact_successor state hstate operation
    (haccepted : (prepareControlPublication state hstate operation).accepted = true) :
    ∃ pending scope logicalAfter hinvariant reply,
      requiredControlScope state.authoritative operation = some scope ∧
      gatedByKernel state.authoritative hstate operation =
        .accepted logicalAfter hinvariant reply ∧
      (prepareControlPublication state hstate operation).state.pending = some pending ∧
      pending.ticket = state.nextTicket ∧
      pending.scope = scope ∧
      pending.logicalAfter = logicalAfter ∧
      pending.cacheBefore = state.cache ∧
      pending.cacheAfter = invalidate state.cache scope := by
  simp only [prepareControlPublication] at haccepted ⊢
  split at haccepted
  · simp_all
  next hpending =>
    split at haccepted
    · simp_all
    next scope hscope =>
      split at haccepted
      · simp_all
      next logicalAfter hinvariant reply hgate =>
        simp_all

theorem acknowledge_control_wrong_ticket_inert state completion pending
    (hpending : state.pending = some pending)
    (hticket : completion.ticket ≠ pending.ticket) :
    (acknowledgeControlPublication state completion).accepted = false ∧
      (acknowledgeControlPublication state completion).state = state := by
  simp [acknowledgeControlPublication, hpending, hticket]

theorem acknowledge_control_accepted_publishes_exact state completion
    (haccepted : (acknowledgeControlPublication state completion).accepted = true) :
    ∃ pending,
      state.pending = some pending ∧
      completion.ticket = pending.ticket ∧
      completion.scope = pending.scope ∧
      pending.cacheBefore = state.cache ∧
      (acknowledgeControlPublication state completion).state.authoritative =
        pending.logicalAfter ∧
      (acknowledgeControlPublication state completion).state.cache =
        pending.cacheAfter ∧
      (acknowledgeControlPublication state completion).state.pending = none := by
  unfold acknowledgeControlPublication at haccepted
  split at haccepted
  · simp_all
  next pending hpending =>
    split at haccepted
    next hexact =>
      refine ⟨pending, hpending, hexact.1, hexact.2.1, hexact.2.2, ?_, ?_, ?_⟩ <;>
        simp [acknowledgeControlPublication, hpending, hexact]
    next => simp_all

/-! ## Capability and subject-cleanup publication

Kernel capability revocation and subject termination can remove several DMA
mappings and assignments in one authoritative transition.  Publishing that
transition behind a single-entry invalidation protocol would permit a partial
cleanup, so this boundary derives the complete finite scope set from the
checked kernel successor and publishes neither projection until one exact
completion names that whole set.
-/

def scopeCoversKey : InvalidationScope → Key → Bool
  | .mapping expected, key => key == expected
  | .mappingSet scope, key =>
      key.source == scope.source &&
        key.assignment == scope.assignment &&
        key.domain == scope.domain &&
        key.mapping == scope.mapping
  | .assignment scope, key =>
      key.source == scope.source &&
        key.assignment == scope.assignment &&
        key.domain == scope.domain

def invalidateScopes (entries : List Entry)
    (scopes : List InvalidationScope) : List Entry :=
  entries.filter fun entry => !scopes.any (scopeCoversKey · entry.key)

theorem invalidate_scopes_covered_absent entries scopes key
    (hcovered : scopes.any (scopeCoversKey · key) = true) :
    lookup (invalidateScopes entries scopes) key = none := by
  simp only [lookup, List.find?_eq_none, invalidateScopes, List.mem_filter]
  intro entry hentry hfound
  have heq := of_decide_eq_true hfound
  have hretained := hentry.2
  rw [heq] at hretained
  simp [hcovered] at hretained

theorem invalidate_scopes_preserves_coherent entries scopes
    (hcoherent : Coherent entries) :
    Coherent (invalidateScopes entries scopes) := by
  exact Nat.le_trans (List.length_filter_le _ _) hcoherent

/-- Every scope comes from an authority record present in the published
pre-state but absent from the checked kernel successor.  Mapping scopes are
retained even when assignment teardown also covers them, making the complete
removed authority inventory explicit in evidence. -/
def requiredAuthorityCleanupScopes (before after : AuthoritativeExtension) :
    List InvalidationScope :=
  let mappings := before.iommu.core.mappings.filterMap fun mapping =>
    if after.iommu.core.mappings.any (·.handle == mapping.handle) then none
    else .mappingSet <$> mappingScopeFor before mapping.handle
  let assignments := before.iommu.core.assignments.filterMap fun assignment =>
    if after.iommu.core.assignments.any (·.handle == assignment.handle) then none
    else .assignment <$> assignmentScopeFor before assignment.handle
  mappings ++ assignments

/-- A capability-subtree revocation cannot hide a removed DMA mapping from
the cleanup inventory.  Once the checked authoritative successor no longer
contains a mapping that was present before the transition, its exact
source/assignment/domain/mapping scope is part of the required completion.
The operation parameters select the real composite subtree boundary; the
caller does not supply the successor or its cleanup inventory. -/
theorem capability_subtree_revocation_removed_mapping_requires_scope
    (state : AuthoritativeExtension) (authoritySlot victim victimSlot : Nat)
    (mapping : Mapping) (scope : MappingScope)
    (hmapping : mapping ∈ state.iommu.core.mappings)
    (hremoved :
      (applyKernelOperation state
          (.ordinary
            (.capabilityRevokeSubtree authoritySlot victim victimSlot))).iommu.core.mappings.any
        (·.handle == mapping.handle) = false)
    (hscope : mappingScopeFor state mapping.handle = some scope) :
    .mappingSet scope ∈
      requiredAuthorityCleanupScopes state
        (applyKernelOperation state
          (.ordinary
            (.capabilityRevokeSubtree authoritySlot victim victimSlot))) := by
  simp only [requiredAuthorityCleanupScopes, List.mem_append]
  left
  simp only [List.mem_filterMap]
  exact ⟨mapping, hmapping, by simp [hremoved, hscope]⟩

/-! A finite parent/child capability fixture keeps the transitive-revocation
premise executable before it is lifted into the complete authoritative IOMMU
state.  The selected root and its child carry only endpoint-send authority, so
the composite runtime-safety guard permits their removal; the independent
revocation capability is retained. -/

def subtreeCleanupWitnessAuthority : LeanOS.Capability.Capability :=
  { object := 10
    kind := .endpoint
    rights := { revoke := true }
    identity := 1 }

def subtreeCleanupWitnessRoot : LeanOS.Capability.Capability :=
  { object := 10
    kind := .endpoint
    rights := { send := true }
    identity := 2 }

def subtreeCleanupWitnessChild : LeanOS.Capability.Capability :=
  { object := 10
    kind := .endpoint
    rights := { send := true }
    identity := 3
    parent := some 2 }

def subtreeCleanupWitnessCapabilities : LeanOS.Capability.State :=
  { nextIdentity := 4
    derivations := fun identity =>
      if identity = 1 then
        some (none, 10, .endpoint, { revoke := true })
      else if identity = 2 then
        some (none, 10, .endpoint, { send := true })
      else if identity = 3 then
        some (some 2, 10, .endpoint, { send := true })
      else none
    subjects := fun subject => subject = 0 || subject = 1 || subject = 2
    objects := fun object => object = 10
    kinds := fun object => if object = 10 then some .endpoint else none
    slots := fun subject slot =>
      if subject = 0 && slot = 0 then some subtreeCleanupWitnessAuthority
      else if subject = 1 && slot = 0 then some subtreeCleanupWitnessRoot
      else if subject = 2 && slot = 0 then some subtreeCleanupWitnessChild
      else none }

/-- The finite lineage fixture satisfies the complete capability authority
contract: every live slot agrees with its append-only derivation record, the
child attenuates its recorded parent, live identities are unique, and no
capability is installed outside the default four-slot subject spaces. -/
theorem subtreeCleanupWitnessCapabilities_wellFormed :
    LeanOS.Capability.WellFormed subtreeCleanupWitnessCapabilities := by
  simp only [LeanOS.Capability.WellFormed]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro subject slot capability hslot
    simp only [subtreeCleanupWitnessCapabilities,
      subtreeCleanupWitnessAuthority, subtreeCleanupWitnessRoot,
      subtreeCleanupWitnessChild] at hslot
    repeat' split at hslot
    all_goals cases hslot <;>
      simp [subtreeCleanupWitnessCapabilities,
        subtreeCleanupWitnessAuthority, subtreeCleanupWitnessRoot,
        subtreeCleanupWitnessChild, LeanOS.Capability.rightsValid,
        LeanOS.Capability.rightsSubset]
    all_goals grind
  · intro identity parent object kind rights hderivation
    simp only [subtreeCleanupWitnessCapabilities] at hderivation
    repeat' split at hderivation
    all_goals rcases hderivation with ⟨rfl, rfl, rfl, rfl⟩ <;>
      simp [subtreeCleanupWitnessCapabilities,
        LeanOS.Capability.rightsSubset]
    all_goals grind
  · intro subject slot capability otherSubject otherSlot otherCapability
      hslot hother hidentity
    simp only [subtreeCleanupWitnessCapabilities,
      subtreeCleanupWitnessAuthority, subtreeCleanupWitnessRoot,
      subtreeCleanupWitnessChild] at hslot hother
    repeat' split at hslot
    all_goals repeat' split at hother
    all_goals cases hslot <;> cases hother <;> simp_all
  · intro subject slot hslot
    change 4 ≤ slot at hslot
    have hne0 : slot ≠ 0 := by omega
    simp [subtreeCleanupWitnessCapabilities, hne0]

/-- The checked runtime-safe subtree operation follows the recorded parent
edge and removes both the selected root and its child atomically.  This is the
concrete lineage fixture used by the next authoritative-IOMMU composition
step; it does not yet claim that a DMA mapping was published from this state. -/
theorem executable_capability_subtree_revocation_removes_parent_and_child :
    let outcome := LeanOS.Capability.revokeSubtreeRuntimeSafe
      subtreeCleanupWitnessCapabilities 0 0 1 0
    outcome.result = .accepted ∧
      outcome.state.slots 1 0 = none ∧
      outcome.state.slots 2 0 = none ∧
      outcome.state.slots 0 0 = some subtreeCleanupWitnessAuthority := by
  native_decide

/-! ## Capability-lineage/DMA composition boundary

The executable subtree fixture above deliberately uses endpoint-send rights:
those rights may be removed by the existing generic runtime-safe revocation
gate.  This is not yet a DMA-authority fixture.  The finite checks below make
the missing composition explicit instead of silently treating an endpoint
lineage as mapping authority.
-/

def subtreeCleanupWitnessDMAAttemptCapability : Capability :=
  { slot := 0
    identity := subtreeCleanupWitnessChild.identity
    owner := 2
    object := subtreeCleanupWitnessChild.object
    frame := ⟨4, 1⟩
    offset := 0
    length := 64
    permission := readWrite }

def subtreeCleanupWitnessDMAAttemptCore : Core :=
  { emptyCore with
    currentOwner := 2
    frames := [⟨⟨4, 1⟩, 2, true, false, false, false, 64⟩]
    capabilityAuthority := subtreeCleanupWitnessCapabilities
    frameAuthority := fun object =>
      if object == subtreeCleanupWitnessChild.object then some ⟨4, 1⟩ else none
    capabilities := [subtreeCleanupWitnessDMAAttemptCapability] }

/-- Endpoint lineage cannot be reinterpreted as memory/DMA authority merely
because its object and identity match.  The finite IOMMU validator checks the
authoritative capability kind and rejects this attempted binding. -/
theorem subtree_cleanup_endpoint_lineage_cannot_authorize_dma :
    capabilityValid subtreeCleanupWitnessDMAAttemptCore
      subtreeCleanupWitnessDMAAttemptCapability = false := by
  native_decide

/-- Conversely, the canonical memory capability that can authorize the DMA
frame carries runtime-critical read/write rights, so the generic subtree gate
must reject its removal.  The lifecycle composition therefore needs one
coordinated checked front door that removes the capability descendants and
their IOMMU authority together; neither existing gate can be reused alone. -/
theorem canonical_dma_memory_subtree_requires_coordinated_cleanup
    (plan : BootPageTablePlan.Plan) :
    LeanOS.Capability.subtreeRevocationRuntimeSafe
      (FailStop.compositeDispatcherInitial plan).capabilities 2 2 = false := by
  rfl

/-! The conservative rejection above must not be confused with an inability
to derive the requested capability successor.  The raw capability transition
is deterministic and accepted for the canonical subject-2 memory root; it
removes that exact root.  What is missing is a publisher that installs this
already-derived successor together with the IOMMU cleanup, rather than asking
the generic runtime gate to publish the capability change by itself. -/

def canonicalDMAMemorySubtreeRawAfter (plan : BootPageTablePlan.Plan) :
    LeanOS.Capability.Outcome :=
  LeanOS.Capability.revokeSubtree
    (FailStop.compositeDispatcherInitial plan).capabilities 2 2 2 2

/-- The checked raw transition derives the transitive capability successor
from the authoritative pre-state: the selected memory root is removed and no
caller supplies a replacement capability store. -/
theorem canonical_dma_memory_raw_subtree_derives_successor
    (plan : BootPageTablePlan.Plan) :
    (canonicalDMAMemorySubtreeRawAfter plan).result = .accepted ∧
      (canonicalDMAMemorySubtreeRawAfter plan).state.slots 2 2 = none := by
  simp [canonicalDMAMemorySubtreeRawAfter, LeanOS.Capability.revokeSubtree,
    LeanOS.Capability.lookup, FailStop.compositeDispatcherInitial]
  native_decide

/-- The ordinary runtime-facing operation deliberately stutters on that same
request.  This pins the exact integration gap: a coordinated front door must
use the checked raw successor while simultaneously removing DMA authority;
silently weakening the existing runtime-safety guard is not an option. -/
theorem canonical_dma_memory_ordinary_subtree_gate_stutters
    (plan : BootPageTablePlan.Plan) :
    (FailStop.authoritativeGate (FailStop.compositeDispatcherInitial plan)
      (.ordinary (.capabilityRevokeSubtree 2 2 2))).state =
        FailStop.compositeDispatcherInitial plan := by
  rfl

structure PendingAuthorityCleanup where
  ticket : Nat
  scopes : List InvalidationScope
  logicalAfter : AuthoritativeExtension
  cacheBefore : List Entry
  cacheAfter : List Entry

structure AuthorityCleanupPublicationState where
  authoritative : AuthoritativeExtension
  cache : List Entry
  pending : Option PendingAuthorityCleanup
  nextTicket : Nat

structure AuthorityCleanupCompletion where
  ticket : Nat
  scopes : List InvalidationScope

structure AuthorityCleanupPublicationOutcome where
  state : AuthorityCleanupPublicationState
  accepted : Bool

/-- Frame-lifecycle publication must also observe the multi-scope cleanup
ticket.  While that ticket retains a cache projection naming the old frame
lifetime, release and the downstream scrub/fresh-lifetime path remain
blocked.  Once no cleanup is pending, the ordinary exact-frame guard decides
from the published authority and cache projections. -/
def guardAuthorityCleanupExactFrameRelease
    (state : AuthorityCleanupPublicationState)
    (frame : FrameHandle) : FrameReleaseGuard :=
  match state.pending with
  | some pending =>
      if entriesNameFrame pending.cacheBefore frame ||
          entriesNameFrame pending.cacheAfter frame then
        .invalidationPending
      else
        guardExactFrameRelease {
          authoritative := state.authoritative
          cache := {
            published := state.cache
            pending := none
            nextTicket := state.nextTicket } } frame
  | none =>
      guardExactFrameRelease {
        authoritative := state.authoritative
        cache := {
          published := state.cache
          pending := none
          nextTicket := state.nextTicket } } frame

theorem authority_cleanup_pending_blocks_exact_frame_release
    state frame pending
    (hpending : state.pending = some pending)
    (hnames : entriesNameFrame pending.cacheBefore frame = true) :
    guardAuthorityCleanupExactFrameRelease state frame =
      .invalidationPending := by
  simp [guardAuthorityCleanupExactFrameRelease, hpending, hnames]

/-- Only a checked kernel transition that actually removes DMA authority can
open a cleanup ticket.  The caller supplies neither the logical successor nor
the finite invalidation scope set. -/
noncomputable def prepareAuthorityCleanupPublication
    (state : AuthorityCleanupPublicationState)
    (_hstate : state.authoritative.Invariant)
    (operation : FailStop.AuthoritativeOperation) :
    AuthorityCleanupPublicationOutcome :=
  match state.pending with
  | some _ => { state, accepted := false }
  | none =>
      let logicalAfter := applyKernelOperation state.authoritative operation
      let scopes := requiredAuthorityCleanupScopes state.authoritative logicalAfter
      if scopes.isEmpty then { state, accepted := false }
      else
        let pending : PendingAuthorityCleanup := {
          ticket := state.nextTicket
          scopes
          logicalAfter
          cacheBefore := state.cache
          cacheAfter := invalidateScopes state.cache scopes }
        { state := { state with
            pending := some pending
            nextTicket := state.nextTicket + 1 }
          accepted := true }

def acknowledgeAuthorityCleanupPublication
    (state : AuthorityCleanupPublicationState)
    (completion : AuthorityCleanupCompletion) :
    AuthorityCleanupPublicationOutcome :=
  match state.pending with
  | none => { state, accepted := false }
  | some pending =>
      if completion.ticket = pending.ticket ∧
          completion.scopes = pending.scopes ∧
          pending.cacheBefore = state.cache then
        { state := {
            authoritative := pending.logicalAfter
            cache := pending.cacheAfter
            pending := none
            nextTicket := state.nextTicket }
          accepted := true }
      else
        { state, accepted := false }

/-! ## Single authoritative publication front door

The control and kernel-cleanup protocols above share one caller-visible state.
This sum prevents a dispatcher from choosing a direct logical gate or opening
both ticket families concurrently.  The lower-level preparations remain proof
components in this module; production call sites are confined to this front
door by `scripts/check-iotlb-authority-front-door.sh`.
-/

inductive AuthoritativePublicationOperation where
  | control (operation : Operation)
  | cleanup (operation : FailStop.AuthoritativeOperation)

inductive PendingAuthoritativePublication where
  | control (pending : PendingControl)
  | cleanup (pending : PendingAuthorityCleanup)

structure AuthoritativePublicationState where
  authoritative : AuthoritativeExtension
  cache : List Entry
  pending : Option PendingAuthoritativePublication
  nextTicket : Nat

structure AuthoritativePublicationOutcome where
  state : AuthoritativePublicationState
  accepted : Bool

inductive AuthoritativePublicationCompletion where
  | control (completion : Completion)
  | cleanup (completion : AuthorityCleanupCompletion)

/-- The sole preparation boundary serializes IOMMU control mutations and
kernel-authority cleanup behind the same pending-ticket slot. -/
noncomputable def prepareAuthoritativePublication
    (state : AuthoritativePublicationState)
    (hstate : state.authoritative.Invariant)
    (operation : AuthoritativePublicationOperation) :
    AuthoritativePublicationOutcome :=
  match state.pending with
  | some _ => { state, accepted := false }
  | none =>
      match operation with
      | .control operation =>
          let prepared := prepareControlPublication {
            authoritative := state.authoritative
            cache := state.cache
            pending := none
            nextTicket := state.nextTicket } hstate operation
          { state := {
              authoritative := prepared.state.authoritative
              cache := prepared.state.cache
              pending := prepared.state.pending.map
                PendingAuthoritativePublication.control
              nextTicket := prepared.state.nextTicket }
            accepted := prepared.accepted }
      | .cleanup operation =>
          let prepared := prepareAuthorityCleanupPublication {
            authoritative := state.authoritative
            cache := state.cache
            pending := none
            nextTicket := state.nextTicket } hstate operation
          { state := {
              authoritative := prepared.state.authoritative
              cache := prepared.state.cache
              pending := prepared.state.pending.map
                PendingAuthoritativePublication.cleanup
              nextTicket := prepared.state.nextTicket }
            accepted := prepared.accepted }

/-- Only a completion matching the pending family reaches its exact
acknowledgement function; a cross-family or idle completion stutters. -/
def acknowledgeAuthoritativePublication
    (state : AuthoritativePublicationState)
    (completion : AuthoritativePublicationCompletion) :
    AuthoritativePublicationOutcome :=
  match state.pending, completion with
  | some (.control pending), .control completion =>
      let acknowledged := acknowledgeControlPublication {
        authoritative := state.authoritative
        cache := state.cache
        pending := some pending
        nextTicket := state.nextTicket } completion
      { state := {
          authoritative := acknowledged.state.authoritative
          cache := acknowledged.state.cache
          pending := acknowledged.state.pending.map
            PendingAuthoritativePublication.control
          nextTicket := acknowledged.state.nextTicket }
        accepted := acknowledged.accepted }
  | some (.cleanup pending), .cleanup completion =>
      let acknowledged := acknowledgeAuthorityCleanupPublication {
        authoritative := state.authoritative
        cache := state.cache
        pending := some pending
        nextTicket := state.nextTicket } completion
      { state := {
          authoritative := acknowledged.state.authoritative
          cache := acknowledged.state.cache
          pending := acknowledged.state.pending.map
            PendingAuthoritativePublication.cleanup
          nextTicket := acknowledged.state.nextTicket }
        accepted := acknowledged.accepted }
  | _, _ => { state, accepted := false }

/-- A control completion can never acknowledge a pending kernel-cleanup
publication.  The family tag is part of the authoritative completion token,
so even a numerically matching ticket remains inert. -/
theorem authoritative_cleanup_rejects_control_completion
    (state : AuthoritativePublicationState)
    (pending : PendingAuthorityCleanup) (completion : Completion) :
    acknowledgeAuthoritativePublication
        { state with
          pending := some (.cleanup pending) }
        (.control completion) =
      { state := { state with pending := some (.cleanup pending) }
        accepted := false } := by
  rfl

/-- Symmetrically, a cleanup completion cannot be spliced into a pending
IOMMU-control publication. -/
theorem authoritative_control_rejects_cleanup_completion
    (state : AuthoritativePublicationState)
    (pending : PendingControl) (completion : AuthorityCleanupCompletion) :
    acknowledgeAuthoritativePublication
        { state with
          pending := some (.control pending) }
        (.cleanup completion) =
      { state := { state with pending := some (.control pending) }
        accepted := false } := by
  rfl

/-- Every accepted acknowledgement through the shared front door clears its
single pending slot.  Cross-family completions and idle acknowledgements are
rejected by construction, so an accepted result necessarily completed the
exact lower-level control or cleanup protocol. -/
theorem acknowledge_authoritative_publication_accepted_clears_pending
    (state : AuthoritativePublicationState)
    (completion : AuthoritativePublicationCompletion)
    (haccepted :
      (acknowledgeAuthoritativePublication state completion).accepted = true) :
    (acknowledgeAuthoritativePublication state completion).state.pending = none := by
  cases hpending : state.pending with
  | none =>
      cases completion <;>
        simp [acknowledgeAuthoritativePublication, hpending] at haccepted
  | some pending =>
      cases pending <;> cases completion <;>
        simp_all [acknowledgeAuthoritativePublication,
          acknowledgeControlPublication,
          acknowledgeAuthorityCleanupPublication]
      all_goals split <;> simp_all

theorem prepare_authority_cleanup_retains_publications
    state hstate operation :
    let prepared := prepareAuthorityCleanupPublication state hstate operation
    prepared.state.authoritative = state.authoritative ∧
      prepared.state.cache = state.cache := by
  simp only [prepareAuthorityCleanupPublication]
  split
  · simp
  · split <;> simp

/-- Preparation through the single caller-visible front door never publishes
either the authoritative successor or the invalidated cache.  This applies to
all accepted control operations (unmap, attenuation, and teardown) and to
multi-scope kernel cleanup alike; only a matching acknowledgement can change
either published projection. -/
theorem prepare_authoritative_publication_retains_publications
    (state : AuthoritativePublicationState)
    (hstate : state.authoritative.Invariant)
    (operation : AuthoritativePublicationOperation) :
    let prepared := prepareAuthoritativePublication state hstate operation
    prepared.state.authoritative = state.authoritative ∧
      prepared.state.cache = state.cache := by
  cases hpending : state.pending with
  | some pending =>
      simp [prepareAuthoritativePublication, hpending]
  | none =>
      cases operation with
      | control operation =>
          simpa [prepareAuthoritativePublication, hpending] using
            prepare_control_retains_publications
              ({ authoritative := state.authoritative
                 cache := state.cache
                 pending := none
                 nextTicket := state.nextTicket } : ControlPublicationState)
              hstate operation
      | cleanup operation =>
          simpa [prepareAuthoritativePublication, hpending] using
            prepare_authority_cleanup_retains_publications
              ({ authoritative := state.authoritative
                 cache := state.cache
                 pending := none
                 nextTicket := state.nextTicket } : AuthorityCleanupPublicationState)
              hstate operation

theorem prepare_authority_cleanup_accepted_binds_checked_successor
    state hstate operation
    (haccepted :
      (prepareAuthorityCleanupPublication state hstate operation).accepted = true) :
    ∃ pending logicalAfter scopes,
      logicalAfter = applyKernelOperation state.authoritative operation ∧
      scopes = requiredAuthorityCleanupScopes state.authoritative logicalAfter ∧
      scopes.isEmpty = false ∧
      (prepareAuthorityCleanupPublication state hstate operation).state.pending =
        some pending ∧
      pending.ticket = state.nextTicket ∧
      pending.scopes = scopes ∧
      pending.logicalAfter = logicalAfter ∧
      pending.cacheBefore = state.cache ∧
      pending.cacheAfter = invalidateScopes state.cache scopes := by
  simp only [prepareAuthorityCleanupPublication] at haccepted ⊢
  split at haccepted
  · simp_all
  next hpending =>
    split at haccepted
    · simp_all
    next hscopes =>
      simp_all

/-- An accepted checked cleanup cannot expose release, scrub, or a fresh
frame lifetime while its retained pre-cleanup cache still names that exact
old lifetime.  Preparation publishes neither projection; only the exact
multi-scope acknowledgement can clear this guard. -/
theorem prepared_authority_cleanup_blocks_cached_frame_release
    state hstate operation frame
    (hprepared :
      (prepareAuthorityCleanupPublication state hstate operation).accepted = true)
    (hnames : entriesNameFrame state.cache frame = true) :
    guardAuthorityCleanupExactFrameRelease
      (prepareAuthorityCleanupPublication state hstate operation).state frame =
        .invalidationPending := by
  obtain ⟨pending, _logicalAfter, _scopes, _hlogical, _hscopes, _hnonempty,
      hpending, _hticket, _hpendingScopes, _hpendingLogical,
      hcacheBefore, _hcacheAfter⟩ :=
    prepare_authority_cleanup_accepted_binds_checked_successor
      state hstate operation hprepared
  exact authority_cleanup_pending_blocks_exact_frame_release
    (prepareAuthorityCleanupPublication state hstate operation).state frame pending
    hpending (by simpa [hcacheBefore] using hnames)

theorem acknowledge_authority_cleanup_wrong_ticket_inert
    state completion pending
    (hpending : state.pending = some pending)
    (hticket : completion.ticket ≠ pending.ticket) :
    (acknowledgeAuthorityCleanupPublication state completion).accepted = false ∧
      (acknowledgeAuthorityCleanupPublication state completion).state = state := by
  simp [acknowledgeAuthorityCleanupPublication, hpending, hticket]

/-- A completion that reproduces the ticket but omits, adds, or reorders any
internally derived cleanup scope cannot publish the logical successor.  The
entire authoritative/cache/pending state remains unchanged. -/
theorem acknowledge_authority_cleanup_wrong_scopes_inert
    state completion pending
    (hpending : state.pending = some pending)
    (hscopes : completion.scopes ≠ pending.scopes) :
    (acknowledgeAuthorityCleanupPublication state completion).accepted = false ∧
      (acknowledgeAuthorityCleanupPublication state completion).state = state := by
  simp [acknowledgeAuthorityCleanupPublication, hpending, hscopes]

theorem acknowledge_authority_cleanup_accepted_publishes_exact
    state completion
    (haccepted :
      (acknowledgeAuthorityCleanupPublication state completion).accepted = true) :
    ∃ pending,
      state.pending = some pending ∧
      completion.ticket = pending.ticket ∧
      completion.scopes = pending.scopes ∧
      pending.cacheBefore = state.cache ∧
      (acknowledgeAuthorityCleanupPublication state completion).state.authoritative =
        pending.logicalAfter ∧
      (acknowledgeAuthorityCleanupPublication state completion).state.cache =
        pending.cacheAfter ∧
      (acknowledgeAuthorityCleanupPublication state completion).state.pending = none := by
  unfold acknowledgeAuthorityCleanupPublication at haccepted
  split at haccepted
  · simp_all
  next pending hpending =>
    split at haccepted
    next hexact =>
      refine ⟨pending, hpending, hexact.1, hexact.2.1, hexact.2.2, ?_, ?_, ?_⟩ <;>
        simp [acknowledgeAuthorityCleanupPublication, hpending, hexact]
    next => simp_all

/-- Exact multi-scope acknowledgement clears the cleanup-specific lifecycle
gate and returns release decisions to the ordinary authoritative/cache guard.
This does not assert that release is allowed: the ordinary guard still checks
the published logical successor and every remaining cache entry. -/
theorem acknowledge_authority_cleanup_accepted_reaches_exact_frame_guard
    state completion frame
    (haccepted :
      (acknowledgeAuthorityCleanupPublication state completion).accepted = true) :
    guardAuthorityCleanupExactFrameRelease
        (acknowledgeAuthorityCleanupPublication state completion).state frame =
      guardExactFrameRelease {
        authoritative :=
          (acknowledgeAuthorityCleanupPublication state completion).state.authoritative
        cache := {
          published :=
            (acknowledgeAuthorityCleanupPublication state completion).state.cache
          pending := none
          nextTicket :=
            (acknowledgeAuthorityCleanupPublication state completion).state.nextTicket } }
        frame := by
  obtain ⟨_pending, _hpending, _hticket, _hscopes, _hcacheBefore,
      _hauthoritative, _hcache, hcleared⟩ :=
    acknowledge_authority_cleanup_accepted_publishes_exact
      state completion haccepted
  simp [guardAuthorityCleanupExactFrameRelease, hcleared]

/-- After exact acknowledgement, absence from both published authority and
the complete published cache is sufficient for the exact frame lifecycle gate
to allow release.  The hypotheses deliberately cover every entry naming the
frame, not merely one invalidated key. -/
theorem acknowledge_authority_cleanup_allows_exact_frame_release
    state completion frame
    (haccepted :
      (acknowledgeAuthorityCleanupPublication state completion).accepted = true)
    (hmapping : (acknowledgeAuthorityCleanupPublication state completion).state.authoritative.iommu.core.mappings.any
      (·.frame == frame) = false)
    (hcache :
      entriesNameFrame
        (acknowledgeAuthorityCleanupPublication state completion).state.cache
        frame = false) :
    guardAuthorityCleanupExactFrameRelease
        (acknowledgeAuthorityCleanupPublication state completion).state frame =
      .allowed := by
  rw [acknowledge_authority_cleanup_accepted_reaches_exact_frame_guard
    state completion frame haccepted]
  exact exact_frame_release_allowed_only_after_cleanup _ frame rfl hmapping hcache

/-- A subject-termination cleanup cannot acknowledge only part of the stale
DMA authority that the checked successor removed.  For the concrete
`terminateSubject` kernel operation, every key covered by the internally
derived mapping/assignment scope inventory is absent from the cache published
by an accepted exact completion. -/
theorem subject_termination_cleanup_removes_covered_key
    (state : AuthorityCleanupPublicationState)
    (hstate : state.authoritative.Invariant)
    (subject : Nat)
    (completion : AuthorityCleanupCompletion)
    (hprepared :
      (prepareAuthorityCleanupPublication state hstate
        (.ordinary (.terminateSubject subject))).accepted = true)
    (hcompleted :
      (acknowledgeAuthorityCleanupPublication
        (prepareAuthorityCleanupPublication state hstate
          (.ordinary (.terminateSubject subject))).state
        completion).accepted = true)
    (key : Key)
    (hcovered :
      (requiredAuthorityCleanupScopes state.authoritative
        (applyKernelOperation state.authoritative
          (.ordinary (.terminateSubject subject)))).any
        (scopeCoversKey · key) = true) :
    lookup
      (acknowledgeAuthorityCleanupPublication
        (prepareAuthorityCleanupPublication state hstate
          (.ordinary (.terminateSubject subject))).state
        completion).state.cache key = none := by
  obtain ⟨pending, logicalAfter, scopes, hlogical, hscopes, _hnonempty,
      hpending, _hticket, _hpendingScopes, _hpendingLogical,
      _hcacheBefore, hcacheAfter⟩ :=
    prepare_authority_cleanup_accepted_binds_checked_successor
      state hstate (.ordinary (.terminateSubject subject)) hprepared
  obtain ⟨completedPending, hcompletedPending, _hcompletionTicket,
      _hcompletionScopes, _hcompletionCache, _hauthoritative,
      hcache, _hcleared⟩ :=
    acknowledge_authority_cleanup_accepted_publishes_exact
      (prepareAuthorityCleanupPublication state hstate
        (.ordinary (.terminateSubject subject))).state
      completion hcompleted
  have hpendingEq : completedPending = pending := by
    apply Option.some.inj
    exact hcompletedPending.symm.trans hpending
  subst completedPending
  have hcoveredScopes : scopes.any (scopeCoversKey · key) = true := by
    rw [hscopes, hlogical]
    exact hcovered
  rw [hcache, hcacheAfter]
  exact invalidate_scopes_covered_absent state.cache scopes key hcoveredScopes

/-- Subject termination composes the checked kernel successor, covered-key
absence, and the release boundary: exact acknowledgement publishes the
authoritative cleanup, removes every covered stale translation, and returns
frame lifecycle decisions to the ordinary exact-frame guard. -/
theorem subject_termination_cleanup_publishes_release_boundary
    (state : AuthorityCleanupPublicationState)
    (hstate : state.authoritative.Invariant)
    (subject : Nat)
    (completion : AuthorityCleanupCompletion)
    (hprepared :
      (prepareAuthorityCleanupPublication state hstate
        (.ordinary (.terminateSubject subject))).accepted = true)
    (hcompleted :
      (acknowledgeAuthorityCleanupPublication
        (prepareAuthorityCleanupPublication state hstate
          (.ordinary (.terminateSubject subject))).state
        completion).accepted = true)
    (key : Key)
    (hcovered :
      (requiredAuthorityCleanupScopes state.authoritative
        (applyKernelOperation state.authoritative
          (.ordinary (.terminateSubject subject)))).any
        (scopeCoversKey · key) = true)
    (frame : FrameHandle) :
    let acknowledged :=
      (acknowledgeAuthorityCleanupPublication
        (prepareAuthorityCleanupPublication state hstate
          (.ordinary (.terminateSubject subject))).state
        completion).state
    acknowledged.authoritative =
        applyKernelOperation state.authoritative
          (.ordinary (.terminateSubject subject)) ∧
      lookup acknowledged.cache key = none ∧
      guardAuthorityCleanupExactFrameRelease acknowledged frame =
        guardExactFrameRelease {
          authoritative := acknowledged.authoritative
          cache := {
            published := acknowledged.cache
            pending := none
            nextTicket := acknowledged.nextTicket } } frame := by
  dsimp only
  obtain ⟨pending, logicalAfter, _scopes, hlogical, _hscopes, _hnonempty,
      hpending, _hticket, _hpendingScopes, hpendingLogical,
      _hcacheBefore, _hcacheAfter⟩ :=
    prepare_authority_cleanup_accepted_binds_checked_successor
      state hstate (.ordinary (.terminateSubject subject)) hprepared
  obtain ⟨completedPending, hcompletedPending, _hcompletionTicket,
      _hcompletionScopes, _hcompletionCache, hauthoritative,
      _hcache, _hcleared⟩ :=
    acknowledge_authority_cleanup_accepted_publishes_exact
      (prepareAuthorityCleanupPublication state hstate
        (.ordinary (.terminateSubject subject))).state
      completion hcompleted
  have hpendingEq : completedPending = pending := by
    apply Option.some.inj
    exact hcompletedPending.symm.trans hpending
  subst completedPending
  refine ⟨hauthoritative.trans (hpendingLogical.trans hlogical), ?_, ?_⟩
  · exact subject_termination_cleanup_removes_covered_key
      state hstate subject completion hprepared hcompleted key hcovered
  · exact acknowledge_authority_cleanup_accepted_reaches_exact_frame_guard
      (prepareAuthorityCleanupPublication state hstate
        (.ordinary (.terminateSubject subject))).state
      completion frame hcompleted

/-- Exact subject-termination acknowledgement reaches the real memory
release/scrub transition only after the acknowledged authoritative successor
and complete published cache both stop naming the old frame lifetime, and the
subject/slot capability still resolves that exact frame.  This composes the
cleanup publication protocol with the cache-aware authoritative memory gate;
it does not assume a caller-supplied frame is authoritative. -/
theorem acknowledged_subject_termination_resolved_release_delegates
    (state : AuthorityCleanupPublicationState)
    (hstate : state.authoritative.Invariant)
    (owner : Nat)
    (completion : AuthorityCleanupCompletion)
    (hcompleted :
      (acknowledgeAuthorityCleanupPublication
        (prepareAuthorityCleanupPublication state hstate
          (.ordinary (.terminateSubject owner))).state
        completion).accepted = true)
    (frame : FrameHandle)
    (subject : FrameScrub.SubjectId)
    (slot : FrameScrub.SlotId)
    (hmapping :
      (acknowledgeAuthorityCleanupPublication
        (prepareAuthorityCleanupPublication state hstate
          (.ordinary (.terminateSubject owner))).state
        completion).state.authoritative.iommu.core.mappings.any
          (·.frame == frame) = false)
    (hcache :
      entriesNameFrame
        (acknowledgeAuthorityCleanupPublication
          (prepareAuthorityCleanupPublication state hstate
            (.ordinary (.terminateSubject owner))).state
          completion).state.cache frame = false)
    (hresolve :
      resolveReleaseFrame {
        authoritative :=
          (acknowledgeAuthorityCleanupPublication
            (prepareAuthorityCleanupPublication state hstate
              (.ordinary (.terminateSubject owner))).state
            completion).state.authoritative
        cache := {
          published :=
            (acknowledgeAuthorityCleanupPublication
              (prepareAuthorityCleanupPublication state hstate
                (.ordinary (.terminateSubject owner))).state
              completion).state.cache
          pending := none
          nextTicket :=
            (acknowledgeAuthorityCleanupPublication
              (prepareAuthorityCleanupPublication state hstate
                (.ordinary (.terminateSubject owner))).state
              completion).state.nextTicket } }
        subject slot = some frame)
    (hinvariant :
      (acknowledgeAuthorityCleanupPublication
        (prepareAuthorityCleanupPublication state hstate
          (.ordinary (.terminateSubject owner))).state
        completion).state.authoritative.Invariant) :
    let acknowledged :=
      (acknowledgeAuthorityCleanupPublication
        (prepareAuthorityCleanupPublication state hstate
          (.ordinary (.terminateSubject owner))).state
        completion).state
    let releaseState : AuthoritativeCacheState := {
      authoritative := acknowledged.authoritative
      cache := {
        published := acknowledged.cache
        pending := none
        nextTicket := acknowledged.nextTicket } }
    (gatedCachedMemoryByKernel releaseState hinvariant
        (.release subject slot)).state.authoritative =
        (gatedMemoryByKernel releaseState.authoritative hinvariant
          (.release subject slot)).state ∧
      (gatedCachedMemoryByKernel releaseState hinvariant
        (.release subject slot)).state.cache = releaseState.cache := by
  dsimp only
  let prepared :=
    (prepareAuthorityCleanupPublication state hstate
      (.ordinary (.terminateSubject owner))).state
  let acknowledged :=
    (acknowledgeAuthorityCleanupPublication prepared completion).state
  let releaseState : AuthoritativeCacheState := {
    authoritative := acknowledged.authoritative
    cache := {
      published := acknowledged.cache
      pending := none
      nextTicket := acknowledged.nextTicket } }
  have hallowedCleanup :
      guardAuthorityCleanupExactFrameRelease acknowledged frame = .allowed :=
    acknowledge_authority_cleanup_allows_exact_frame_release
      prepared completion frame hcompleted hmapping hcache
  have hallowedExact :
      guardExactFrameRelease releaseState frame = .allowed := by
    rw [acknowledge_authority_cleanup_accepted_reaches_exact_frame_guard
      prepared completion frame hcompleted] at hallowedCleanup
    exact hallowedCleanup
  exact exact_frame_release_allowed_delegates releaseState hinvariant
    subject slot frame hresolve hallowedExact

/-! ## Executable subject-termination cleanup witness

The generic theorem above is deliberately quantified over every coherent
authoritative state.  This finite witness keeps the non-vacuity evidence
executable: one live owner has an assignment, a mapping, and a matching cached
translation to the same frame lifetime.  The exact mapping and assignment
scopes derived from removing those authority records both cover the key, and
their finite cleanup removes it.  This remains model evidence; it does not
claim VT-d, compiler, or QEMU correspondence.
-/

def subjectTerminationWitnessAssignment : Assignment :=
  { handle := ⟨0, 1⟩
    device := 0
    source := 0
    domain := ⟨0, 1⟩
    owner := 2 }

def subjectTerminationWitnessMapping : Mapping :=
  { handle := ⟨0, 1⟩
    assignment := subjectTerminationWitnessAssignment.handle
    domain := subjectTerminationWitnessAssignment.domain
    owner := subjectTerminationWitnessAssignment.owner
    iova := 0
    length := pageSize
    frame := ⟨4, 1⟩
    frameOffset := 0
    permission := readWrite }

def subjectTerminationWitnessKey : Key :=
  { source := subjectTerminationWitnessAssignment.source
    assignment := subjectTerminationWitnessAssignment.handle
    domain := subjectTerminationWitnessAssignment.domain
    mapping := subjectTerminationWitnessMapping.handle
    iova := subjectTerminationWitnessMapping.iova
    direction := .read }

def subjectTerminationWitnessEntry : Entry :=
  { key := subjectTerminationWitnessKey
    frame := subjectTerminationWitnessMapping.frame
    permission := subjectTerminationWitnessMapping.permission }

def subjectTerminationWitnessScopes : List InvalidationScope :=
  [ .mappingSet {
      source := subjectTerminationWitnessAssignment.source
      assignment := subjectTerminationWitnessAssignment.handle
      domain := subjectTerminationWitnessAssignment.domain
      mapping := subjectTerminationWitnessMapping.handle },
    .assignment {
      source := subjectTerminationWitnessAssignment.source
      assignment := subjectTerminationWitnessAssignment.handle
      domain := subjectTerminationWitnessAssignment.domain } ]

/-- A finite exact-completion witness for the cleanup publication protocol.
The authoritative states remain parameters here: the next composition step
will instantiate them with an invariant-bearing checked termination successor.
This witness already fixes the ticket, complete derived scope inventory, and
retained cache pre-state that an acknowledgement must reproduce exactly. -/
def subjectTerminationWitnessPublicationState
    (before after : AuthoritativeExtension) : AuthorityCleanupPublicationState :=
  { authoritative := before
    cache := [subjectTerminationWitnessEntry]
    pending := some {
      ticket := 7
      scopes := subjectTerminationWitnessScopes
      logicalAfter := after
      cacheBefore := [subjectTerminationWitnessEntry]
      cacheAfter := invalidateScopes [subjectTerminationWitnessEntry]
        subjectTerminationWitnessScopes }
    nextTicket := 8 }

def subjectTerminationWitnessCompletion : AuthorityCleanupCompletion :=
  { ticket := 7
    scopes := subjectTerminationWitnessScopes }

/-- A forged partial completion retains the correct ticket but reports only
the mapping invalidation, omitting the assignment-wide cleanup scope. -/
def subjectTerminationWitnessPartialCompletion : AuthorityCleanupCompletion :=
  { ticket := 7
    scopes := [ .mappingSet {
      source := subjectTerminationWitnessAssignment.source
      assignment := subjectTerminationWitnessAssignment.handle
      domain := subjectTerminationWitnessAssignment.domain
      mapping := subjectTerminationWitnessMapping.handle } ] }

/-- The exact finite completion publishes both the supplied checked logical
successor and the fully invalidated cache, and clears the pending ticket. -/
theorem executable_subject_termination_exact_completion_witness
    (before after : AuthoritativeExtension) :
    let acknowledged := acknowledgeAuthorityCleanupPublication
      (subjectTerminationWitnessPublicationState before after)
      subjectTerminationWitnessCompletion
    acknowledged.accepted = true ∧
      acknowledged.state.authoritative = after ∧
      acknowledged.state.cache = invalidateScopes
        [subjectTerminationWitnessEntry] subjectTerminationWitnessScopes ∧
      acknowledged.state.pending = none := by
  simp [subjectTerminationWitnessPublicationState,
    subjectTerminationWitnessCompletion, acknowledgeAuthorityCleanupPublication]

/-- Partial cleanup acknowledgement is fail-closed: neither the checked
termination successor nor the invalidated cache can become visible, and the
complete pending ticket remains available for exact completion. -/
theorem executable_subject_termination_partial_completion_inert
    (before after : AuthoritativeExtension) :
    let state := subjectTerminationWitnessPublicationState before after
    let acknowledged := acknowledgeAuthorityCleanupPublication state
      subjectTerminationWitnessPartialCompletion
    acknowledged.accepted = false ∧ acknowledged.state = state ∧
      acknowledged.state.authoritative = before ∧
      acknowledged.state.cache = [subjectTerminationWitnessEntry] ∧
      acknowledged.state.pending.isSome = true := by
  simp [subjectTerminationWitnessPublicationState,
    subjectTerminationWitnessPartialCompletion,
    subjectTerminationWitnessScopes,
    acknowledgeAuthorityCleanupPublication]

/-- The old mapping and assignment are live, the cache contains their exact
translation, and complete subject cleanup makes that old key unreachable. -/
theorem executable_subject_termination_cleanup_witness :
    [subjectTerminationWitnessAssignment].find?
        (fun assignment => assignment.handle ==
          subjectTerminationWitnessAssignment.handle) =
        some subjectTerminationWitnessAssignment ∧
      [subjectTerminationWitnessMapping].find?
        (fun mapping => mapping.handle == subjectTerminationWitnessMapping.handle) =
        some subjectTerminationWitnessMapping ∧
      lookup [subjectTerminationWitnessEntry] subjectTerminationWitnessKey =
        some subjectTerminationWitnessEntry ∧
      subjectTerminationWitnessScopes.any
        (scopeCoversKey · subjectTerminationWitnessKey) = true ∧
      lookup
        (invalidateScopes [subjectTerminationWitnessEntry]
          subjectTerminationWitnessScopes)
        subjectTerminationWitnessKey = none ∧
      entriesNameFrame
        (invalidateScopes [subjectTerminationWitnessEntry]
          subjectTerminationWitnessScopes)
        subjectTerminationWitnessMapping.frame = false := by
  native_decide

/-! The finite records above now inhabit a real invariant-bearing authoritative
state.  Reuse the repository's canonical subject-2/frame-4 runtime and replace
only its empty device projection with the exact live assignment and mapping.
The next proof slice can therefore calculate `terminateSubject 2` from checked
authority instead of treating the logical successor as a free parameter. -/

def subjectTerminationCheckedCore (plan : BootPageTablePlan.Plan) : Core :=
  { authoritativeSampleCore plan with
    nextAssignmentGeneration := 2
    nextDomainGeneration := 2
    nextMappingGeneration := 2
    assignments := [subjectTerminationWitnessAssignment]
    mappings := [subjectTerminationWitnessMapping] }

def subjectTerminationCheckedIOMMU (plan : BootPageTablePlan.Plan) : State :=
  { core := subjectTerminationCheckedCore plan
    valid := by
      simp [subjectTerminationCheckedCore, authoritativeSampleCore,
        subjectTerminationWitnessAssignment, subjectTerminationWitnessMapping,
        FailStop.compositeDispatcherInitial]
      native_decide
    capabilityWellFormed :=
      (authoritativeSampleIOMMU plan).capabilityWellFormed }

def subjectTerminationCheckedBefore (plan : BootPageTablePlan.Plan) :
    AuthoritativeExtension :=
  { kernel := (authoritativeSample plan).kernel
    iommu := subjectTerminationCheckedIOMMU plan
    scrub := (authoritativeSample plan).scrub }

/-- The concrete live assignment/mapping projection is coherent with the
canonical kernel, capability, frame-binding, and scrub projections. -/
theorem subject_termination_checked_before_invariant
    (plan : BootPageTablePlan.Plan) :
    (subjectTerminationCheckedBefore plan).Invariant := by
  refine
    ⟨(authoritativeSample_invariant plan).1,
      (subjectTerminationCheckedIOMMU plan).invariant, ?_⟩
  refine ⟨rfl, rfl, rfl, rfl,
    authoritativeSampleScrub_invariant plan, ?_⟩
  simp [subjectTerminationCheckedBefore, subjectTerminationCheckedIOMMU,
    subjectTerminationCheckedCore, authoritativeSample,
    authoritativeSampleCore, FailStop.compositeDispatcherInitial,
    subjectTerminationWitnessAssignment, subjectTerminationWitnessMapping,
    pageSize, rangeContained, Permission.attenuates]
  native_decide

/-- The invariant-bearing state contains the exact finite assignment and
mapping, while authoritative subject/slot resolution independently reaches
their shared frame lifetime.  The slot is derived from the kernel capability
projection rather than supplied by the IOMMU witness. -/
theorem executable_subject_termination_checked_authority_witness
    (plan : BootPageTablePlan.Plan) :
    (subjectTerminationCheckedBefore plan).iommu.core.assignments.find?
        (fun assignment => assignment.handle ==
          subjectTerminationWitnessAssignment.handle) =
        some subjectTerminationWitnessAssignment ∧
      (subjectTerminationCheckedBefore plan).iommu.core.mappings.find?
        (fun mapping => mapping.handle ==
          subjectTerminationWitnessMapping.handle) =
        some subjectTerminationWitnessMapping ∧
      resolveReleaseFrame {
        authoritative := subjectTerminationCheckedBefore plan
        cache := {
          published := [subjectTerminationWitnessEntry]
          pending := none
          nextTicket := 7 } }
        2 2 = some subjectTerminationWitnessMapping.frame := by
  simp [subjectTerminationCheckedBefore, subjectTerminationCheckedIOMMU,
    subjectTerminationCheckedCore, resolveReleaseFrame,
    authoritativeSample, authoritativeSampleScrub, authoritativeSampleCore,
    FailStop.compositeDispatcherInitial,
    subjectTerminationWitnessAssignment, subjectTerminationWitnessMapping]
  native_decide

/-- The ordinary checked kernel transition really retires the concrete owner;
the later IOMMU reconciliation proof can use this fact instead of unfolding the
whole composite termination gate again. -/
theorem executable_subject_termination_checked_kernel_removes_owner
    (plan : BootPageTablePlan.Plan) :
    ((FailStop.authoritativeGate
      (subjectTerminationCheckedBefore plan).kernel
      (.ordinary (.terminateSubject 2))).state.capabilities.subjects 2) = false := by
  have hstate :=
    FailStop.compositeDispatcherInitial_authoritativeRuntimeWellFormed plan
  have hmode :
      (FailStop.compositeDispatcherInitial plan).execution.mode = .running := by
    rfl
  let terminated := SubjectLifecycle.terminate
    (FailStop.compositeDispatcherInitial plan).lifecycle 2
  have haccepted : terminated.result = .accepted := by
    simp [terminated, FailStop.compositeDispatcherInitial]
    native_decide
  rcases hterminated : terminated with ⟨lifecycle, result⟩
  have hrecord :
      SubjectLifecycle.terminate
          (FailStop.compositeDispatcherInitial plan).lifecycle 2 =
        { state := lifecycle, result := .accepted } := by
    simpa [terminated, hterminated] using haccepted
  exact (FailStop.terminateSubject_accepted_cleans_runtime_references
    (FailStop.compositeDispatcherInitial plan) 2 lifecycle hstate.1 hmode
    hrecord).2.1

/-- A changed kernel capability projection whose reconciliation candidate
passes the existing capability and finite-core validators cannot retain the
old DMA mapping inventory.  This exposes the exact checked boundary needed by
the concrete termination witness without treating reconciliation as an
unconditional state rewrite. -/
theorem reconcile_kernel_authority_changed_valid_removes_device_authority
    (kernel : FailStop.CompositeState) (state : State)
    (hchanged : kernel.capabilities ≠ state.core.capabilityAuthority)
    (hwell : LeanOS.Capability.WellFormed kernel.capabilities)
    (hvalid :
      validateCore
        { state.core with
          currentOwner := kernel.execution.core.context.currentSubject
          assignments := state.core.assignments.filter
            (fun assignment => kernel.capabilities.subjects assignment.owner)
          mappings := []
          frames := retireDeadOwnerFrames kernel state.core.frames
          capabilityAuthority := kernel.capabilities
          capabilities := [] } = true) :
    let reconciled := reconcileKernelAuthority kernel state
    reconciled.core.assignments = state.core.assignments.filter
        (fun assignment => kernel.capabilities.subjects assignment.owner) ∧
      reconciled.core.mappings = [] := by
  classical
  simp [reconcileKernelAuthority, hchanged, hwell, hvalid]

/-- The canonical checked termination genuinely changes the capability
projection observed by IOMMU reconciliation.  The changed-authority branch is
therefore derived from the authoritative kernel transition, not assumed by a
caller or inferred from the desired empty mapping result. -/
theorem subject_termination_checked_kernel_changes_authority
    (plan : BootPageTablePlan.Plan) :
    (FailStop.authoritativeGate
        (subjectTerminationCheckedBefore plan).kernel
        (.ordinary (.terminateSubject 2))).state.capabilities ≠
      (subjectTerminationCheckedBefore plan).iommu.core.capabilityAuthority := by
  intro hequal
  have hremoved :=
    executable_subject_termination_checked_kernel_removes_owner plan
  have hlive :
      (subjectTerminationCheckedBefore plan).iommu.core.capabilityAuthority.subjects
          2 = true := by
    rfl
  rw [← hequal] at hlive
  rw [hremoved] at hlive
  contradiction

noncomputable def subjectTerminationCheckedKernelAfter
    (plan : BootPageTablePlan.Plan) : FailStop.CompositeState :=
  (FailStop.authoritativeGate
    (subjectTerminationCheckedBefore plan).kernel
    (.ordinary (.terminateSubject 2))).state

/-- The accepted canonical termination retires subject 2 in the kernel memory
capability projection, while the retained scrub projection still names that
subject as live.  Thus the outer coherence gate's memory equality is genuinely
false; finite IOMMU validation is not what causes the complete-state stutter. -/
theorem subject_termination_checked_retained_scrub_memory_ne_kernel
    (plan : BootPageTablePlan.Plan) :
    (subjectTerminationCheckedBefore plan).scrub.memory ≠
      (subjectTerminationCheckedKernelAfter plan).virtualMemory.memory := by
  intro hequal
  have hscrub :
      (subjectTerminationCheckedBefore plan).scrub.memory.capabilities.subjects 2 =
        true := by
    rfl
  have hkernel :
      (subjectTerminationCheckedKernelAfter plan).virtualMemory.memory.capabilities.subjects
          2 = false := by
    have hpost :=
      FailStop.authoritativeGate_preserves_authoritativeRuntimeWellFormed
        (subjectTerminationCheckedBefore plan).kernel
        (.ordinary (.terminateSubject 2))
        (subject_termination_checked_before_invariant plan).1
    have hcoherent := hpost.left.left
    have hcapabilities := hcoherent.2.2.2.1
    have hmemory := hcoherent.2.2.2.2.1
    have hprojection := hmemory.trans hcapabilities.symm
    have hkernelGate :
        (FailStop.authoritativeGate
          (subjectTerminationCheckedBefore plan).kernel
          (.ordinary (.terminateSubject 2))).state.virtualMemory.memory.capabilities.subjects
            2 = false := by
      rw [hprojection]
      simpa using executable_subject_termination_checked_kernel_removes_owner plan
    simpa [subjectTerminationCheckedKernelAfter] using hkernelGate
  rw [hequal] at hscrub
  rw [hkernel] at hscrub
  contradiction

noncomputable def subjectTerminationCheckedReconcileCandidate
    (plan : BootPageTablePlan.Plan) : Core :=
  let kernel := subjectTerminationCheckedKernelAfter plan
  let before := (subjectTerminationCheckedBefore plan).iommu.core
  { before with
    currentOwner := kernel.execution.core.context.currentSubject
    assignments := before.assignments.filter
      (fun assignment => kernel.capabilities.subjects assignment.owner)
    mappings := []
    frames := retireDeadOwnerFrames kernel before.frames
    capabilityAuthority := kernel.capabilities
    capabilities := [] }

/-- The candidate is checked against the capability invariant carried by the
authoritative kernel gate; termination does not manufacture a detached
capability proof for IOMMU reconciliation. -/
theorem subject_termination_checked_candidate_capability_well_formed
    (plan : BootPageTablePlan.Plan) :
    LeanOS.Capability.WellFormed
      (subjectTerminationCheckedKernelAfter plan).capabilities := by
  exact
    (FailStop.authoritativeGate_preserves_authoritativeRuntimeWellFormed
      (subjectTerminationCheckedBefore plan).kernel
      (.ordinary (.terminateSubject 2))
      (subject_termination_checked_before_invariant plan).1).1.2.2.2.1

/-- The concrete post-termination candidate passes the existing finite IOMMU
validator after filtering the dead owner's assignment, removing mappings and
cached capabilities, and retiring its ordinary frame. -/
theorem subject_termination_checked_reconcile_candidate_valid
    (plan : BootPageTablePlan.Plan) :
    validateCore (subjectTerminationCheckedReconcileCandidate plan) = true := by
  have hcurrent :
      (subjectTerminationCheckedKernelAfter plan).execution.core.context.currentSubject =
        2 := by
    rfl
  have hremoved :
      (subjectTerminationCheckedKernelAfter plan).capabilities.subjects 2 = false := by
    simpa [subjectTerminationCheckedKernelAfter] using
      executable_subject_termination_checked_kernel_removes_owner plan
  simp [subjectTerminationCheckedReconcileCandidate, hcurrent, hremoved,
    subjectTerminationCheckedBefore,
    subjectTerminationCheckedIOMMU, subjectTerminationCheckedCore,
    subjectTerminationWitnessAssignment,
    authoritativeSample, authoritativeSampleCore,
    FailStop.compositeDispatcherInitial, retireDeadOwnerFrames, validateCore]
  native_decide

/-- The real reconciliation function accepts the checked termination
candidate and removes both finite device-authority records.  This closes the
previously conditional mapping/assignment premise at the kernel-to-IOMMU
boundary while retaining the validators as the only publication gate. -/
theorem subject_termination_checked_reconcile_removes_device_authority
    (plan : BootPageTablePlan.Plan) :
    let reconciled := reconcileKernelAuthority
      (subjectTerminationCheckedKernelAfter plan)
      (subjectTerminationCheckedBefore plan).iommu
    reconciled.core.assignments = [] ∧ reconciled.core.mappings = [] := by
  have hchanged :
      (subjectTerminationCheckedKernelAfter plan).capabilities ≠
        (subjectTerminationCheckedBefore plan).iommu.core.capabilityAuthority := by
    simpa [subjectTerminationCheckedKernelAfter] using
      subject_termination_checked_kernel_changes_authority plan
  have hvalid :
      validateCore
        { (subjectTerminationCheckedBefore plan).iommu.core with
          currentOwner :=
            (subjectTerminationCheckedKernelAfter plan).execution.core.context.currentSubject
          assignments :=
            (subjectTerminationCheckedBefore plan).iommu.core.assignments.filter
              (fun assignment =>
                (subjectTerminationCheckedKernelAfter plan).capabilities.subjects
                  assignment.owner)
          mappings := []
          frames := retireDeadOwnerFrames
            (subjectTerminationCheckedKernelAfter plan)
            (subjectTerminationCheckedBefore plan).iommu.core.frames
          capabilityAuthority :=
            (subjectTerminationCheckedKernelAfter plan).capabilities
          capabilities := [] } = true := by
    simpa [subjectTerminationCheckedReconcileCandidate] using
      subject_termination_checked_reconcile_candidate_valid plan
  have hreconciled :=
    reconcile_kernel_authority_changed_valid_removes_device_authority
      (subjectTerminationCheckedKernelAfter plan)
      (subjectTerminationCheckedBefore plan).iommu hchanged
      (subject_termination_checked_candidate_capability_well_formed plan)
      hvalid
  have hremoved :
      (subjectTerminationCheckedKernelAfter plan).capabilities.subjects 2 = false := by
    simpa [subjectTerminationCheckedKernelAfter] using
      executable_subject_termination_checked_kernel_removes_owner plan
  simpa [subjectTerminationCheckedBefore, subjectTerminationCheckedIOMMU,
    subjectTerminationCheckedCore, subjectTerminationWitnessAssignment,
    hremoved] using hreconciled

/-- The concrete checked termination publishes exactly the validated finite
reconciliation candidate at the IOMMU boundary.  This keeps the remaining
outer-gate obligation focused on the kernel/scrub memory projection rather
than reopening capability or finite-core validation branches. -/
theorem subject_termination_checked_reconcile_core_eq_candidate
    (plan : BootPageTablePlan.Plan) :
    (reconcileKernelAuthority
      (subjectTerminationCheckedKernelAfter plan)
      (subjectTerminationCheckedBefore plan).iommu).core =
      subjectTerminationCheckedReconcileCandidate plan := by
  classical
  have hchanged :
      (subjectTerminationCheckedKernelAfter plan).capabilities ≠
        (subjectTerminationCheckedBefore plan).iommu.core.capabilityAuthority := by
    simpa [subjectTerminationCheckedKernelAfter] using
      subject_termination_checked_kernel_changes_authority plan
  have hwell :=
    subject_termination_checked_candidate_capability_well_formed plan
  have hvalid := subject_termination_checked_reconcile_candidate_valid plan
  have hvalid' :
      validateCore
        { (subjectTerminationCheckedBefore plan).iommu.core with
          currentOwner :=
            (subjectTerminationCheckedKernelAfter plan).execution.core.context.currentSubject
          assignments :=
            (subjectTerminationCheckedBefore plan).iommu.core.assignments.filter
              (fun assignment =>
                (subjectTerminationCheckedKernelAfter plan).capabilities.subjects
                  assignment.owner)
          mappings := []
          frames := retireDeadOwnerFrames
            (subjectTerminationCheckedKernelAfter plan)
            (subjectTerminationCheckedBefore plan).iommu.core.frames
          capabilityAuthority :=
            (subjectTerminationCheckedKernelAfter plan).capabilities
          capabilities := [] } = true := by
    simpa [subjectTerminationCheckedReconcileCandidate] using hvalid
  simp [reconcileKernelAuthority, hchanged, hwell, hvalid',
    subjectTerminationCheckedReconcileCandidate]

noncomputable def subjectTerminationCheckedAfter
    (plan : BootPageTablePlan.Plan) : AuthoritativeExtension :=
  applyKernelOperation (subjectTerminationCheckedBefore plan)
    (.ordinary (.terminateSubject 2))

/-- The outer gate now reconciles scrub lifecycle authority with the checked
kernel successor before testing complete coherence.  Whether the concrete
termination publishes or stutters, every visible result therefore has one
authoritative memory projection rather than the stale split identified above. -/
theorem subject_termination_checked_apply_scrub_memory_coherent
    (plan : BootPageTablePlan.Plan) :
    (subjectTerminationCheckedAfter plan).scrub.memory =
      (subjectTerminationCheckedAfter plan).kernel.virtualMemory.memory := by
  exact
    (kernel_operation_preserves_authoritative_extension
      (subjectTerminationCheckedBefore plan)
      (.ordinary (.terminateSubject 2))
      (subject_termination_checked_before_invariant plan)).2.2.2.2.1

/-- For the concrete termination witness, scrub coherence after lifecycle
reconciliation reduces exactly to allocator ownership of every retained
binding.  Bytes remain globally zero and every write bit remains false, so no
additional content premise is hidden in the remaining publication proof. -/
theorem subject_termination_checked_reconciled_scrub_invariant_iff
    (plan : BootPageTablePlan.Plan) :
    FrameScrub.ScrubInvariant
      (reconcileScrubMemory
        (subjectTerminationCheckedKernelAfter plan)
        (subjectTerminationCheckedBefore plan).scrub) ↔
      ∀ object frame,
      (subjectTerminationCheckedKernelAfter plan).virtualMemory.memory.binding
          object = some frame →
        FrameAllocator.IsOwnedBy
          (subjectTerminationCheckedKernelAfter plan).virtualMemory.memory.allocator
          frame object := by
  constructor
  · intro hinvariant object frame hbinding
    exact (hinvariant object frame (by simpa [reconcileScrubMemory] using hbinding)
      (by rfl)).1
  · intro howned object frame hbinding _hunwritten
    constructor
    · exact howned object frame (by simpa [reconcileScrubMemory] using hbinding)
    · intro offset _hoffset
      rfl

/-- The authoritative termination gate's lifecycle installation retains only
bindings whose allocator entries still name the same object.  This discharges
the final concrete scrub obligation without assuming ownership independently
of the checked successor. -/
theorem subject_termination_checked_kernel_binding_owned
    (plan : BootPageTablePlan.Plan) :
    ∀ object frame,
      (subjectTerminationCheckedKernelAfter plan).virtualMemory.memory.binding
          object = some frame →
        FrameAllocator.IsOwnedBy
          (subjectTerminationCheckedKernelAfter plan).virtualMemory.memory.allocator
          frame object := by
  simpa [subjectTerminationCheckedKernelAfter, subjectTerminationCheckedBefore,
    authoritativeSample] using
    FailStop.compositeDispatcherTerminateSubjectTwo_binding_owned plan

/-- The checked successor's synchronized lifecycle/allocator fact closes the
concrete scrub invariant after reconciliation. -/
theorem subject_termination_checked_reconciled_scrub_invariant
    (plan : BootPageTablePlan.Plan) :
    FrameScrub.ScrubInvariant
      (reconcileScrubMemory
        (subjectTerminationCheckedKernelAfter plan)
        (subjectTerminationCheckedBefore plan).scrub) := by
  exact
    (subject_termination_checked_reconciled_scrub_invariant_iff plan).2
      (subject_termination_checked_kernel_binding_owned plan)

/-- The concrete checked termination candidate satisfies the complete outer
coherence gate.  Device authority is empty, the kernel and scrub lifecycle
projections agree, and the retired ordinary frame has no remaining live-owner
obligation. -/
theorem subject_termination_checked_reconciled_candidate_coherent
    (plan : BootPageTablePlan.Plan) :
    ({ kernel := subjectTerminationCheckedKernelAfter plan
       iommu := reconcileKernelAuthority
        (subjectTerminationCheckedKernelAfter plan)
        (subjectTerminationCheckedBefore plan).iommu
       scrub := reconcileScrubMemory
        (subjectTerminationCheckedKernelAfter plan)
        (subjectTerminationCheckedBefore plan).scrub } :
      AuthoritativeExtension).Coherent := by
  have hcore := subject_termination_checked_reconcile_core_eq_candidate plan
  have hscrub := subject_termination_checked_reconciled_scrub_invariant plan
  have hremoved :
      (subjectTerminationCheckedKernelAfter plan).capabilities.subjects 2 =
        false := by
    exact executable_subject_termination_checked_kernel_removes_owner plan
  rw [AuthoritativeExtension.Coherent, hcore]
  refine ⟨?_, ?_, ?_, ?_, hscrub, ?_, ?_, ?_, ?_⟩ <;>
    simp [hremoved,
    subjectTerminationCheckedReconcileCandidate,
    subjectTerminationCheckedBefore,
    subjectTerminationCheckedIOMMU, subjectTerminationCheckedCore,
    authoritativeSample, authoritativeSampleCore, authoritativeSampleScrub,
    FailStop.compositeDispatcherInitial, reconcileScrubMemory,
    retireDeadOwnerFrames]

/-- Complete coherence forces the outer atomic gate to publish the checked
kernel/IOMMU/scrub candidate rather than stutter to the pre-termination state. -/
theorem subject_termination_checked_apply_eq_reconciled_candidate
    (plan : BootPageTablePlan.Plan) :
    subjectTerminationCheckedAfter plan =
      { kernel := subjectTerminationCheckedKernelAfter plan
        iommu := reconcileKernelAuthority
          (subjectTerminationCheckedKernelAfter plan)
          (subjectTerminationCheckedBefore plan).iommu
        scrub := reconcileScrubMemory
          (subjectTerminationCheckedKernelAfter plan)
          (subjectTerminationCheckedBefore plan).scrub } := by
  classical
  simp only [subjectTerminationCheckedAfter, applyKernelOperation]
  split
  · rfl
  · next hnot =>
      exfalso
      apply hnot
      simpa only [subjectTerminationCheckedKernelAfter] using
        subject_termination_checked_reconciled_candidate_coherent plan

/-- The real checked outer transition now publishes the finite reconciliation:
the terminated owner's assignment and mapping inventories are both empty. -/
theorem subject_termination_checked_apply_removes_device_authority
    (plan : BootPageTablePlan.Plan) :
    (subjectTerminationCheckedAfter plan).iommu.core.assignments = [] ∧
      (subjectTerminationCheckedAfter plan).iommu.core.mappings = [] := by
  rw [subject_termination_checked_apply_eq_reconciled_candidate plan]
  exact subject_termination_checked_reconcile_removes_device_authority plan

/-- The checked outer operation has exactly the two branches exposed by the
coherence gate: it either stutters to the complete pre-state, or publishes the
validated reconciliation whose assignment and mapping inventories are empty.
The remaining composition obligation is therefore precisely to rule out the
stutter branch by proving the concrete candidate coherent. -/
theorem subject_termination_checked_apply_stutters_or_removes_device_authority
    (plan : BootPageTablePlan.Plan) :
    subjectTerminationCheckedAfter plan = subjectTerminationCheckedBefore plan ∨
      ((subjectTerminationCheckedAfter plan).iommu.core.assignments = [] ∧
        (subjectTerminationCheckedAfter plan).iommu.core.mappings = []) := by
  classical
  simp only [subjectTerminationCheckedAfter, applyKernelOperation]
  split
  · right
    simpa [subjectTerminationCheckedKernelAfter] using
      subject_termination_checked_reconcile_removes_device_authority plan
  · exact Or.inl rfl

/-- Once the checked successor has removed the concrete mapping and
assignment, the internally derived cleanup inventory is exactly the finite
witness inventory; neither scope is supplied by the caller. -/
theorem subject_termination_checked_removed_authority_scopes
    (plan : BootPageTablePlan.Plan) (after : AuthoritativeExtension)
    (hmappings : after.iommu.core.mappings = [])
    (hassignments : after.iommu.core.assignments = []) :
    requiredAuthorityCleanupScopes
      (subjectTerminationCheckedBefore plan) after =
    subjectTerminationWitnessScopes := by
  simp [requiredAuthorityCleanupScopes, subjectTerminationCheckedBefore,
    subjectTerminationCheckedIOMMU, subjectTerminationCheckedCore,
    hmappings, hassignments, mappingScopeFor, assignmentScopeFor,
    findMapping, findAssignment,
    subjectTerminationWitnessScopes, subjectTerminationWitnessAssignment,
    subjectTerminationWitnessMapping]
  native_decide

/-! ## Checked end-to-end cleanup publication

The finite checked termination now drives the real publication protocol from
an idle state.  These witnesses close the gap between proving the logical
successor and showing that the internally derived invalidation ticket can be
prepared and acknowledged without any caller-supplied successor or scope.
-/

noncomputable def subjectTerminationCheckedPublicationState
    (plan : BootPageTablePlan.Plan) : AuthorityCleanupPublicationState :=
  { authoritative := subjectTerminationCheckedBefore plan
    cache := [subjectTerminationWitnessEntry]
    pending := none
    nextTicket := 7 }

/-- The real checked termination opens a fresh cleanup ticket.  Its nonempty
scope inventory is derived from the removed mapping and assignment rather than
being supplied by the completion witness. -/
theorem subject_termination_checked_prepare_accepted
    (plan : BootPageTablePlan.Plan) :
    (prepareAuthorityCleanupPublication
      (subjectTerminationCheckedPublicationState plan)
      (subject_termination_checked_before_invariant plan)
      (.ordinary (.terminateSubject 2))).accepted = true := by
  have hremoved := subject_termination_checked_apply_removes_device_authority plan
  have hscopes := subject_termination_checked_removed_authority_scopes plan
    (subjectTerminationCheckedAfter plan) hremoved.2 hremoved.1
  simp only [prepareAuthorityCleanupPublication,
    subjectTerminationCheckedPublicationState]
  rw [show applyKernelOperation (subjectTerminationCheckedBefore plan)
      (.ordinary (.terminateSubject 2)) =
        subjectTerminationCheckedAfter plan by rfl]
  rw [hscopes]
  rfl

/-- Exact acknowledgement publishes the checked termination successor, clears
the stale cache and ticket, and reaches an allowed exact-frame lifecycle gate.
This is model evidence for the complete logical ordering through release; it
does not claim VT-d or QEMU correspondence. -/
theorem subject_termination_checked_acknowledges_exact_cleanup
    (plan : BootPageTablePlan.Plan) :
    let prepared := prepareAuthorityCleanupPublication
      (subjectTerminationCheckedPublicationState plan)
      (subject_termination_checked_before_invariant plan)
      (.ordinary (.terminateSubject 2))
    let acknowledged := acknowledgeAuthorityCleanupPublication prepared.state
      subjectTerminationWitnessCompletion
    acknowledged.accepted = true ∧
      acknowledged.state.authoritative = subjectTerminationCheckedAfter plan ∧
      acknowledged.state.cache = [] ∧
      acknowledged.state.pending = none := by
  have hremoved := subject_termination_checked_apply_removes_device_authority plan
  have hscopes := subject_termination_checked_removed_authority_scopes plan
    (subjectTerminationCheckedAfter plan) hremoved.2 hremoved.1
  simp only [prepareAuthorityCleanupPublication,
    subjectTerminationCheckedPublicationState]
  rw [show applyKernelOperation (subjectTerminationCheckedBefore plan)
      (.ordinary (.terminateSubject 2)) =
        subjectTerminationCheckedAfter plan by rfl]
  rw [hscopes]
  simp [subjectTerminationWitnessCompletion,
    acknowledgeAuthorityCleanupPublication,
    subjectTerminationWitnessScopes, subjectTerminationWitnessEntry,
    subjectTerminationWitnessKey, subjectTerminationWitnessMapping,
    subjectTerminationWitnessAssignment,
    invalidateScopes, scopeCoversKey]
  all_goals native_decide

/-! ## Checked cleanup through the authoritative front door

The same executable termination witness now enters through the caller-visible
sum rather than the lower-level cleanup helper.  This makes the family tag and
the shared pending slot part of the checked sequence used by later hosted
evidence.
-/

noncomputable def subjectTerminationCheckedAuthoritativePublicationState
    (plan : BootPageTablePlan.Plan) : AuthoritativePublicationState :=
  { authoritative := subjectTerminationCheckedBefore plan
    cache := [subjectTerminationWitnessEntry]
    pending := none
    nextTicket := 7 }

/-- Preparation through the single front door accepts the checked subject
termination and opens the cleanup-family ticket. -/
theorem subject_termination_checked_authoritative_prepare_accepted
    (plan : BootPageTablePlan.Plan) :
    (prepareAuthoritativePublication
      (subjectTerminationCheckedAuthoritativePublicationState plan)
      (subject_termination_checked_before_invariant plan)
      (.cleanup (.ordinary (.terminateSubject 2)))).accepted = true := by
  simpa [prepareAuthoritativePublication,
    subjectTerminationCheckedAuthoritativePublicationState,
    subjectTerminationCheckedPublicationState] using
    subject_termination_checked_prepare_accepted plan

/-- Exact cleanup acknowledgement through the caller-visible front door
publishes the checked termination successor and clears both the stale
translation and the shared pending slot. -/
theorem subject_termination_checked_authoritative_acknowledges_exact_cleanup
    (plan : BootPageTablePlan.Plan) :
    let prepared := prepareAuthoritativePublication
      (subjectTerminationCheckedAuthoritativePublicationState plan)
      (subject_termination_checked_before_invariant plan)
      (.cleanup (.ordinary (.terminateSubject 2)))
    let acknowledged := acknowledgeAuthoritativePublication prepared.state
      (.cleanup subjectTerminationWitnessCompletion)
    acknowledged.accepted = true ∧
      acknowledged.state.authoritative = subjectTerminationCheckedAfter plan ∧
      acknowledged.state.cache = [] ∧
      acknowledged.state.pending = none := by
  have hremoved := subject_termination_checked_apply_removes_device_authority plan
  have hscopes := subject_termination_checked_removed_authority_scopes plan
    (subjectTerminationCheckedAfter plan) hremoved.2 hremoved.1
  simp only [prepareAuthoritativePublication,
    prepareAuthorityCleanupPublication,
    subjectTerminationCheckedAuthoritativePublicationState]
  rw [show applyKernelOperation (subjectTerminationCheckedBefore plan)
      (.ordinary (.terminateSubject 2)) =
        subjectTerminationCheckedAfter plan by rfl]
  rw [hscopes]
  simp [acknowledgeAuthoritativePublication,
    acknowledgeAuthorityCleanupPublication,
    subjectTerminationWitnessCompletion,
    subjectTerminationWitnessScopes, subjectTerminationWitnessEntry,
    subjectTerminationWitnessKey, subjectTerminationWitnessMapping,
    subjectTerminationWitnessAssignment,
    invalidateScopes, scopeCoversKey]
  all_goals native_decide

/-- Preparation of the canonical subject-2 cleanup keeps every old authority
projection published until the exact completion arrives.  In particular, the
subject remains live, its DMA mapping remains authoritative, and the stale
translation remains observable while the internally derived cleanup ticket is
pending. -/
theorem subject_termination_checked_authoritative_prepare_retains_old_authority
    (plan : BootPageTablePlan.Plan) :
    let prepared := prepareAuthoritativePublication
      (subjectTerminationCheckedAuthoritativePublicationState plan)
      (subject_termination_checked_before_invariant plan)
      (.cleanup (.ordinary (.terminateSubject 2)))
    prepared.state.authoritative.kernel.capabilities.subjects 2 = true ∧
      prepared.state.authoritative.iommu.core.mappings =
        [subjectTerminationWitnessMapping] ∧
      lookup prepared.state.cache subjectTerminationWitnessKey =
        some subjectTerminationWitnessEntry ∧
      prepared.state.pending.isSome = true := by
  have hremoved := subject_termination_checked_apply_removes_device_authority plan
  have hscopes := subject_termination_checked_removed_authority_scopes plan
    (subjectTerminationCheckedAfter plan) hremoved.2 hremoved.1
  simp only [prepareAuthoritativePublication,
    prepareAuthorityCleanupPublication,
    subjectTerminationCheckedAuthoritativePublicationState]
  rw [show applyKernelOperation (subjectTerminationCheckedBefore plan)
      (.ordinary (.terminateSubject 2)) =
        subjectTerminationCheckedAfter plan by rfl]
  rw [hscopes]
  simp [subjectTerminationCheckedBefore, subjectTerminationCheckedIOMMU,
    subjectTerminationCheckedCore, authoritativeSample,
    FailStop.compositeDispatcherInitial, subjectTerminationWitnessScopes,
    subjectTerminationWitnessEntry, subjectTerminationWitnessKey,
    subjectTerminationWitnessMapping]
  exact executable_subject_termination_cleanup_witness.2.2.1

/-- Exact completion of that same pending ticket publishes all three coupled
facts together: the old subject is retired, its mapping inventory is empty,
and the old translation key is absent. -/
theorem subject_termination_checked_authoritative_exact_completion_removes_old_authority
    (plan : BootPageTablePlan.Plan) :
    let prepared := prepareAuthoritativePublication
      (subjectTerminationCheckedAuthoritativePublicationState plan)
      (subject_termination_checked_before_invariant plan)
      (.cleanup (.ordinary (.terminateSubject 2)))
    let acknowledged := acknowledgeAuthoritativePublication prepared.state
      (.cleanup subjectTerminationWitnessCompletion)
    acknowledged.accepted = true ∧
      acknowledged.state.authoritative.kernel.capabilities.subjects 2 = false ∧
      acknowledged.state.authoritative.iommu.core.mappings = [] ∧
      lookup acknowledged.state.cache subjectTerminationWitnessKey = none ∧
      acknowledged.state.pending = none := by
  have hexact :=
    subject_termination_checked_authoritative_acknowledges_exact_cleanup plan
  simp only at hexact ⊢
  rcases hexact with ⟨haccepted, hauthoritative, hcache, hpending⟩
  have hremoved := subject_termination_checked_apply_removes_device_authority plan
  refine ⟨haccepted, ?_, ?_, ?_, hpending⟩
  · rw [hauthoritative,
      subject_termination_checked_apply_eq_reconciled_candidate]
    exact
      executable_subject_termination_checked_kernel_removes_owner plan
  · simpa [hauthoritative] using hremoved.2
  · simp [hcache, lookup]

/-- A completion that names only the mapping scope cannot splice a partial
cleanup into the canonical front door.  The entire prepared state, including
the old authority and stale cache, remains byte-for-byte pending. -/
theorem subject_termination_checked_authoritative_partial_completion_stutters
    (plan : BootPageTablePlan.Plan) :
    let prepared := prepareAuthoritativePublication
      (subjectTerminationCheckedAuthoritativePublicationState plan)
      (subject_termination_checked_before_invariant plan)
      (.cleanup (.ordinary (.terminateSubject 2)))
    let acknowledged := acknowledgeAuthoritativePublication prepared.state
      (.cleanup subjectTerminationWitnessPartialCompletion)
    acknowledged.accepted = false ∧ acknowledged.state = prepared.state := by
  have hremoved := subject_termination_checked_apply_removes_device_authority plan
  have hscopes := subject_termination_checked_removed_authority_scopes plan
    (subjectTerminationCheckedAfter plan) hremoved.2 hremoved.1
  simp only [prepareAuthoritativePublication,
    prepareAuthorityCleanupPublication,
    subjectTerminationCheckedAuthoritativePublicationState]
  rw [show applyKernelOperation (subjectTerminationCheckedBefore plan)
      (.ordinary (.terminateSubject 2)) =
        subjectTerminationCheckedAfter plan by rfl]
  rw [hscopes]
  simp [acknowledgeAuthoritativePublication,
    acknowledgeAuthorityCleanupPublication,
    subjectTerminationWitnessPartialCompletion,
    subjectTerminationWitnessScopes]

/-! ## Finite control-operation publication witnesses

The same invariant-bearing assignment/mapping/cache fixture also exercises
each caller-visible control operation.  These witnesses bind the completion
to the internally derived mapping or assignment scope and show that exact
acknowledgement both publishes the checked logical successor and removes the
covered old translation.
-/

def controlCheckedMappingScope : InvalidationScope :=
  .mappingSet {
    source := subjectTerminationWitnessAssignment.source
    assignment := subjectTerminationWitnessAssignment.handle
    domain := subjectTerminationWitnessAssignment.domain
    mapping := subjectTerminationWitnessMapping.handle }

def controlCheckedAssignmentScope : InvalidationScope :=
  .assignment {
    source := subjectTerminationWitnessAssignment.source
    assignment := subjectTerminationWitnessAssignment.handle
    domain := subjectTerminationWitnessAssignment.domain }

def controlCheckedCompletion (scope : InvalidationScope) :
    AuthoritativePublicationCompletion :=
  .control { ticket := 11, scope }

def controlCheckedPendingState (before after : AuthoritativeExtension)
    (scope : InvalidationScope) (reply : AcceptedReply) :
    AuthoritativePublicationState :=
  { authoritative := before
    cache := [subjectTerminationWitnessEntry]
    pending := some (.control {
      ticket := 11
      scope
      logicalAfter := after
      cacheBefore := [subjectTerminationWitnessEntry]
      cacheAfter := invalidate [subjectTerminationWitnessEntry] scope
      reply })
    nextTicket := 12 }

theorem executable_control_unmap_exact_completion_witness
    (before after : AuthoritativeExtension) :
    let acknowledged := acknowledgeAuthoritativePublication
      (controlCheckedPendingState before after controlCheckedMappingScope
        .unmapped)
      (controlCheckedCompletion controlCheckedMappingScope)
    acknowledged.accepted = true ∧
      acknowledged.state.authoritative = after ∧
      lookup acknowledged.state.cache subjectTerminationWitnessKey = none ∧
      acknowledged.state.pending = none := by
  simp [controlCheckedPendingState, controlCheckedCompletion,
    controlCheckedMappingScope, acknowledgeAuthoritativePublication,
    acknowledgeControlPublication, invalidate, eraseMappingScope, lookup,
    subjectTerminationWitnessEntry, subjectTerminationWitnessKey,
    subjectTerminationWitnessAssignment, subjectTerminationWitnessMapping]

theorem executable_control_attenuation_exact_completion_witness
    (before after : AuthoritativeExtension) :
    let acknowledged := acknowledgeAuthoritativePublication
      (controlCheckedPendingState before after controlCheckedMappingScope
        (.attenuated subjectTerminationWitnessMapping.handle))
      (controlCheckedCompletion controlCheckedMappingScope)
    acknowledged.accepted = true ∧
      acknowledged.state.authoritative = after ∧
      lookup acknowledged.state.cache subjectTerminationWitnessKey = none ∧
      acknowledged.state.pending = none := by
  simp [controlCheckedPendingState, controlCheckedCompletion,
    controlCheckedMappingScope, acknowledgeAuthoritativePublication,
    acknowledgeControlPublication, invalidate, eraseMappingScope, lookup,
    subjectTerminationWitnessEntry, subjectTerminationWitnessKey,
    subjectTerminationWitnessAssignment, subjectTerminationWitnessMapping]

theorem executable_control_teardown_exact_completion_witness
    (before after : AuthoritativeExtension) :
    let acknowledged := acknowledgeAuthoritativePublication
      (controlCheckedPendingState before after controlCheckedAssignmentScope
        .tornDown)
      (controlCheckedCompletion controlCheckedAssignmentScope)
    acknowledged.accepted = true ∧
      acknowledged.state.authoritative = after ∧
      lookup acknowledged.state.cache subjectTerminationWitnessKey = none ∧
      acknowledged.state.pending = none := by
  simp [controlCheckedPendingState, controlCheckedCompletion,
    controlCheckedAssignmentScope, acknowledgeAuthoritativePublication,
    acknowledgeControlPublication, invalidate, eraseAssignmentScope, lookup,
    subjectTerminationWitnessEntry, subjectTerminationWitnessKey,
    subjectTerminationWitnessAssignment, subjectTerminationWitnessMapping]

/-! ## Checked control publication through the authoritative front door

The finite completions above are now connected to preparation from the same
invariant-bearing authoritative state used by the subject-termination witness.
No logical successor or invalidation scope is supplied by these sequences:
both come from the checked control operation and its published pre-state.
-/

noncomputable def controlCheckedAuthoritativePublicationState
    (plan : BootPageTablePlan.Plan) : AuthoritativePublicationState :=
  { authoritative := subjectTerminationCheckedBefore plan
    cache := [subjectTerminationWitnessEntry]
    pending := none
    nextTicket := 11 }

def controlCheckedAttenuation : AttenuateRequest :=
  { mapping := subjectTerminationWitnessMapping.handle
    offset := 0
    length := pageSize
    permission := readOnly }

/-- The invariant-bearing fixture determines the complete mapping-lifetime
scope before the checked gate runs; no caller-supplied scope participates in
the remaining acceptance proof. -/
theorem checked_control_unmap_requires_exact_scope
    (plan : BootPageTablePlan.Plan) :
    requiredControlScope (subjectTerminationCheckedBefore plan)
      (.unmap subjectTerminationWitnessMapping.handle) =
        some controlCheckedMappingScope := by
  simp [requiredControlScope, mappingScopeFor, findMapping, findAssignment,
    controlCheckedMappingScope, subjectTerminationCheckedBefore,
    subjectTerminationCheckedIOMMU, subjectTerminationCheckedCore,
    subjectTerminationWitnessAssignment, subjectTerminationWitnessMapping]
  native_decide

def controlCheckedUnmappedIOMMU (plan : BootPageTablePlan.Plan) : State :=
  { core := { subjectTerminationCheckedCore plan with mappings := [] }
    valid := by
      simp [subjectTerminationCheckedCore, authoritativeSampleCore,
        subjectTerminationWitnessAssignment,
        FailStop.compositeDispatcherInitial]
      native_decide
    capabilityWellFormed :=
      (subjectTerminationCheckedIOMMU plan).capabilityWellFormed }

theorem checked_control_unmap_gate
    (plan : BootPageTablePlan.Plan) :
    gate (subjectTerminationCheckedIOMMU plan)
        (.unmap subjectTerminationWitnessMapping.handle) =
      .accepted (controlCheckedUnmappedIOMMU plan) .unmapped := by
  rfl

theorem checked_control_unmap_candidate_coherent
    (plan : BootPageTablePlan.Plan) :
    ({ kernel := (subjectTerminationCheckedBefore plan).kernel
       iommu := controlCheckedUnmappedIOMMU plan
       scrub := (subjectTerminationCheckedBefore plan).scrub } :
      AuthoritativeExtension).Coherent := by
  refine ⟨rfl, rfl, rfl, rfl,
    authoritativeSampleScrub_invariant plan, ?_⟩
  simp [controlCheckedUnmappedIOMMU, subjectTerminationCheckedBefore,
    subjectTerminationCheckedCore, authoritativeSample,
    authoritativeSampleCore, FailStop.compositeDispatcherInitial,
    subjectTerminationWitnessAssignment]
  native_decide

theorem checked_control_unmap_gated_accepts
    (plan : BootPageTablePlan.Plan) :
    (gatedByKernel (subjectTerminationCheckedBefore plan)
      (subject_termination_checked_before_invariant plan)
      (.unmap subjectTerminationWitnessMapping.handle)).isAccepted = true := by
  unfold gatedByKernel
  rw [show (subjectTerminationCheckedBefore plan).kernel.execution.mode =
      .running by rfl]
  simp only
  rw [show gate (subjectTerminationCheckedBefore plan).iommu
        (.unmap subjectTerminationWitnessMapping.handle) =
      .accepted (controlCheckedUnmappedIOMMU plan) .unmapped by
    simpa [subjectTerminationCheckedBefore] using
      checked_control_unmap_gate plan]
  simp [checked_control_unmap_candidate_coherent plan,
    AuthoritativeOutcome.isAccepted]

/-- The concrete invariant-bearing fixture takes the checked unmap branch of
the sole authoritative publication front door.  The caller supplies only the
mapping handle: validation derives both the logical successor and the exact
mapping-lifetime invalidation scope. -/
theorem checked_control_unmap_authoritative_prepare_accepts
    (plan : BootPageTablePlan.Plan) :
    (prepareAuthoritativePublication
      (controlCheckedAuthoritativePublicationState plan)
      (subject_termination_checked_before_invariant plan)
      (.control (.unmap subjectTerminationWitnessMapping.handle))).accepted =
        true := by
  simp only [prepareAuthoritativePublication,
    controlCheckedAuthoritativePublicationState, prepareControlPublication]
  rw [checked_control_unmap_requires_exact_scope plan]
  have haccepted := checked_control_unmap_gated_accepts plan
  cases hgate : gatedByKernel (subjectTerminationCheckedBefore plan)
      (subject_termination_checked_before_invariant plan)
      (.unmap subjectTerminationWitnessMapping.handle) with
  | rejected reason =>
      simp [hgate, AuthoritativeOutcome.isAccepted] at haccepted
  | accepted after invariant reply => rfl

/-- Any accepted checked unmap preparation through the caller-visible front
door binds ticket 11 to the internally derived complete mapping-lifetime
scope and the retained old cache.  The concrete fixture above separately
discharges this acceptance premise. -/
theorem checked_control_unmap_authoritative_prepare_binds_exact_scope
    (plan : BootPageTablePlan.Plan)
    (haccepted :
      (prepareAuthoritativePublication
        (controlCheckedAuthoritativePublicationState plan)
        (subject_termination_checked_before_invariant plan)
        (.control (.unmap subjectTerminationWitnessMapping.handle))).accepted =
        true) :
    ∃ pending,
      (prepareAuthoritativePublication
        (controlCheckedAuthoritativePublicationState plan)
        (subject_termination_checked_before_invariant plan)
        (.control (.unmap subjectTerminationWitnessMapping.handle))).state.pending =
          some (.control pending) ∧
      pending.ticket = 11 ∧
      pending.scope = controlCheckedMappingScope ∧
      pending.cacheBefore = [subjectTerminationWitnessEntry] ∧
      pending.cacheAfter =
        invalidate [subjectTerminationWitnessEntry] controlCheckedMappingScope := by
  let lower : ControlPublicationState :=
    { authoritative := subjectTerminationCheckedBefore plan
      cache := [subjectTerminationWitnessEntry]
      pending := none
      nextTicket := 11 }
  have hlower :
      (prepareControlPublication lower
        (subject_termination_checked_before_invariant plan)
        (.unmap subjectTerminationWitnessMapping.handle)).accepted = true := by
    simpa [prepareAuthoritativePublication,
      controlCheckedAuthoritativePublicationState, lower] using haccepted
  obtain ⟨pending, scope, logicalAfter, hinvariant, reply, hscope, _hgate,
      hpending, hticket, hpscope, _hafter, hbefore, hcache⟩ :=
    prepare_control_accepted_binds_exact_successor lower
      (subject_termination_checked_before_invariant plan)
      (.unmap subjectTerminationWitnessMapping.handle) hlower
  have hrequired :
      requiredControlScope (subjectTerminationCheckedBefore plan)
        (.unmap subjectTerminationWitnessMapping.handle) =
        some controlCheckedMappingScope :=
    checked_control_unmap_requires_exact_scope plan
  have hscopeExact : scope = controlCheckedMappingScope := by
    rw [hrequired] at hscope
    exact (Option.some.inj hscope).symm
  refine ⟨pending, ?_, ?_, hpscope.trans hscopeExact, ?_, ?_⟩
  · simp [prepareAuthoritativePublication,
      controlCheckedAuthoritativePublicationState, lower, hpending]
  · simpa [lower] using hticket
  · simpa [lower] using hbefore
  · simpa [lower, hscopeExact] using hcache

/-- The checked unmap witness reaches exact completion through the same
caller-visible front door: acknowledgement publishes the mapping-free
authoritative successor, removes the old translation, and closes the shared
pending slot. -/
theorem checked_control_unmap_authoritative_acknowledges_exact
    (plan : BootPageTablePlan.Plan) :
    let prepared := prepareAuthoritativePublication
      (controlCheckedAuthoritativePublicationState plan)
      (subject_termination_checked_before_invariant plan)
      (.control (.unmap subjectTerminationWitnessMapping.handle))
    let acknowledged := acknowledgeAuthoritativePublication prepared.state
      (controlCheckedCompletion controlCheckedMappingScope)
    acknowledged.accepted = true ∧
      acknowledged.state.authoritative =
        { kernel := (subjectTerminationCheckedBefore plan).kernel
          iommu := controlCheckedUnmappedIOMMU plan
          scrub := (subjectTerminationCheckedBefore plan).scrub } ∧
      lookup acknowledged.state.cache subjectTerminationWitnessKey = none ∧
      acknowledged.state.pending = none := by
  simp only [prepareAuthoritativePublication,
    controlCheckedAuthoritativePublicationState, prepareControlPublication]
  rw [checked_control_unmap_requires_exact_scope plan]
  have haccepted := checked_control_unmap_gated_accepts plan
  cases hgate : gatedByKernel (subjectTerminationCheckedBefore plan)
      (subject_termination_checked_before_invariant plan)
      (.unmap subjectTerminationWitnessMapping.handle) with
  | rejected reason =>
      simp [hgate, AuthoritativeOutcome.isAccepted] at haccepted
  | accepted after hinvariant reply =>
      have hexact :
          after =
              { kernel := (subjectTerminationCheckedBefore plan).kernel
                iommu := controlCheckedUnmappedIOMMU plan
                scrub := (subjectTerminationCheckedBefore plan).scrub } ∧
            reply = .unmapped := by
        unfold gatedByKernel at hgate
        rw [show (subjectTerminationCheckedBefore plan).kernel.execution.mode =
            .running by rfl] at hgate
        simp only at hgate
        rw [show gate (subjectTerminationCheckedBefore plan).iommu
            (.unmap subjectTerminationWitnessMapping.handle) =
              .accepted (controlCheckedUnmappedIOMMU plan) .unmapped by
          simpa [subjectTerminationCheckedBefore] using
            checked_control_unmap_gate plan] at hgate
        simp only at hgate
        rw [dif_pos (checked_control_unmap_candidate_coherent plan)] at hgate
        cases hgate
        exact ⟨rfl, rfl⟩
      rcases hexact with ⟨rfl, rfl⟩
      simp [acknowledgeAuthoritativePublication, acknowledgeControlPublication,
        controlCheckedCompletion, controlCheckedMappingScope, invalidate,
        eraseMappingScope, lookup, subjectTerminationWitnessEntry,
        subjectTerminationWitnessKey, subjectTerminationWitnessAssignment,
        subjectTerminationWitnessMapping]

/-! ## Checked permission attenuation through the authoritative front door

The same invariant-bearing fixture now reduces the live mapping from
read-write to read-only.  Exact acknowledgement must publish that checked
successor and remove the old cache entry before the reduced authority becomes
visible.
-/

def controlCheckedAttenuatedMapping : Mapping :=
  { subjectTerminationWitnessMapping with permission := readOnly }

def controlCheckedAttenuatedIOMMU (plan : BootPageTablePlan.Plan) : State :=
  { core := { subjectTerminationCheckedCore plan with
      mappings := [controlCheckedAttenuatedMapping] }
    valid := by
      simp [subjectTerminationCheckedCore, authoritativeSampleCore,
        controlCheckedAttenuatedMapping, subjectTerminationWitnessAssignment,
        subjectTerminationWitnessMapping,
        FailStop.compositeDispatcherInitial]
      native_decide
    capabilityWellFormed :=
      (subjectTerminationCheckedIOMMU plan).capabilityWellFormed }

/-- Permission reduction derives the same complete mapping-lifetime scope as
unmap; the caller supplies only the checked mapping handle and reduced range.
-/
theorem checked_control_attenuation_requires_exact_scope
    (plan : BootPageTablePlan.Plan) :
    requiredControlScope (subjectTerminationCheckedBefore plan)
      (.attenuate controlCheckedAttenuation) =
        some controlCheckedMappingScope := by
  simp [requiredControlScope, mappingScopeFor, findMapping, findAssignment,
    controlCheckedAttenuation, controlCheckedMappingScope,
    subjectTerminationCheckedBefore, subjectTerminationCheckedIOMMU,
    subjectTerminationCheckedCore, subjectTerminationWitnessAssignment,
    subjectTerminationWitnessMapping]
  native_decide

theorem checked_control_attenuation_gate
    (plan : BootPageTablePlan.Plan) :
    gate (subjectTerminationCheckedIOMMU plan)
        (.attenuate controlCheckedAttenuation) =
      .accepted (controlCheckedAttenuatedIOMMU plan)
        (.attenuated subjectTerminationWitnessMapping.handle) := by
  rfl

theorem checked_control_attenuation_candidate_coherent
    (plan : BootPageTablePlan.Plan) :
    ({ kernel := (subjectTerminationCheckedBefore plan).kernel
       iommu := controlCheckedAttenuatedIOMMU plan
       scrub := (subjectTerminationCheckedBefore plan).scrub } :
      AuthoritativeExtension).Coherent := by
  refine ⟨rfl, rfl, rfl, rfl,
    authoritativeSampleScrub_invariant plan, ?_⟩
  simp [controlCheckedAttenuatedIOMMU, controlCheckedAttenuatedMapping,
    subjectTerminationCheckedBefore, subjectTerminationCheckedCore,
    authoritativeSample, authoritativeSampleCore,
    FailStop.compositeDispatcherInitial,
    subjectTerminationWitnessAssignment, subjectTerminationWitnessMapping]
  native_decide

theorem checked_control_attenuation_gated_accepts
    (plan : BootPageTablePlan.Plan) :
    (gatedByKernel (subjectTerminationCheckedBefore plan)
      (subject_termination_checked_before_invariant plan)
      (.attenuate controlCheckedAttenuation)).isAccepted = true := by
  unfold gatedByKernel
  rw [show (subjectTerminationCheckedBefore plan).kernel.execution.mode =
      .running by rfl]
  simp only
  rw [show gate (subjectTerminationCheckedBefore plan).iommu
        (.attenuate controlCheckedAttenuation) =
      .accepted (controlCheckedAttenuatedIOMMU plan)
        (.attenuated subjectTerminationWitnessMapping.handle) by
    simpa [subjectTerminationCheckedBefore] using
      checked_control_attenuation_gate plan]
  simp [checked_control_attenuation_candidate_coherent plan,
    AuthoritativeOutcome.isAccepted]

/-- Exact acknowledgement of the checked reduction publishes the read-only
authoritative mapping, removes the old broader cache entry, and clears the
shared pending slot. -/
theorem checked_control_attenuation_authoritative_acknowledges_exact
    (plan : BootPageTablePlan.Plan) :
    let prepared := prepareAuthoritativePublication
      (controlCheckedAuthoritativePublicationState plan)
      (subject_termination_checked_before_invariant plan)
      (.control (.attenuate controlCheckedAttenuation))
    let acknowledged := acknowledgeAuthoritativePublication prepared.state
      (controlCheckedCompletion controlCheckedMappingScope)
    acknowledged.accepted = true ∧
      acknowledged.state.authoritative =
        { kernel := (subjectTerminationCheckedBefore plan).kernel
          iommu := controlCheckedAttenuatedIOMMU plan
          scrub := (subjectTerminationCheckedBefore plan).scrub } ∧
      (acknowledged.state.authoritative.iommu.core.mappings.find?
        (fun mapping => mapping.handle ==
          subjectTerminationWitnessMapping.handle)).map
          (fun mapping => mapping.permission) = some readOnly ∧
      lookup acknowledged.state.cache subjectTerminationWitnessKey = none ∧
      acknowledged.state.pending = none := by
  simp only [prepareAuthoritativePublication,
    controlCheckedAuthoritativePublicationState, prepareControlPublication]
  rw [checked_control_attenuation_requires_exact_scope plan]
  have haccepted := checked_control_attenuation_gated_accepts plan
  cases hgate : gatedByKernel (subjectTerminationCheckedBefore plan)
      (subject_termination_checked_before_invariant plan)
      (.attenuate controlCheckedAttenuation) with
  | rejected reason =>
      simp [hgate, AuthoritativeOutcome.isAccepted] at haccepted
  | accepted after hinvariant reply =>
      have hexact :
          after =
              { kernel := (subjectTerminationCheckedBefore plan).kernel
                iommu := controlCheckedAttenuatedIOMMU plan
                scrub := (subjectTerminationCheckedBefore plan).scrub } ∧
            reply =
              .attenuated subjectTerminationWitnessMapping.handle := by
        unfold gatedByKernel at hgate
        rw [show (subjectTerminationCheckedBefore plan).kernel.execution.mode =
            .running by rfl] at hgate
        simp only at hgate
        rw [show gate (subjectTerminationCheckedBefore plan).iommu
            (.attenuate controlCheckedAttenuation) =
              .accepted (controlCheckedAttenuatedIOMMU plan)
                (.attenuated subjectTerminationWitnessMapping.handle) by
          simpa [subjectTerminationCheckedBefore] using
            checked_control_attenuation_gate plan] at hgate
        simp only at hgate
        rw [dif_pos (checked_control_attenuation_candidate_coherent plan)] at hgate
        cases hgate
        exact ⟨rfl, rfl⟩
      rcases hexact with ⟨rfl, rfl⟩
      simp [acknowledgeAuthoritativePublication, acknowledgeControlPublication,
        controlCheckedCompletion, controlCheckedMappingScope, invalidate,
        eraseMappingScope, lookup, controlCheckedAttenuatedIOMMU,
        controlCheckedAttenuatedMapping, subjectTerminationWitnessEntry,
        subjectTerminationWitnessKey, subjectTerminationWitnessAssignment,
        subjectTerminationWitnessMapping]
      all_goals native_decide

/-! ## Checked assignment teardown through the authoritative front door

The invariant-bearing fixture now removes the live assignment and every
mapping derived from it. Exact acknowledgement must publish that checked
assignment/mapping-free successor and invalidate the complete old
source/domain cache scope before teardown becomes visible.
-/

def controlCheckedTornDownIOMMU (plan : BootPageTablePlan.Plan) : State :=
  { core := { subjectTerminationCheckedCore plan with
      assignments := []
      mappings := [] }
    valid := by
      simp [subjectTerminationCheckedCore, authoritativeSampleCore,
        subjectTerminationWitnessAssignment,
        FailStop.compositeDispatcherInitial]
      native_decide
    capabilityWellFormed :=
      (subjectTerminationCheckedIOMMU plan).capabilityWellFormed }

/-- Assignment teardown derives the complete source/domain scope from the
published assignment rather than accepting a caller-selected cache target. -/
theorem checked_control_teardown_requires_exact_scope
    (plan : BootPageTablePlan.Plan) :
    requiredControlScope (subjectTerminationCheckedBefore plan)
      (.teardown subjectTerminationWitnessAssignment.handle) =
        some controlCheckedAssignmentScope := by
  simp [requiredControlScope, assignmentScopeFor, findAssignment,
    controlCheckedAssignmentScope, subjectTerminationCheckedBefore,
    subjectTerminationCheckedIOMMU, subjectTerminationCheckedCore,
    subjectTerminationWitnessAssignment]
  native_decide

theorem checked_control_teardown_gate
    (plan : BootPageTablePlan.Plan) :
    gate (subjectTerminationCheckedIOMMU plan)
        (.teardown subjectTerminationWitnessAssignment.handle) =
      .accepted (controlCheckedTornDownIOMMU plan) .tornDown := by
  rfl

theorem checked_control_teardown_candidate_coherent
    (plan : BootPageTablePlan.Plan) :
    ({ kernel := (subjectTerminationCheckedBefore plan).kernel
       iommu := controlCheckedTornDownIOMMU plan
       scrub := (subjectTerminationCheckedBefore plan).scrub } :
      AuthoritativeExtension).Coherent := by
  refine ⟨rfl, rfl, rfl, rfl,
    authoritativeSampleScrub_invariant plan, ?_⟩
  simp [controlCheckedTornDownIOMMU, subjectTerminationCheckedBefore,
    subjectTerminationCheckedCore, authoritativeSample,
    authoritativeSampleCore, FailStop.compositeDispatcherInitial,
    subjectTerminationWitnessAssignment]
  native_decide

theorem checked_control_teardown_gated_accepts
    (plan : BootPageTablePlan.Plan) :
    (gatedByKernel (subjectTerminationCheckedBefore plan)
      (subject_termination_checked_before_invariant plan)
      (.teardown subjectTerminationWitnessAssignment.handle)).isAccepted = true := by
  unfold gatedByKernel
  rw [show (subjectTerminationCheckedBefore plan).kernel.execution.mode =
      .running by rfl]
  simp only
  rw [show gate (subjectTerminationCheckedBefore plan).iommu
        (.teardown subjectTerminationWitnessAssignment.handle) =
      .accepted (controlCheckedTornDownIOMMU plan) .tornDown by
    simpa [subjectTerminationCheckedBefore] using
      checked_control_teardown_gate plan]
  simp [checked_control_teardown_candidate_coherent plan,
    AuthoritativeOutcome.isAccepted]

/-- Preparing checked assignment teardown cannot make any old device authority
disappear early.  The assignment, its descendant mapping, and its cached
translation remain published while the internally derived assignment-scope
ticket is pending; only exact completion may publish their removal. -/
theorem checked_control_teardown_authoritative_prepare_retains_old_authority
    (plan : BootPageTablePlan.Plan) :
    let prepared := prepareAuthoritativePublication
      (controlCheckedAuthoritativePublicationState plan)
      (subject_termination_checked_before_invariant plan)
      (.control (.teardown subjectTerminationWitnessAssignment.handle))
    prepared.state.authoritative.iommu.core.assignments =
        [subjectTerminationWitnessAssignment] ∧
      prepared.state.authoritative.iommu.core.mappings =
        [subjectTerminationWitnessMapping] ∧
      lookup prepared.state.cache subjectTerminationWitnessKey =
        some subjectTerminationWitnessEntry ∧
      prepared.state.pending.isSome = true := by
  simp only [prepareAuthoritativePublication,
    controlCheckedAuthoritativePublicationState, prepareControlPublication]
  rw [checked_control_teardown_requires_exact_scope plan]
  have haccepted := checked_control_teardown_gated_accepts plan
  cases hgate : gatedByKernel (subjectTerminationCheckedBefore plan)
      (subject_termination_checked_before_invariant plan)
      (.teardown subjectTerminationWitnessAssignment.handle) with
  | rejected reason =>
      simp [hgate, AuthoritativeOutcome.isAccepted] at haccepted
  | accepted after hinvariant reply =>
      simp [subjectTerminationCheckedBefore, subjectTerminationCheckedIOMMU,
        subjectTerminationCheckedCore, authoritativeSample,
        FailStop.compositeDispatcherInitial, subjectTerminationWitnessEntry,
        subjectTerminationWitnessKey, subjectTerminationWitnessAssignment,
        subjectTerminationWitnessMapping, lookup]

/-- Exact acknowledgement of checked assignment teardown publishes the
assignment/mapping-free successor, removes the old source/domain cache entry,
and closes the shared pending slot. -/
theorem checked_control_teardown_authoritative_acknowledges_exact
    (plan : BootPageTablePlan.Plan) :
    let prepared := prepareAuthoritativePublication
      (controlCheckedAuthoritativePublicationState plan)
      (subject_termination_checked_before_invariant plan)
      (.control (.teardown subjectTerminationWitnessAssignment.handle))
    let acknowledged := acknowledgeAuthoritativePublication prepared.state
      (controlCheckedCompletion controlCheckedAssignmentScope)
    acknowledged.accepted = true ∧
      acknowledged.state.authoritative =
        { kernel := (subjectTerminationCheckedBefore plan).kernel
          iommu := controlCheckedTornDownIOMMU plan
          scrub := (subjectTerminationCheckedBefore plan).scrub } ∧
      acknowledged.state.authoritative.iommu.core.assignments = [] ∧
      acknowledged.state.authoritative.iommu.core.mappings = [] ∧
      lookup acknowledged.state.cache subjectTerminationWitnessKey = none ∧
      acknowledged.state.pending = none := by
  simp only [prepareAuthoritativePublication,
    controlCheckedAuthoritativePublicationState, prepareControlPublication]
  rw [checked_control_teardown_requires_exact_scope plan]
  have haccepted := checked_control_teardown_gated_accepts plan
  cases hgate : gatedByKernel (subjectTerminationCheckedBefore plan)
      (subject_termination_checked_before_invariant plan)
      (.teardown subjectTerminationWitnessAssignment.handle) with
  | rejected reason =>
      simp [hgate, AuthoritativeOutcome.isAccepted] at haccepted
  | accepted after hinvariant reply =>
      have hexact :
          after =
              { kernel := (subjectTerminationCheckedBefore plan).kernel
                iommu := controlCheckedTornDownIOMMU plan
                scrub := (subjectTerminationCheckedBefore plan).scrub } ∧
            reply = .tornDown := by
        unfold gatedByKernel at hgate
        rw [show (subjectTerminationCheckedBefore plan).kernel.execution.mode =
            .running by rfl] at hgate
        simp only at hgate
        rw [show gate (subjectTerminationCheckedBefore plan).iommu
            (.teardown subjectTerminationWitnessAssignment.handle) =
              .accepted (controlCheckedTornDownIOMMU plan) .tornDown by
          simpa [subjectTerminationCheckedBefore] using
            checked_control_teardown_gate plan] at hgate
        simp only at hgate
        rw [dif_pos (checked_control_teardown_candidate_coherent plan)] at hgate
        cases hgate
        exact ⟨rfl, rfl⟩
      rcases hexact with ⟨rfl, rfl⟩
      simp [acknowledgeAuthoritativePublication, acknowledgeControlPublication,
        controlCheckedCompletion, controlCheckedAssignmentScope, invalidate,
        eraseAssignmentScope, lookup, controlCheckedTornDownIOMMU,
        subjectTerminationWitnessEntry, subjectTerminationWitnessKey,
        subjectTerminationWitnessAssignment, subjectTerminationWitnessMapping]
      all_goals native_decide

/-- A mapping-scoped completion cannot partially acknowledge assignment
teardown.  The authoritative assignment, its descendant mapping, the cached
translation, and the exact assignment-scoped pending publication all remain
unchanged until the derived teardown scope completes. -/
theorem checked_control_teardown_partial_completion_stutters
    (plan : BootPageTablePlan.Plan) :
    let prepared := prepareAuthoritativePublication
      (controlCheckedAuthoritativePublicationState plan)
      (subject_termination_checked_before_invariant plan)
      (.control (.teardown subjectTerminationWitnessAssignment.handle))
    let acknowledged := acknowledgeAuthoritativePublication prepared.state
      (controlCheckedCompletion controlCheckedMappingScope)
    acknowledged.accepted = false ∧ acknowledged.state = prepared.state := by
  simp only [prepareAuthoritativePublication,
    controlCheckedAuthoritativePublicationState, prepareControlPublication]
  rw [checked_control_teardown_requires_exact_scope plan]
  have haccepted := checked_control_teardown_gated_accepts plan
  cases hgate : gatedByKernel (subjectTerminationCheckedBefore plan)
      (subject_termination_checked_before_invariant plan)
      (.teardown subjectTerminationWitnessAssignment.handle) with
  | rejected reason =>
      simp [hgate, AuthoritativeOutcome.isAccepted] at haccepted
  | accepted after hinvariant reply =>
      simp [acknowledgeAuthoritativePublication, acknowledgeControlPublication,
        controlCheckedCompletion, controlCheckedMappingScope,
        controlCheckedAssignmentScope]

/-! ## Assigned-EDU reuse binding

The machine lane uses the generated VT-d projection, whose requester 16 is the
hardware projection of authoritative model source 0.  This boundary binds the
hardware call order to the complete old mapping and frame lifetime instead of
reusing the unrelated hosted scalar example below.
-/

def assignedEDUReuseKey : Key := {
  source := 0
  assignment := IOMMU.assignment0
  domain := IOMMU.domain0
  mapping := IOMMU.mapping0
  iova := 0
  direction := .read }

def assignedEDUReuseEntry : Entry := {
  key := assignedEDUReuseKey
  frame := IOMMU.readOnlyState.core.mappings.head!.frame
  permission := readOnly }

def assignedEDUReuseInitial : PublicationState := {
  published := [assignedEDUReuseEntry]
  pending := none
  nextTicket := 1 }

private def assignedEDUReuseInputsMatch
    (version requester source assignment assignmentGeneration domain
      domainGeneration mapping mappingGeneration modelIova frame frameGeneration
      hardwareIova : UInt64) : Bool :=
  version == 1 && requester == 16 &&
    source == 0 && assignment == 0 && assignmentGeneration == 1 &&
    domain == 0 && domainGeneration == 1 &&
    mapping == 0 && mappingGeneration == 1 && modelIova == 0 &&
    frame == 0 && frameGeneration == 1 &&
    hardwareIova == 0

def assignedEDUReusePublicationDemo
    (action version requester source assignment assignmentGeneration domain
      domainGeneration mapping mappingGeneration modelIova frame frameGeneration
      hardwareIova : UInt64) : UInt64 :=
  if !assignedEDUReuseInputsMatch version requester source assignment
      assignmentGeneration domain domainGeneration mapping mappingGeneration
      modelIova frame frameGeneration hardwareIova then
    1
  else
    let prepared := prepareInvalidation assignedEDUReuseInitial
      (.mapping assignedEDUReuseKey)
    if action = 1 then
      if prepared.accepted && prepared.state.pending.isSome &&
          lookup prepared.state.published assignedEDUReuseKey =
            some assignedEDUReuseEntry then 0 else 2
    else if action = 2 then
      let acknowledged := acknowledgeInvalidation prepared.state {
        ticket := 1, scope := .mapping assignedEDUReuseKey }
      if acknowledged.accepted && acknowledged.state.pending.isNone &&
          lookup acknowledged.state.published assignedEDUReuseKey = none then 0 else 3
    else
      4

/-- Allocation-free fixed-width validator for the assigned-EDU reuse scope.
This export validates the two call shapes used by the machine lane; it is not
a stateful publication protocol and does not by itself prove that completion
consumes the preparation call.  The source/final-ELF policy pins their machine
ordering, while the stateful `prepareInvalidation`/`acknowledgeInvalidation`
model below owns the exact pending-state and replay theorems. -/
@[export leanos_assigned_edu_reuse_publication]
def assignedEDUReusePublicationExport
    (action version requester source assignment assignmentGeneration domain
      domainGeneration mapping mappingGeneration modelIova frame frameGeneration
      hardwareIova : UInt64) : UInt64 :=
  if !assignedEDUReuseInputsMatch version requester source assignment
      assignmentGeneration domain domainGeneration mapping mappingGeneration
      modelIova frame frameGeneration hardwareIova then 1
  else if action = 1 || action = 2 then 0
  else 4

theorem assigned_edu_reuse_export_agrees_with_protocol :
    assignedEDUReusePublicationExport 1 1 16 0 0 1 0 1 0 1 0 0 1 0 =
        assignedEDUReusePublicationDemo 1 1 16 0 0 1 0 1 0 1 0 0 1 0 ∧
      assignedEDUReusePublicationExport 2 1 16 0 0 1 0 1 0 1 0 0 1 0 =
        assignedEDUReusePublicationDemo 2 1 16 0 0 1 0 1 0 1 0 0 1 0 ∧
      assignedEDUReusePublicationExport 1 2 16 0 0 1 0 1 0 1 0 0 1 0 = 1 ∧
      assignedEDUReusePublicationExport 1 1 17 0 0 1 0 1 0 1 0 0 1 0 = 1 ∧
      assignedEDUReusePublicationExport 1 1 16 1 0 1 0 1 0 1 0 0 1 0 = 1 ∧
      assignedEDUReusePublicationExport 1 1 16 0 1 1 0 1 0 1 0 0 1 0 = 1 ∧
      assignedEDUReusePublicationExport 1 1 16 0 0 2 0 1 0 1 0 0 1 0 = 1 ∧
      assignedEDUReusePublicationExport 1 1 16 0 0 1 1 1 0 1 0 0 1 0 = 1 ∧
      assignedEDUReusePublicationExport 1 1 16 0 0 1 0 2 0 1 0 0 1 0 = 1 ∧
      assignedEDUReusePublicationExport 1 1 16 0 0 1 0 1 1 1 0 0 1 0 = 1 ∧
      assignedEDUReusePublicationExport 1 1 16 0 0 1 0 1 0 2 0 0 1 0 = 1 ∧
      assignedEDUReusePublicationExport 1 1 16 0 0 1 0 1 0 1 0x1000 0 1 0 = 1 ∧
      assignedEDUReusePublicationExport 1 1 16 0 0 1 0 1 0 1 0 1 1 0 = 1 ∧
      assignedEDUReusePublicationExport 1 1 16 0 0 1 0 1 0 1 0 0 2 0 = 1 ∧
      assignedEDUReusePublicationExport 1 1 16 0 0 1 0 1 0 1 0 0 1 0x1000 = 1 := by
  native_decide

/-! ## Checked assigned-EDU protocol trace

The fixed-shape validator above intentionally validates individual machine
calls.  This allocation-free second boundary validates the fixed assigned-EDU
lifecycle shape as one finite scalar trace.  Its pending ticket is produced
inside this invocation, consumed by exact completion, and unavailable to a
requested replay.  The theorem below binds the canonical scalar result back
to the authoritative publication model; this boundary does not claim that a
caller-provided scalar is itself a non-forgeable pending token.
-/

@[export leanos_assigned_edu_reuse_protocol]
def assignedEDUReuseProtocolExport
    (prepareRequested completionRequested completionTicket replayRequested : UInt64) :
    UInt64 :=
  let pendingAfterPrepare : UInt64 := if prepareRequested = 1 then 1 else 0
  if pendingAfterPrepare = 0 then
    2
  else if completionRequested != 1 then
    1
  else if completionTicket != pendingAfterPrepare then
    3
  else
    let pendingAfterCompletion : UInt64 :=
      if completionTicket = pendingAfterPrepare then 0 else pendingAfterPrepare
    if pendingAfterCompletion != 0 then
      5
    else if replayRequested = 1 then
      if pendingAfterCompletion = completionTicket then 5 else 4
    else
      0

theorem assigned_edu_reuse_protocol_regressions :
    assignedEDUReuseProtocolExport 1 1 1 0 = 0 ∧
      assignedEDUReuseProtocolExport 0 1 1 0 = 2 ∧
      assignedEDUReuseProtocolExport 1 0 1 0 = 1 ∧
      assignedEDUReuseProtocolExport 1 1 2 0 = 3 ∧
      assignedEDUReuseProtocolExport 1 1 1 1 = 4 := by
  native_decide

def assignedEDUReuseProtocolModelAdapter
    (prepareRequested completionRequested completionTicket replayRequested : UInt64) :
    UInt64 :=
  if prepareRequested != 1 then
    2
  else
    let prepared := prepareInvalidation assignedEDUReuseInitial
      (.mapping assignedEDUReuseKey)
    if !prepared.accepted then
      2
    else if completionRequested != 1 then
      1
    else
      let completion : Completion := {
        ticket := completionTicket.toNat
        scope := .mapping assignedEDUReuseKey }
      let acknowledged := acknowledgeInvalidation prepared.state completion
      if !acknowledged.accepted then
        3
      else if acknowledged.state.pending.isSome then
        5
      else if replayRequested = 1 then
        let replayed := acknowledgeInvalidation acknowledged.state completion
        if replayed.accepted || replayed.state.pending.isSome then 5 else 4
      else
        0

theorem assigned_edu_reuse_protocol_export_agrees_with_model :
    assignedEDUReuseProtocolExport 1 1 1 0 =
        assignedEDUReuseProtocolModelAdapter 1 1 1 0 ∧
      assignedEDUReuseProtocolExport 0 1 1 0 =
        assignedEDUReuseProtocolModelAdapter 0 1 1 0 ∧
      assignedEDUReuseProtocolExport 1 0 1 0 =
        assignedEDUReuseProtocolModelAdapter 1 0 1 0 ∧
      assignedEDUReuseProtocolExport 1 1 2 0 =
        assignedEDUReuseProtocolModelAdapter 1 1 2 0 ∧
      assignedEDUReuseProtocolExport 1 1 1 1 =
        assignedEDUReuseProtocolModelAdapter 1 1 1 1 := by
  native_decide

/-! ## Assigned-EDU release gate

Completion of the invalidation protocol is necessary but not sufficient for
frame reuse: the authoritative mapping and published translation must also
stop naming the old lifetime.  This fixed-width boundary exposes those three
ordered checks to the hosted generated-C lane. -/

def frameReleaseGuardCode : FrameReleaseGuard → UInt64
  | .allowed => 0
  | .invalidationPending => 1
  | .mappingLive => 2
  | .cachedTranslationLive => 3
  | .missingAuthority => 4

@[export leanos_assigned_edu_reuse_release_gate]
def assignedEDUReuseReleaseGateExport
    (completionAccepted mappingLive cacheLive : UInt64) : UInt64 :=
  if completionAccepted != 1 then 1
  else if mappingLive = 1 then 2
  else if cacheLive = 1 then 3
  else 0

theorem assigned_edu_reuse_release_gate_regressions :
    assignedEDUReuseReleaseGateExport 0 0 0 = 1 ∧
      assignedEDUReuseReleaseGateExport 1 1 0 = 2 ∧
      assignedEDUReuseReleaseGateExport 1 0 1 = 3 ∧
      assignedEDUReuseReleaseGateExport 1 0 0 = 0 := by
  native_decide

theorem assigned_edu_reuse_release_pending_agrees_with_model state frame pending
    (hpending : state.cache.pending = some pending)
    (hnames : pendingNamesFrame pending frame = true) :
    assignedEDUReuseReleaseGateExport 0 0 0 =
      frameReleaseGuardCode (guardExactFrameRelease state frame) := by
  rw [pending_invalidation_blocks_exact_frame_release state frame pending
    hpending hnames]
  rfl

theorem assigned_edu_reuse_release_mapping_agrees_with_model state frame
    (hpending : state.cache.pending = none)
    (hmapping :
      state.authoritative.iommu.core.mappings.any (·.frame == frame) = true) :
    assignedEDUReuseReleaseGateExport 1 1 0 =
      frameReleaseGuardCode (guardExactFrameRelease state frame) := by
  rw [live_mapping_blocks_exact_frame_release state frame hpending hmapping]
  rfl

theorem assigned_edu_reuse_release_cache_agrees_with_model state frame
    (hpending : state.cache.pending = none)
    (hmapping :
      state.authoritative.iommu.core.mappings.any (·.frame == frame) = false)
    (hcache : entriesNameFrame state.cache.published frame = true) :
    assignedEDUReuseReleaseGateExport 1 0 1 =
      frameReleaseGuardCode (guardExactFrameRelease state frame) := by
  rw [published_translation_blocks_exact_frame_release state frame hpending
    hmapping hcache]
  rfl

theorem assigned_edu_reuse_release_allowed_agrees_with_model state frame
    (hpending : state.cache.pending = none)
    (hmapping :
      state.authoritative.iommu.core.mappings.any (·.frame == frame) = false)
    (hcache : entriesNameFrame state.cache.published frame = false) :
    assignedEDUReuseReleaseGateExport 1 0 0 =
      frameReleaseGuardCode (guardExactFrameRelease state frame) := by
  rw [exact_frame_release_allowed_only_after_cleanup state frame hpending
    hmapping hcache]
  rfl

/-! ## Assigned-EDU fresh-lifetime publication ordering

The clean release decision above is consumed by a second small state machine.
It makes release, scrub completion, and fresh-lifetime publication distinct
steps: a rejected step stutters, and publication is accepted only from the
scrubbed phase.  This is still a hosted protocol model rather than a claim
about the QEMU device or VT-d completion machinery.
-/

inductive AssignedEDUReusePhase where
  | oldLifetime
  | released
  | scrubbed
  | freshPublished
  deriving BEq, DecidableEq, Repr

inductive AssignedEDUReuseCommand where
  | release (guard : FrameReleaseGuard)
  | scrub
  | publishFresh
  deriving DecidableEq, Repr

structure AssignedEDUReuseStep where
  phase : AssignedEDUReusePhase
  accepted : Bool
  deriving DecidableEq, Repr

def advanceAssignedEDUReuse
    (phase : AssignedEDUReusePhase) : AssignedEDUReuseCommand → AssignedEDUReuseStep
  | .release .allowed =>
      if phase == .oldLifetime then { phase := .released, accepted := true }
      else { phase, accepted := false }
  | .release _ => { phase, accepted := false }
  | .scrub =>
      if phase == .released then { phase := .scrubbed, accepted := true }
      else { phase, accepted := false }
  | .publishFresh =>
      if phase == .scrubbed then { phase := .freshPublished, accepted := true }
      else { phase, accepted := false }

def runAssignedEDUReuse
    (commands : List AssignedEDUReuseCommand) : AssignedEDUReuseStep :=
  commands.foldl (fun state command =>
    let next := advanceAssignedEDUReuse state.phase command
    { phase := next.phase, accepted := state.accepted && next.accepted })
    { phase := .oldLifetime, accepted := true }

private def assignedEDUReuseGuardFromCode : UInt64 → FrameReleaseGuard
  | 0 => .allowed
  | 1 => .invalidationPending
  | 2 => .mappingLive
  | 3 => .cachedTranslationLive
  | _ => .missingAuthority

private def assignedEDUReuseCommands
    (guardCode sequence : UInt64) : List AssignedEDUReuseCommand :=
  let release := AssignedEDUReuseCommand.release
    (assignedEDUReuseGuardFromCode guardCode)
  if sequence = 0 then [release, .scrub, .publishFresh]
  else if sequence = 1 then [.scrub, release, .publishFresh]
  else if sequence = 2 then [release, .publishFresh, .scrub]
  else [release]

def assignedEDUReuseFreshPublicationModel
    (guardCode sequence : UInt64) : UInt64 :=
  let result := runAssignedEDUReuse
    (assignedEDUReuseCommands guardCode sequence)
  if guardCode != 0 then 1
  else if !result.accepted then 2
  else if result.phase != .freshPublished then 3
  else 0

@[export leanos_assigned_edu_reuse_fresh_publication]
def assignedEDUReuseFreshPublicationExport
    (guardCode sequence : UInt64) : UInt64 :=
  if guardCode != 0 then 1
  else if sequence = 1 || sequence = 2 then 2
  else if sequence != 0 then 3
  else 0

theorem assigned_edu_reuse_fresh_publication_regressions :
    assignedEDUReuseFreshPublicationExport 0 0 = 0 ∧
      assignedEDUReuseFreshPublicationExport 1 0 = 1 ∧
      assignedEDUReuseFreshPublicationExport 2 0 = 1 ∧
      assignedEDUReuseFreshPublicationExport 3 0 = 1 ∧
      assignedEDUReuseFreshPublicationExport 0 1 = 2 ∧
      assignedEDUReuseFreshPublicationExport 0 2 = 2 ∧
      assignedEDUReuseFreshPublicationExport 0 3 = 3 := by
  native_decide

theorem assigned_edu_reuse_fresh_publication_export_agrees_with_model :
    assignedEDUReuseFreshPublicationExport 0 0 =
        assignedEDUReuseFreshPublicationModel 0 0 ∧
      assignedEDUReuseFreshPublicationExport 1 0 =
        assignedEDUReuseFreshPublicationModel 1 0 ∧
      assignedEDUReuseFreshPublicationExport 2 0 =
        assignedEDUReuseFreshPublicationModel 2 0 ∧
      assignedEDUReuseFreshPublicationExport 3 0 =
        assignedEDUReuseFreshPublicationModel 3 0 ∧
      assignedEDUReuseFreshPublicationExport 0 1 =
        assignedEDUReuseFreshPublicationModel 0 1 ∧
      assignedEDUReuseFreshPublicationExport 0 2 =
        assignedEDUReuseFreshPublicationModel 0 2 ∧
      assignedEDUReuseFreshPublicationExport 0 3 =
        assignedEDUReuseFreshPublicationModel 0 3 := by
  native_decide

/-! ## Authoritative release-to-scrub composition

The hosted phase machine above is not itself the allocator.  The theorem
below connects its successful row to the two real model boundaries: an
accepted `gatedCachedMemoryByKernel` release (which can only have passed the
exact cache-aware guard) and the subsequent `FrameScrub.allocate` transition
(which atomically clears the selected frame before publishing its new
lifetime).  Thus the abstract `released -> scrubbed -> freshPublished` path is
justified by authoritative outcomes rather than caller-provided success bits.
-/

theorem cached_release_then_allocation_orders_fresh_publication
    (state : AuthoritativeCacheState)
    (hstate : state.authoritative.Invariant)
    (oldSubject : FrameScrub.SubjectId)
    (oldSlot : FrameScrub.SlotId)
    (freshObject : FrameScrub.ObjectId)
    (freshSubject : FrameScrub.SubjectId)
    (freshSlot : FrameScrub.SlotId)
    (hrelease :
      (gatedCachedMemoryByKernel state hstate
        (.release oldSubject oldSlot)).isAccepted = true)
    (hallocate :
      (FrameScrub.allocate
        (gatedCachedMemoryByKernel state hstate
          (.release oldSubject oldSlot)).state.authoritative.scrub
        freshObject freshSubject freshSlot).result = .accepted) :
    let released := advanceAssignedEDUReuse .oldLifetime
      (.release (guardFrameRelease state oldSubject oldSlot))
    let scrubbed := advanceAssignedEDUReuse released.phase .scrub
    let published := advanceAssignedEDUReuse scrubbed.phase .publishFresh
    released.accepted = true ∧
      scrubbed.accepted = true ∧
      published.accepted = true ∧
      published.phase = .freshPublished ∧
      FrameScrub.Fresh
        (FrameScrub.allocate
          (gatedCachedMemoryByKernel state hstate
            (.release oldSubject oldSlot)).state.authoritative.scrub
          freshObject freshSubject freshSlot).state
        freshObject := by
  have hguard := cached_release_accepted_requires_guard_allowed
    state hstate oldSubject oldSlot hrelease
  have hfresh := FrameScrub.allocation_publishes_scrubbed
    (gatedCachedMemoryByKernel state hstate
      (.release oldSubject oldSlot)).state.authoritative.scrub
    freshObject freshSubject freshSlot hallocate
  dsimp only
  rw [hguard]
  refine ⟨?_, ?_, ?_, ?_, hfresh⟩ <;> native_decide

/-- The controlled assigned-EDU call-order row cannot jump from a caller's
completion bit directly to fresh publication.  Its cache premise is the exact
state produced by preparing and acknowledging the assigned-EDU mapping
invalidation; an accepted release then supplies authoritative capability
resolution and the exact-frame guard, and the real allocator supplies the
scrubbed fresh lifetime.  This remains a model/hosted boundary and does not
claim VT-d completion or QEMU refinement. -/
theorem assigned_edu_completion_release_allocation_orders_fresh_publication
    (state : AuthoritativeCacheState)
    (hstate : state.authoritative.Invariant)
    (oldSubject : FrameScrub.SubjectId)
    (oldSlot : FrameScrub.SlotId)
    (freshObject : FrameScrub.ObjectId)
    (freshSubject : FrameScrub.SubjectId)
    (freshSlot : FrameScrub.SlotId)
    (hcache :
      state.cache =
        (acknowledgeInvalidation
          (prepareInvalidation assignedEDUReuseInitial
            (.mapping assignedEDUReuseKey)).state
          { ticket := 1, scope := .mapping assignedEDUReuseKey }).state)
    (hrelease :
      (gatedCachedMemoryByKernel state hstate
        (.release oldSubject oldSlot)).isAccepted = true)
    (hresolveAssigned :
      resolveReleaseFrame state oldSubject oldSlot =
        some assignedEDUReuseEntry.frame)
    (hallocate :
      (FrameScrub.allocate
        (gatedCachedMemoryByKernel state hstate
          (.release oldSubject oldSlot)).state.authoritative.scrub
        freshObject freshSubject freshSlot).result = .accepted)
    (hreuseAssigned :
      (FrameScrub.allocate
        (gatedCachedMemoryByKernel state hstate
          (.release oldSubject oldSlot)).state.authoritative.scrub
        freshObject freshSubject freshSlot).state.memory.binding freshObject =
          some assignedEDUReuseEntry.frame.frame) :
    state.cache.pending = none ∧
      lookup state.cache.published assignedEDUReuseKey = none ∧
      resolveReleaseFrame state oldSubject oldSlot =
        some assignedEDUReuseEntry.frame ∧
      guardExactFrameRelease state assignedEDUReuseEntry.frame = .allowed ∧
      (FrameScrub.allocate
        (gatedCachedMemoryByKernel state hstate
          (.release oldSubject oldSlot)).state.authoritative.scrub
        freshObject freshSubject freshSlot).state.memory.binding freshObject =
          some assignedEDUReuseEntry.frame.frame ∧
      assignedEDUReuseFreshPublicationExport 0 0 = 0 ∧
      FrameScrub.Fresh
        (FrameScrub.allocate
          (gatedCachedMemoryByKernel state hstate
            (.release oldSubject oldSlot)).state.authoritative.scrub
          freshObject freshSubject freshSlot).state
        freshObject := by
  have hresolved := cached_release_accepted_resolves_guarded_frame
    state hstate oldSubject oldSlot hrelease
  obtain ⟨frame, hresolve, hguard⟩ := hresolved
  rw [hresolveAssigned] at hresolve
  injection hresolve with hframe
  subst frame
  have hfresh := FrameScrub.allocation_publishes_scrubbed
    (gatedCachedMemoryByKernel state hstate
      (.release oldSubject oldSlot)).state.authoritative.scrub
    freshObject freshSubject freshSlot hallocate
  refine ⟨?_, ?_, hresolveAssigned, hguard, hreuseAssigned,
    by native_decide, hfresh⟩
  · rw [hcache]
    native_decide
  · rw [hcache]
    native_decide

/-- Allocation acceptance alone cannot establish assigned-frame reuse: an
earlier unrelated free frame wins the allocator's deterministic first-free
selection.  The composition theorem therefore requires and publishes the
exact fresh-object binding to the assigned EDU frame. -/
private def assignedEDUEarlierFreeAllocator : FrameAllocator.State := {
  frames := [1, assignedEDUReuseEntry.frame.frame]
  status := fun _ => .free }

private def assignedEDUEarlierFreeSelection : Option FrameAllocator.FrameId :=
  match FrameAllocator.allocate assignedEDUEarlierFreeAllocator 99 with
  | .ok allocation => some allocation.frame
  | .error _ => none

theorem assigned_edu_reuse_rejects_unbound_allocation_regression :
    assignedEDUEarlierFreeSelection = some 1 ∧
      assignedEDUEarlierFreeSelection ≠
        some assignedEDUReuseEntry.frame.frame := by
  native_decide

/-! ## Fixed-width hosted invalidation sequence

This small scalar boundary exposes the first generated-C slice of the IOTLB
publication protocol.  It deliberately exercises the cache protocol itself,
not VT-d: the fixed initial state contains one live translation, preparation
must retain it, a mismatched completion must stutter, exact completion removes
it, and replay of that completion must remain inert.
-/

def scalarKey : Key := {
  source := 1
  assignment := ⟨2, 1⟩
  domain := ⟨3, 1⟩
  mapping := ⟨4, 1⟩
  iova := 0x1000
  direction := .read }

def scalarEntry : Entry := {
  key := scalarKey
  frame := ⟨5, 1⟩
  permission := readOnly }

def scalarInitial : PublicationState := {
  published := [scalarEntry]
  pending := none
  nextTicket := 7 }

private def scalarScope (source domain mapping iova : UInt64) : InvalidationScope :=
  .mapping {
    source := source.toNat
    assignment := ⟨2, 1⟩
    domain := ⟨domain.toNat, 1⟩
    mapping := ⟨mapping.toNat, 1⟩
    iova := iova.toNat
    direction := .read }

private def encodeScalarState (accepted : Bool) (state : PublicationState) : UInt64 :=
  (if accepted then 1 else 0) +
    (if state.pending.isSome then 2 else 0) +
    (if (lookup state.published scalarKey).isSome then 4 else 0) +
    UInt64.ofNat state.nextTicket * 0x100

/-- Actions: zero observes the filled cache; one prepares exact invalidation;
two acknowledges a caller-described completion; three acknowledges the exact
completion and immediately attempts to replay it.  The completion scope is
fully lifetime-bearing, so changing source/domain/mapping/IOVA is observable. -/
def iotlbPublicationDemo (action ticket source domain mapping iova : UInt64) : UInt64 :=
  let completion : Completion := {
    ticket := ticket.toNat
    scope := scalarScope source domain mapping iova }
  let prepared := prepareInvalidation scalarInitial (.mapping scalarKey)
  if action = 0 then
    encodeScalarState false scalarInitial
  else if action = 1 then
    encodeScalarState prepared.accepted prepared.state
  else if action = 2 then
    let acknowledged := acknowledgeInvalidation prepared.state completion
    encodeScalarState acknowledged.accepted acknowledged.state
  else if action = 3 then
    let exact := acknowledgeInvalidation prepared.state {
      ticket := 7, scope := .mapping scalarKey }
    let replayed := acknowledgeInvalidation exact.state completion
    encodeScalarState replayed.accepted replayed.state
  else
    0

/-- Allocation-free generated-C adapter for the hosted fixed-width boundary.
The proof below binds every hosted row back to `iotlbPublicationDemo`, which
remains the executable cache protocol and the source of the oracle values. -/
@[export leanos_iotlb_publication_demo]
def iotlbPublicationDemoExport
    (action ticket source domain mapping iova : UInt64) : UInt64 :=
  if action = 0 then
    0x704
  else if action = 1 then
    0x807
  else if action = 2 then
    if ticket = 7 && source = 1 && domain = 3 && mapping = 4 && iova = 0x1000 then
      0x801
    else
      0x806
  else if action = 3 then
    0x800
  else
    0

theorem scalar_export_agrees_with_protocol_on_hosted_sequence :
    iotlbPublicationDemoExport 0 0 0 0 0 0 =
        iotlbPublicationDemo 0 0 0 0 0 0 ∧
      iotlbPublicationDemoExport 1 0 0 0 0 0 =
        iotlbPublicationDemo 1 0 0 0 0 0 ∧
      iotlbPublicationDemoExport 2 6 1 3 4 0x1000 =
        iotlbPublicationDemo 2 6 1 3 4 0x1000 ∧
      iotlbPublicationDemoExport 2 7 9 3 4 0x1000 =
        iotlbPublicationDemo 2 7 9 3 4 0x1000 ∧
      iotlbPublicationDemoExport 2 7 1 9 4 0x1000 =
        iotlbPublicationDemo 2 7 1 9 4 0x1000 ∧
      iotlbPublicationDemoExport 2 7 1 3 9 0x1000 =
        iotlbPublicationDemo 2 7 1 3 9 0x1000 ∧
      iotlbPublicationDemoExport 2 7 1 3 4 0x2000 =
        iotlbPublicationDemo 2 7 1 3 4 0x2000 ∧
      iotlbPublicationDemoExport 2 7 1 3 4 0x1000 =
        iotlbPublicationDemo 2 7 1 3 4 0x1000 ∧
      iotlbPublicationDemoExport 3 7 1 3 4 0x1000 =
        iotlbPublicationDemo 3 7 1 3 4 0x1000 := by
  native_decide

theorem scalar_publication_sequence :
    iotlbPublicationDemo 0 0 0 0 0 0 = 0x704 ∧
      iotlbPublicationDemo 1 0 0 0 0 0 = 0x807 ∧
      iotlbPublicationDemo 2 6 1 3 4 0x1000 = 0x806 ∧
      iotlbPublicationDemo 2 7 9 3 4 0x1000 = 0x806 ∧
      iotlbPublicationDemo 2 7 1 9 4 0x1000 = 0x806 ∧
      iotlbPublicationDemo 2 7 1 3 9 0x1000 = 0x806 ∧
      iotlbPublicationDemo 2 7 1 3 4 0x2000 = 0x806 ∧
      iotlbPublicationDemo 2 7 1 3 4 0x1000 = 0x801 ∧
      iotlbPublicationDemo 3 7 1 3 4 0x1000 = 0x800 := by
  native_decide

end LeanOS.IOMMU.IOTLB
