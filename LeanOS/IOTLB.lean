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

theorem prepare_authority_cleanup_retains_publications
    state hstate operation :
    let prepared := prepareAuthorityCleanupPublication state hstate operation
    prepared.state.authoritative = state.authoritative ∧
      prepared.state.cache = state.cache := by
  simp only [prepareAuthorityCleanupPublication]
  split
  · simp
  · split <;> simp

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

end LeanOS.IOMMU.IOTLB
