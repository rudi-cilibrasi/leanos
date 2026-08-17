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

inductive InvalidationScope where
  | mapping (key : Key)
  | assignment (scope : AssignmentScope)
  deriving BEq, DecidableEq, Repr

def eraseAssignmentScope (entries : List Entry)
    (scope : AssignmentScope) : List Entry :=
  entries.filter fun entry => decide
    (entry.key.source ≠ scope.source ∨
      entry.key.assignment ≠ scope.assignment ∨
      entry.key.domain ≠ scope.domain)

def invalidate (entries : List Entry) : InvalidationScope → List Entry
  | .mapping key => eraseKey entries key
  | .assignment scope => eraseAssignmentScope entries scope

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

end LeanOS.IOMMU.IOTLB
