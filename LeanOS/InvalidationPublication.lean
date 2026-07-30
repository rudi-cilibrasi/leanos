import LeanOS.StaleTranslation

/-!
# Stateful invalidation publication protocol

`StaleTranslation.step` computes an accepted logical mutation and its exact
machine effect atomically.  A concrete runtime must still perform that effect
before publishing the logical successor.  This module makes that ordering
explicit for the bounded generated dispatcher:

* `prepare` retains the complete published state and records one pending step;
* `acknowledge` publishes the pending state only when the supplied effect is
  exactly the effect computed by that step; and
* `publishReuse` is disabled until both the release and destruction effects
  have been acknowledged.

The final reuse operation is only the existing finite model fixture.  It does
not add an allocator quota, reclamation policy, or fresh-object runtime path.
-/
namespace LeanOS.InvalidationPublication

open LeanOS
open LeanOS.StaleTranslation

inductive TransitionKind where
  | unmap
  | protect
  | release
  | destroy
  | switch
  deriving DecidableEq, Repr

/-- The operation family is determined by the checked logical request.  It is
not caller-selected metadata: retirement acknowledgement must be earned only
by an actual release or destruction step. -/
def requestKind : StaleTranslation.Request → TransitionKind
  | .unmap .. => .unmap
  | .protect .. => .protect
  | .release .. => .release
  | .destroy .. => .destroy
  | .switch .. => .switch

structure Pending where
  ticket : Nat
  kind : TransitionKind
  step : StaleTranslation.Step

/-- A machine-effect completion is useful only for the exact pending
publication that issued its ticket.  The ticket prevents an earlier completion
with the same effect (for example, a release flush) from acknowledging a later
pending flush. -/
structure Acknowledgement where
  ticket : Nat
  effect : StaleTranslation.Effect
  deriving DecidableEq, Repr

structure State where
  published : TLB.State
  pending : Option Pending
  nextTicket : Nat
  releaseAcknowledged : Bool
  destroyAcknowledged : Bool

structure Outcome where
  state : State
  accepted : Bool
  effect : StaleTranslation.Effect

/-- The publication protocol carries the bounded-cache invariant for both the
currently visible state and the exact logical successor retained behind a
pending machine effect.  This is deliberately narrower than the full
authoritative composite invariant: release and destruction are not yet public
operations of that composite runtime. -/
def WellFormed (state : State) : Prop :=
  TLB.Coherent state.published ∧
    ∀ pending, state.pending = some pending → TLB.Coherent pending.step.state

/-- The canonical sequence starts with a writable mapping and a translation
filled from that exact PTE so the accepted protection step is a real permission
reduction rather than a same-permission replacement. -/
def writableCold : TLB.State :=
  { StaleTranslation.cold with
    virtual := VirtualMapping.setMapping StaleTranslation.cold.virtual 1 7
      (some { object := 10, permissions := { read := true, write := true } }) }

def writableFilled : TLB.State :=
  match TLB.fill writableCold 7 StaleTranslation.ctx with
  | .ok (_, state) => state
  | .error _ => writableCold

def initial : State :=
  { published := writableFilled
    pending := none
    nextTicket := 0
    releaseAcknowledged := false
    destroyAcknowledged := false }

theorem initial_wellFormed : WellFormed initial := by
  refine ⟨?_, ?_⟩
  · change TLB.Coherent writableFilled
    unfold writableFilled
    cases hfill : TLB.fill writableCold 7 StaleTranslation.ctx with
    | error error =>
        simp [TLB.Coherent, writableCold, StaleTranslation.cold]
    | ok result =>
        rcases result with ⟨frame, next⟩
        exact TLB.fill_preserves_coherent _ _ _ _ _ hfill
  intro pending hpending
  simp [initial] at hpending

/-- Compute one logical transition while retaining the complete caller-visible
state.  Rejections and attempts to overlap pending effects are inert. -/
def prepare (state : State) (kind : TransitionKind)
    (request : StaleTranslation.Request) : Outcome :=
  match state.pending with
  | some _ => { state, accepted := false, effect := .none }
  | none =>
      if kind = requestKind request then
        let next := StaleTranslation.step state.published request
        if next.accepted then
          { state :=
              { state with
                pending := some { ticket := state.nextTicket, kind, step := next }
                nextTicket := state.nextTicket + 1 }
            accepted := true
            effect := next.effect }
        else
          { state, accepted := false, effect := .none }
      else
        { state, accepted := false, effect := .none }

/-- Publish exactly one pending logical successor only after an acknowledgement
names both its fresh ticket and exact effect.  A missing, stale, or mismatched
acknowledgement is a complete stutter. -/
def acknowledge (state : State) (ack : Acknowledgement) : Outcome :=
  match state.pending with
  | none => { state, accepted := false, effect := .none }
  | some pending =>
      if ack.ticket = pending.ticket ∧ ack.effect = pending.step.effect then
        { state :=
            { published := pending.step.state
              pending := none
              nextTicket := state.nextTicket
              releaseAcknowledged :=
                state.releaseAcknowledged || pending.kind = .release
              destroyAcknowledged :=
                state.destroyAcknowledged || pending.kind = .destroy }
          accepted := true
          effect := ack.effect }
      else
        { state, accepted := false, effect := .none }

/-- The issue-local bounded reuse witness.  The retired frame is allocated to
object 11 using the existing finite lifecycle model; no quota/reclamation
policy is introduced here. -/
def reusedFixture (state : TLB.State) : TLB.State :=
  { state with
    virtual :=
      { state.virtual with
        memory := (MemoryLifecycle.allocate state.virtual.memory 11 0 0).state } }

/-- Reallocation publication is guarded by acknowledged release and destruction
and by the absence of any still-pending machine effect. -/
def publishReuse (state : State) : Outcome :=
  match state.pending with
  | some _ => { state, accepted := false, effect := .none }
  | none =>
      if state.releaseAcknowledged && state.destroyAcknowledged then
        let next := reusedFixture state.published
        match (MemoryLifecycle.allocate state.published.virtual.memory 11 0 0).result with
        | .accepted =>
            { state := { state with published := next }
              accepted := true
              effect := .none }
        | .rejected _ => { state, accepted := false, effect := .none }
      else
        { state, accepted := false, effect := .none }

/-! ## General ordering laws -/

theorem prepare_retains_published state kind request :
    (prepare state kind request).state.published = state.published := by
  cases hpending : state.pending with
  | some pending => simp [prepare, hpending]
  | none =>
      by_cases hkind : kind = requestKind request
      · by_cases haccepted :
            (StaleTranslation.step state.published request).accepted = true
        <;> simp [prepare, hpending, hkind, haccepted]
      · simp [prepare, hpending, hkind]

/-- Preparation cannot publish a cache that violates the bound and, when it
accepts, records a successor whose cache satisfies the same bound. -/
theorem prepare_preserves_wellFormed state kind request
    (hstate : WellFormed state) :
    WellFormed (prepare state kind request).state := by
  rcases hstate with ⟨hpublished, hpending⟩
  cases hcurrent : state.pending with
  | some current =>
      simpa [prepare, hcurrent] using (show WellFormed state from
        ⟨hpublished, hpending⟩)
  | none =>
      by_cases hkind : kind = requestKind request
      · by_cases haccepted :
            (StaleTranslation.step state.published request).accepted = true
        · refine ⟨?_, ?_⟩
          · simpa [prepare, hcurrent, hkind, haccepted] using hpublished
          · intro pending hpending'
            simp [prepare, hcurrent, hkind, haccepted] at hpending'
            subst pending
            exact StaleTranslation.step_preserves_coherent
              state.published request hpublished
        · simpa [prepare, hcurrent, hkind, haccepted] using
            (show WellFormed state from ⟨hpublished, hpending⟩)
      · simpa [prepare, hcurrent, hkind] using
          (show WellFormed state from ⟨hpublished, hpending⟩)

theorem prepare_rejected_inert state kind request
    (h : (prepare state kind request).accepted = false) :
    (prepare state kind request).state = state ∧
      (prepare state kind request).effect = .none := by
  simp only [prepare] at h ⊢
  split at h <;> try simp_all
  split at h <;> try simp_all
  split at h <;> simp_all

/-- A caller cannot relabel a mapping operation as a lifecycle retirement (or
vice versa).  A mismatched family/request pair is a complete stutter and
requests no machine mutation. -/
theorem prepare_wrong_kind_inert state kind request
    (hkind : kind ≠ requestKind request) :
    (prepare state kind request).accepted = false ∧
      (prepare state kind request).state = state ∧
      (prepare state kind request).effect = .none := by
  cases hpending : state.pending with
  | some pending => simp [prepare, hpending]
  | none => simp [prepare, hpending, hkind]

theorem acknowledge_rejected_inert state ack
    (h : (acknowledge state ack).accepted = false) :
    (acknowledge state ack).state = state ∧
      (acknowledge state ack).effect = .none := by
  unfold acknowledge at h ⊢
  split
  · simp
  next pending hpending =>
    split
    · simp_all
    next => simp

theorem acknowledge_accepted_exact state ack
    (h : (acknowledge state ack).accepted = true) :
    ∃ pending,
      state.pending = some pending ∧
      ack.ticket = pending.ticket ∧
      ack.effect = pending.step.effect ∧
      (acknowledge state ack).state.published = pending.step.state ∧
      (acknowledge state ack).state.pending = none := by
  unfold acknowledge at h
  split at h
  · simp_all
  next pending hpending =>
    split at h
    next hexact =>
      refine ⟨pending, hpending, hexact.1, hexact.2, ?_, ?_⟩
      · simp [acknowledge, hpending, hexact]
      · simp [acknowledge, hpending, hexact]
    next => simp_all

/-- Acknowledgement either stutters or publishes the exact pending successor,
so it preserves the cache bound without trusting the supplied effect. -/
theorem acknowledge_preserves_wellFormed state ack
    (hstate : WellFormed state) :
    WellFormed (acknowledge state ack).state := by
  rcases hstate with ⟨hpublished, hpending⟩
  cases hcurrent : state.pending with
  | none =>
      simpa [acknowledge, hcurrent] using (show WellFormed state from
        ⟨hpublished, hpending⟩)
  | some current =>
      by_cases hexact :
          ack.ticket = current.ticket ∧ ack.effect = current.step.effect
      · have hnext := hpending current hcurrent
        refine ⟨?_, ?_⟩
        · simpa [acknowledge, hcurrent, hexact] using hnext
        · intro pending hpending'
          simp [acknowledge, hcurrent, hexact] at hpending'
      · simpa [acknowledge, hcurrent, hexact] using
          (show WellFormed state from ⟨hpublished, hpending⟩)

/-- Every accepted preparation allocates the pending effect's ticket from the
pre-state and advances the counter before any acknowledgement can arrive. -/
theorem prepare_accepted_fresh_ticket state kind request
    (h : (prepare state kind request).accepted = true) :
    ∃ pending,
      (prepare state kind request).state.pending = some pending ∧
      pending.ticket = state.nextTicket ∧
      (prepare state kind request).state.nextTicket = state.nextTicket + 1 := by
  cases hpending : state.pending with
  | some pending =>
      simp [prepare, hpending] at h
  | none =>
      by_cases hkind : kind = requestKind request
      · by_cases haccepted :
            (StaleTranslation.step state.published request).accepted = true
        · simp [prepare, hpending, hkind, haccepted]
        · simp [prepare, hpending, hkind, haccepted] at h
      · simp [prepare, hpending, hkind] at h

/-- An accepted preparation retains the exact logical step behind its fresh
ticket.  In particular, neither the operation family nor its checked request
can be replaced between effect determination and publication. -/
theorem prepare_accepted_pending_exact state kind request
    (h : (prepare state kind request).accepted = true) :
    ∃ pending,
      (prepare state kind request).state.pending = some pending ∧
      pending.ticket = state.nextTicket ∧
      pending.kind = kind ∧
      pending.step = StaleTranslation.step state.published request ∧
      pending.step.accepted = true ∧
      (prepare state kind request).effect = pending.step.effect ∧
      (prepare state kind request).state.published = state.published := by
  cases hpending : state.pending with
  | some pending =>
      simp [prepare, hpending] at h
  | none =>
      by_cases hkind : kind = requestKind request
      · by_cases haccepted :
            (StaleTranslation.step state.published request).accepted = true
        · simp [prepare, hpending, hkind, haccepted]
        · simp [prepare, hpending, hkind, haccepted] at h
      · simp [prepare, hpending, hkind] at h

/-- A completion from any earlier pending publication cannot be spliced into a
later one, even when both machine effects have the same shape. -/
theorem acknowledge_wrong_ticket_inert state ack pending
    (hpending : state.pending = some pending)
    (hticket : ack.ticket ≠ pending.ticket) :
    (acknowledge state ack).accepted = false ∧
      (acknowledge state ack).state = state ∧
      (acknowledge state ack).effect = .none := by
  simp [acknowledge, hpending, hticket]

/-- A prepared release cannot expose retirement: its complete published state
is literally the pre-state until the required flush is acknowledged. -/
theorem release_not_published_before_ack state subject slot :
    (prepare state .release (.release subject slot)).state.published =
      state.published :=
  prepare_retains_published state .release (.release subject slot)

/-- The bounded fresh-lifetime witness cannot publish unless both retirement
effects were acknowledged and no effect remains pending. -/
theorem reuse_publication_requires_retirement_ack state
    (h : (publishReuse state).accepted = true) :
    state.pending = none ∧
      state.releaseAcknowledged = true ∧
      state.destroyAcknowledged = true := by
  simp only [publishReuse] at h
  split at h
  · simp_all
  next hpending =>
    split at h <;> try simp_all

/-- The bounded reuse witness changes only the virtual lifecycle projection;
the already-invalidated cache and its bound remain literal pre-state data. -/
theorem publishReuse_preserves_wellFormed state
    (hstate : WellFormed state) :
    WellFormed (publishReuse state).state := by
  rcases hstate with ⟨hpublished, hpending⟩
  cases hcurrent : state.pending with
  | some current =>
      simpa [publishReuse, hcurrent] using (show WellFormed state from
        ⟨hpublished, hpending⟩)
  | none =>
      simp only [publishReuse, hcurrent]
      split
      next hretired =>
        split
        next hallocated =>
          refine ⟨?_, ?_⟩
          · change state.published.entries.length ≤ TLB.capacity
            exact hpublished
          · intro pending hpending'
            simp at hpending'
        next =>
          exact ⟨hpublished, hpending⟩
      next =>
        exact ⟨hpublished, hpending⟩

/-! ## Canonical stateful sequence

This corpus covers independent accepted unmap and switch-away/back
prepare/acknowledge branches, plus a sequence with wrong-owner rejection,
accepted protection, mismatched effect rejection, exact acknowledgement,
release, stale-handle rejection, address-space destruction, root switch, and
bounded reuse publication. -/

def unmapPending : State :=
  (prepare initial .unmap (.unmap 0 1 7)).state

def unmappedState : State :=
  (acknowledge unmapPending { ticket := 0, effect := .page 1 7 }).state

def switchAwayPending : State :=
  (prepare initial .switch (.switch 2)).state

def switchedAway : State :=
  (acknowledge switchAwayPending { ticket := 0, effect := .flush }).state

def switchBackPending : State :=
  (prepare switchedAway .switch (.switch 1)).state

def switchedBack : State :=
  (acknowledge switchBackPending { ticket := 1, effect := .flush }).state

def wrongOwnerRejected : State :=
  (prepare initial .protect (.protect 1 1 7 { read := true })).state

def protectPending : State :=
  (prepare wrongOwnerRejected .protect (.protect 0 1 7 { read := true })).state

def protectMismatchRejected : State :=
  (acknowledge protectPending { ticket := 0, effect := .space 1 }).state

def protectedState : State :=
  (acknowledge protectMismatchRejected { ticket := 0, effect := .page 1 7 }).state

def releasePending : State :=
  (prepare protectedState .release (.release 0 0)).state

def releaseMismatchRejected : State :=
  (acknowledge releasePending { ticket := 1, effect := .page 1 7 }).state

def released : State :=
  (acknowledge releaseMismatchRejected { ticket := 1, effect := .flush }).state

def staleReleaseRejected : State :=
  (prepare released .release (.release 0 0)).state

def destroyPending : State :=
  (prepare staleReleaseRejected .destroy (.destroy 0 1)).state

def destroyed : State :=
  (acknowledge destroyPending { ticket := 2, effect := .space 1 }).state

def switchPending : State :=
  (prepare destroyed .switch (.switch 2)).state

def switched : State :=
  (acknowledge switchPending { ticket := 3, effect := .flush }).state

def reused : State :=
  (publishReuse switched).state

theorem canonical_effects :
    (prepare initial .protect (.protect 1 1 7 { read := true })).accepted = false ∧
    (prepare initial .protect (.protect 1 1 7 { read := true })).effect = .none ∧
    (prepare wrongOwnerRejected .protect
        (.protect 0 1 7 { read := true })).effect = .page 1 7 ∧
    (acknowledge protectPending { ticket := 0, effect := .space 1 }).accepted = false ∧
    (acknowledge protectMismatchRejected
        { ticket := 0, effect := .page 1 7 }).accepted = true ∧
    (prepare protectedState .release (.release 0 0)).effect = .flush ∧
    (acknowledge releasePending
        { ticket := 1, effect := .page 1 7 }).accepted = false ∧
    (acknowledge releaseMismatchRejected
        { ticket := 1, effect := .flush }).accepted = true ∧
    (prepare released .release (.release 0 0)).accepted = false ∧
    (prepare released .release (.release 0 0)).effect = .none ∧
    (prepare staleReleaseRejected .destroy (.destroy 0 1)).effect = .space 1 ∧
    (acknowledge destroyPending
        { ticket := 2, effect := .space 1 }).accepted = true ∧
    (prepare destroyed .switch (.switch 2)).effect = .flush ∧
    (acknowledge switchPending
        { ticket := 3, effect := .flush }).accepted = true ∧
    (publishReuse switched).accepted = true := by
  native_decide

/-- Preparing the canonical unmap cannot expose its logical successor before
the required page invalidation is acknowledged. -/
theorem canonical_unmap_pending_retains_published :
    unmapPending.published = initial.published :=
  prepare_retains_published initial .unmap (.unmap 0 1 7)

/-- The exact acknowledgement removes both the authoritative mapping and
cached translation for the accepted unmap. -/
theorem canonical_unmap_publication_order :
    (prepare initial .unmap (.unmap 0 1 7)).accepted = true ∧
    (prepare initial .unmap (.unmap 0 1 7)).effect = .page 1 7 ∧
    unmapPending.pending.isSome = true ∧
    unmapPending.published.virtual.mappings 1 7 =
      some { object := 10, permissions := { read := true, write := true } } ∧
    (acknowledge unmapPending
      { ticket := 0, effect := .page 1 7 }).accepted = true ∧
    unmappedState.pending.isNone = true ∧
    unmappedState.published.virtual.mappings 1 7 = none ∧
    TLB.lookup unmappedState.published.entries
      { addressSpace := 1, page := 7 } StaleTranslation.ctx = none := by
  native_decide

/-- The canonical round trip publishes neither root switch until its own fresh
flush ticket is acknowledged; the second acknowledgement restores root 1 and
cannot be authorized by the first switch's completion. -/
theorem canonical_switch_away_back_publication_order :
    (prepare initial .switch (.switch 2)).accepted = true ∧
    (prepare initial .switch (.switch 2)).effect = .flush ∧
    switchAwayPending.published.active = initial.published.active ∧
    (acknowledge switchAwayPending
      { ticket := 0, effect := .flush }).accepted = true ∧
    switchedAway.published.active = some 2 ∧
    (prepare switchedAway .switch (.switch 1)).effect = .flush ∧
    switchBackPending.published.active = some 2 ∧
    switchBackPending.pending.map (·.ticket) = some 1 ∧
    (acknowledge switchBackPending
      { ticket := 0, effect := .flush }).accepted = false ∧
    (acknowledge switchBackPending
      { ticket := 0, effect := .flush }).effect = .none ∧
    (acknowledge switchBackPending
      { ticket := 1, effect := .flush }).accepted = true ∧
    switchedBack.published.active = some 1 ∧
    switchedBack.pending.isNone = true := by
  native_decide

/-- The release and root-switch stages both require `.flush`, but the release
completion's old ticket cannot publish the later switch successor. -/
theorem canonical_release_ack_cannot_splice_switch :
    (acknowledge switchPending { ticket := 1, effect := .flush }).accepted = false ∧
    (acknowledge switchPending { ticket := 1, effect := .flush }).state =
      switchPending ∧
    (acknowledge switchPending { ticket := 1, effect := .flush }).effect = .none := by
  have hrejected :
      (acknowledge switchPending { ticket := 1, effect := .flush }).accepted =
        false := by
    native_decide
  exact ⟨hrejected,
    acknowledge_rejected_inert switchPending { ticket := 1, effect := .flush }
      hrejected⟩

theorem canonical_retirement_and_reuse_order :
    protectPending.published.virtual.mappings 1 7 =
        some { object := 10, permissions := { read := true, write := true } } ∧
    protectedState.published.virtual.mappings 1 7 =
        some { object := 10, permissions := { read := true, write := false } } ∧
    releasePending.published.virtual.memory.binding 10 = some 4 ∧
    released.published.virtual.memory.binding 10 = none ∧
    destroyPending.published.virtual.owner 1 = some 0 ∧
    destroyed.published.virtual.owner 1 = none ∧
    switched.releaseAcknowledged = true ∧
    switched.destroyAcknowledged = true ∧
    reused.published.virtual.memory.binding 11 = some 4 ∧
    reused.published.virtual.mappings 1 7 = none ∧
    (TLB.access reused.published 7 StaleTranslation.ctx).isOk = false := by
  native_decide

end LeanOS.InvalidationPublication
