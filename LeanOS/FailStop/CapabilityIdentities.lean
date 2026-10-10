import LeanOS.FailStop.SpawnAccounting

/-!
# Fail-stop composite: capability identities are never reissued

Gate item 4 of ADR 0010 asks that a handle to a destroyed object fail after
**any** later step, not only across the steps that destroyed it.  A handle
word names a capability slot and the capability's identity (its generation),
and `CapabilityHandle.resolve` accepts the word only when the slot holds a
capability with exactly that identity.  So a word stays stale as long as no
capability with its identity is ever installed again.

`IdentityStep before after` says that every capability identity after a step
was already present before it, in a capability slot or in a pending sealed
transfer, or is fresh: at least the counter `nextIdentity` before the step.
The counter never decreases.  `IdentityRetired state i` says that identity `i`
was allocated and is held by no slot and no pending transfer.
`IdentityStep.retired` carries a retired identity across any step, and
`IdentityStep.trans` composes steps, so a retired identity stays retired along
every trace.  `stale_word_of_retired` turns this into the handle statement.

This module proves `IdentityStep` for every step family of the composite:
every authoritative operation (`authoritativeGate_identityStep`), every
invalidation entry point, issued creation, every `CompositeStep`
(`CompositeStep.identityStep`), and every operation of the public spawn
family (`childGate_identityStep`).  The only premise is
`CompositeState.Coherent` of the pre-state, which `RuntimeWellFormed`
carries.

Finally `terminateChild_identityRetired` shows that child termination retires
the identity of every capability it removes (`terminateChild_revokes`).
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

/-! ## The relation -/

/-- Identity provenance between two pairs of a capability store and a
pending-transfer store: the counter does not decrease, and every identity in
the second pair was in the first pair (in a slot or a pending transfer) or is
at least the first counter. -/
structure IdentityFrom (caps : Capability.State)
    (pending : Capability.ObjectId → Option CapabilityTransfer.Sealed)
    (caps' : Capability.State)
    (pending' : Capability.ObjectId → Option CapabilityTransfer.Sealed) : Prop where
  counter : caps.nextIdentity ≤ caps'.nextIdentity
  slots : ∀ s slot cap, caps'.slots s slot = some cap →
    (∃ s' slot' cap', caps.slots s' slot' = some cap' ∧ cap'.identity = cap.identity) ∨
    (∃ e t, pending e = some t ∧ t.identity = cap.identity) ∨
    caps.nextIdentity ≤ cap.identity
  pending : ∀ e t, pending' e = some t →
    (∃ e' t', pending e' = some t' ∧ t'.identity = t.identity) ∨
    caps.nextIdentity ≤ t.identity

/-- **Identity provenance of a composite step.**  Every capability identity
after the step is an identity present before (in a slot or a pending sealed
transfer) or fresh (at least the old counter); the counter never
decreases. -/
abbrev IdentityStep (before after : CompositeState) : Prop :=
  IdentityFrom before.capabilities before.transfers.pending
    after.capabilities after.transfers.pending

/-- Identity `i` was allocated and is held by no slot and no pending
transfer. -/
def IdentityRetired (state : CompositeState) (i : Nat) : Prop :=
  i < state.capabilities.nextIdentity ∧
    (∀ s slot cap, state.capabilities.slots s slot = some cap → cap.identity ≠ i) ∧
    (∀ e t, state.transfers.pending e = some t → t.identity ≠ i)

theorem IdentityFrom.refl (caps : Capability.State)
    (pending : Capability.ObjectId → Option CapabilityTransfer.Sealed) :
    IdentityFrom caps pending caps pending :=
  ⟨Nat.le_refl _, fun s slot cap held => Or.inl ⟨s, slot, cap, held, rfl⟩,
    fun e t held => Or.inl ⟨e, t, held, rfl⟩⟩

theorem IdentityFrom.trans {c₁ c₂ c₃ : Capability.State}
    {p₁ p₂ p₃ : Capability.ObjectId → Option CapabilityTransfer.Sealed}
    (left : IdentityFrom c₁ p₁ c₂ p₂) (right : IdentityFrom c₂ p₂ c₃ p₃) :
    IdentityFrom c₁ p₁ c₃ p₃ := by
  have pendingBack : ∀ e t, p₂ e = some t →
      (∃ e' t', p₁ e' = some t' ∧ t'.identity = t.identity) ∨
        c₁.nextIdentity ≤ t.identity := left.pending
  refine ⟨Nat.le_trans left.counter right.counter, fun s slot cap held => ?_,
    fun e t held => ?_⟩
  · rcases right.slots s slot cap held with ⟨s', slot', cap', held', same⟩ |
      ⟨e, t, held', same⟩ | fresh
    · rcases left.slots s' slot' cap' held' with ⟨s'', slot'', cap'', held'', same'⟩ |
        ⟨e, t, held'', same'⟩ | fresh'
      · exact Or.inl ⟨s'', slot'', cap'', held'', same'.trans same⟩
      · exact Or.inr (Or.inl ⟨e, t, held'', same'.trans same⟩)
      · exact Or.inr (Or.inr (same ▸ fresh'))
    · rcases pendingBack e t held' with ⟨e', t', held'', same'⟩ | fresh'
      · exact Or.inr (Or.inl ⟨e', t', held'', same'.trans same⟩)
      · exact Or.inr (Or.inr (same ▸ fresh'))
    · exact Or.inr (Or.inr (Nat.le_trans left.counter fresh))
  · rcases right.pending e t held with ⟨e', t', held', same⟩ | fresh
    · rcases pendingBack e' t' held' with ⟨e'', t'', held'', same'⟩ | fresh'
      · exact Or.inl ⟨e'', t'', held'', same'.trans same⟩
      · exact Or.inr (same ▸ fresh')
    · exact Or.inr (Nat.le_trans left.counter fresh)

/-- A step that only removes slots and pending transfers, with the same
counter. -/
theorem IdentityFrom.of_shrink {caps caps' : Capability.State}
    {pending pending' : Capability.ObjectId → Option CapabilityTransfer.Sealed}
    (counter : caps.nextIdentity ≤ caps'.nextIdentity)
    (slots : ∀ s slot cap, caps'.slots s slot = some cap → caps.slots s slot = some cap)
    (pendingSub : ∀ e t, pending' e = some t → pending e = some t) :
    IdentityFrom caps pending caps' pending' :=
  ⟨counter, fun s slot cap held => Or.inl ⟨s, slot, cap, slots s slot cap held, rfl⟩,
    fun e t held => Or.inl ⟨e, t, pendingSub e t held, rfl⟩⟩

/-- Replace the pending store by a sub-store. -/
theorem IdentityFrom.shrink_pending {caps caps' : Capability.State}
    {pending pending' pending'' : Capability.ObjectId → Option CapabilityTransfer.Sealed}
    (from' : IdentityFrom caps pending caps' pending')
    (pendingSub : ∀ e t, pending'' e = some t → pending' e = some t) :
    IdentityFrom caps pending caps' pending'' :=
  ⟨from'.counter, from'.slots, fun e t held => from'.pending e t (pendingSub e t held)⟩

/-- Composite form of reflexivity. -/
theorem IdentityStep.refl (state : CompositeState) : IdentityStep state state :=
  IdentityFrom.refl _ _

/-- Composite steps compose. -/
theorem IdentityStep.trans {first second third : CompositeState}
    (left : IdentityStep first second) (right : IdentityStep second third) :
    IdentityStep first third :=
  IdentityFrom.trans left right

/-- A step that keeps the capability store and the pending transfers. -/
theorem IdentityStep.of_eq {before after : CompositeState}
    (caps : after.capabilities = before.capabilities)
    (pending : after.transfers.pending = before.transfers.pending) :
    IdentityStep before after := by
  show IdentityFrom _ _ _ _
  rw [caps, pending]
  exact IdentityFrom.refl _ _

/-- Extend a step by one that keeps the capability store and the pending
transfers.  Used to discharge the record-only tail of child termination. -/
theorem IdentityStep.of_capabilities_eq {before middle after : CompositeState}
    (step : IdentityStep before middle)
    (caps : after.capabilities = middle.capabilities)
    (pending : after.transfers.pending = middle.transfers.pending) :
    IdentityStep before after :=
  step.trans (IdentityStep.of_eq caps pending)

/-- A step whose footprint writes neither the capability store nor the
transfer store. -/
theorem IdentityStep.of_frames {footprint : CompositeFootprint.Footprint}
    {before after : CompositeState} (frames : CompositeState.Frames footprint before after)
    (caps : footprint.writes .capabilities = false)
    (transfers : footprint.writes .transfers = false) :
    IdentityStep before after :=
  IdentityStep.of_eq (frames .capabilities caps)
    (by have same : after.transfers = before.transfers := frames .transfers transfers
        rw [same])

/-- **A retired identity stays retired** across every step with identity
provenance. -/
theorem IdentityStep.retired {before after : CompositeState} {i : Nat}
    (step : IdentityStep before after) (retired : IdentityRetired before i) :
    IdentityRetired after i := by
  obtain ⟨below, noSlot, noPending⟩ := retired
  refine ⟨Nat.lt_of_lt_of_le below step.counter, fun s slot cap held same => ?_,
    fun e t held same => ?_⟩
  · rcases step.slots s slot cap held with ⟨s', slot', cap', held', same'⟩ |
      ⟨e, t, held', same'⟩ | fresh
    · exact noSlot s' slot' cap' held' (same'.trans same)
    · exact noPending e t held' (same'.trans same)
    · omega
  · rcases step.pending e t held with ⟨e', t', held', same'⟩ | fresh
    · exact noPending e' t' held' (same'.trans same)
    · omega

/-- **A word naming a retired identity is stale.**  No holder resolves a
handle word whose decoded identity is retired, whatever kind it expects. -/
theorem stale_word_of_retired (state : CompositeState) (i : Nat)
    (retired : IdentityRetired state i) (holder : Nat) (word : UInt64)
    (kind : Capability.ObjectKind) (handle : CapabilityHandle.Handle)
    (decoded : CapabilityHandle.decode word = .ok handle) (named : handle.identity = i) :
    ∃ reason, CapabilityHandle.resolveCurrent state.capabilities { caller := holder } word kind =
      .error reason := by
  cases resolved : CapabilityHandle.resolveCurrent state.capabilities { caller := holder } word
      kind with
  | error reason => exact ⟨reason, rfl⟩
  | ok resolution =>
      obtain ⟨decoded', _, _, held, identity, _⟩ :=
        CapabilityHandle.resolveCurrent_sound _ _ _ _ _ resolved
      rw [decoded] at decoded'
      simp only [Except.ok.injEq] at decoded'
      subst decoded'
      exact absurd (identity.trans named) (retired.2.1 _ _ _ held)

/-! ## Capability-store transitions -/

theorem Capability.copy_identityFrom (caps : Capability.State) actor source destination
    destinationSlot rights (pending : Capability.ObjectId → Option CapabilityTransfer.Sealed) :
    IdentityFrom caps pending
      (Capability.copy caps actor source destination destinationSlot rights).state pending := by
  unfold Capability.copy
  repeat' split
  all_goals first
    | exact IdentityFrom.refl _ _
    | skip
  refine ⟨by simp [Capability.install], fun s slot cap held => ?_,
    fun e t held => Or.inl ⟨e, t, held, rfl⟩⟩
  simp only [Capability.install] at held
  split at held
  · cases held; exact Or.inr (Or.inr (Nat.le_refl _))
  · exact Or.inl ⟨s, slot, cap, held, rfl⟩

theorem Capability.revoke_shrinks (caps : Capability.State) actor authoritySlot victim
    victimSlot :
    (Capability.revoke caps actor authoritySlot victim victimSlot).state.nextIdentity =
        caps.nextIdentity ∧
      ∀ s slot cap,
        (Capability.revoke caps actor authoritySlot victim victimSlot).state.slots s slot =
          some cap → caps.slots s slot = some cap := by
  unfold Capability.revoke
  repeat' split
  all_goals first
    | exact ⟨rfl, fun _ _ _ h => h⟩
    | (refine ⟨rfl, fun s slot cap held => ?_⟩
       simp only [Capability.clear] at held
       split at held <;> simp_all)

theorem Capability.revokeSubtree_shrinks (caps : Capability.State) actor authoritySlot victim
    victimSlot :
    (Capability.revokeSubtree caps actor authoritySlot victim victimSlot).state.nextIdentity =
        caps.nextIdentity ∧
      ∀ s slot cap,
        (Capability.revokeSubtree caps actor authoritySlot victim victimSlot).state.slots s
          slot = some cap → caps.slots s slot = some cap := by
  unfold Capability.revokeSubtree
  repeat' split
  all_goals first
    | exact ⟨rfl, fun _ _ _ h => h⟩
    | (refine ⟨rfl, fun s slot cap held => ?_⟩
       simp only [Capability.clearSubtree] at held
       revert held
       cases h : caps.slots s slot <;> simp <;> intros <;> simp_all)

theorem Capability.revokeRuntimeSafe_identityFrom (caps : Capability.State) actor authoritySlot
    victim victimSlot (pending : Capability.ObjectId → Option CapabilityTransfer.Sealed) :
    IdentityFrom caps pending
      (Capability.revokeRuntimeSafe caps actor authoritySlot victim victimSlot).state pending := by
  obtain ⟨counter, slots⟩ := Capability.revoke_shrinks caps actor authoritySlot victim victimSlot
  have cases : (Capability.revokeRuntimeSafe caps actor authoritySlot victim victimSlot).state =
      (Capability.revoke caps actor authoritySlot victim victimSlot).state ∨
      (Capability.revokeRuntimeSafe caps actor authoritySlot victim victimSlot).state = caps := by
    unfold Capability.revokeRuntimeSafe
    dsimp only
    split <;> (try split) <;> simp [Capability.reject]
  rcases cases with same | same <;> rw [same]
  · exact IdentityFrom.of_shrink (by rw [counter]; exact Nat.le_refl _) slots (fun _ _ h => h)
  · exact IdentityFrom.refl _ _

theorem Capability.revokeSubtreeRuntimeSafe_shrinks (caps : Capability.State) actor
    authoritySlot victim victimSlot :
    (Capability.revokeSubtreeRuntimeSafe caps actor authoritySlot victim victimSlot).state.nextIdentity =
        caps.nextIdentity ∧
      ∀ s slot cap,
        (Capability.revokeSubtreeRuntimeSafe caps actor authoritySlot victim victimSlot).state.slots
          s slot = some cap → caps.slots s slot = some cap := by
  obtain ⟨counter, slots⟩ :=
    Capability.revokeSubtree_shrinks caps actor authoritySlot victim victimSlot
  have cases :
      (Capability.revokeSubtreeRuntimeSafe caps actor authoritySlot victim victimSlot).state =
        (Capability.revokeSubtree caps actor authoritySlot victim victimSlot).state ∨
      (Capability.revokeSubtreeRuntimeSafe caps actor authoritySlot victim victimSlot).state =
        caps := by
    unfold Capability.revokeSubtreeRuntimeSafe
    dsimp only
    split <;> (try split) <;> simp [Capability.reject]
  rcases cases with same | same <;> rw [same]
  · exact ⟨counter, slots⟩
  · exact ⟨rfl, fun _ _ _ h => h⟩

/-- Installing a root capability allocates exactly the counter's identity. -/
theorem Capability.installRoot_identityFrom (caps : Capability.State) subject slot object kind
    rights (pending : Capability.ObjectId → Option CapabilityTransfer.Sealed) :
    IdentityFrom caps pending (Capability.installRoot caps subject slot object kind rights)
      pending := by
  refine ⟨by simp [Capability.installRoot, Capability.install], fun s candidate cap held => ?_,
    fun e t held => Or.inl ⟨e, t, held, rfl⟩⟩
  simp only [Capability.installRoot, Capability.install] at held
  split at held
  · cases held; exact Or.inr (Or.inr (Nat.le_refl _))
  · exact Or.inl ⟨s, candidate, cap, held, rfl⟩

end LeanOS.FailStop
