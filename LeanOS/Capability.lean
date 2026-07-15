/-!
# Capability authority model

This executable, sequential reference model defines authority as a capability
in a subject's slot granting a right over an object. `copy` requires `grant`
and a rights subset; `revoke` removes one named capability and requires
`revoke` over the same object. `revokeSubtree` instead follows explicit,
bounded derivation metadata and removes one selected lineage atomically. Every
rejection preserves the complete state.

Object lifetimes, concurrency, information flow, timing and covert channels
are outside the model.
-/
namespace LeanOS.Capability

abbrev SubjectId := Nat
abbrev ObjectId := Nat
abbrev SlotId := Nat

inductive ObjectKind where | memory | addressSpace | endpoint
  deriving DecidableEq, Repr

inductive Right where | read | write | send | receive | grant | revoke
  deriving DecidableEq, Repr

structure Rights where
  read : Bool := false
  write : Bool := false
  send : Bool := false
  receive : Bool := false
  grant : Bool := false
  revoke : Bool := false
  deriving DecidableEq, Repr

def noRights : Rights := {}
def oneRight (wanted : Right) : Rights :=
  match wanted with
  | .read => { read := true }
  | .write => { write := true }
  | .send => { send := true }
  | .receive => { receive := true }
  | .grant => { grant := true }
  | .revoke => { revoke := true }
def allRights : Rights := { read := true, write := true, grant := true, revoke := true }
def permits (rights : Rights) : Right → Bool
  | .read => rights.read | .write => rights.write
  | .send => rights.send | .receive => rights.receive
  | .grant => rights.grant | .revoke => rights.revoke
def hasRight (rights : Rights) (right : Right) : Prop := permits rights right = true
def nonemptyRights (rights : Rights) : Bool :=
  rights.read || rights.write || rights.send || rights.receive || rights.grant || rights.revoke
def rightsSubset (requested source : Rights) : Bool :=
  (!requested.read || source.read) && (!requested.write || source.write) &&
    (!requested.send || source.send) && (!requested.receive || source.receive) &&
    (!requested.grant || source.grant) && (!requested.revoke || source.revoke)

structure Capability where
  object : ObjectId
  kind : ObjectKind
  rights : Rights
  /-- Never-reused identity within one capability state. -/
  identity : Nat := 0
  /-- The capability copied to create this capability; roots have no parent. -/
  parent : Option Nat := none
  deriving DecidableEq, Repr

structure State where
  /-- First identity not yet allocated by `copy`. Root constructors allocate below it. -/
  nextIdentity : Nat := 1
  /-- Metadata for identities allocated by delegation. Entries are never reused. -/
  derivations : Nat → Option (Option Nat × ObjectId × ObjectKind × Rights) := fun _ => none
  subjects : SubjectId → Bool
  objects : ObjectId → Bool
  kinds : ObjectId → Option ObjectKind
  slots : SubjectId → SlotId → Option Capability

abbrev Derivation := Option Nat × ObjectId × ObjectKind × Rights

def rightsValid : ObjectKind → Rights → Bool
  | .memory, rights => (!rights.send && !rights.receive) && nonemptyRights rights
  | .addressSpace, rights => (!rights.read && !rights.write && !rights.send && !rights.receive) &&
      (rights.grant || rights.revoke)
  | .endpoint, rights => (!rights.read && !rights.write) &&
      (rights.send || rights.receive || rights.grant || rights.revoke)

inductive LookupOutcome where
  | invalidSubject | staleSlot | found (capability : Capability)
  deriving DecidableEq, Repr

def lookup (state : State) (subject : SubjectId) (slot : SlotId) : LookupOutcome :=
  if state.subjects subject then
    match state.slots subject slot with
    | some capability => .found capability
    | none => .staleSlot
  else .invalidSubject

def SlotsWellFormed (state : State) : Prop :=
  ∀ subject slot capability, state.slots subject slot = some capability →
    state.subjects subject = true ∧ state.objects capability.object = true ∧
      state.kinds capability.object = some capability.kind ∧
      rightsValid capability.kind capability.rights = true ∧
      capability.identity < state.nextIdentity ∧
      state.derivations capability.identity =
        some (capability.parent, capability.object, capability.kind, capability.rights) ∧
      match capability.parent with
      | none => True
      | some parentIdentity => parentIdentity < capability.identity ∧
          ∃ parentParent parentRights,
            state.derivations parentIdentity =
              some (parentParent, capability.object, capability.kind, parentRights) ∧
            rightsSubset capability.rights parentRights = true

/-- The append-only derivation history agrees on object and kind, attenuates
rights at every parent edge, and orders every parent before its child. The
strict identity order is the construction invariant ruling out cycles. -/
def DerivationsWellFormed (state : State) : Prop :=
  ∀ identity parent object kind rights,
    state.derivations identity = some (parent, object, kind, rights) →
      identity < state.nextIdentity ∧ match parent with
      | none => True
      | some parentIdentity => parentIdentity < identity

/-- No two live slots can name the same capability identity. -/
def LiveIdentitiesUnique (state : State) : Prop :=
  ∀ subject slot capability otherSubject otherSlot otherCapability,
    state.slots subject slot = some capability →
    state.slots otherSubject otherSlot = some otherCapability →
    capability.identity = otherCapability.identity →
    subject = otherSubject ∧ slot = otherSlot

def WellFormed (state : State) : Prop :=
  SlotsWellFormed state ∧ DerivationsWellFormed state ∧ LiveIdentitiesUnique state

/-- A subject has authority exactly when a slot grants the object/right pair. -/
def HasAuthority (state : State) (subject : SubjectId) (object : ObjectId)
    (right : Right) : Prop :=
  ∃ slot capability, state.slots subject slot = some capability ∧
    capability.object = object ∧ hasRight capability.rights right

inductive Denial where
  | invalidSubject | staleSlot | occupiedSlot | emptyRights
  | missingGrant | rightsNotSubset | missingRevoke | objectMismatch | kindMismatch
  | invalidRights
  deriving DecidableEq, Repr

inductive Result where
  | accepted | rejected (reason : Denial)
  deriving DecidableEq, Repr

structure Outcome where
  state : State
  result : Result

/-- Resolve a capability only when its recorded kind and the live registry agree
with the operation's expected kind. This is the common typed-dispatch boundary. -/
def authorizeKind (state : State) (subject : SubjectId) (slot : SlotId)
    (expected : ObjectKind) : Except Denial Capability :=
  match lookup state subject slot with
  | .invalidSubject => .error .invalidSubject
  | .staleSlot => .error .staleSlot
  | .found capability =>
      if capability.kind != expected then .error .kindMismatch
      else if state.objects capability.object != true then .error .staleSlot
      else if state.kinds capability.object != some expected then .error .kindMismatch
      else .ok capability

def install (state : State) (subject : SubjectId) (slot : SlotId)
    (capability : Capability) : State :=
  { state with slots := fun candidate candidateSlot =>
      if candidate = subject ∧ candidateSlot = slot then some capability
      else state.slots candidate candidateSlot }

/-- Allocate and record a fresh root identity while installing its capability.
Lifecycle operations use this instead of relying on the structure default. -/
def installRoot (state : State) (subject : SubjectId) (slot : SlotId)
    (object : ObjectId) (kind : ObjectKind) (rights : Rights) : State :=
  let identity := state.nextIdentity
  install
    { state with
      nextIdentity := identity + 1
      derivations := fun candidate =>
        if candidate = identity then some (none, object, kind, rights)
        else state.derivations candidate }
    subject slot { object, kind, rights, identity, parent := none }

def clear (state : State) (subject : SubjectId) (slot : SlotId) : State :=
  { state with slots := fun candidate candidateSlot =>
      if candidate = subject ∧ candidateSlot = slot then none
      else state.slots candidate candidateSlot }

def reject (state : State) (reason : Denial) : Outcome :=
  { state := state, result := .rejected reason }

theorem lookup_found_slot (state : State) (subject : SubjectId) (slot : SlotId)
    (capability : Capability) (hfound : lookup state subject slot = .found capability) :
    state.slots subject slot = some capability := by
  simp only [lookup] at hfound
  split at hfound
  · split at hfound <;> simp_all
  · simp_all

/-- Delegate a nonempty subset of one capability into an empty slot. -/
def copy (state : State) (actor : SubjectId) (source : SlotId)
    (destination : SubjectId) (destinationSlot : SlotId)
    (requested : Rights) : Outcome :=
  match lookup state actor source with
  | .invalidSubject => reject state .invalidSubject
  | .staleSlot => reject state .staleSlot
  | .found capability =>
      if state.subjects destination != true then reject state .invalidSubject
      else if (state.slots destination destinationSlot).isSome then
        reject state .occupiedSlot
      else if rightsValid capability.kind requested then
        if capability.rights.grant then
          if rightsSubset requested capability.rights then
            { state := install
                { state with
                  nextIdentity := state.nextIdentity + 1
                  derivations := fun identity =>
                    if identity = state.nextIdentity then
                      some (some capability.identity, capability.object,
                        capability.kind, requested)
                    else state.derivations identity }
                destination destinationSlot
                { identity := state.nextIdentity, parent := some capability.identity,
                  object := capability.object, kind := capability.kind, rights := requested },
              result := .accepted }
          else reject state .rightsNotSubset
        else reject state .missingGrant
      else reject state .emptyRights

/-- Directly remove one capability when the actor has revoke over its object. -/
def revoke (state : State) (actor : SubjectId) (authoritySlot : SlotId)
    (victim : SubjectId) (victimSlot : SlotId) : Outcome :=
  match lookup state actor authoritySlot with
  | .invalidSubject => reject state .invalidSubject
  | .staleSlot => reject state .staleSlot
  | .found authority =>
      if authority.rights.revoke then
        match lookup state victim victimSlot with
        | .invalidSubject => reject state .invalidSubject
        | .staleSlot => reject state .staleSlot
        | .found target =>
            if authority.object = target.object && authority.kind = target.kind then
              { state := clear state victim victimSlot, result := .accepted }
            else reject state .objectMismatch
      else reject state .missingRevoke

/-- Follow at most `fuel` recorded parent edges. The explicit bound makes
revocation total even for malformed external states. -/
def descendsFrom (state : State) (candidate ancestor : Nat) : Nat → Bool
  | 0 => candidate == ancestor
  | fuel + 1 =>
      if candidate == ancestor then true
      else match state.derivations candidate with
        | some (some parent, _, _, _) => descendsFrom state parent ancestor fuel
        | _ => false

def clearSubtree (state : State) (identity : Nat) : State :=
  { state with slots := fun subject slot =>
      match state.slots subject slot with
      | some capability =>
          if descendsFrom state capability.identity identity state.nextIdentity then none
          else some capability
      | none => none }

theorem clearSubtree_slot_survives (state : State) (identity : Nat)
    (subject : SubjectId) (slot : SlotId) (capability : Capability) :
    (clearSubtree state identity).slots subject slot = some capability →
      state.slots subject slot = some capability := by
  simp only [clearSubtree]
  split
  · rename_i found hfound
    split
    · simp
    · rename_i hsurvives
      intro heq
      cases heq
      exact hfound
  · simp

theorem clearSubtree_removes_descendant (state : State) (identity : Nat)
    (subject : SubjectId) (slot : SlotId) (capability : Capability)
    (hslot : state.slots subject slot = some capability)
    (hdescendant : descendsFrom state capability.identity identity state.nextIdentity = true) :
    (clearSubtree state identity).slots subject slot = none := by
  simp [clearSubtree, hslot, hdescendant]

theorem clearSubtree_authority_subset (state : State) (identity : Nat)
    (subject : SubjectId) (object : ObjectId) (right : Right)
    (hauthority : HasAuthority (clearSubtree state identity) subject object right) :
    HasAuthority state subject object right := by
  rcases hauthority with ⟨slot, capability, hslot, hobject, hright⟩
  have hold := clearSubtree_slot_survives state identity subject slot capability hslot
  exact ⟨slot, capability, hold, hobject, hright⟩

theorem clear_preserves_wellFormed (state : State) (subject : SubjectId)
    (slot : SlotId) (hstate : WellFormed state) :
    WellFormed (clear state subject slot) := by
  rcases hstate with ⟨hslots, hhistory, hunique⟩
  refine ⟨?_, ?_, ?_⟩
  · intro candidate candidateSlot capability hslot
    apply hslots candidate candidateSlot capability
    by_cases htarget : candidate = subject ∧ candidateSlot = slot
    · simp [clear, htarget] at hslot
    · simpa [clear, htarget] using hslot
  · simpa [DerivationsWellFormed, clear] using hhistory
  · intro left leftSlot leftCap right rightSlot rightCap hleft hright hid
    apply hunique left leftSlot leftCap right rightSlot rightCap
    · by_cases htarget : left = subject ∧ leftSlot = slot
      · simp [clear, htarget] at hleft
      · simpa [clear, htarget] using hleft
    · by_cases htarget : right = subject ∧ rightSlot = slot
      · simp [clear, htarget] at hright
      · simpa [clear, htarget] using hright
    · exact hid

theorem clearSubtree_preserves_wellFormed (state : State) (identity : Nat)
    (hstate : WellFormed state) : WellFormed (clearSubtree state identity) := by
  rcases hstate with ⟨hslots, hhistory, hunique⟩
  refine ⟨?_, ?_, ?_⟩
  · intro subject slot capability hslot
    exact hslots subject slot capability
      (clearSubtree_slot_survives state identity subject slot capability hslot)
  · simpa [DerivationsWellFormed, clearSubtree] using hhistory
  · intro left leftSlot leftCap right rightSlot rightCap hleft hright hid
    exact hunique left leftSlot leftCap right rightSlot rightCap
      (clearSubtree_slot_survives state identity left leftSlot leftCap hleft)
      (clearSubtree_slot_survives state identity right rightSlot rightCap hright) hid

/-- Atomically remove the selected capability and every recorded descendant.
The authority and selected root are resolved before mutation, so every denial
preserves the complete state. -/
def revokeSubtree (state : State) (actor : SubjectId) (authoritySlot : SlotId)
    (victim : SubjectId) (victimSlot : SlotId) : Outcome :=
  match lookup state actor authoritySlot with
  | .invalidSubject => reject state .invalidSubject
  | .staleSlot => reject state .staleSlot
  | .found authority =>
      if authority.rights.revoke then
        match lookup state victim victimSlot with
        | .invalidSubject => reject state .invalidSubject
        | .staleSlot => reject state .staleSlot
        | .found target =>
            if authority.object = target.object && authority.kind = target.kind then
              { state := clearSubtree state target.identity, result := .accepted }
            else reject state .objectMismatch
      else reject state .missingRevoke

theorem clear_authority_subset (state : State) (subject : SubjectId) (slot : SlotId)
    (candidate : SubjectId) (object : ObjectId) (right : Right)
    (hauthority : HasAuthority (clear state subject slot) candidate object right) :
    HasAuthority state candidate object right := by
  rcases hauthority with ⟨candidateSlot, capability, hslot, hobject, hright⟩
  by_cases htarget : candidate = subject ∧ candidateSlot = slot
  · simp [clear, htarget] at hslot
  · exact ⟨candidateSlot, capability, by simpa [clear, htarget] using hslot,
      hobject, hright⟩

theorem install_no_authority_amplification (state : State)
    (actor destination : SubjectId) (destinationSlot : SlotId)
    (capability : Capability) (sourceRights : Rights)
    (hsubset : rightsSubset capability.rights sourceRights = true)
    (hactor : ∀ right, hasRight sourceRights right →
      HasAuthority state actor capability.object right)
    (candidate : SubjectId) (object : ObjectId) (right : Right)
    (hauthority : HasAuthority (install state destination destinationSlot capability)
      candidate object right) :
    HasAuthority state candidate object right ∨ HasAuthority state actor object right := by
  rcases hauthority with ⟨slot, found, hslot, hobject, hright⟩
  by_cases htarget : candidate = destination ∧ slot = destinationSlot
  · have hfound : found = capability := by
      symm
      simpa [install, htarget] using hslot
    subst found
    right
    rw [hobject] at hactor
    apply hactor right
    cases right <;> simp_all [hasRight, permits, rightsSubset]
  · left
    exact ⟨slot, found, by simpa [install, htarget] using hslot, hobject, hright⟩

theorem copy_preserves_wellFormed (state : State) (actor : SubjectId)
    (source : SlotId) (destination : SubjectId) (destinationSlot : SlotId)
    (requested : Rights) (hstate : WellFormed state) :
    WellFormed (copy state actor source destination destinationSlot requested).state := by
  simp only [copy]
  split <;> try simp_all [reject]
  next capability hlookup =>
    split <;> try simp_all
    split <;> try simp_all
    split <;> try simp_all
    next hnonempty =>
      split <;> try simp_all
      split
      · rcases hstate with ⟨hslots, hhistory, hunique⟩
        have hsource := lookup_found_slot state actor source capability hlookup
        have hsourceValid := hslots actor source capability hsource
        refine ⟨?_, ?_, ?_⟩
        · intro subject slot found hslot
          by_cases htarget : subject = destination ∧ slot = destinationSlot
          · rcases htarget with ⟨rfl, rfl⟩
            have hfound : found =
                ({ identity := state.nextIdentity, parent := some capability.identity,
                   object := capability.object, kind := capability.kind,
                   rights := requested } : Capability) := by
              symm
              simpa [install] using hslot
            subst found
            refine ⟨by simpa [install] using ‹state.subjects subject = true›,
              hsourceValid.2.1, hsourceValid.2.2.1, by simpa using hnonempty,
              Nat.lt_succ_self _, ?_, ?_⟩
            · simp [install]
            · refine ⟨hsourceValid.2.2.2.2.1, ?_⟩
              exact ⟨capability.parent, capability.rights,
                by simpa [install, Nat.ne_of_lt hsourceValid.2.2.2.2.1] using
                  hsourceValid.2.2.2.2.2.1,
                by simpa using ‹rightsSubset requested capability.rights = true›⟩
          · have hold := hslots subject slot found (by simpa [install, htarget] using hslot)
            rcases hold with ⟨hsubject, hobject, hkind, hrights, hid, hentry, hedge⟩
            refine ⟨by simpa [install] using hsubject, hobject, hkind, hrights,
              Nat.lt_succ_of_lt hid, ?_, ?_⟩
            · simp [install, Nat.ne_of_lt hid]
              exact hentry
            · cases hparentEq : found.parent <;> simp only [hparentEq] at hedge ⊢
              rename_i parentIdentity
              rcases hedge with ⟨hparent, parentParent, parentRights, hpentry, hsubset⟩
              refine ⟨hparent, parentParent, parentRights, ?_, hsubset⟩
              simp [install, Nat.ne_of_lt (Nat.lt_trans hparent hid)]
              exact hpentry
        · intro identity parent object kind rights hentry
          by_cases hnew : identity = state.nextIdentity
          · subst identity
            simp [install] at hentry
            rcases hentry with ⟨rfl, rfl, rfl, rfl⟩
            exact ⟨Nat.lt_succ_self _, hsourceValid.2.2.2.2.1⟩
          · have hold := hhistory identity parent object kind rights (by
                simpa [install, hnew] using hentry)
            refine ⟨Nat.lt_succ_of_lt hold.1, ?_⟩
            cases parent with
            | none => trivial
            | some parentIdentity => exact hold.2
        · intro left leftSlot leftCap right rightSlot rightCap hleft hright hid
          by_cases hleftTarget : left = destination ∧ leftSlot = destinationSlot
          · by_cases hrightTarget : right = destination ∧ rightSlot = destinationSlot
            · exact ⟨hleftTarget.1.trans hrightTarget.1.symm,
                hleftTarget.2.trans hrightTarget.2.symm⟩
            · rcases hleftTarget with ⟨rfl, rfl⟩
              have hleftCap : leftCap =
                  (⟨capability.object, capability.kind, requested,
                    state.nextIdentity, some capability.identity⟩ : Capability) := by
                symm; simpa [install] using hleft
              subst leftCap
              have hrightOld := hslots right rightSlot rightCap
                (by simpa [install, hrightTarget] using hright)
              have heq : state.nextIdentity = rightCap.identity := by simpa using hid
              have hlt := hrightOld.2.2.2.2.1
              omega
          · by_cases hrightTarget : right = destination ∧ rightSlot = destinationSlot
            · rcases hrightTarget with ⟨rfl, rfl⟩
              have hrightCap : rightCap =
                  (⟨capability.object, capability.kind, requested,
                    state.nextIdentity, some capability.identity⟩ : Capability) := by
                symm; simpa [install] using hright
              subst rightCap
              have hleftOld := hslots left leftSlot leftCap
                (by simpa [install, hleftTarget] using hleft)
              have heq : leftCap.identity = state.nextIdentity := by simpa using hid
              have hlt := hleftOld.2.2.2.2.1
              omega
            · exact hunique left leftSlot leftCap right rightSlot rightCap
                (by simpa [install, hleftTarget] using hleft)
                (by simpa [install, hrightTarget] using hright) hid
      · simpa [reject] using hstate

theorem revoke_preserves_wellFormed (state : State) (actor : SubjectId)
    (authoritySlot : SlotId) (victim : SubjectId) (victimSlot : SlotId)
    (hstate : WellFormed state) :
    WellFormed (revoke state actor authoritySlot victim victimSlot).state := by
  simp only [revoke]
  split <;> try simp_all [reject]
  next authority hlookup =>
    split <;> try simp_all
    split <;> try simp_all
    next target hvictim =>
      split <;> try simp_all
      exact clear_preserves_wellFormed state victim victimSlot hstate

theorem revokeSubtree_preserves_wellFormed (state : State) (actor : SubjectId)
    (authoritySlot : SlotId) (victim : SubjectId) (victimSlot : SlotId)
    (hstate : WellFormed state) :
    WellFormed (revokeSubtree state actor authoritySlot victim victimSlot).state := by
  simp only [revokeSubtree]
  split <;> try simp_all [reject]
  next authority =>
    split <;> try simp_all
    split <;> try simp_all
    next target hvictim =>
      split <;> try simp_all
      exact clearSubtree_preserves_wellFormed state target.identity hstate

/-- Copy cannot create a right without pre-state authority provenance. -/
theorem copy_no_authority_amplification (state : State) (actor : SubjectId)
    (source : SlotId) (destination : SubjectId) (destinationSlot : SlotId)
    (requested : Rights) (candidate : SubjectId) (object : ObjectId)
    (right : Right)
    (hauthority : HasAuthority
      (copy state actor source destination destinationSlot requested).state
      candidate object right) :
    HasAuthority state candidate object right ∨ HasAuthority state actor object right := by
  simp only [copy] at hauthority
  split at hauthority <;> try simp_all [reject]
  next capability hlookup =>
    split at hauthority <;> try simp_all
    split at hauthority <;> try simp_all
    split at hauthority <;> try simp_all
    split at hauthority <;> try simp_all
    split at hauthority
    · have h := install_no_authority_amplification
        { state with nextIdentity := state.nextIdentity + 1 }
        actor destination destinationSlot
        { identity := state.nextIdentity, parent := some capability.identity,
          object := capability.object, kind := capability.kind, rights := requested }
        capability.rights
        (by simpa using ‹rightsSubset requested capability.rights = true›)
        (by
          intro granted hgranted
          have hslot := lookup_found_slot state actor source capability hlookup
          exact ⟨source, capability, hslot, rfl, hgranted⟩)
        candidate object right hauthority
      rcases h with h | h
      · left
        rcases h with ⟨slot, cap, hslot, rest⟩
        exact ⟨slot, cap, hslot, rest⟩
      · right
        rcases h with ⟨slot, cap, hslot, rest⟩
        exact ⟨slot, cap, hslot, rest⟩
    · try simp_all

theorem revoke_no_authority_amplification (state : State) (actor : SubjectId)
    (authoritySlot : SlotId) (victim : SubjectId) (victimSlot : SlotId)
    (candidate : SubjectId) (object : ObjectId) (right : Right)
    (hauthority : HasAuthority
      (revoke state actor authoritySlot victim victimSlot).state
      candidate object right) : HasAuthority state candidate object right := by
  simp only [revoke] at hauthority
  split at hauthority <;> try simp_all [reject]
  next authority hlookup =>
    split at hauthority <;> try simp_all
    split at hauthority <;> try simp_all
    next target hvictim =>
      split at hauthority
      · exact clear_authority_subset state victim victimSlot candidate object right hauthority
      · try simp_all

theorem copy_rejected_unchanged (state : State) (actor : SubjectId)
    (source : SlotId) (destination : SubjectId) (destinationSlot : SlotId)
    (requested : Rights) (reason : Denial)
    (hrejected : (copy state actor source destination destinationSlot requested).result =
      .rejected reason) :
    (copy state actor source destination destinationSlot requested).state = state := by
  simp only [copy] at hrejected ⊢
  split <;> try simp_all [reject]
  next capability =>
    split <;> try simp_all
    split <;> try simp_all
    split <;> try simp_all
    split <;> try simp_all
    split <;> try simp_all

theorem revoke_rejected_unchanged (state : State) (actor : SubjectId)
    (authoritySlot : SlotId) (victim : SubjectId) (victimSlot : SlotId)
    (reason : Denial)
    (hrejected : (revoke state actor authoritySlot victim victimSlot).result =
      .rejected reason) :
    (revoke state actor authoritySlot victim victimSlot).state = state := by
  simp only [revoke] at hrejected ⊢
  split <;> try simp_all [reject]
  next authority =>
    split <;> try simp_all
    split <;> try simp_all
    next target => split <;> try simp_all

theorem revokeSubtree_rejected_unchanged (state : State) (actor : SubjectId)
    (authoritySlot : SlotId) (victim : SubjectId) (victimSlot : SlotId)
    (reason : Denial)
    (hrejected : (revokeSubtree state actor authoritySlot victim victimSlot).result =
      .rejected reason) :
    (revokeSubtree state actor authoritySlot victim victimSlot).state = state := by
  simp only [revokeSubtree] at hrejected ⊢
  split <;> try simp_all [reject]
  next authority =>
    split <;> try simp_all
    split <;> try simp_all
    next target => split <;> try simp_all

theorem revokeSubtree_no_authority_amplification (state : State) (actor : SubjectId)
    (authoritySlot : SlotId) (victim : SubjectId) (victimSlot : SlotId)
    (candidate : SubjectId) (object : ObjectId) (right : Right)
    (hauthority : HasAuthority
      (revokeSubtree state actor authoritySlot victim victimSlot).state
      candidate object right) : HasAuthority state candidate object right := by
  simp only [revokeSubtree] at hauthority
  split at hauthority <;> try simp_all [reject]
  next authority =>
    split at hauthority <;> try simp_all
    split at hauthority <;> try simp_all
    next target hvictim =>
      split at hauthority
      · exact clearSubtree_authority_subset state target.identity candidate object right hauthority
      · simp_all

private def exampleSubjects : SubjectId → Bool := fun subject => subject < 2
private def exampleObjects : ObjectId → Bool := fun object => object = 7
private def exampleKinds : ObjectId → Option ObjectKind := fun object =>
  if object = 7 then some .memory else none
private def ownerRights : Rights := allRights
private def readOnly : Rights := oneRight .read
private def exampleState : State :=
  { subjects := exampleSubjects, objects := exampleObjects, kinds := exampleKinds
    slots := fun subject slot =>
      if subject = 0 ∧ slot = 0 then some { object := 7, kind := .memory, rights := ownerRights }
      else none }

example : lookup exampleState 9 0 = .invalidSubject := by decide
example : lookup exampleState 0 8 = .staleSlot := by decide
example : (copy exampleState 0 0 1 0 readOnly).result = .accepted := by decide
example : (copy exampleState 9 0 1 0 readOnly).result = .rejected .invalidSubject := by decide
example : (copy exampleState 0 8 1 0 readOnly).result = .rejected .staleSlot := by decide
example : (copy exampleState 0 0 9 0 readOnly).result = .rejected .invalidSubject := by decide
example : (copy exampleState 0 0 0 0 readOnly).result = .rejected .occupiedSlot := by decide
example : (copy exampleState 0 0 1 0 noRights).result = .rejected .emptyRights := by decide
example : (copy exampleState 0 0 1 0
    { read := true, write := true, grant := true, revoke := true }).result =
    .accepted := by decide

private def withoutGrant : State :=
  { exampleState with slots := fun subject slot =>
      if subject = 0 ∧ slot = 0 then some { object := 7, kind := .memory, rights := readOnly }
      else none }

private def grantReadRights : Rights := { read := true, grant := true }

example : (copy withoutGrant 0 0 1 0 readOnly).result = .rejected .missingGrant := by decide
example : (copy withoutGrant 0 0 1 0 (oneRight .write)).result =
    .rejected .missingGrant := by decide

private def grantReadOnly : State :=
  { exampleState with slots := fun subject slot => (if subject = 0 ∧ slot = 0 then
      some ({ object := 7, kind := .memory, rights := grantReadRights } : Capability)
    else none) }

example : (copy grantReadOnly 0 0 1 0 (oneRight .write)).result =
    .rejected .rightsNotSubset := by decide
example : (revoke exampleState 0 0 1 0).result = .rejected .staleSlot := by decide
example : (revoke exampleState 9 0 1 0).result = .rejected .invalidSubject := by decide
example : (revoke exampleState 0 0 9 0).result = .rejected .invalidSubject := by decide
example : (revoke withoutGrant 0 0 1 0).result = .rejected .missingRevoke := by decide
example : (revoke (copy exampleState 0 0 1 0 readOnly).state 0 0 1 0).result =
    .accepted := by decide

private def secondObjectState : State :=
  { subjects := exampleSubjects, objects := fun object => object = 7 ∨ object = 8
    kinds := fun object => if object = 7 ∨ object = 8 then some .memory else none
    slots := fun subject slot => (if subject = 0 ∧ slot = 0 then
      some { object := 7, kind := .memory, rights := ownerRights }
    else if subject = 1 ∧ slot = 0 then
      some ({ object := 8, kind := .memory, rights := readOnly } : Capability)
    else none) }

example : (revoke secondObjectState 0 0 1 0).result = .rejected .objectMismatch := by decide
example : lookup
    (revoke (copy exampleState 0 0 1 0 readOnly).state 0 0 1 0).state 1 0 =
    .staleSlot := by decide

private def lineageSubjects : SubjectId → Bool := fun subject => subject < 5
private def lineageRoot : Capability :=
  { identity := 1, object := 7, kind := .memory, rights := allRights }
private def lineageState : State :=
  { nextIdentity := 2
    derivations := fun identity =>
      if identity = 1 then some (none, 7, .memory, allRights) else none
    subjects := lineageSubjects
    objects := exampleObjects
    kinds := exampleKinds
    slots := fun subject slot =>
      if subject = 0 ∧ slot = 0 then some lineageRoot else none }
private def lineageA := (copy lineageState 0 0 1 0 allRights).state
private def lineageB := (copy lineageA 1 0 2 0 allRights).state
private def lineageC := (copy lineageB 2 0 3 0 readOnly).state

/-- Direct slot deletion is deliberately not transitive: this executable
counterexample keeps both descendants live after deleting their parent. -/
example :
    lookup (revoke lineageC 0 0 1 0).state 1 0 = .staleSlot ∧
    lookup (revoke lineageC 0 0 1 0).state 2 0 = .found
      { identity := 3, parent := some 2, object := 7, kind := .memory, rights := allRights } ∧
    lookup (revoke lineageC 0 0 1 0).state 3 0 = .found
      { identity := 4, parent := some 3, object := 7, kind := .memory, rights := readOnly } := by
  decide

/-- Subtree revocation closes the `root → A → B → C` delegation escape. -/
example :
    (revokeSubtree lineageC 0 0 1 0).result = .accepted ∧
    lookup (revokeSubtree lineageC 0 0 1 0).state 1 0 = .staleSlot ∧
    lookup (revokeSubtree lineageC 0 0 1 0).state 2 0 = .staleSlot ∧
    lookup (revokeSubtree lineageC 0 0 1 0).state 3 0 = .staleSlot ∧
    lookup (revokeSubtree lineageC 0 0 1 0).state 0 0 = .found lineageRoot := by
  decide

/-- Repeating a revocation through the stale victim slot is rejected without mutation. -/
example :
    let revoked := (revokeSubtree lineageC 0 0 1 0).state
    (revokeSubtree revoked 0 0 1 0).result = .rejected .staleSlot ∧
      (revokeSubtree revoked 0 0 1 0).state = revoked := by
  dsimp only
  have hrejected :
      (revokeSubtree (revokeSubtree lineageC 0 0 1 0).state 0 0 1 0).result =
        .rejected .staleSlot := by decide
  exact ⟨hrejected, revokeSubtree_rejected_unchanged _ 0 0 1 0 .staleSlot hrejected⟩

/-- Reusing the cleared slot allocates a fresh identity; stale lineage identity
cannot capture the new capability. -/
private def reusedLineageSlot :=
  copy (revokeSubtree lineageC 0 0 1 0).state 0 0 1 0 readOnly
example : reusedLineageSlot.result = .accepted := by decide
example : lookup reusedLineageSlot.state 1 0 = .found
    { identity := 5, parent := some 1, object := 7, kind := .memory, rights := readOnly } := by
  decide

/-- Revocation is lineage-selective even when two roots name the same object. -/
private def twoRootState : State :=
  installRoot lineageState 4 0 7 .memory allRights
private def twoRootA := (copy twoRootState 0 0 1 0 allRights).state
private def twoRootRevoked := (revokeSubtree twoRootA 4 0 1 0).state
example : lookup twoRootRevoked 1 0 = .staleSlot ∧
    lookup twoRootRevoked 4 0 = .found
      { identity := 2, parent := none, object := 7, kind := .memory, rights := allRights } := by
  decide

private def addressRights : Rights := { grant := true, revoke := true }
private def addressCapability : Capability :=
  { object := 9, kind := .addressSpace, rights := addressRights }
private def addressState : State :=
  { subjects := exampleSubjects
    objects := fun object => object = 9
    kinds := fun object => if object = 9 then some .addressSpace else none
    slots := fun subject slot =>
      if subject = 0 ∧ slot = 0 then some addressCapability else none }
private def staleAddressState : State :=
  { addressState with objects := fun _ => false, kinds := fun _ => none }

/-- Adversarial typed-dispatch examples: neither object kind can stand in for the other. -/
example : authorizeKind exampleState 0 0 .addressSpace = .error .kindMismatch := by rfl
example : authorizeKind addressState 0 0 .memory = .error .kindMismatch := by rfl
example : authorizeKind staleAddressState 0 0 .addressSpace = .error .staleSlot := by rfl
example : (copy addressState 0 0 1 0 { grant := true }).result = .accepted := by decide
example : (revoke (copy addressState 0 0 1 0 { grant := true }).state 0 0 1 0).result =
    .accepted := by decide

end LeanOS.Capability
