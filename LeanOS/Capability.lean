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

def WellFormed (state : State) : Prop :=
  ∀ subject slot capability, state.slots subject slot = some capability →
    state.subjects subject = true ∧ state.objects capability.object = true ∧
      state.kinds capability.object = some capability.kind ∧
      rightsValid capability.kind capability.rights = true

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
      · intro subject slot found hslot
        by_cases htarget : subject = destination ∧ slot = destinationSlot
        · have hdestination : state.subjects destination = true := by simp_all
          rcases htarget with ⟨rfl, rfl⟩
          have hfound : found =
              ({ identity := state.nextIdentity, parent := some capability.identity,
                 object := capability.object, kind := capability.kind,
                 rights := requested } : Capability) := by
            symm
            simpa [install] using hslot
          subst found
          have hsource := lookup_found_slot state actor source capability hlookup
          have hvalid := hstate actor source capability hsource
          exact ⟨by simpa [install] using hdestination,
            hvalid.2.1, hvalid.2.2.1, by simpa using hnonempty⟩
        · exact hstate subject slot found (by simpa [install, htarget] using hslot)
      · try simp_all

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
      intro subject slot capability hslot
      by_cases htarget : subject = victim ∧ slot = victimSlot
      · simp [clear, htarget] at hslot
      · exact hstate subject slot capability (by simpa [clear, htarget] using hslot)

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
      intro subject slot capability hslot
      exact hstate subject slot capability
        (clearSubtree_slot_survives state target.identity subject slot capability hslot)

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
