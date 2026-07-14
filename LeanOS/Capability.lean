/-!
# Capability authority model

This executable, sequential reference model defines authority as a capability
in a subject's slot granting a right over an object. `copy` requires `grant`
and a rights subset; `revoke` removes one named capability and requires
`revoke` over the same object. Every rejection preserves the complete state.

Object lifetimes, concurrency, derivation trees, recursive revocation,
information flow, timing and covert channels are outside the model.
-/
namespace LeanOS.Capability

abbrev SubjectId := Nat
abbrev ObjectId := Nat
abbrev SlotId := Nat

inductive Right where | read | write | grant | revoke
  deriving DecidableEq, Repr

structure Rights where
  read : Bool := false
  write : Bool := false
  grant : Bool := false
  revoke : Bool := false
  deriving DecidableEq, Repr

def noRights : Rights := {}
def oneRight (wanted : Right) : Rights :=
  match wanted with
  | .read => { read := true }
  | .write => { write := true }
  | .grant => { grant := true }
  | .revoke => { revoke := true }
def allRights : Rights := { read := true, write := true, grant := true, revoke := true }
def permits (rights : Rights) : Right → Bool
  | .read => rights.read | .write => rights.write
  | .grant => rights.grant | .revoke => rights.revoke
def hasRight (rights : Rights) (right : Right) : Prop := permits rights right = true
def nonemptyRights (rights : Rights) : Bool :=
  rights.read || rights.write || rights.grant || rights.revoke
def rightsSubset (requested source : Rights) : Bool :=
  (!requested.read || source.read) && (!requested.write || source.write) &&
    (!requested.grant || source.grant) && (!requested.revoke || source.revoke)

structure Capability where
  object : ObjectId
  rights : Rights
  deriving DecidableEq, Repr

structure State where
  subjects : SubjectId → Bool
  objects : ObjectId → Bool
  slots : SubjectId → SlotId → Option Capability

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
      nonemptyRights capability.rights = true

/-- A subject has authority exactly when a slot grants the object/right pair. -/
def HasAuthority (state : State) (subject : SubjectId) (object : ObjectId)
    (right : Right) : Prop :=
  ∃ slot capability, state.slots subject slot = some capability ∧
    capability.object = object ∧ hasRight capability.rights right

inductive Denial where
  | invalidSubject | staleSlot | occupiedSlot | emptyRights
  | missingGrant | rightsNotSubset | missingRevoke | objectMismatch
  deriving DecidableEq, Repr

inductive Result where
  | accepted | rejected (reason : Denial)
  deriving DecidableEq, Repr

structure Outcome where
  state : State
  result : Result

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
      else if nonemptyRights requested then
        if capability.rights.grant then
          if rightsSubset requested capability.rights then
            { state := install state destination destinationSlot
                { object := capability.object, rights := requested },
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
            if authority.object = target.object then
              { state := clear state victim victimSlot, result := .accepted }
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
          have hfound : found = { object := capability.object, rights := requested } := by
            symm
            simpa [install] using hslot
          subst found
          have hsource := lookup_found_slot state actor source capability hlookup
          have hvalid := hstate actor source capability hsource
          exact ⟨by simpa [install] using hdestination,
            hvalid.2.1, by simpa using hnonempty⟩
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
    · apply install_no_authority_amplification state actor destination destinationSlot
        { object := capability.object, rights := requested } capability.rights
        (by simpa using ‹rightsSubset requested capability.rights = true›)
      · intro granted hgranted
        have hslot := lookup_found_slot state actor source capability hlookup
        exact ⟨source, capability, hslot, rfl, hgranted⟩
      · exact hauthority
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

private def exampleSubjects : SubjectId → Bool := fun subject => subject < 2
private def exampleObjects : ObjectId → Bool := fun object => object = 7
private def ownerRights : Rights := allRights
private def readOnly : Rights := oneRight .read
private def exampleState : State :=
  { subjects := exampleSubjects, objects := exampleObjects
    slots := fun subject slot =>
      if subject = 0 ∧ slot = 0 then some { object := 7, rights := ownerRights }
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
      if subject = 0 ∧ slot = 0 then some { object := 7, rights := readOnly }
      else none }

private def grantReadRights : Rights := { read := true, grant := true }

example : (copy withoutGrant 0 0 1 0 readOnly).result = .rejected .missingGrant := by decide
example : (copy withoutGrant 0 0 1 0 (oneRight .write)).result =
    .rejected .missingGrant := by decide

private def grantReadOnly : State :=
  { exampleState with slots := fun subject slot =>
      if subject = 0 ∧ slot = 0 then some { object := 7, rights := grantReadRights }
      else none }

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
    slots := fun subject slot =>
      if subject = 0 ∧ slot = 0 then some { object := 7, rights := ownerRights }
      else if subject = 1 ∧ slot = 0 then some { object := 8, rights := readOnly }
      else none }

example : (revoke secondObjectState 0 0 1 0).result = .rejected .objectMismatch := by decide
example : lookup
    (revoke (copy exampleState 0 0 1 0 readOnly).state 0 0 1 0).state 1 0 =
    .staleSlot := by decide

end LeanOS.Capability
