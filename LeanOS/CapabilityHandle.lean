import LeanOS.Capability

/-!
# Generation-bound capability handles

Holder-visible handles pair a finite slot with the never-reused identity of the
capability installed there.  Resolution remains scoped to a kernel-selected
subject; neither word in a handle can select a different capability space.
-/

namespace LeanOS.CapabilityHandle

open LeanOS.Capability

/-- A holder-visible reference. `identity` is opaque to authority-consuming
operations: it is compared with, never substituted for, the installed record. -/
structure Handle where
  slot : SlotId
  identity : Nat
  deriving DecidableEq, Repr

inductive ResolveDenial where
  | invalidSubject | outOfRange | staleHandle | kindMismatch
  deriving DecidableEq, Repr

/-- The one canonical generation-aware capability resolver. -/
def resolve (state : State) (trustedSubject : SubjectId) (handle : Handle)
    (expected : ObjectKind) : Except ResolveDenial Capability :=
  if state.subjects trustedSubject != true then .error .invalidSubject
  else if !slotInRange state trustedSubject handle.slot then .error .outOfRange
  else match state.slots trustedSubject handle.slot with
    | none => .error .staleHandle
    | some capability =>
        if capability.identity != handle.identity then .error .staleHandle
        else if capability.kind != expected then .error .kindMismatch
        else if state.objects capability.object != true then .error .staleHandle
        else if state.kinds capability.object != some expected then .error .kindMismatch
        else .ok capability

def issue (slot : SlotId) (capability : Capability) : Handle :=
  { slot, identity := capability.identity }

def denial : ResolveDenial → Denial
  | .invalidSubject => .invalidSubject
  | .outOfRange => .outOfRange
  | .staleHandle => .staleSlot
  | .kindMismatch => .kindMismatch

/-- Holder-facing delegation.  The raw-slot operation remains the internal
transition after the generation check has selected its authority record. -/
def copy (state : State) (actor : SubjectId) (source : Handle)
    (expected : ObjectKind) (destination : SubjectId) (destinationSlot : SlotId)
    (requested : Rights) : Outcome :=
  match resolve state actor source expected with
  | .error reason => reject state (denial reason)
  | .ok _ => Capability.copy state actor source.slot destination destinationSlot requested

/-- Holder-facing direct revocation checks both the authority and selected
victim generations before invoking the atomic raw-slot transition. -/
def revoke (state : State) (actor : SubjectId) (authority : Handle)
    (expected : ObjectKind) (victim : SubjectId) (target : Handle) : Outcome :=
  match resolve state actor authority expected with
  | .error reason => reject state (denial reason)
  | .ok _ => match resolve state victim target expected with
    | .error reason => reject state (denial reason)
    | .ok _ => Capability.revoke state actor authority.slot victim target.slot

/-- Holder-facing transitive revocation has the same generation checks. -/
def revokeSubtree (state : State) (actor : SubjectId) (authority : Handle)
    (expected : ObjectKind) (victim : SubjectId) (target : Handle) : Outcome :=
  match resolve state actor authority expected with
  | .error reason => reject state (denial reason)
  | .ok _ => match resolve state victim target expected with
    | .error reason => reject state (denial reason)
    | .ok _ => Capability.revokeSubtree state actor authority.slot victim target.slot

/-- A handle freshly issued for the capability currently installed in a live,
in-range slot resolves to exactly that capability. -/
theorem resolve_issued (state : State) (trustedSubject : SubjectId) (slot : SlotId)
    (capability : Capability) (expected : ObjectKind)
    (hsubject : state.subjects trustedSubject = true)
    (hrange : slotInRange state trustedSubject slot = true)
    (hslot : state.slots trustedSubject slot = some capability)
    (hkind : capability.kind = expected)
    (hlive : state.objects capability.object = true)
    (hregistry : state.kinds capability.object = some expected) :
    resolve state trustedSubject (issue slot capability) expected = .ok capability := by
  simp [resolve, issue, hsubject, hrange, hslot, hkind, hlive, hregistry]

theorem resolve_sound (state : State) (trustedSubject : SubjectId) (handle : Handle)
    (expected : ObjectKind) (capability : Capability)
    (hresolve : resolve state trustedSubject handle expected = .ok capability) :
    state.subjects trustedSubject = true ∧
      slotInRange state trustedSubject handle.slot = true ∧
      state.slots trustedSubject handle.slot = some capability ∧
      capability.identity = handle.identity ∧ capability.kind = expected ∧
      state.objects capability.object = true ∧
      state.kinds capability.object = some expected := by
  unfold resolve at hresolve
  split at hresolve <;> try simp_all
  split at hresolve <;> try simp_all
  split at hresolve <;> try simp_all
  split at hresolve <;> try simp_all
  split at hresolve <;> try simp_all
  split at hresolve <;> try simp_all
  split at hresolve <;> simp_all

/-- Clearing a slot permanently invalidates its old handle at that point. -/
theorem clear_denies_handle (state : State) (subject : SubjectId) (handle : Handle)
    (expected : ObjectKind) (hsubject : state.subjects subject = true)
    (hrange : slotInRange state subject handle.slot = true) :
    resolve (clear state subject handle.slot) subject handle expected =
      .error .staleHandle := by
  have hrange' : handle.slot < state.slotCapacity subject := by
    simpa [slotInRange] using hrange
  simp [resolve, clear, slotInRange, hsubject, hrange']

/-- Reusing a numbered slot cannot make an old generation name its replacement. -/
theorem replacement_denies_old_handle (state : State) (subject : SubjectId)
    (handle : Handle) (replacement : Capability) (expected : ObjectKind)
    (hsubject : state.subjects subject = true)
    (hrange : slotInRange state subject handle.slot = true)
    (hfresh : replacement.identity != handle.identity) :
    resolve (install state subject handle.slot replacement) subject handle expected =
      .error .staleHandle := by
  have hrange' : handle.slot < state.slotCapacity subject := by
    simpa [slotInRange] using hrange
  simp [resolve, install, slotInRange, hsubject, hrange', hfresh]

/-- Direct or transitive revocation removes the named generation, so its
holder-visible handle no longer resolves. -/
theorem clearSubtree_denies_descendant_handle (state : State) (subject : SubjectId)
    (handle : Handle) (capability : Capability) (revokedIdentity : Nat)
    (expected : ObjectKind)
    (hsubject : state.subjects subject = true)
    (hrange : slotInRange state subject handle.slot = true)
    (hslot : state.slots subject handle.slot = some capability)
    (hdescendant :
      descendsFrom state capability.identity revokedIdentity state.nextIdentity = true) :
    resolve (clearSubtree state revokedIdentity) subject handle expected =
      .error .staleHandle := by
  have hcleared := clearSubtree_removes_descendant state revokedIdentity subject
    handle.slot capability hslot hdescendant
  have hsubject' : (clearSubtree state revokedIdentity).subjects subject = true := by
    simpa [clearSubtree] using hsubject
  have hrange' :
      slotInRange (clearSubtree state revokedIdentity) subject handle.slot = true := by
    change decide (handle.slot < state.slotCapacity subject) = true
    simpa only [slotInRange] using hrange
  simp [resolve, hsubject', hrange', hcleared]

/-- Equal handle words remain scoped to the trusted subject. -/
theorem install_other_subject_cannot_resolve (state : State) (owner other : SubjectId)
    (handle : Handle) (capability : Capability) (expected : ObjectKind)
    (hne : other ≠ owner) :
    resolve (install state owner handle.slot capability) other handle expected =
      resolve state other handle expected := by
  simp [resolve, install, slotInRange, hne]

/-- Global live-identity uniqueness means two simultaneously live issued
handles cannot alias different capability slots. -/
theorem live_issued_handles_nonaliasing (state : State)
    (hunique : LiveIdentitiesUnique state)
    (subject otherSubject : SubjectId) (slot otherSlot : SlotId)
    (capability otherCapability : Capability)
    (hslot : state.slots subject slot = some capability)
    (hother : state.slots otherSubject otherSlot = some otherCapability)
    (heq : issue slot capability = issue otherSlot otherCapability) :
    subject = otherSubject ∧ slot = otherSlot := by
  have hid : capability.identity = otherCapability.identity := by
    simpa [issue] using congrArg Handle.identity heq
  exact hunique subject slot capability otherSubject otherSlot otherCapability
    hslot hother hid

private def demoCapability : Capability :=
  { object := 7, kind := .memory, rights := oneRight .read, identity := 12 }

private def demoState : State :=
  { nextIdentity := 13
    derivations := fun identity =>
      if identity = 12 then some (none, 7, .memory, oneRight .read) else none
    subjects := fun subject => subject = 0 || subject = 1
    objects := fun object => object = 7 || object = 8
    kinds := fun object => if object = 7 || object = 8 then some .memory else none
    slotCapacity := fun _ => 2
    slots := fun subject slot =>
      if subject = 0 && slot = 0 then some demoCapability else none }

private def demoHandle : Handle := issue 0 demoCapability

/-- Deliberately unsafe historical behavior, retained only as a negative
regression: resolving a raw slot cannot distinguish two generations. -/
private def resolveBySlotAlone (state : State) (trustedSubject : SubjectId)
    (slot : SlotId) : Option Capability :=
  match lookup state trustedSubject slot with
  | .found capability => some capability
  | _ => none

example : resolve demoState 0 demoHandle .memory = .ok demoCapability := by rfl
example : resolve demoState 1 demoHandle .memory = .error .staleHandle := by rfl
example : resolve (clear demoState 0 0) 0 demoHandle .memory = .error .staleHandle := by
  rfl
example :
    resolve
      (install (clear demoState 0 0) 0 0
        { object := 8, kind := .memory, rights := oneRight .read, identity := 13 })
      0 demoHandle .memory = .error .staleHandle := by
  rfl

example :
    let replacement : Capability :=
      { object := 8, kind := .memory, rights := oneRight .write, identity := 13 }
    let reused := install (clear demoState 0 0) 0 0 replacement
    resolveBySlotAlone reused 0 demoHandle.slot = some replacement ∧
      resolve reused 0 demoHandle .memory = .error .staleHandle := by
  dsimp
  constructor <;> rfl

end LeanOS.CapabilityHandle
