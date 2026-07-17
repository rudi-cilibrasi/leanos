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

/-! ## Canonical fixed-width encoding

The userspace word is divided into a 16-bit slot field and a 48-bit generation
field.  The all-ones value of each field is reserved, as is generation zero.
Consequently, allocation must stop before `generationReserved`; wrapping or
reusing a generation is never an encoding policy.
-/

def slotRadix : Nat := 2 ^ 16
def generationRadix : Nat := 2 ^ 48
def slotReserved : Nat := slotRadix - 1
def generationReserved : Nat := generationRadix - 1

private theorem slotRadix_value : slotRadix = 65536 := by native_decide
private theorem slotReserved_value : slotReserved = 65535 := by native_decide
private theorem generationReserved_value : generationReserved = 281474976710655 := by
  native_decide
private theorem wordSpace : generationRadix * slotRadix = 2 ^ 64 := by native_decide

def Encodable (handle : Handle) : Prop :=
  handle.slot < slotReserved ∧ 0 < handle.identity ∧ handle.identity < generationReserved

instance (handle : Handle) : Decidable (Encodable handle) := by
  unfold Encodable
  infer_instance

inductive DecodeError where
  | reservedSlot | reservedGeneration
  deriving DecidableEq, Repr

/-- Encode exactly the bounded, non-reserved handle domain. -/
def encode (handle : Handle) : Option UInt64 :=
  if Encodable handle then
    some (UInt64.ofNat (handle.slot + handle.identity * slotRadix))
  else none

/-- Total decoder for the canonical 16/48 split.  Every rejected word names a
reserved slot or generation; there is no truncating conversion to a raw slot. -/
def decode (word : UInt64) : Except DecodeError Handle :=
  let slot := word.toNat % slotRadix
  let identity := word.toNat / slotRadix
  if slot = slotReserved then .error .reservedSlot
  else if identity = 0 ∨ identity = generationReserved then .error .reservedGeneration
  else .ok { slot, identity }

/-- Encoding a valid bounded handle and decoding its word is exact. -/
theorem decode_encode (handle : Handle) (word : UInt64)
    (hencode : encode handle = some word) : decode word = .ok handle := by
  simp only [encode] at hencode
  split at hencode
  case isTrue hvalid =>
    simp only [Option.some.injEq] at hencode
    subst word
    rcases hvalid with ⟨hslot, hpositive, hgeneration⟩
    have hslotRadix : handle.slot < slotRadix := by
      exact Nat.lt_trans hslot (by native_decide)
    have hgenerationRadix : handle.identity < generationRadix := by
      exact Nat.lt_trans hgeneration (by native_decide)
    have hword : handle.slot + handle.identity * slotRadix < 2 ^ 64 := by
      have hsum :
          handle.slot + handle.identity * slotRadix <
            (handle.identity + 1) * slotRadix := by
        simpa [Nat.add_mul, Nat.add_comm] using
          Nat.add_lt_add_right hslotRadix (handle.identity * slotRadix)
      have hmul :
          (handle.identity + 1) * slotRadix ≤ generationRadix * slotRadix :=
        Nat.mul_le_mul_right slotRadix (Nat.succ_le_of_lt hgenerationRadix)
      rw [wordSpace] at hmul
      exact Nat.lt_of_lt_of_le hsum hmul
    have htoNat :
        (UInt64.ofNat (handle.slot + handle.identity * slotRadix)).toNat =
          handle.slot + handle.identity * slotRadix := by
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hword]
    have hmod :
        (handle.slot + handle.identity * slotRadix) % slotRadix = handle.slot := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hslotRadix]
    have hdiv :
        (handle.slot + handle.identity * slotRadix) / slotRadix = handle.identity := by
      rw [Nat.add_mul_div_right handle.slot handle.identity]
      · rw [Nat.div_eq_of_lt hslotRadix, Nat.zero_add]
      · simp [slotRadix]
    have hnotSlot : handle.slot ≠ slotReserved := by
      exact Nat.ne_of_lt hslot
    have hnotGeneration : handle.identity ≠ generationReserved := by
      exact Nat.ne_of_lt hgeneration
    simp only [decode, htoNat]
    rw [hmod, hdiv]
    simp [hnotSlot, Nat.ne_of_gt hpositive, hnotGeneration]
  case isFalse hinvalid => simp at hencode

/-- Canonical uniqueness: one accepted word cannot encode two handles. -/
theorem encode_injective (first second : Handle) (word : UInt64)
    (hfirst : encode first = some word) (hsecond : encode second = some word) :
    first = second := by
  have dfirst := decode_encode first word hfirst
  have dsecond := decode_encode second word hsecond
  rw [dfirst] at dsecond
  exact Except.ok.inj dsecond

inductive ResolveDenial where
  | invalidSubject | outOfRange | staleHandle | kindMismatch
  deriving DecidableEq, Repr

/-- Trusted entry/scheduler provenance.  It is intentionally not part of the
untrusted handle word. -/
structure TrustedCaller where
  caller : SubjectId
  deriving DecidableEq, Repr

inductive WordResolveDenial where
  | malformed (reason : DecodeError)
  | denied (reason : ResolveDenial)
  deriving DecidableEq, Repr

/-- A successful userspace resolution keeps the canonical decoded handle next
to the exact authority record selected by it. -/
structure Resolution where
  handle : Handle
  capability : Capability
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

/-- The reusable userspace boundary: decode one opaque word, then resolve only
inside the capability space selected by trusted current-caller context. -/
def resolveCurrent (state : State) (context : TrustedCaller) (word : UInt64)
    (expected : ObjectKind) : Except WordResolveDenial Resolution :=
  match decode word with
  | .error reason => .error (.malformed reason)
  | .ok handle =>
      match resolve state context.caller handle expected with
      | .error reason => .error (.denied reason)
      | .ok capability => .ok { handle, capability }

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

/-- Userspace delegation boundary. The source word cannot select the actor or
destination subject and is decoded before the internal slot transition. -/
def copyWord (state : State) (actor : SubjectId) (sourceWord : UInt64)
    (expected : ObjectKind) (destination : SubjectId) (destinationSlot : SlotId)
    (requested : Rights) : Outcome :=
  match resolveCurrent state { caller := actor } sourceWord expected with
  | .error (.denied reason) => reject state (denial reason)
  | .error (.malformed _) => reject state .staleSlot
  | .ok source =>
      Capability.copy state actor source.handle.slot destination destinationSlot requested

/-- An accepted userspace copy records successful full-word resolution of the
exact source authority before delegation. -/
theorem copyWord_accepted_resolves state actor sourceWord expected destination
    destinationSlot requested
    (haccepted : (copyWord state actor sourceWord expected destination destinationSlot
      requested).result = .accepted) :
    ∃ source,
      resolveCurrent state { caller := actor } sourceWord expected = .ok source ∧
      (Capability.copy state actor source.handle.slot destination destinationSlot
        requested).result = .accepted := by
  cases hsource : resolveCurrent state { caller := actor } sourceWord expected with
  | error reason =>
      cases reason with
      | malformed decodeReason => simp [copyWord, hsource, reject] at haccepted
      | denied resolveReason =>
          cases resolveReason <;> simp [copyWord, hsource, reject] at haccepted
  | ok source =>
      exact ⟨source, rfl, by simpa [copyWord, hsource] using haccepted⟩

/-- A malformed or denied copy word is state preserving. -/
theorem copyWord_resolution_rejected_unchanged state actor sourceWord expected
    destination destinationSlot requested reason
    (hresolve : resolveCurrent state { caller := actor } sourceWord expected = .error reason) :
    (copyWord state actor sourceWord expected destination destinationSlot requested).state = state := by
  cases reason with
  | malformed decodeReason => simp [copyWord, hresolve, reject]
  | denied resolveReason => cases resolveReason <;> simp [copyWord, hresolve, reject]

/-- Holder-facing direct revocation checks both the authority and selected
victim generations before invoking the atomic raw-slot transition. -/
def revoke (state : State) (actor : SubjectId) (authority : Handle)
    (expected : ObjectKind) (victim : SubjectId) (target : Handle) : Outcome :=
  match resolve state actor authority expected with
  | .error reason => reject state (denial reason)
  | .ok _ => match resolve state victim target expected with
    | .error reason => reject state (denial reason)
    | .ok _ => Capability.revoke state actor authority.slot victim target.slot

/-- Userspace direct-revocation boundary. Both authority-consuming words are
decoded in kernel-selected capability spaces before atomic revocation. -/
def revokeWords (state : State) (actor : SubjectId) (authorityWord : UInt64)
    (expected : ObjectKind) (victim : SubjectId) (targetWord : UInt64) : Outcome :=
  match resolveCurrent state { caller := actor } authorityWord expected with
  | .error (.denied reason) => reject state (denial reason)
  | .error (.malformed _) => reject state .staleSlot
  | .ok authority =>
      match resolveCurrent state { caller := victim } targetWord expected with
      | .error (.denied reason) => reject state (denial reason)
      | .error (.malformed _) => reject state .staleSlot
      | .ok target => Capability.revoke state actor authority.handle.slot victim target.handle.slot

/-- Holder-facing transitive revocation has the same generation checks. -/
def revokeSubtree (state : State) (actor : SubjectId) (authority : Handle)
    (expected : ObjectKind) (victim : SubjectId) (target : Handle) : Outcome :=
  match resolve state actor authority expected with
  | .error reason => reject state (denial reason)
  | .ok _ => match resolve state victim target expected with
    | .error reason => reject state (denial reason)
    | .ok _ => Capability.revokeSubtree state actor authority.slot victim target.slot

/-- Userspace transitive-revocation boundary with the same two-word checks. -/
def revokeSubtreeWords (state : State) (actor : SubjectId) (authorityWord : UInt64)
    (expected : ObjectKind) (victim : SubjectId) (targetWord : UInt64) : Outcome :=
  match resolveCurrent state { caller := actor } authorityWord expected with
  | .error (.denied reason) => reject state (denial reason)
  | .error (.malformed _) => reject state .staleSlot
  | .ok authority =>
      match resolveCurrent state { caller := victim } targetWord expected with
      | .error (.denied reason) => reject state (denial reason)
      | .error (.malformed _) => reject state .staleSlot
      | .ok target =>
          Capability.revokeSubtree state actor authority.handle.slot victim target.handle.slot

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

theorem resolveCurrent_sound (state : State) (context : TrustedCaller) (word : UInt64)
    (expected : ObjectKind) (resolution : Resolution)
    (hresolve : resolveCurrent state context word expected = .ok resolution) :
      decode word = .ok resolution.handle ∧
      state.subjects context.caller = true ∧
      slotInRange state context.caller resolution.handle.slot = true ∧
      state.slots context.caller resolution.handle.slot = some resolution.capability ∧
      resolution.capability.identity = resolution.handle.identity ∧
      resolution.capability.kind = expected ∧
      state.objects resolution.capability.object = true ∧
      state.kinds resolution.capability.object = some expected := by
  rcases resolution with ⟨expectedHandle, expectedCapability⟩
  cases hdecode : decode word with
  | error reason => simp [resolveCurrent, hdecode] at hresolve
  | ok handle =>
      cases hresolved : resolve state context.caller handle expected with
      | error reason => simp [resolveCurrent, hdecode, hresolved] at hresolve
      | ok found =>
          have heq : ({ handle, capability := found } : Resolution) =
              { handle := expectedHandle, capability := expectedCapability } := by
            simpa [resolveCurrent, hdecode, hresolved] using hresolve
          have hhandle : handle = expectedHandle := congrArg Resolution.handle heq
          have hcapability : found = expectedCapability :=
            congrArg Resolution.capability heq
          subst expectedHandle
          subst expectedCapability
          exact ⟨rfl,
            resolve_sound state context.caller handle expected found hresolved⟩

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
private def demoWord : UInt64 := 12 * 65536

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

-- Canonical fixed-width vectors and malformed/reserved negative cases.
example : encode demoHandle = some demoWord := by native_decide
example : decode demoWord = .ok demoHandle := by rfl
example : decode 0 = .error .reservedGeneration := by rfl
example : decode (12 * 65536 + 65535) = .error .reservedSlot := by rfl
example : decode ((281474976710655 : UInt64) * 65536) =
    .error .reservedGeneration := by rfl
example : encode { slot := 0, identity := generationReserved } = none := by native_decide
example : encode { slot := slotReserved, identity := 12 } = none := by native_decide

-- The decoded word is resolved only in the capability space named by trusted
-- current-caller context; neither changing generation bits nor reusing the
-- same word under another caller can select authority.
example : resolveCurrent demoState { caller := 0 } demoWord .memory =
    .ok { handle := demoHandle, capability := demoCapability } := by
  rfl
example : resolveCurrent demoState { caller := 1 } demoWord .memory =
    .error (.denied .staleHandle) := by rfl
example : resolveCurrent demoState { caller := 0 } (13 * 65536) .memory =
    .error (.denied .staleHandle) := by rfl
example : resolveCurrent demoState { caller := 0 } (12 * 65536 + 65535) .memory =
    .error (.malformed .reservedSlot) := by rfl

-- Capability copy/revoke userspace adapters share the same decoder rather than
-- recovering a raw slot by masking or truncation.
example :
    let source : Capability :=
      { demoCapability with rights := { read := true, grant := true } }
    let state := install demoState 0 0 source
    (copyWord state 0 demoWord .memory 1 0 (oneRight .read)).result = .accepted := by
  native_decide
example :
    let replacement : Capability :=
      { object := 8, kind := .memory, rights := oneRight .read, identity := 13 }
    let reused := install (clear demoState 0 0) 0 0 replacement
    (copyWord reused 0 demoWord .memory 1 0 (oneRight .read)).result =
        .rejected .staleSlot ∧
      (copyWord reused 0 demoWord .memory 1 0 (oneRight .read)).state.slots 1 0 = none := by
  native_decide
example :
    (copyWord demoState 0 (12 * 65536 + 65535) .memory 1 0 (oneRight .read)).result =
        .rejected .staleSlot ∧
      (copyWord demoState 0 (12 * 65536 + 65535) .memory 1 0
        (oneRight .read)).state.slots 1 0 = none := by
  native_decide

end LeanOS.CapabilityHandle
