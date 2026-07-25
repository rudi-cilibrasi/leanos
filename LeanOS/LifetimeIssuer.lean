/-!
# Bounded lifetime-identity issuers

This module is the one reviewed lifetime-identity abstraction for subject and
object lifetimes.  Identities occupy one canonical 64-bit word per domain.
The zero word is the reserved null encoding and the all-ones word is the
reserved terminal encoding, so the representable identities are exactly
`1 .. 2^64 - 2`.  A kernel-owned issuer hands out the next representable
identity and fails closed with a typed `exhausted` result before the terminal
encoding could ever be issued; wrapping, truncating, and reuse are never an
issuance policy.  The typed `Domain` index keeps the subject issuer and the
object issuer distinct even though both use the same word width.

Subject identities, object identities, capability identities
(`Capability.State.nextIdentity` with its separate 48-bit generation bound),
slots, frames, and address-space names remain distinct resources; this module
deliberately shares no counter with any of them.
-/
namespace LeanOS.LifetimeIssuer

/-- The two lifetime-identity domains.  One issuer per domain; the phantom
index makes a subject issuer and an object issuer different types. -/
inductive Domain where
  | subject
  | object
  deriving DecidableEq, Repr

/-- Canonical fixed-width identity space: one full 64-bit word per domain. -/
def identityRadix : Nat := 2 ^ 64

/-- The all-ones terminal encoding.  Issuance must stop strictly before it. -/
def identityReserved : Nat := identityRadix - 1

private theorem identityReserved_value : identityReserved = 18446744073709551615 := by
  native_decide

private theorem identityRadix_value : identityRadix = 18446744073709551616 := by
  native_decide

/-- Exactly the identities a canonical word can carry: zero is the reserved
null encoding and `identityReserved` is the reserved terminal encoding. -/
def Representable (identity : Nat) : Prop :=
  0 < identity ∧ identity < identityReserved

instance (identity : Nat) : Decidable (Representable identity) := by
  unfold Representable
  infer_instance

/-- Kernel-owned bounded issuer for one identity domain.  `next` is the next
identity to hand out; `1` is the first issued value of every domain. -/
structure Issuer (domain : Domain) where
  next : Nat := 1
  deriving DecidableEq, Repr

/-- Fail-closed exhaustion: the malformed zero counter and every counter at or
past the reserved terminal encoding refuse further issuance. -/
def exhausted (issuer : Issuer domain) : Bool :=
  issuer.next = 0 || identityReserved ≤ issuer.next

/-- Typed issuance result.  There is no wrapped or recycled alternative. -/
inductive IssueResult (domain : Domain) where
  | issued (identity : Nat) (issuer : Issuer domain)
  | exhausted
  deriving DecidableEq, Repr

/-- Total, deterministic issuance: hand out exactly `next` and advance by one,
or fail closed with the typed `exhausted` result and no state change. -/
def issue (issuer : Issuer domain) : IssueResult domain :=
  if exhausted issuer then .exhausted
  else .issued issuer.next { next := issuer.next + 1 }

/-! ## Canonical fixed-width codec -/

inductive DecodeError where
  | reservedNull
  | reservedTerminal
  deriving DecidableEq, Repr

/-- Encode exactly the representable identity domain into one word. -/
def encode (identity : Nat) : Option UInt64 :=
  if Representable identity then some (UInt64.ofNat identity) else none

/-- Total decoder.  Every rejected word is one of the two reserved encodings;
there is no truncating or wrapping conversion. -/
def decode (word : UInt64) : Except DecodeError Nat :=
  if word.toNat = 0 then .error .reservedNull
  else if word.toNat = identityReserved then .error .reservedTerminal
  else .ok word.toNat

/-- Encoding a representable identity and decoding its word is exact. -/
theorem decode_encode (identity : Nat) (word : UInt64)
    (hencode : encode identity = some word) : decode word = .ok identity := by
  simp only [encode] at hencode
  split at hencode
  case isTrue hvalid =>
    simp only [Option.some.injEq] at hencode
    subst word
    rcases hvalid with ⟨hpositive, hbound⟩
    have hradix : identity < identityRadix := by
      rw [identityRadix_value]
      rw [identityReserved_value] at hbound
      omega
    have htoNat : (UInt64.ofNat identity).toNat = identity := by
      rw [UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt (by simpa [identityRadix_value] using hradix)
    simp [decode, htoNat, Nat.ne_of_gt hpositive, Nat.ne_of_lt hbound]
  case isFalse => simp at hencode

/-- Every successfully decoded word is the unique canonical encoding of the
decoded identity, so acceptance is exactly the image of `encode`. -/
theorem encode_decode (word : UInt64) (identity : Nat)
    (hdecode : decode word = .ok identity) : encode identity = some word := by
  simp only [decode] at hdecode
  split at hdecode <;> try contradiction
  next hnull =>
    split at hdecode <;> try contradiction
    next hterminal =>
      injection hdecode with hidentity
      subst identity
      have hbound : word.toNat < identityReserved := by
        have hword := word.toNat_lt
        rw [identityReserved_value]
        rw [show 2 ^ 64 = 18446744073709551616 from by native_decide] at hword
        rw [identityReserved_value] at hterminal
        omega
      have hrepresentable : Representable word.toNat :=
        ⟨Nat.pos_of_ne_zero hnull, hbound⟩
      simp only [encode, if_pos hrepresentable, Option.some.injEq]
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt word.toNat_lt]

/-- Canonical uniqueness: one accepted word cannot encode two identities. -/
theorem encode_injective (first second : Nat) (word : UInt64)
    (hfirst : encode first = some word) (hsecond : encode second = some word) :
    first = second := by
  have dfirst := decode_encode first word hfirst
  have dsecond := decode_encode second word hsecond
  rw [dfirst] at dsecond
  exact Except.ok.inj dsecond

/-! ## Issuance contract -/

/-- Issuance is a total function of the issuer alone, so it is deterministic
and no caller input can perturb it. -/
theorem issue_deterministic (issuer : Issuer domain) (first second : IssueResult domain)
    (hfirst : issue issuer = first) (hsecond : issue issuer = second) : first = second := by
  rw [← hfirst, ← hsecond]

/-- Every accepted issuance hands out exactly the next counter value, advances
the counter by exactly one, and stays inside the representable range. -/
theorem issued_facts {domain : Domain} {issuer follower : Issuer domain} {identity : Nat}
    (hissued : issue issuer = .issued identity follower) :
    identity = issuer.next ∧ follower.next = issuer.next + 1 ∧
      0 < issuer.next ∧ issuer.next < identityReserved := by
  unfold issue at hissued
  split at hissued
  · contradiction
  · next hlive =>
      injection hissued with hidentity hfollower
      subst hidentity
      subst hfollower
      simp only [exhausted, Bool.or_eq_true, decide_eq_true_eq, not_or] at hlive
      exact ⟨rfl, rfl, Nat.pos_of_ne_zero hlive.1, Nat.lt_of_not_ge hlive.2⟩

/-- Every accepted issuance is representable, hence encodable as one word. -/
theorem issued_representable {domain : Domain} {issuer follower : Issuer domain}
    {identity : Nat} (hissued : issue issuer = .issued identity follower) :
    Representable identity ∧ encode identity = some (UInt64.ofNat identity) := by
  obtain ⟨hidentity, _, hpositive, hbound⟩ := issued_facts hissued
  subst hidentity
  exact ⟨⟨hpositive, hbound⟩, by simp [encode, Representable, hpositive, hbound]⟩

/-- The advanced counter never leaves the bounded domain. -/
theorem issued_bounded {domain : Domain} {issuer follower : Issuer domain} {identity : Nat}
    (hissued : issue issuer = .issued identity follower) :
    follower.next ≤ identityReserved := by
  obtain ⟨_, hfollower, _, hbound⟩ := issued_facts hissued
  omega

/-- Acceptance strictly advances the counter: no accepted issuance can repeat
or skip a value. -/
theorem issued_strictly_monotone {domain : Domain} {issuer follower : Issuer domain}
    {identity : Nat} (hissued : issue issuer = .issued identity follower) :
    issuer.next < follower.next := by
  obtain ⟨_, hfollower, _, _⟩ := issued_facts hissued
  omega

/-- An exhausted issuer refuses issuance; there is no wrapping alternative. -/
theorem exhausted_issue {domain : Domain} (issuer : Issuer domain)
    (hexhausted : exhausted issuer = true) : issue issuer = .exhausted := by
  simp [issue, hexhausted]

/-- Exhaustion is decided exactly by the counter bound, so a live issuance
result certifies a strictly in-range counter. -/
theorem issue_total (issuer : Issuer domain) :
    (exhausted issuer = true ∧ issue issuer = .exhausted) ∨
      (exhausted issuer = false ∧
        issue issuer = .issued issuer.next { next := issuer.next + 1 }) := by
  cases hexhausted : exhausted issuer with
  | true => exact Or.inl ⟨rfl, exhausted_issue issuer hexhausted⟩
  | false => exact Or.inr ⟨rfl, by simp [issue, hexhausted]⟩

/-- Exhaustion is absorbing at the issuer level: nothing an exhausted issuer
can do produces a successor issuer, so its counter can never move again. -/
theorem exhausted_absorbing {domain : Domain} (issuer follower : Issuer domain)
    (identity : Nat) (hexhausted : exhausted issuer = true) :
    issue issuer ≠ .issued identity follower := by
  rw [exhausted_issue issuer hexhausted]
  intro hcontra
  cases hcontra

/-! ## Executable boundary vectors -/

/-- First issued value of a fresh subject issuer. -/
example : issue ({} : Issuer .subject) = .issued 1 { next := 2 } := by native_decide

/-- Penultimate value: the last representable identity is issued and the
counter parks exactly on the reserved terminal encoding. -/
example : issue ({ next := identityReserved - 1 } : Issuer .object) =
    .issued (identityReserved - 1) { next := identityReserved } := by native_decide

/-- Terminal: the parked counter fails closed with the typed result. -/
example : issue ({ next := identityReserved } : Issuer .object) = .exhausted := by
  native_decide

/-- Past-terminal and malformed-zero counters also fail closed. -/
example : issue ({ next := identityRadix } : Issuer .object) = .exhausted := by
  native_decide
example : issue ({ next := 0 } : Issuer .subject) = .exhausted := by native_decide

/-- Reserved encodings are rejected by the codec in both directions. -/
example : encode 0 = none := by native_decide
example : encode identityReserved = none := by native_decide
example : encode identityRadix = none := by native_decide
example : decode 0 = .error .reservedNull := by rfl
example : decode (UInt64.ofNat identityReserved) = .error .reservedTerminal := by rfl

/-- Round trip at the first and last representable identities. -/
example : encode 1 = some 1 := by native_decide
example : decode 1 = .ok 1 := by rfl
example : encode (identityReserved - 1) = some (UInt64.ofNat (identityReserved - 1)) := by
  native_decide
example : decode (UInt64.ofNat (identityReserved - 1)) = .ok (identityReserved - 1) := by rfl

/-- An out-of-range natural is never silently truncated into a word. -/
example : encode (identityRadix + 2) = none := by native_decide

end LeanOS.LifetimeIssuer
