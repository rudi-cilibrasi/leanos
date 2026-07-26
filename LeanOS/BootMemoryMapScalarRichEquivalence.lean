import LeanOS.BootMemoryMapFullProjectionABI
import LeanOS.BootMemoryMapStreamAuthority

/-!
# Universal scalar/rich boot-memory projection equivalence

The freestanding ABI transports the three Boolean candidate predicates as
fixed-width words.  This module gives their canonical encoding from the exact
rich decoded/reserved state and proves, for arbitrary entries, intervals, and
frames, that the allocation-free consumer accepts exactly that rich
projection.  No fixture, concrete memory size, or entry ordering appears in
the theorem.

The raw streaming decoder is responsible for producing these fields; the
production C boundary may transport them but may not reinterpret or replace
them.  Final-ELF policy retains only `leanos_boot_consume_exact_projection` as
the selection consumer.
-/
namespace LeanOS.BootMemoryMapScalarRichEquivalence

open LeanOS
open LeanOS.BootMemoryMap
open LeanOS.BootMemoryMapStreamAuthority

def usableWord (entries : List RawEntry) (frame : Nat) : UInt64 :=
  if entries.any (fun entry =>
      entry.kind == .usable &&
        covers entry (frame * pageBytes) (frame * pageBytes + pageBytes))
  then 1 else 0

def blockedWord (entries : List RawEntry) (frame : Nat) : UInt64 :=
  if entries.any (fun entry =>
      entry.kind != .usable &&
        overlaps entry (frame * pageBytes) (frame * pageBytes + pageBytes))
  then 1 else 0

def manifestWord (intervals : List BootReservation.Interval) (frame : Nat) : UInt64 :=
  if BootReservation.reservedBy intervals frame then 0 else 1

theorem field_words_iff_rich_predicates
    (entries : List RawEntry) (intervals : List BootReservation.Interval) (frame : Nat) :
    (usableWord entries frame == 1 && blockedWord entries frame == 0 &&
        manifestWord intervals frame == 1) =
      (usableFrameSound entries frame &&
        !BootReservation.reservedBy intervals frame) := by
  unfold usableWord blockedWord manifestWord usableFrameSound
  split <;> split <;> split <;> simp_all

/-- Universal scalar-rich equivalence used at the freestanding selection
boundary.  The hypotheses name field agreement explicitly, so a caller cannot
replace a parser result, reservation result, or candidate identity and still
apply the theorem. -/
theorem consume_exact_projection_iff
    (entries : List RawEntry) (intervals : List BootReservation.Interval)
    (frame : Nat) (candidate usable blocked manifest : UInt64)
    (hframe : frame < frameLimit)
    (hcandidate : candidate = UInt64.ofNat frame)
    (husable : usable = usableWord entries frame)
    (hblocked : blocked = blockedWord entries frame)
    (hmanifest : manifest = manifestWord intervals frame) :
    (consumeExactProjection 4096 candidate complete usable blocked manifest == candidate) =
      (usableFrameSound entries frame &&
        !BootReservation.reservedBy intervals frame) := by
  subst candidate
  subst usable
  subst blocked
  subst manifest
  change frame < 4096 at hframe
  have hsize : frame < UInt64.size := Nat.lt_trans hframe (by decide)
  have hc : UInt64.ofNat frame < 4096 := by
    exact (UInt64.ofNat_lt_iff_lt hsize (by decide)).2 hframe
  unfold consumeExactProjection
  have hne : (4096 : UInt64) ≠ UInt64.ofNat frame := by
    intro heq
    rw [← heq] at hc
    simp at hc
  simp [hc, field_words_iff_rich_predicates]
  cases hu : usableFrameSound entries frame <;>
    cases hr : BootReservation.reservedBy intervals frame <;>
    simp_all

/-- An accepted exact rich authority supplies the canonical field equations
needed by the universal consumer theorem for its selected frame. -/
theorem accepted_authority_projection_consumable
    (authority : BootMemoryMapFullProjectionABI.Authority)
    (hreserved :
      BootReservation.reservedBy authority.reserved.intervals
        authority.allocation.frame = false) :
    consumeExactProjection 4096 (UInt64.ofNat authority.allocation.frame) complete
        (usableWord authority.decoded.entries authority.allocation.frame)
        (blockedWord authority.decoded.entries authority.allocation.frame)
        (manifestWord authority.reserved.intervals authority.allocation.frame) =
      UInt64.ofNat authority.allocation.frame := by
  have heq := consume_exact_projection_iff authority.decoded.entries
    authority.reserved.intervals authority.allocation.frame
    (UInt64.ofNat authority.allocation.frame)
    (usableWord authority.decoded.entries authority.allocation.frame)
    (blockedWord authority.decoded.entries authority.allocation.frame)
    (manifestWord authority.reserved.intervals authority.allocation.frame)
    authority.selectedWithinBound rfl rfl rfl rfl
  rw [authority.selectedUsable, hreserved] at heq
  simpa using heq

end LeanOS.BootMemoryMapScalarRichEquivalence
