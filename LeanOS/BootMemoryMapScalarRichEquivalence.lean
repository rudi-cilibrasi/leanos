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

/-- The proof-side form of the production range-overlap test.  Keeping this in
`Nat` makes its relationship to `BootReservation.roundInterval` explicit;
accepted production range words are all below the 16 MiB physical limit, so
their `UInt64` arithmetic is exact. -/
def byteRangeReserves (reservation : BootReservation.Reservation) (frame : Nat) : Bool :=
  reservation.start < frame * pageBytes + pageBytes &&
    frame * pageBytes < reservation.start + reservation.length

/-- Rounding a checked half-open byte range to frames preserves exactly the
production overlap predicate for every queried frame. -/
theorem roundInterval_contains_iff_byteRangeReserves
    (reservation : BootReservation.Reservation)
    (interval : BootReservation.Interval)
    (hround : BootReservation.roundInterval reservation = .ok interval)
    (frame : Nat) :
    interval.contains frame = byteRangeReserves reservation frame := by
  by_cases hzero : reservation.length == 0
  · simp [BootReservation.roundInterval, hzero] at hround
    change Except.error BootReservation.Error.zeroLength = Except.ok interval at hround
    contradiction
  · by_cases hoverflow :
        reservation.start ≥ wordLimit || reservation.length ≥ wordLimit ||
          reservation.length > wordLimit - reservation.start
    · simp [BootReservation.roundInterval, hzero, hoverflow] at hround
      change Except.error BootReservation.Error.addressOverflow = Except.ok interval at hround
      contradiction
    · let stop := reservation.start + reservation.length
      let lastFrame := (stop + pageBytes - 1) / pageBytes
      by_cases houtside : stop > physicalLimit || lastFrame > frameLimit
      · simp [BootReservation.roundInterval, hzero, hoverflow, stop, lastFrame,
          houtside] at hround
        change Except.error BootReservation.Error.outsidePhysicalLimit =
          Except.ok interval at hround
        contradiction
      · simp [BootReservation.roundInterval, hzero, hoverflow, stop, lastFrame,
          houtside] at hround
        change Except.ok
          { identity := reservation.identity
            firstFrame := reservation.start / pageBytes
            frameCount := (reservation.start + reservation.length + pageBytes - 1) /
              pageBytes - reservation.start / pageBytes
            lifetime := reservation.lifetime } = Except.ok interval at hround
        injection hround with hinterval
        subst interval
        unfold BootReservation.Interval.contains byteRangeReserves
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        have hlength : 0 < reservation.length := by
          simpa using (Nat.pos_of_ne_zero (by simpa using hzero))
        simp only [pageBytes] at *
        omega

/-- Any list of successfully rounded reservations has exactly the same
per-frame exclusion result before and after rounding.  In particular this
applies at once to the complete nine-identity production manifest; no identity
or range can disappear between the scalar range overlay and the rich checked
interval overlay. -/
theorem rounded_ranges_reservedBy_iff
    (manifest : List BootReservation.Reservation)
    (intervals : List BootReservation.Interval)
    (hround : manifest.mapM BootReservation.roundInterval = .ok intervals)
    (frame : Nat) :
    BootReservation.reservedBy intervals frame =
      manifest.any (fun reservation => byteRangeReserves reservation frame) := by
  induction manifest generalizing intervals with
  | nil =>
      change Except.ok [] = Except.ok intervals at hround
      injection hround with hintervals
      subst intervals
      rfl
  | cons reservation rest ih =>
      cases hfirst : BootReservation.roundInterval reservation with
      | error reason =>
          rw [List.mapM_cons, hfirst] at hround
          contradiction
      | ok interval =>
          cases hrest : rest.mapM BootReservation.roundInterval with
          | error reason =>
              rw [List.mapM_cons, hfirst, hrest] at hround
              contradiction
          | ok tail =>
              rw [List.mapM_cons, hfirst, hrest] at hround
              injection hround with hintervals
              subst intervals
              change
                (interval.contains frame || BootReservation.reservedBy tail frame) =
                  (byteRangeReserves reservation frame ||
                    rest.any (fun reservation => byteRangeReserves reservation frame))
              rw [roundInterval_contains_iff_byteRangeReserves reservation interval hfirst,
                ih tail hrest]

/-- The manifest word transported to the production consumer is therefore
exactly the exclusion word computed directly from all checked byte ranges. -/
theorem manifestWord_eq_rounded_range_word
    (manifest : List BootReservation.Reservation)
    (intervals : List BootReservation.Interval)
    (hround : manifest.mapM BootReservation.roundInterval = .ok intervals)
    (frame : Nat) :
    manifestWord intervals frame =
      if manifest.any (fun reservation => byteRangeReserves reservation frame)
      then 0 else 1 := by
  unfold manifestWord
  rw [rounded_ranges_reservedBy_iff manifest intervals hround frame]

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

/-- The production consumer instantiated with the canonical rich-state fields
accepts exactly the rich usable-and-unreserved predicate.  Unlike the transport
lemma above, this public theorem has no caller-supplied field equations: the
candidate identity and all three decision words are fixed directly by the
decoded entries, checked reservation intervals, and candidate frame. -/
theorem consume_canonical_projection_iff
    (entries : List RawEntry) (intervals : List BootReservation.Interval)
    (frame : Nat) (hframe : frame < frameLimit) :
    (consumeExactProjection 4096 (UInt64.ofNat frame) complete
        (usableWord entries frame) (blockedWord entries frame)
        (manifestWord intervals frame) == UInt64.ofNat frame) =
      (usableFrameSound entries frame &&
        !BootReservation.reservedBy intervals frame) :=
  consume_exact_projection_iff entries intervals frame
    (UInt64.ofNat frame) (usableWord entries frame) (blockedWord entries frame)
    (manifestWord intervals frame) hframe rfl rfl rfl rfl

/-- An accepted exact rich authority supplies a consumable canonical production
projection without any external readiness or reservation premise. -/
theorem accepted_authority_projection_consumable
    (authority : BootMemoryMapFullProjectionABI.Authority) :
    consumeExactProjection 4096 (UInt64.ofNat authority.allocation.frame) complete
        (usableWord authority.decoded.entries authority.allocation.frame)
        (blockedWord authority.decoded.entries authority.allocation.frame)
        (manifestWord authority.reserved.intervals authority.allocation.frame) =
      UInt64.ofNat authority.allocation.frame := by
  have hreserved :=
    BootReservation.allocation_excludes_reservations authority.reserved authority.owner
      authority.allocation authority.allocatedBy
  have heq := consume_canonical_projection_iff authority.decoded.entries
    authority.reserved.intervals authority.allocation.frame
    authority.selectedWithinBound
  rw [authority.selectedUsable, hreserved] at heq
  simpa using heq

end LeanOS.BootMemoryMapScalarRichEquivalence
