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

/-- The rich reservation manifest denoted by the production ABI's canonical
positional words.  Identity and lifetime are fixed here rather than supplied
by the caller. -/
def canonicalManifest
    (lowStart lowLength imageStart imageLength pageStart pageLength
    descriptorStart descriptorLength stacksStart stacksLength
    guardStart guardLength entryStart entryLength usersStart usersLength
    infoStart infoLength : UInt64) : List BootReservation.Reservation :=
  [{ identity := .lowMemory, start := lowStart.toNat, length := lowLength.toNat,
     lifetime := .permanent },
   { identity := .loadedImage, start := imageStart.toNat, length := imageLength.toNat,
     lifetime := .permanent },
   { identity := .pageTables, start := pageStart.toNat, length := pageLength.toNat,
     lifetime := .permanent },
   { identity := .descriptorTables, start := descriptorStart.toNat,
     length := descriptorLength.toNat, lifetime := .permanent },
   { identity := .kernelStacks, start := stacksStart.toNat, length := stacksLength.toNat,
     lifetime := .permanent },
   { identity := .ordinaryEntryGuard, start := guardStart.toNat,
     length := guardLength.toNat, lifetime := .permanent },
   { identity := .ordinaryEntryStack, start := entryStart.toNat,
     length := entryLength.toNat, lifetime := .permanent },
   { identity := .embeddedUsers, start := usersStart.toNat, length := usersLength.toNat,
     lifetime := .permanent },
   { identity := .multibootInfo, start := infoStart.toNat, length := infoLength.toNat,
     lifetime := .bootstrap }]

/-- The positional ABI construction supplies every rich manifest identity
exactly once and cannot introduce an identity outside the reviewed vocabulary.
This discharges the two structural gates of `BootReservation.validateManifest`
independently of the caller-supplied range words. -/
theorem canonicalManifest_identity_valid
    (lowStart lowLength imageStart imageLength pageStart pageLength
    descriptorStart descriptorLength stacksStart stacksLength
    guardStart guardLength entryStart entryLength usersStart usersLength
    infoStart infoLength : UInt64) :
    (BootReservation.requiredIdentities.all fun identity =>
        BootReservation.exactlyOnce identity
          (canonicalManifest lowStart lowLength imageStart imageLength pageStart pageLength
            descriptorStart descriptorLength stacksStart stacksLength
            guardStart guardLength entryStart entryLength usersStart usersLength
            infoStart infoLength)) = true ∧
      ((canonicalManifest lowStart lowLength imageStart imageLength pageStart pageLength
          descriptorStart descriptorLength stacksStart stacksLength
          guardStart guardLength entryStart entryLength usersStart usersLength
          infoStart infoLength).all fun reservation =>
            BootReservation.requiredIdentities.contains reservation.identity) = true := by
  simp +decide [canonicalManifest, BootReservation.requiredIdentities,
    BootReservation.exactlyOnce]

/-- The containment gate used by rich manifest validation, named so the
canonical ABI proof can expose its remaining arithmetic obligation directly. -/
def richImageContained (intervals : List BootReservation.Interval) : Bool :=
  let image := intervals.find? (·.identity == .loadedImage)
  intervals.all fun interval =>
    interval.identity == .lowMemory || interval.identity == .multibootInfo ||
      match image with
      | none => false
      | some loaded => loaded.firstFrame ≤ interval.firstFrame &&
          interval.firstFrame + interval.frameCount ≤
            loaded.firstFrame + loaded.frameCount

/-- The rich interval obtained by rounding one canonical scalar byte range. -/
def roundedInterval (identity : BootReservation.Identity)
    (lifetime : BootReservation.Lifetime) (start length : UInt64) :
    BootReservation.Interval :=
  { identity
    firstFrame := start.toNat / pageBytes
    frameCount := (start.toNat + length.toNat + pageBytes - 1) / pageBytes -
      start.toNat / pageBytes
    lifetime }

/-- The nine rich intervals denoted by the canonical positional ABI. -/
def canonicalIntervals
    (lowStart lowLength imageStart imageLength pageStart pageLength
    descriptorStart descriptorLength stacksStart stacksLength
    guardStart guardLength entryStart entryLength usersStart usersLength
    infoStart infoLength : UInt64) : List BootReservation.Interval :=
  [roundedInterval .lowMemory .permanent lowStart lowLength,
   roundedInterval .loadedImage .permanent imageStart imageLength,
   roundedInterval .pageTables .permanent pageStart pageLength,
   roundedInterval .descriptorTables .permanent descriptorStart descriptorLength,
   roundedInterval .kernelStacks .permanent stacksStart stacksLength,
   roundedInterval .ordinaryEntryGuard .permanent guardStart guardLength,
   roundedInterval .ordinaryEntryStack .permanent entryStart entryLength,
   roundedInterval .embeddedUsers .permanent usersStart usersLength,
   roundedInterval .multibootInfo .bootstrap infoStart infoLength]

/-- A scalar range accepted below the physical bound has the exact `Nat`
arithmetic required by the rich reservation model. -/
theorem withinPhysicalLimit_nat (start length : UInt64)
    (h : withinPhysicalLimit start length = true) :
    length.toNat ≠ 0 ∧ start.toNat + length.toNat ≤ physicalLimit := by
  simp only [withinPhysicalLimit, validRange, Bool.and_eq_true, bne_iff_ne,
    decide_eq_true_eq] at h
  rcases h with ⟨⟨hnz, hvalid⟩, hphysical⟩
  have hnzNat : length.toNat ≠ 0 := by
    intro hz
    apply hnz
    apply UInt64.toNat_inj.mp
    simpa using hz
  have hmaxNat : UInt64.toNat (18446744073709551615 : UInt64) =
      18446744073709551615 := by decide
  have hsmax : start ≤ (18446744073709551615 : UInt64) := by
    rw [UInt64.le_iff_toNat_le, hmaxNat]
    have hs := start.toNat_lt
    omega
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ hsmax, hmaxNat] at hvalid
  have hsumlt : start.toNat + length.toNat < 2 ^ 64 := by omega
  have hadd : (start + length).toNat = start.toNat + length.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt hsumlt]
  have hphysicalNat : (start + length).toNat ≤ physicalLimit := by
    rw [UInt64.le_iff_toNat_le] at hphysical
    have hpNat : (UInt64.ofNat physicalLimit).toNat = physicalLimit := by decide
    simpa [physicalByteLimit, hpNat] using hphysical
  exact ⟨hnzNat, by rwa [hadd] at hphysicalNat⟩

/-- The scalar physical-bound check is sufficient for rich interval rounding,
with no extra range premise supplied by C. -/
theorem roundInterval_of_withinPhysicalLimit
    (identity : BootReservation.Identity) (lifetime : BootReservation.Lifetime)
    (start length : UInt64) (h : withinPhysicalLimit start length = true) :
    BootReservation.roundInterval
      { identity, start := start.toNat, length := length.toNat, lifetime } =
        .ok (roundedInterval identity lifetime start length) := by
  have hn := withinPhysicalLimit_nat start length h
  have hs := start.toNat_lt
  have hl := length.toNat_lt
  have hlast :
      (start.toNat + length.toNat + pageBytes - 1) / pageBytes ≤ frameLimit := by
    simp only [pageBytes, physicalLimit, frameLimit] at *
    omega
  have hoverflow : ¬(start.toNat ≥ wordLimit || length.toNat ≥ wordLimit ||
      length.toNat > wordLimit - start.toNat) := by
    simp only [wordLimit, Bool.or_eq_true, decide_eq_true_eq]
    simp only [physicalLimit] at hn
    omega
  have houtside : ¬(start.toNat + length.toNat > physicalLimit ||
      (start.toNat + length.toNat + pageBytes - 1) / pageBytes > frameLimit) := by
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega
  by_cases hzero : length.toNat == 0
  · simp at hzero
    exact (hn.1 hzero).elim
  · simp [BootReservation.roundInterval, roundedInterval, hzero, hoverflow, houtside]
    change Except.ok _ = Except.ok _
    rfl

/-- Scalar containment under a physically bounded outer range makes the inner
range independently acceptable to rich rounding. -/
theorem contained_withinPhysicalLimit
    (outerStart outerLength start length : UInt64)
    (houter : withinPhysicalLimit outerStart outerLength = true)
    (hcontained : contained outerStart outerLength start length = true) :
    withinPhysicalLimit start length = true := by
  simp only [withinPhysicalLimit, contained, validRange, Bool.and_eq_true,
    bne_iff_ne, decide_eq_true_eq] at *
  exact ⟨hcontained.1.1.2, Nat.le_trans hcontained.2 houter.2⟩

/-- Byte containment is preserved when both endpoints are rounded outward to
frames. -/
theorem roundedInterval_contained
    (outerIdentity identity : BootReservation.Identity)
    (outerLifetime lifetime : BootReservation.Lifetime)
    (outerStart outerLength start length : UInt64)
    (houter : withinPhysicalLimit outerStart outerLength = true)
    (hcontained : contained outerStart outerLength start length = true) :
    let outer := roundedInterval outerIdentity outerLifetime outerStart outerLength
    let inner := roundedInterval identity lifetime start length
    outer.firstFrame ≤ inner.firstFrame ∧
      inner.firstFrame + inner.frameCount ≤ outer.firstFrame + outer.frameCount := by
  have hinner := contained_withinPhysicalLimit outerStart outerLength start length
    houter hcontained
  have hon := withinPhysicalLimit_nat outerStart outerLength houter
  have hin := withinPhysicalLimit_nat start length hinner
  simp only [contained, validRange, Bool.and_eq_true, bne_iff_ne,
    decide_eq_true_eq] at hcontained
  have hstart : outerStart.toNat ≤ start.toNat := by
    simpa [UInt64.le_iff_toNat_le] using hcontained.1.2
  have hoSumLt : outerStart.toNat + outerLength.toNat < 2 ^ 64 := by
    simp only [physicalLimit] at hon
    omega
  have hiSumLt : start.toNat + length.toNat < 2 ^ 64 := by
    simp only [physicalLimit] at hin
    omega
  have hend : start.toNat + length.toNat ≤
      outerStart.toNat + outerLength.toNat := by
    have hendsWord := hcontained.2
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_add, UInt64.toNat_add] at hendsWord
    simpa [Nat.mod_eq_of_lt hiSumLt, Nat.mod_eq_of_lt hoSumLt] using hendsWord
  have hfirst := Nat.div_le_div_right hstart (c := pageBytes)
  have hpast := Nat.div_le_div_right
    (Nat.add_le_add_right hend (pageBytes - 1)) (c := pageBytes)
  have houterFirstPast :
      outerStart.toNat / pageBytes ≤
        (outerStart.toNat + outerLength.toNat + pageBytes - 1) / pageBytes :=
    Nat.div_le_div_right (by omega) (c := pageBytes)
  have hinnerFirstPast :
      start.toNat / pageBytes ≤
        (start.toNat + length.toNat + pageBytes - 1) / pageBytes :=
    Nat.div_le_div_right (by omega) (c := pageBytes)
  simp only [roundedInterval]
  constructor
  · exact hfirst
  · rw [Nat.add_sub_of_le hinnerFirstPast, Nat.add_sub_of_le houterFirstPast]
    exact hpast

/-- `manifestValid` lifts the scalar physical-limit bridge across all nine
canonical identities: the seven image-owned ranges inherit the loaded-image
bound, while low memory and Multiboot info are checked independently. -/
theorem canonicalManifest_rounds_of_manifestValid
    (lowStart lowLength imageStart imageLength pageStart pageLength
    descriptorStart descriptorLength stacksStart stacksLength
    guardStart guardLength entryStart entryLength usersStart usersLength
    infoStart infoLength : UInt64)
    (hvalid : manifestValid lowStart lowLength imageStart imageLength pageStart pageLength
      descriptorStart descriptorLength stacksStart stacksLength
      guardStart guardLength entryStart entryLength usersStart usersLength
      infoStart infoLength = true) :
    (canonicalManifest lowStart lowLength imageStart imageLength pageStart pageLength
      descriptorStart descriptorLength stacksStart stacksLength
      guardStart guardLength entryStart entryLength usersStart usersLength
      infoStart infoLength).mapM BootReservation.roundInterval =
        .ok (canonicalIntervals lowStart lowLength imageStart imageLength
          pageStart pageLength descriptorStart descriptorLength stacksStart stacksLength
          guardStart guardLength entryStart entryLength usersStart usersLength
          infoStart infoLength) := by
  have hfacts :
      lowStart = 0 ∧ lowLength = 0x100000 ∧
      withinPhysicalLimit imageStart imageLength = true ∧
      contained imageStart imageLength pageStart pageLength = true ∧
      contained imageStart imageLength descriptorStart descriptorLength = true ∧
      contained imageStart imageLength stacksStart stacksLength = true ∧
      contained imageStart imageLength guardStart guardLength = true ∧
      contained imageStart imageLength entryStart entryLength = true ∧
      contained imageStart imageLength usersStart usersLength = true ∧
      withinPhysicalLimit infoStart infoLength = true := by
    simp only [manifestValid, Bool.and_eq_true] at hvalid
    grind
  rcases hfacts with
    ⟨rfl, rfl, himage, hpage, hdescriptor, hstacks, hguard, hentry, husers, hinfo⟩
  have hlow : withinPhysicalLimit 0 0x100000 = true := by decide
  have hpage' := contained_withinPhysicalLimit imageStart imageLength pageStart pageLength
    himage hpage
  have hdescriptor' := contained_withinPhysicalLimit imageStart imageLength
    descriptorStart descriptorLength himage hdescriptor
  have hstacks' := contained_withinPhysicalLimit imageStart imageLength stacksStart
    stacksLength himage hstacks
  have hguard' := contained_withinPhysicalLimit imageStart imageLength guardStart guardLength
    himage hguard
  have hentry' := contained_withinPhysicalLimit imageStart imageLength entryStart entryLength
    himage hentry
  have husers' := contained_withinPhysicalLimit imageStart imageLength usersStart usersLength
    himage husers
  have hlr := roundInterval_of_withinPhysicalLimit .lowMemory .permanent
    (0 : UInt64) 0x100000 hlow
  have hir := roundInterval_of_withinPhysicalLimit .loadedImage .permanent
    imageStart imageLength himage
  have hpr := roundInterval_of_withinPhysicalLimit .pageTables .permanent
    pageStart pageLength hpage'
  have hdr := roundInterval_of_withinPhysicalLimit .descriptorTables .permanent
    descriptorStart descriptorLength hdescriptor'
  have hsr := roundInterval_of_withinPhysicalLimit .kernelStacks .permanent
    stacksStart stacksLength hstacks'
  have hgr := roundInterval_of_withinPhysicalLimit .ordinaryEntryGuard .permanent
    guardStart guardLength hguard'
  have her := roundInterval_of_withinPhysicalLimit .ordinaryEntryStack .permanent
    entryStart entryLength hentry'
  have hur := roundInterval_of_withinPhysicalLimit .embeddedUsers .permanent
    usersStart usersLength husers'
  have hmr := roundInterval_of_withinPhysicalLimit .multibootInfo .bootstrap
    infoStart infoLength hinfo
  simp only [canonicalManifest, canonicalIntervals, List.mapM_cons, List.mapM_nil,
    hlr, hir, hpr, hdr, hsr, hgr, her, hur, hmr]
  rfl

/-- The intervals forced by `manifestValid` satisfy the rich loaded-image
containment gate after outward page rounding. -/
theorem canonicalIntervals_contained_of_manifestValid
    (lowStart lowLength imageStart imageLength pageStart pageLength
    descriptorStart descriptorLength stacksStart stacksLength
    guardStart guardLength entryStart entryLength usersStart usersLength
    infoStart infoLength : UInt64)
    (hvalid : manifestValid lowStart lowLength imageStart imageLength pageStart pageLength
      descriptorStart descriptorLength stacksStart stacksLength
      guardStart guardLength entryStart entryLength usersStart usersLength
      infoStart infoLength = true) :
    richImageContained
      (canonicalIntervals lowStart lowLength imageStart imageLength pageStart pageLength
        descriptorStart descriptorLength stacksStart stacksLength
        guardStart guardLength entryStart entryLength usersStart usersLength
        infoStart infoLength) = true := by
  have hfacts :
      withinPhysicalLimit imageStart imageLength = true ∧
      contained imageStart imageLength pageStart pageLength = true ∧
      contained imageStart imageLength descriptorStart descriptorLength = true ∧
      contained imageStart imageLength stacksStart stacksLength = true ∧
      contained imageStart imageLength guardStart guardLength = true ∧
      contained imageStart imageLength entryStart entryLength = true ∧
      contained imageStart imageLength usersStart usersLength = true := by
    simp only [manifestValid, Bool.and_eq_true] at hvalid
    grind
  rcases hfacts with ⟨himage, hpage, hdescriptor, hstacks, hguard, hentry, husers⟩
  have hp := roundedInterval_contained .loadedImage .pageTables .permanent .permanent
    imageStart imageLength pageStart pageLength himage hpage
  have hd := roundedInterval_contained .loadedImage .descriptorTables .permanent .permanent
    imageStart imageLength descriptorStart descriptorLength himage hdescriptor
  have hs := roundedInterval_contained .loadedImage .kernelStacks .permanent .permanent
    imageStart imageLength stacksStart stacksLength himage hstacks
  have hg := roundedInterval_contained .loadedImage .ordinaryEntryGuard .permanent .permanent
    imageStart imageLength guardStart guardLength himage hguard
  have he := roundedInterval_contained .loadedImage .ordinaryEntryStack .permanent .permanent
    imageStart imageLength entryStart entryLength himage hentry
  have hu := roundedInterval_contained .loadedImage .embeddedUsers .permanent .permanent
    imageStart imageLength usersStart usersLength himage husers
  simp only [roundedInterval] at hp hd hs hg he hu
  have hfind :
      (canonicalIntervals lowStart lowLength imageStart imageLength pageStart pageLength
        descriptorStart descriptorLength stacksStart stacksLength
        guardStart guardLength entryStart entryLength usersStart usersLength
        infoStart infoLength).find? (·.identity == .loadedImage) =
          some (roundedInterval .loadedImage .permanent imageStart imageLength) := by
    simp +decide [canonicalIntervals, roundedInterval]
  unfold richImageContained
  rw [hfind]
  simp +decide only [canonicalIntervals, roundedInterval, List.all_cons, List.all_nil,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  exact ⟨by simp, by simp, Or.inr hp, Or.inr hd, Or.inr hs, Or.inr hg,
    Or.inr he, Or.inr hu, by simp⟩

/-- Once the nine canonical ranges round successfully and satisfy rich
loaded-image containment, `validateManifest` accepts exactly those intervals.
The identity/cardinality gates cannot fail because they are fixed by the ABI
constructor rather than transported from C. -/
theorem canonicalManifest_validate_of_rounds
    (lowStart lowLength imageStart imageLength pageStart pageLength
    descriptorStart descriptorLength stacksStart stacksLength
    guardStart guardLength entryStart entryLength usersStart usersLength
    infoStart infoLength : UInt64)
    (intervals : List BootReservation.Interval)
    (hround :
      (canonicalManifest lowStart lowLength imageStart imageLength pageStart pageLength
        descriptorStart descriptorLength stacksStart stacksLength
        guardStart guardLength entryStart entryLength usersStart usersLength
        infoStart infoLength).mapM BootReservation.roundInterval = .ok intervals)
    (hcontained : richImageContained intervals = true) :
    BootReservation.validateManifest
      (canonicalManifest lowStart lowLength imageStart imageLength pageStart pageLength
        descriptorStart descriptorLength stacksStart stacksLength
        guardStart guardLength entryStart entryLength usersStart usersLength
        infoStart infoLength) = .ok intervals := by
  let manifest :=
    canonicalManifest lowStart lowLength imageStart imageLength pageStart pageLength
      descriptorStart descriptorLength stacksStart stacksLength
      guardStart guardLength entryStart entryLength usersStart usersLength
      infoStart infoLength
  have hidentity := canonicalManifest_identity_valid
    lowStart lowLength imageStart imageLength pageStart pageLength
    descriptorStart descriptorLength stacksStart stacksLength
    guardStart guardLength entryStart entryLength usersStart usersLength
    infoStart infoLength
  have hsize : ¬manifest.length > BootReservation.maxReservations := by
    simp [manifest, canonicalManifest, BootReservation.maxReservations]
  have hrequired :
      ¬(!(BootReservation.requiredIdentities.all fun identity =>
        BootReservation.exactlyOnce identity manifest)) = true := by
    simp [manifest, hidentity.1]
  have hvocabulary :
      ¬(!(manifest.all fun reservation =>
        BootReservation.requiredIdentities.contains reservation.identity)) = true := by
    simp [manifest, hidentity.2]
  change BootReservation.validateManifest manifest = .ok intervals
  simp only [BootReservation.validateManifest]
  rw [if_neg hsize, if_neg hrequired, if_neg hvocabulary]
  change manifest.mapM BootReservation.roundInterval = .ok intervals at hround
  rw [hround]
  change (if !richImageContained intervals then
      Except.error BootReservation.Error.inconsistentImage
    else Except.ok intervals) = Except.ok intervals
  simp [hcontained]

/-- The production scalar manifest gate is sufficient, by itself, to
construct and validate the complete canonical rich manifest. -/
theorem canonicalManifest_validate_of_manifestValid
    (lowStart lowLength imageStart imageLength pageStart pageLength
    descriptorStart descriptorLength stacksStart stacksLength
    guardStart guardLength entryStart entryLength usersStart usersLength
    infoStart infoLength : UInt64)
    (hvalid : manifestValid lowStart lowLength imageStart imageLength pageStart pageLength
      descriptorStart descriptorLength stacksStart stacksLength
      guardStart guardLength entryStart entryLength usersStart usersLength
      infoStart infoLength = true) :
    let intervals :=
      canonicalIntervals lowStart lowLength imageStart imageLength pageStart pageLength
        descriptorStart descriptorLength stacksStart stacksLength
        guardStart guardLength entryStart entryLength usersStart usersLength
        infoStart infoLength
    (canonicalManifest lowStart lowLength imageStart imageLength pageStart pageLength
      descriptorStart descriptorLength stacksStart stacksLength
      guardStart guardLength entryStart entryLength usersStart usersLength
      infoStart infoLength).mapM BootReservation.roundInterval = .ok intervals ∧
      richImageContained intervals = true ∧
      BootReservation.validateManifest
        (canonicalManifest lowStart lowLength imageStart imageLength pageStart pageLength
          descriptorStart descriptorLength stacksStart stacksLength
          guardStart guardLength entryStart entryLength usersStart usersLength
          infoStart infoLength) = .ok intervals := by
  have hround := canonicalManifest_rounds_of_manifestValid
    lowStart lowLength imageStart imageLength pageStart pageLength
    descriptorStart descriptorLength stacksStart stacksLength
    guardStart guardLength entryStart entryLength usersStart usersLength
    infoStart infoLength hvalid
  have hcontained := canonicalIntervals_contained_of_manifestValid
    lowStart lowLength imageStart imageLength pageStart pageLength
    descriptorStart descriptorLength stacksStart stacksLength
    guardStart guardLength entryStart entryLength usersStart usersLength
    infoStart infoLength hvalid
  exact ⟨hround, hcontained, canonicalManifest_validate_of_rounds
    lowStart lowLength imageStart imageLength pageStart pageLength
    descriptorStart descriptorLength stacksStart stacksLength
    guardStart guardLength entryStart entryLength usersStart usersLength
    infoStart infoLength _ hround hcontained⟩

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
