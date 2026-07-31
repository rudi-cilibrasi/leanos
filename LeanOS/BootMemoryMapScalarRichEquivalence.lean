import LeanOS.BootMemoryMapFullProjectionABI
import LeanOS.BootMemoryMapStreamAuthority
import LeanOS.BootMemoryMapStreamPipeline
import LeanOS.FrameScrub

/-!
# Universal scalar/rich boot-memory projection equivalence

The freestanding ABI transports the three Boolean candidate predicates as
fixed-width words.  This module gives their canonical encoding from the exact
rich decoded/reserved state and proves, for arbitrary entries, intervals, and
frames, that the allocation-free consumer accepts exactly that rich
projection.  No fixture, concrete memory size, or entry ordering appears in
the theorem.

These are conditional comparison theorems: they start from decoded rich
objects or an existing `BootMemoryMapFullProjectionABI.Authority`.  They do not
prove that production scalar acceptance constructs that authority or that its
event fold is complete.  The allocation-free production C boundary remains
separate tested code.
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

/-- The manifest intervals retained by an accepted allocator initialization
are extensionally the same intervals returned by the manifest validator. -/
theorem initialized_intervals_eq_validated
    (handoff : Handoff) (manifest : List BootReservation.Reservation)
    (intervals : List BootReservation.Interval) (result : BootReservation.Result)
    (hvalidated : BootReservation.validateManifest manifest = .ok intervals)
    (hinitialized :
      BootReservation.initializeAllocator handoff manifest = .ok result) :
    result.intervals = intervals := by
  unfold BootReservation.initializeAllocator at hinitialized
  cases hnormalize : normalize handoff with
  | error reason =>
      rw [hnormalize] at hinitialized
      contradiction
  | ok firmware =>
      rw [hnormalize] at hinitialized
      change (do
        let intervals ← BootReservation.validateManifest manifest
        let regions := BootReservation.overlay intervals firmware.regions
        if hnonempty : regions.isEmpty then throw BootReservation.Error.emptyOutput
        else if hshape : regionShape regions then
          if hdisjoint : pairwiseDisjoint regions then
            if hprecedence : BootReservation.reservationPrecedence intervals regions then
              if hsound : usableSound firmware.entries regions then
                if hentry : BootReservation.ordinaryEntrySeparated intervals then
                  match hinit : FrameAllocator.init regions with
                  | .error _ => throw BootReservation.Error.allocatorRejected
                  | .ok allocator =>
                      if hexcluded :
                          BootReservation.reservationsNonfree intervals allocator then
                        pure
                          (BootReservation.Result.mk firmware intervals regions
                            (Bool.eq_false_iff.mpr hnonempty) hshape hdisjoint
                            hprecedence hsound hentry allocator hinit hexcluded)
                      else throw BootReservation.Error.normalizationInvariant
                else throw BootReservation.Error.ordinaryEntryOverlap
              else throw BootReservation.Error.normalizationInvariant
            else throw BootReservation.Error.normalizationInvariant
          else throw BootReservation.Error.normalizationInvariant
        else throw BootReservation.Error.normalizationInvariant) = .ok result at hinitialized
      rw [hvalidated] at hinitialized
      dsimp only [pure, Except.pure, bind, Except.bind] at hinitialized
      split at hinitialized <;> try contradiction
      split at hinitialized <;> try contradiction
      split at hinitialized <;> try contradiction
      split at hinitialized <;> try contradiction
      split at hinitialized <;> try contradiction
      split at hinitialized <;> try contradiction
      next hnonempty hshape hdisjoint hprecedence hsound hentry =>
        split at hinitialized <;> try contradiction
        next allocator hallocator =>
          split at hinitialized <;> try contradiction
          next hexcluded =>
            injection hinitialized with hresult
            subst result
            rfl

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

/-- The scalar consumer instantiated with canonical rich-state fields
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

/-- An accepted exact rich authority supplies a consumable canonical scalar
projection without any external readiness or reservation premise.  This
direction does not construct rich authority from scalar acceptance. -/
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

/-- The three scalar decision words are fixed consequences of the returned
rich authority.  In particular, production publication cannot ask a caller to
restate usability or reservation exclusion as independent Boolean premises. -/
theorem accepted_authority_field_words
    (authority : BootMemoryMapFullProjectionABI.Authority) :
    usableWord authority.decoded.entries authority.allocation.frame = 1 ∧
      blockedWord authority.decoded.entries authority.allocation.frame = 0 ∧
      manifestWord authority.reserved.intervals authority.allocation.frame = 1 := by
  have husable := authority.selectedUsable
  have hreserved :=
    BootReservation.allocation_excludes_reservations authority.reserved authority.owner
      authority.allocation authority.allocatedBy
  simp only [usableFrameSound, Bool.and_eq_true] at husable
  have hblocked :
      (authority.decoded.entries.any fun entry =>
        entry.kind != .usable &&
          overlaps entry (authority.allocation.frame * pageBytes)
            (authority.allocation.frame * pageBytes + pageBytes)) = false := by
    simpa using husable.2
  unfold usableWord blockedWord manifestWord
  rw [husable.1, hblocked, hreserved]
  simp

/-! ## First-candidate scan refinement

An isolated accepted candidate is not an inverse of rich allocation: a later
candidate can satisfy all three predicates after the rich allocator has
already selected an earlier frame.  The production loop instead has authority
only through its *first* accepted candidate.  The definitions below model that
observable scan contract without adding a freestanding export or changing the
fixed-width production ABI.
-/

/-- The rich decoded/reserved predicate tested for one candidate. -/
def richCandidateAccepted
    (entries : List RawEntry) (intervals : List BootReservation.Interval)
    (frame : Nat) : Bool :=
  usableFrameSound entries frame &&
    !BootReservation.reservedBy intervals frame

/-- The semantic per-frame counterpart of production's usable event fold. -/
def foldUsableEvents (entries : List RawEntry) (frame : Nat) : Bool :=
  entries.foldl (fun usable entry =>
    usable || (entry.kind == .usable &&
      covers entry (frame * pageBytes) (frame * pageBytes + pageBytes))) false

/-- The semantic per-frame counterpart of production's blocking event fold. -/
def foldBlockedEvents (entries : List RawEntry) (frame : Nat) : Bool :=
  entries.foldl (fun blocked entry =>
    blocked || (entry.kind != .usable &&
      overlaps entry (frame * pageBytes) (frame * pageBytes + pageBytes))) false

private theorem foldl_or_eq
    {α : Type} (predicate : α → Bool) (entries : List α) (initial : Bool) :
    entries.foldl (fun found entry => found || predicate entry) initial =
      (initial || entries.any predicate) := by
  induction entries generalizing initial with
  | nil => simp
  | cons entry rest ih =>
      simp only [List.foldl_cons, List.any_cons]
      rw [ih]
      cases initial <;> cases predicate entry <;> simp

/-- The event fold used to build the bitmap is exactly the rich entry
classification, rather than an independent caller-provided predicate. -/
theorem eventFoldProjection_eq_rich
    (entries : List RawEntry) (frame : Nat) :
    (foldUsableEvents entries frame &&
        !foldBlockedEvents entries frame) =
      usableFrameSound entries frame := by
  simp only [foldUsableEvents, foldBlockedEvents, foldl_or_eq]
  rfl

/-- Manifest overlay on the event fold is exactly the complete rich candidate
projection for every bounded bitmap position. -/
theorem eventFoldFreeProjection_eq_richCandidateAccepted
    (entries : List RawEntry) (intervals : List BootReservation.Interval)
    (frame : Nat) :
    (foldUsableEvents entries frame &&
        !foldBlockedEvents entries frame &&
        !BootReservation.reservedBy intervals frame) =
      richCandidateAccepted entries intervals frame := by
  rw [eventFoldProjection_eq_rich]
  rfl

/-- The actual canonical scalar replay used for an arbitrary scanned
candidate, over the immutable input bytes and the candidate-specific initial
target word. -/
def canonicalScalarReplayAt
    (input : BootMemoryMapDecoder.Input) (frame : Nat) :
    BootMemoryMapStreamPipeline.ScalarState :=
  let identity := UInt64.ofNat input.infoAddress
  BootMemoryMapStreamPipeline.scalarReplay
    (BootMemoryMapStreaming.canonicalChunks identity input.bytes)
    (BootMemoryMapStreamPipeline.scalarInitialAt identity input.bytes.length frame)

/-- The exact UInt64-only production decision for one canonical candidate. -/
def scalarCandidateAccepted
    (input : BootMemoryMapDecoder.Input)
    (intervals : List BootReservation.Interval)
    (frame : Nat) : Bool :=
  let scalar := canonicalScalarReplayAt input frame
  consumeExactProjection 4096 (UInt64.ofNat frame) complete
      scalar.word[14]! scalar.word[15]!
      (manifestWord intervals frame) == UInt64.ofNat frame

set_option maxHeartbeats 2000000 in
/-- Candidate-by-candidate acceptance and rejection agreement.  In particular,
this supplies the rejection direction needed at every position preceding the
first accepted production candidate. -/
theorem scalarCandidateAccepted_eq_richCandidateAccepted
    (input : BootMemoryMapDecoder.Input) (decoded : BootMemoryMapDecoder.Decoded)
    (intervals : List BootReservation.Interval)
    (frame : Nat)
    (hdecode : BootMemoryMapDecoder.decode input = .ok decoded)
    (hframe : frame < frameLimit) :
    scalarCandidateAccepted input intervals frame =
      richCandidateAccepted decoded.entries intervals frame := by
  obtain ⟨terminal, htraversal⟩ :=
    BootMemoryMapStreamPipeline.successfulScalarRichTraversal_of_decode
      input decoded frame hdecode hframe
  have hinitial :=
    BootMemoryMapStreamPipeline.scalarInitialAt_of_decode
      input decoded frame hdecode hframe
  have hterminal :=
    BootMemoryMapStreamPipeline.successfulScalarRichTraversal_canonical_terminal
      frame decoded.entries
      (BootMemoryMapStreamPipeline.scalarInitialAt
        (UInt64.ofNat input.infoAddress) input.bytes.length frame)
      terminal
      (BootMemoryMapStreaming.canonicalChunks
        (UInt64.ofNat input.infoAddress) input.bytes)
      hinitial.2.2.2.2.2.2.1 hinitial.2.2.2.2.2.2.2.1 htraversal
  have hterminalEq : terminal = canonicalScalarReplayAt input frame := by
    simpa [canonicalScalarReplayAt] using hterminal.1.symm
  subst terminal
  have husable :
      (canonicalScalarReplayAt input frame).word[14]! =
        usableWord decoded.entries frame := by
    simpa [usableWord] using hterminal.2.2.2.1
  have hblocked :
      (canonicalScalarReplayAt input frame).word[15]! =
        blockedWord decoded.entries frame := by
    simpa [blockedWord] using hterminal.2.2.2.2
  dsimp only [scalarCandidateAccepted]
  rw [husable, hblocked]
  simpa [richCandidateAccepted] using
    (consume_canonical_projection_iff decoded.entries intervals frame hframe)

/-- A declarative model of the actual increasing production scan: `selected`
is in the scanned interval, it accepts, and every earlier candidate rejects.
This is deliberately stronger than merely exhibiting one accepted candidate. -/
def FirstCandidateScan
    (input : BootMemoryMapDecoder.Input)
    (intervals : List BootReservation.Interval)
    (start selected : Nat) : Prop :=
  start ≤ selected ∧
    selected < frameLimit ∧
    scalarCandidateAccepted input intervals selected = true ∧
    ∀ candidate, start ≤ candidate → candidate < selected →
      scalarCandidateAccepted input intervals candidate = false

/-- The first accepted result of an increasing scalar scan is unique. -/
theorem firstCandidateScan_unique
    (input : BootMemoryMapDecoder.Input)
    (intervals : List BootReservation.Interval)
    (start first second : Nat)
    (hfirst : FirstCandidateScan input intervals start first)
    (hsecond : FirstCandidateScan input intervals start second) :
    first = second := by
  by_cases hlt : first < second
  · have hrejected := hsecond.2.2.2 first hfirst.1 hlt
    rw [hfirst.2.2.1] at hrejected
    contradiction
  · by_cases heq : first = second
    · exact heq
    · have hgt : second < first := by omega
      have hrejected := hfirst.2.2.2 second hsecond.1 hgt
      rw [hsecond.2.2.1] at hrejected
      contradiction

/-- A rich authority whose allocator predicate rejects every earlier scanned
candidate constructs the exact first-candidate scalar scan certificate.  The
selected candidate's acceptance is derived from the rich allocation witness;
all earlier scalar rejections are derived from scalar/rich predicate
equivalence rather than assumed independently. -/
theorem authority_constructs_firstCandidateScan
    (authority : BootMemoryMapFullProjectionABI.Authority)
    (start : Nat)
    (hstart : start ≤ authority.allocation.frame) :
    FirstCandidateScan authority.input authority.reserved.intervals
      start authority.allocation.frame := by
  refine ⟨hstart, authority.selectedWithinBound, ?_, ?_⟩
  · rw [scalarCandidateAccepted_eq_richCandidateAccepted
      authority.input authority.decoded authority.reserved.intervals
      authority.allocation.frame authority.decodedBy authority.selectedWithinBound]
    unfold richCandidateAccepted
    rw [authority.selectedUsable]
    have hreserved :=
      BootReservation.allocation_excludes_reservations authority.reserved
        authority.owner authority.allocation authority.allocatedBy
    rw [hreserved]
    rfl
  · intro candidate hcstart hclt
    rw [scalarCandidateAccepted_eq_richCandidateAccepted
      authority.input authority.decoded authority.reserved.intervals candidate
      authority.decodedBy
      (Nat.lt_trans hclt authority.selectedWithinBound)]
    exact authority.earlierCandidatesRejected candidate hclt

/-- Sound inverse binding for the production scan.  A claimed first scalar
result over the same decoded entries and checked intervals must equal the rich
allocator result, provided the rich allocator rejects every preceding numeric
candidate.  The conclusion retains the complete decode/reserve/allocate chain
and states scalar/rich rejection agreement for every earlier candidate.

Unlike the false isolated-candidate converse, this theorem cannot identify a
later accepted frame (for example 300) when the rich allocator and scalar scan
both first accept an earlier frame (for example 256). -/
theorem firstCandidateScan_binds_rich_authority
    (authority : BootMemoryMapFullProjectionABI.Authority)
    (start selected : Nat)
    (hscan :
      FirstCandidateScan authority.input authority.reserved.intervals
        start selected)
    (hstart : start ≤ authority.allocation.frame) :
    selected = authority.allocation.frame ∧
      BootMemoryMapDecoder.decode authority.input = .ok authority.decoded ∧
      BootReservation.initializeAllocator authority.decoded.handoff
          authority.manifest = .ok authority.reserved ∧
      FrameAllocator.allocate authority.reserved.allocator authority.owner =
          .ok authority.allocation ∧
      (∀ candidate, start ≤ candidate → candidate < selected →
        (scalarCandidateAccepted authority.input authority.reserved.intervals
            candidate = false ↔
          richCandidateAccepted authority.decoded.entries
            authority.reserved.intervals candidate = false)) := by
  have hauthority :=
    authority_constructs_firstCandidateScan authority start hstart
  have hselected :=
    firstCandidateScan_unique authority.input authority.reserved.intervals
      start selected authority.allocation.frame hscan hauthority
  subst selected
  refine ⟨rfl, authority.decodedBy, authority.reservedBy, authority.allocatedBy, ?_⟩
  intro candidate _ hcandidate
  rw [scalarCandidateAccepted_eq_richCandidateAccepted
    authority.input authority.decoded authority.reserved.intervals candidate
    authority.decodedBy
    (Nat.lt_trans hcandidate authority.selectedWithinBound)]

/-- Querying a second frame is an allocator transition, not a second set bit
accepted from bitmap transport.  Any exposed continuation result is exactly
the allocation performed from the first allocation's successor state. -/
theorem authority_continuation_binds_second_allocation
    (authority : BootMemoryMapFullProjectionABI.Authority)
    (second : FrameAllocator.Allocation)
    (hsecond : authority.continuation = .ok second) :
    FrameAllocator.allocate authority.allocation.state authority.owner =
      .ok second := by
  rw [authority.continuedBy, hsecond]

/-- Once a separate rescan names the same selected frame and the frame-scrub
boundary supplies its success word, production publication is determined by
the complete rich authority.  Decode status and all candidate predicates are
constructed here rather than accepted from the caller.  Scrub success remains
an explicit premise until the boot allocator is composed with `FrameScrub`. -/
theorem accepted_authority_publishes_after_rescan_and_scrub
    (authority : BootMemoryMapFullProjectionABI.Authority)
    (rescanned scrubbed : UInt64)
    (hrescanned : rescanned = UInt64.ofNat authority.allocation.frame)
    (hscrubbed : scrubbed = 1) :
    publishAuthority (UInt64.ofNat authority.allocation.frame) rescanned complete
        (usableWord authority.decoded.entries authority.allocation.frame)
        (blockedWord authority.decoded.entries authority.allocation.frame)
        (manifestWord authority.reserved.intervals authority.allocation.frame)
        scrubbed =
      UInt64.ofNat authority.allocation.frame + 1 := by
  obtain ⟨husable, hblocked, hmanifest⟩ :=
    accepted_authority_field_words authority
  subst rescanned
  subst scrubbed
  rw [husable, hblocked, hmanifest]
  unfold publishAuthority
  have hframe : UInt64.ofNat authority.allocation.frame < 4096 := by
    have hsize : authority.allocation.frame < UInt64.size :=
      Nat.lt_trans authority.selectedWithinBound (by decide)
    exact
      (UInt64.ofNat_lt_iff_lt hsize (by decide)).2 authority.selectedWithinBound
  simp [hframe]

/-- The proof-relevant boundary between one complete rich boot-memory result
and one accepted scrub publication.  The scrub model must publish the exact
frame retained by the rich allocation witness; no scalar rescan identity or
scrub-success word is stored in this certificate. -/
structure ScrubbedPublication where
  rich : BootMemoryMapFullProjectionABI.Authority
  before : FrameScrub.State
  subject : FrameScrub.SubjectId
  slot : FrameScrub.SlotId
  accepted :
    (FrameScrub.allocate before rich.owner subject slot).result = .accepted
  selected :
    (FrameScrub.allocate before rich.owner subject slot).state.memory.binding rich.owner =
      some rich.allocation.frame

/-- Minimal fresh lifetime state whose allocator is exactly the reservation-
overlaid allocator retained by the rich authority.  Bytes are an explicit
input because their pre-scrub contents are irrelevant; all capability and
lifetime authority begins empty. -/
def sharedAllocatorScrubState
    (rich : BootMemoryMapFullProjectionABI.Authority)
    (bytes : FrameScrub.FrameBytes) : FrameScrub.State :=
  { memory :=
      { capabilities :=
          { subjects := fun subject => subject == 0
            objects := fun _ => false
            kinds := fun _ => none
            slots := fun _ _ => none }
        allocator := rich.reserved.allocator
        binding := fun _ => none
        issued := fun _ => false }
    bytes
    written := fun _ => false }

/-- The shared allocator transition is accepted by the scrub model without a
second selection premise.  The accepted rich allocation equation rewrites the
only allocator call made by `FrameScrub.allocate`. -/
theorem sharedAllocatorScrubState_accepts
    (rich : BootMemoryMapFullProjectionABI.Authority)
    (bytes : FrameScrub.FrameBytes) :
    (FrameScrub.allocate (sharedAllocatorScrubState rich bytes)
      rich.owner 0 0).result = .accepted := by
  have hslot : CapabilityHandle.slotRadix - 1 ≠ 0 := by native_decide
  have hgeneration : ¬CapabilityHandle.generationRadix ≤ 2 := by native_decide
  simp [FrameScrub.allocate, sharedAllocatorScrubState,
    MemoryLifecycle.allocate, Capability.slotInRange,
    CapabilityHandle.slotReserved, CapabilityHandle.generationReserved,
    hslot, hgeneration, rich.allocatedBy, MemoryLifecycle.setBinding]

/-- The binding published by the shared scrub transition is the exact frame
selected by the rich decoder/reservation/allocator chain. -/
theorem sharedAllocatorScrubState_selects
    (rich : BootMemoryMapFullProjectionABI.Authority)
    (bytes : FrameScrub.FrameBytes) :
    (FrameScrub.allocate (sharedAllocatorScrubState rich bytes)
      rich.owner 0 0).state.memory.binding rich.owner =
        some rich.allocation.frame := by
  have hslot : CapabilityHandle.slotRadix - 1 ≠ 0 := by native_decide
  have hgeneration : ¬CapabilityHandle.generationRadix ≤ 2 := by native_decide
  simp [FrameScrub.allocate, sharedAllocatorScrubState,
    MemoryLifecycle.allocate, Capability.slotInRange,
    CapabilityHandle.slotReserved, CapabilityHandle.generationReserved,
    hslot, hgeneration, rich.allocatedBy, MemoryLifecycle.setBinding]

/-- Construct scrub/publication authority directly from one rich authority and
arbitrary prior frame bytes.  No caller supplies an accepted bit, rescanned
identity, selected-frame equality, or independent allocator state. -/
def scrubbedPublicationOfAuthority
    (rich : BootMemoryMapFullProjectionABI.Authority)
    (bytes : FrameScrub.FrameBytes) : ScrubbedPublication :=
  { rich
    before := sharedAllocatorScrubState rich bytes
    subject := 0
    slot := 0
    accepted := sharedAllocatorScrubState_accepts rich bytes
    selected := sharedAllocatorScrubState_selects rich bytes }

/-- A scrubbed publication certificate binds all three production decisions
to the complete rich result: exact scalar selection returns its frame,
publication derives its token without caller-supplied decision words, and the
same published lifetime is completely scrubbed and allocator-owned. -/
theorem scrubbedPublication_complete_authority
    (publication : ScrubbedPublication) :
    consumeExactProjection 4096
        (UInt64.ofNat publication.rich.allocation.frame) complete
        (usableWord publication.rich.decoded.entries
          publication.rich.allocation.frame)
        (blockedWord publication.rich.decoded.entries
          publication.rich.allocation.frame)
        (manifestWord publication.rich.reserved.intervals
          publication.rich.allocation.frame) =
      UInt64.ofNat publication.rich.allocation.frame ∧
    publishAuthority
        (UInt64.ofNat publication.rich.allocation.frame)
        (UInt64.ofNat publication.rich.allocation.frame) complete
        (usableWord publication.rich.decoded.entries
          publication.rich.allocation.frame)
        (blockedWord publication.rich.decoded.entries
          publication.rich.allocation.frame)
        (manifestWord publication.rich.reserved.intervals
          publication.rich.allocation.frame) 1 =
      UInt64.ofNat publication.rich.allocation.frame + 1 ∧
    FrameScrub.Fresh
      (FrameScrub.allocate publication.before publication.rich.owner
        publication.subject publication.slot).state publication.rich.owner ∧
    FrameAllocator.IsOwnedBy
      (FrameScrub.allocate publication.before publication.rich.owner
        publication.subject publication.slot).state.memory.allocator
      publication.rich.allocation.frame publication.rich.owner := by
  have hselection :=
    accepted_authority_projection_consumable publication.rich
  have hpublication :=
    accepted_authority_publishes_after_rescan_and_scrub publication.rich
      (UInt64.ofNat publication.rich.allocation.frame) 1 rfl rfl
  have hfresh :=
    FrameScrub.allocation_publishes_scrubbed publication.before
      publication.rich.owner publication.subject publication.slot publication.accepted
  obtain ⟨frame, hbinding, howned⟩ :=
    FrameScrub.allocation_publishes_owned publication.before
      publication.rich.owner publication.subject publication.slot publication.accepted
  rw [publication.selected] at hbinding
  injection hbinding with hframe
  subst frame
  exact ⟨hselection, hpublication, hfresh, howned⟩

/-- Every rich authority constructs the complete scrub/publication
certificate when paired with arbitrary prior frame bytes.  The pre-state
shares `rich.reserved.allocator`, so `rich.allocatedBy` proves both selections
are the same transition rather than merely equal post-hoc observations. -/
theorem scrubbedPublicationOfAuthority_complete
    (rich : BootMemoryMapFullProjectionABI.Authority)
    (bytes : FrameScrub.FrameBytes) :
    let publication := scrubbedPublicationOfAuthority rich bytes
    consumeExactProjection 4096
        (UInt64.ofNat rich.allocation.frame) complete
        (usableWord rich.decoded.entries rich.allocation.frame)
        (blockedWord rich.decoded.entries rich.allocation.frame)
        (manifestWord rich.reserved.intervals rich.allocation.frame) =
      UInt64.ofNat rich.allocation.frame ∧
    publishAuthority
        (UInt64.ofNat rich.allocation.frame)
        (UInt64.ofNat rich.allocation.frame) complete
        (usableWord rich.decoded.entries rich.allocation.frame)
        (blockedWord rich.decoded.entries rich.allocation.frame)
        (manifestWord rich.reserved.intervals rich.allocation.frame) 1 =
      UInt64.ofNat rich.allocation.frame + 1 ∧
    FrameScrub.Fresh
      (FrameScrub.allocate publication.before rich.owner
        publication.subject publication.slot).state rich.owner ∧
    FrameAllocator.IsOwnedBy
      (FrameScrub.allocate publication.before rich.owner
        publication.subject publication.slot).state.memory.allocator
      rich.allocation.frame rich.owner := by
  exact scrubbedPublication_complete_authority
    (scrubbedPublicationOfAuthority rich bytes)

/-- The exact terminal scalar fields that still require semantic refinement
from the rich decoder.  Naming this relation keeps the production composition
honest: chunk reconstruction alone does not establish parser-state agreement,
and callers cannot substitute synthetic readiness or coverage words. -/
def ScalarTerminalProjectionAgrees
    (scalar : BootMemoryMapStreamPipeline.ScalarState)
    (authority : BootMemoryMapFullProjectionABI.Authority) : Prop :=
  scalar.word[1]! = complete ∧
    scalar.word[2]! = noError ∧
    scalar.word[14]! =
      usableWord authority.decoded.entries authority.allocation.frame ∧
    scalar.word[15]! =
      blockedWord authority.decoded.entries authority.allocation.frame

/-- Executable form of `ScalarTerminalProjectionAgrees`, used by the
fail-closed canonical authorization gate. -/
def scalarTerminalProjectionMatches
    (scalar : BootMemoryMapStreamPipeline.ScalarState)
    (authority : BootMemoryMapFullProjectionABI.Authority) : Bool :=
  scalar.word[1]! == complete &&
    scalar.word[2]! == noError &&
    scalar.word[14]! ==
      usableWord authority.decoded.entries authority.allocation.frame &&
    scalar.word[15]! ==
      blockedWord authority.decoded.entries authority.allocation.frame

theorem scalarTerminalProjectionMatches_iff
    (scalar : BootMemoryMapStreamPipeline.ScalarState)
    (authority : BootMemoryMapFullProjectionABI.Authority) :
    scalarTerminalProjectionMatches scalar authority = true ↔
      ScalarTerminalProjectionAgrees scalar authority := by
  simp only [scalarTerminalProjectionMatches, ScalarTerminalProjectionAgrees,
    Bool.and_eq_true, beq_iff_eq]
  constructor
  · intro h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  · intro h
    exact ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩

/-! ## Raw-byte/canonical-manifest production composition

This proof-only composition mirrors the production gates without adding a
freestanding export.  The immutable raw input is passed unchanged to the exact
rich transition, while the positional ABI words construct the only manifest
that can reach it. -/

def runCanonical
    (input : BootMemoryMapDecoder.Input)
    (lowStart lowLength imageStart imageLength pageStart pageLength
    descriptorStart descriptorLength stacksStart stacksLength
    guardStart guardLength entryStart entryLength usersStart usersLength
    infoStart infoLength : UInt64)
    (owner : FrameAllocator.OwnerId) :
    Except BootMemoryMapFullProjectionABI.Error
      BootMemoryMapFullProjectionABI.Authority :=
  if manifestValid lowStart lowLength imageStart imageLength pageStart pageLength
      descriptorStart descriptorLength stacksStart stacksLength
      guardStart guardLength entryStart entryLength usersStart usersLength
      infoStart infoLength then
    BootMemoryMapFullProjectionABI.run input
      (canonicalManifest lowStart lowLength imageStart imageLength pageStart pageLength
        descriptorStart descriptorLength stacksStart stacksLength
        guardStart guardLength entryStart entryLength usersStart usersLength
        infoStart infoLength) owner
  else
    .error (.reservation .inconsistentImage)

/-- Acceptance of the composed production specification universally binds the
immutable raw bytes to the rich decoder, all canonical manifest identities to
the rich validator, and the selected rich authority to the exact scalar
consumer.  There are no fixture, entry-order, or memory-size premises. -/
theorem runCanonical_acceptance_binding
    (input : BootMemoryMapDecoder.Input)
    (lowStart lowLength imageStart imageLength pageStart pageLength
    descriptorStart descriptorLength stacksStart stacksLength
    guardStart guardLength entryStart entryLength usersStart usersLength
    infoStart infoLength : UInt64)
    (owner : FrameAllocator.OwnerId)
    (authority : BootMemoryMapFullProjectionABI.Authority)
    (haccepted :
      runCanonical input lowStart lowLength imageStart imageLength pageStart pageLength
        descriptorStart descriptorLength stacksStart stacksLength
        guardStart guardLength entryStart entryLength usersStart usersLength
        infoStart infoLength owner = .ok authority) :
    let manifest :=
      canonicalManifest lowStart lowLength imageStart imageLength pageStart pageLength
        descriptorStart descriptorLength stacksStart stacksLength
        guardStart guardLength entryStart entryLength usersStart usersLength
        infoStart infoLength
    let intervals :=
      canonicalIntervals lowStart lowLength imageStart imageLength pageStart pageLength
        descriptorStart descriptorLength stacksStart stacksLength
        guardStart guardLength entryStart entryLength usersStart usersLength
        infoStart infoLength
    manifestValid lowStart lowLength imageStart imageLength pageStart pageLength
        descriptorStart descriptorLength stacksStart stacksLength
        guardStart guardLength entryStart entryLength usersStart usersLength
        infoStart infoLength = true ∧
      authority.input = input ∧
      authority.manifest = manifest ∧
      BootMemoryMapDecoder.decode input = .ok authority.decoded ∧
      BootReservation.validateManifest manifest = .ok intervals ∧
      authority.reserved.intervals = intervals ∧
      consumeExactProjection 4096 (UInt64.ofNat authority.allocation.frame) complete
          (usableWord authority.decoded.entries authority.allocation.frame)
          (blockedWord authority.decoded.entries authority.allocation.frame)
          (manifestWord authority.reserved.intervals authority.allocation.frame) =
        UInt64.ofNat authority.allocation.frame := by
  dsimp only
  unfold runCanonical at haccepted
  split at haccepted
  · rename_i hvalid
    have hinputs := BootMemoryMapFullProjectionABI.accepted_inputs
      input
      (canonicalManifest lowStart lowLength imageStart imageLength pageStart pageLength
        descriptorStart descriptorLength stacksStart stacksLength
        guardStart guardLength entryStart entryLength usersStart usersLength
        infoStart infoLength)
      owner authority haccepted
    have hvalidated := canonicalManifest_validate_of_manifestValid
      lowStart lowLength imageStart imageLength pageStart pageLength
      descriptorStart descriptorLength stacksStart stacksLength
      guardStart guardLength entryStart entryLength usersStart usersLength
      infoStart infoLength hvalid
    have hdecoded : BootMemoryMapDecoder.decode input = .ok authority.decoded := by
      rw [← hinputs.1]
      exact authority.decodedBy
    have hintervals : authority.reserved.intervals =
        canonicalIntervals lowStart lowLength imageStart imageLength pageStart pageLength
          descriptorStart descriptorLength stacksStart stacksLength
          guardStart guardLength entryStart entryLength usersStart usersLength
          infoStart infoLength := by
      apply initialized_intervals_eq_validated authority.decoded.handoff
        (canonicalManifest lowStart lowLength imageStart imageLength pageStart pageLength
          descriptorStart descriptorLength stacksStart stacksLength
          guardStart guardLength entryStart entryLength usersStart usersLength
          infoStart infoLength)
      · exact hvalidated.2.2
      · rw [← hinputs.2.1]
        exact authority.reservedBy
    exact ⟨hvalid, hinputs.1, hinputs.2.1, hdecoded,
      hvalidated.2.2, hintervals, accepted_authority_projection_consumable authority⟩
  · contradiction

/-- Every rich authority structurally initializes its canonical scalar replay
with the admitted parser header and the exact rich-selected target.  The next
refinement slice can therefore induct over chunks without assuming an initial
status, diagnostic, identity, extent, parser phase, or coverage accumulator. -/
theorem canonicalScalarInitial_of_authority
    (authority : BootMemoryMapFullProjectionABI.Authority) :
    let initial :=
      BootMemoryMapStreamPipeline.scalarInitialAt
        (UInt64.ofNat authority.input.infoAddress)
        authority.input.bytes.length authority.allocation.frame
    initial.word[1]! = active ∧
      initial.word[2]! = noError ∧
      initial.word[3]! = UInt64.ofNat authority.input.infoAddress ∧
      initial.word[4]! = UInt64.ofNat authority.input.bytes.length ∧
      initial.word[5]! = 0 ∧
      initial.word[7]! = phaseInfo ∧
      initial.word[14]! = 0 ∧
      initial.word[15]! = 0 ∧
      initial.word[16]! = UInt64.ofNat authority.allocation.frame := by
  exact BootMemoryMapStreamPipeline.scalarInitialAt_of_decode
    authority.input authority.decoded authority.allocation.frame
    authority.decodedBy authority.selectedWithinBound

/-- The actual terminal scalar replay paired with one rich authority.  Its
stream identity comes from the immutable decoder input, and its candidate is
the frame selected by the rich allocator. -/
def canonicalScalarReplay
    (input : BootMemoryMapDecoder.Input)
    (authority : BootMemoryMapFullProjectionABI.Authority) :
    BootMemoryMapStreamPipeline.ScalarState :=
  let identity := UInt64.ofNat input.infoAddress
  BootMemoryMapStreamPipeline.scalarReplay
    (BootMemoryMapStreaming.canonicalChunks identity input.bytes)
    (BootMemoryMapStreamPipeline.scalarInitialAt identity input.bytes.length
      authority.allocation.frame)

/-- The universal terminal-state structural refinement specialized to one
complete rich authority.  The checked rich-byte replay cannot terminate at a
different scalar state, and its initial identity, extent, phase, accumulators,
and selected target are derived from the authority rather than supplied by a
caller. -/
theorem canonicalScalarReplay_structurally_refines_authority
    (authority : BootMemoryMapFullProjectionABI.Authority) :
    let identity := UInt64.ofNat authority.input.infoAddress
    let initial :=
      BootMemoryMapStreamPipeline.scalarInitialAt identity
        authority.input.bytes.length authority.allocation.frame
    initial.word[1]! = active ∧
      initial.word[2]! = noError ∧
      initial.word[3]! = identity ∧
      initial.word[4]! = UInt64.ofNat authority.input.bytes.length ∧
      initial.word[5]! = 0 ∧
      initial.word[7]! = phaseInfo ∧
      initial.word[14]! = 0 ∧
      initial.word[15]! = 0 ∧
      initial.word[16]! = UInt64.ofNat authority.allocation.frame ∧
      BootMemoryMapStreamPipeline.checkedScalarReplay
          (BootMemoryMapStreaming.canonicalChunks identity authority.input.bytes)
          initial =
        .ok (canonicalScalarReplay authority.input authority) := by
  simpa [canonicalScalarReplay] using
    (BootMemoryMapStreamPipeline.canonicalTerminalReplay_of_decode
      authority.input authority.decoded authority.allocation.frame
      authority.decodedBy authority.selectedWithinBound)

/-- The structural scalar/rich traversal certificate is sufficient to prove
the four terminal fields rechecked by `authorizeCanonical`; no additional
terminal-value assumption is needed. -/
theorem successfulScalarRichTraversal_agrees_authority
    (authority : BootMemoryMapFullProjectionABI.Authority)
    (htraversal :
      BootMemoryMapStreamPipeline.SuccessfulScalarRichTraversal
        authority.allocation.frame authority.decoded.entries
        (BootMemoryMapStreamPipeline.scalarInitialAt
          (UInt64.ofNat authority.input.infoAddress) authority.input.bytes.length
          authority.allocation.frame)
        (BootMemoryMapStreaming.canonicalChunks
          (UInt64.ofNat authority.input.infoAddress) authority.input.bytes)
        (canonicalScalarReplay authority.input authority)) :
    ScalarTerminalProjectionAgrees
      (canonicalScalarReplay authority.input authority) authority := by
  have hinitial := canonicalScalarInitial_of_authority authority
  have hterminal :=
    BootMemoryMapStreamPipeline.successfulScalarRichTraversal_canonical_terminal
      authority.allocation.frame authority.decoded.entries
      (BootMemoryMapStreamPipeline.scalarInitialAt
        (UInt64.ofNat authority.input.infoAddress) authority.input.bytes.length
        authority.allocation.frame)
      (canonicalScalarReplay authority.input authority)
      (BootMemoryMapStreaming.canonicalChunks
        (UInt64.ofNat authority.input.infoAddress) authority.input.bytes)
      hinitial.2.2.2.2.2.2.1 hinitial.2.2.2.2.2.2.2.1 htraversal
  exact ⟨hterminal.2.1, hterminal.2.2.1,
    by simpa [usableWord] using hterminal.2.2.2.1,
    by simpa [blockedWord] using hterminal.2.2.2.2⟩

/-- Every rich authority necessarily passes the scalar terminal projection:
the whole-tag structural induction constructs the traversal, and whole-replay
folding fixes completion, diagnostics, usable coverage, and blocked overlap. -/
theorem canonicalScalarReplay_agrees_authority
    (authority : BootMemoryMapFullProjectionABI.Authority) :
    ScalarTerminalProjectionAgrees
      (canonicalScalarReplay authority.input authority) authority := by
  obtain ⟨terminal, htraversal⟩ :=
    BootMemoryMapStreamPipeline.successfulScalarRichTraversal_of_decode
      authority.input authority.decoded authority.allocation.frame
      authority.decodedBy authority.selectedWithinBound
  have hterminal :=
    BootMemoryMapStreamPipeline.successfulScalarRichTraversal_terminal_words
      authority.allocation.frame authority.decoded.entries
      (BootMemoryMapStreamPipeline.scalarInitialAt
        (UInt64.ofNat authority.input.infoAddress) authority.input.bytes.length
        authority.allocation.frame)
      terminal
      (BootMemoryMapStreaming.canonicalChunks
        (UInt64.ofNat authority.input.infoAddress) authority.input.bytes)
      htraversal
  have hterminalEq :
      terminal = canonicalScalarReplay authority.input authority := by
    simpa [canonicalScalarReplay] using hterminal.1.symm
  subst terminal
  exact successfulScalarRichTraversal_agrees_authority authority htraversal

theorem scalarTerminalProjectionMatches_canonicalScalarReplay
    (authority : BootMemoryMapFullProjectionABI.Authority) :
    scalarTerminalProjectionMatches
        (canonicalScalarReplay authority.input authority) authority = true :=
  (scalarTerminalProjectionMatches_iff _ _).2
    (canonicalScalarReplay_agrees_authority authority)

/-- Canonical production composition with the complete rich projection as an
explicit claimed output.  Unlike `runCanonical`, this boundary cannot return
authority after a caller mutates an entry, normalized region, checked
reservation interval, overlaid region, or selected frame.  It also rejects
unless the actual scalar replay's terminal parser and coverage fields agree
with the rich authority. -/
def authorizeCanonical
    (input : BootMemoryMapDecoder.Input)
    (lowStart lowLength imageStart imageLength pageStart pageLength
    descriptorStart descriptorLength stacksStart stacksLength
    guardStart guardLength entryStart entryLength usersStart usersLength
    infoStart infoLength : UInt64)
    (owner : FrameAllocator.OwnerId)
    (claimed : BootMemoryMapFullProjectionABI.Projection) :
    Except BootMemoryMapFullProjectionABI.Error
      BootMemoryMapFullProjectionABI.Authority :=
  if manifestValid lowStart lowLength imageStart imageLength pageStart pageLength
      descriptorStart descriptorLength stacksStart stacksLength
      guardStart guardLength entryStart entryLength usersStart usersLength
      infoStart infoLength then
    do
      let authority ←
        BootMemoryMapFullProjectionABI.authorize input
          (canonicalManifest lowStart lowLength imageStart imageLength pageStart pageLength
            descriptorStart descriptorLength stacksStart stacksLength
            guardStart guardLength entryStart entryLength usersStart usersLength
            infoStart infoLength) owner claimed
      if scalarTerminalProjectionMatches (canonicalScalarReplay input authority) authority then
        pure authority
      else
        throw .outputMutation
  else
    .error (.reservation .inconsistentImage)

/-- Every accepted canonical authorization universally binds the actual scalar
terminal replay to the returned complete rich authority.  Mismatching parser
status, diagnostics, usable coverage, or non-usable overlap rejects before any
authority escapes. -/
theorem authorizeCanonical_acceptance_scalar_agreement
    (input : BootMemoryMapDecoder.Input)
    (lowStart lowLength imageStart imageLength pageStart pageLength
    descriptorStart descriptorLength stacksStart stacksLength
    guardStart guardLength entryStart entryLength usersStart usersLength
    infoStart infoLength : UInt64)
    (owner : FrameAllocator.OwnerId)
    (claimed : BootMemoryMapFullProjectionABI.Projection)
    (authority : BootMemoryMapFullProjectionABI.Authority)
    (haccepted :
      authorizeCanonical input lowStart lowLength imageStart imageLength
        pageStart pageLength descriptorStart descriptorLength stacksStart stacksLength
        guardStart guardLength entryStart entryLength usersStart usersLength
        infoStart infoLength owner claimed = .ok authority) :
    let manifest :=
      canonicalManifest lowStart lowLength imageStart imageLength pageStart pageLength
        descriptorStart descriptorLength stacksStart stacksLength
        guardStart guardLength entryStart entryLength usersStart usersLength
        infoStart infoLength
    manifestValid lowStart lowLength imageStart imageLength pageStart pageLength
        descriptorStart descriptorLength stacksStart stacksLength
        guardStart guardLength entryStart entryLength usersStart usersLength
        infoStart infoLength = true ∧
      BootMemoryMapFullProjectionABI.authorize input manifest owner claimed =
        .ok authority ∧
      ScalarTerminalProjectionAgrees (canonicalScalarReplay input authority) authority := by
  dsimp only
  unfold authorizeCanonical at haccepted
  split at haccepted
  · rename_i hvalid
    let manifest :=
      canonicalManifest lowStart lowLength imageStart imageLength pageStart pageLength
        descriptorStart descriptorLength stacksStart stacksLength
        guardStart guardLength entryStart entryLength usersStart usersLength
        infoStart infoLength
    cases hauthorize :
        BootMemoryMapFullProjectionABI.authorize input manifest owner claimed with
    | error reason =>
        rw [hauthorize] at haccepted
        contradiction
    | ok canonical =>
        rw [hauthorize] at haccepted
        dsimp only [bind, Except.bind] at haccepted
        by_cases hmatches :
            scalarTerminalProjectionMatches
              (canonicalScalarReplay input canonical) canonical = true
        · rw [if_pos hmatches] at haccepted
          injection haccepted with heq
          subst authority
          exact ⟨hvalid, rfl,
            (scalarTerminalProjectionMatches_iff _ _).1 hmatches⟩
        · rw [if_neg hmatches] at haccepted
          contradiction
  · contradiction

/-- Acceptance through the complete-output gate implies the existing
raw-byte/canonical-manifest binding and additionally fixes the entire claimed
rich projection to the returned authority.  The stronger scalar agreement
theorem above additionally binds the actual terminal replay. -/
theorem authorizeCanonical_acceptance_binding
    (input : BootMemoryMapDecoder.Input)
    (lowStart lowLength imageStart imageLength pageStart pageLength
    descriptorStart descriptorLength stacksStart stacksLength
    guardStart guardLength entryStart entryLength usersStart usersLength
    infoStart infoLength : UInt64)
    (owner : FrameAllocator.OwnerId)
    (claimed : BootMemoryMapFullProjectionABI.Projection)
    (authority : BootMemoryMapFullProjectionABI.Authority)
    (haccepted :
      authorizeCanonical input lowStart lowLength imageStart imageLength
        pageStart pageLength descriptorStart descriptorLength stacksStart stacksLength
        guardStart guardLength entryStart entryLength usersStart usersLength
        infoStart infoLength owner claimed = .ok authority) :
    let manifest :=
      canonicalManifest lowStart lowLength imageStart imageLength pageStart pageLength
        descriptorStart descriptorLength stacksStart stacksLength
        guardStart guardLength entryStart entryLength usersStart usersLength
        infoStart infoLength
    let intervals :=
      canonicalIntervals lowStart lowLength imageStart imageLength pageStart pageLength
        descriptorStart descriptorLength stacksStart stacksLength
        guardStart guardLength entryStart entryLength usersStart usersLength
        infoStart infoLength
    manifestValid lowStart lowLength imageStart imageLength pageStart pageLength
        descriptorStart descriptorLength stacksStart stacksLength
        guardStart guardLength entryStart entryLength usersStart usersLength
        infoStart infoLength = true ∧
      authority.input = input ∧
      authority.manifest = manifest ∧
      BootMemoryMapDecoder.decode input = .ok authority.decoded ∧
      BootReservation.validateManifest manifest = .ok intervals ∧
      authority.reserved.intervals = intervals ∧
      consumeExactProjection 4096 (UInt64.ofNat authority.allocation.frame) complete
          (usableWord authority.decoded.entries authority.allocation.frame)
          (blockedWord authority.decoded.entries authority.allocation.frame)
          (manifestWord authority.reserved.intervals authority.allocation.frame) =
        UInt64.ofNat authority.allocation.frame ∧
      claimed = BootMemoryMapFullProjectionABI.projection authority := by
  dsimp only
  let manifest :=
    canonicalManifest lowStart lowLength imageStart imageLength pageStart pageLength
      descriptorStart descriptorLength stacksStart stacksLength
      guardStart guardLength entryStart entryLength usersStart usersLength
      infoStart infoLength
  have hscalar := authorizeCanonical_acceptance_scalar_agreement input
    lowStart lowLength imageStart imageLength pageStart pageLength
    descriptorStart descriptorLength stacksStart stacksLength
    guardStart guardLength entryStart entryLength usersStart usersLength
    infoStart infoLength owner claimed authority haccepted
  have hauthorize :=
    BootMemoryMapFullProjectionABI.authorize_acceptance_binding
      input manifest owner claimed authority hscalar.2.1
  have hrunCanonical :
      runCanonical input lowStart lowLength imageStart imageLength pageStart pageLength
        descriptorStart descriptorLength stacksStart stacksLength
        guardStart guardLength entryStart entryLength usersStart usersLength
        infoStart infoLength owner = .ok authority := by
    unfold runCanonical
    rw [if_pos hscalar.1]
    exact hauthorize.1
  have hbinding := runCanonical_acceptance_binding input
    lowStart lowLength imageStart imageLength pageStart pageLength
    descriptorStart descriptorLength stacksStart stacksLength
    guardStart guardLength entryStart entryLength usersStart usersLength
    infoStart infoLength owner authority hrunCanonical
  exact ⟨hbinding.1, hbinding.2.1, hbinding.2.2.1, hbinding.2.2.2.1,
    hbinding.2.2.2.2.1, hbinding.2.2.2.2.2.1,
    hbinding.2.2.2.2.2.2, hauthorize.2⟩

/-- At the accepted canonical production boundary, the checked immutable-byte
replay, the generated scalar replay, and the complete rich authority have one
terminal result.  In particular, the terminal usable and non-usable words are
the classifications of the returned rich decoded entries, not caller-supplied
substitutes. -/
theorem authorizeCanonical_checkedReplay_semantic_agreement
    (input : BootMemoryMapDecoder.Input)
    (lowStart lowLength imageStart imageLength pageStart pageLength
    descriptorStart descriptorLength stacksStart stacksLength
    guardStart guardLength entryStart entryLength usersStart usersLength
    infoStart infoLength : UInt64)
    (owner : FrameAllocator.OwnerId)
    (claimed : BootMemoryMapFullProjectionABI.Projection)
    (authority : BootMemoryMapFullProjectionABI.Authority)
    (haccepted :
      authorizeCanonical input lowStart lowLength imageStart imageLength
        pageStart pageLength descriptorStart descriptorLength stacksStart stacksLength
        guardStart guardLength entryStart entryLength usersStart usersLength
        infoStart infoLength owner claimed = .ok authority) :
    let identity := UInt64.ofNat authority.input.infoAddress
    let initial :=
      BootMemoryMapStreamPipeline.scalarInitialAt identity
        authority.input.bytes.length authority.allocation.frame
    let terminal := canonicalScalarReplay authority.input authority
    BootMemoryMapStreamPipeline.checkedScalarReplay
          (BootMemoryMapStreaming.canonicalChunks identity authority.input.bytes)
          initial = .ok terminal ∧
      terminal.word[1]! = complete ∧
      terminal.word[2]! = noError ∧
      terminal.word[14]! =
        usableWord authority.decoded.entries authority.allocation.frame ∧
      terminal.word[15]! =
        blockedWord authority.decoded.entries authority.allocation.frame := by
  dsimp only
  have hstructural :=
    canonicalScalarReplay_structurally_refines_authority authority
  have hscalar := authorizeCanonical_acceptance_scalar_agreement input
    lowStart lowLength imageStart imageLength pageStart pageLength
    descriptorStart descriptorLength stacksStart stacksLength
    guardStart guardLength entryStart entryLength usersStart usersLength
    infoStart infoLength owner claimed authority haccepted
  have hbinding := authorizeCanonical_acceptance_binding input
    lowStart lowLength imageStart imageLength pageStart pageLength
    descriptorStart descriptorLength stacksStart stacksLength
    guardStart guardLength entryStart entryLength usersStart usersLength
    infoStart infoLength owner claimed authority haccepted
  have hagreement :
      ScalarTerminalProjectionAgrees
        (canonicalScalarReplay authority.input authority) authority := by
    rw [hbinding.2.1]
    exact hscalar.2.2
  unfold ScalarTerminalProjectionAgrees at hagreement
  exact ⟨hstructural.2.2.2.2.2.2.2.2.2,
    hagreement.1, hagreement.2.1,
    hagreement.2.2.1, hagreement.2.2.2⟩

/-- The canonical authorization gate feeds the actual scalar replay's terminal
fields—not rich-side substitutes—into the production consumer and returns
exactly the rich-selected frame. -/
theorem authorizeCanonical_scalarReplay_projection_binding
    (input : BootMemoryMapDecoder.Input)
    (lowStart lowLength imageStart imageLength pageStart pageLength
    descriptorStart descriptorLength stacksStart stacksLength
    guardStart guardLength entryStart entryLength usersStart usersLength
    infoStart infoLength : UInt64)
    (owner : FrameAllocator.OwnerId)
    (claimed : BootMemoryMapFullProjectionABI.Projection)
    (authority : BootMemoryMapFullProjectionABI.Authority)
    (haccepted :
      authorizeCanonical input lowStart lowLength imageStart imageLength
        pageStart pageLength descriptorStart descriptorLength stacksStart stacksLength
        guardStart guardLength entryStart entryLength usersStart usersLength
        infoStart infoLength owner claimed = .ok authority) :
    let scalar := canonicalScalarReplay input authority
    scalar.word[1]! = complete ∧
      scalar.word[2]! = noError ∧
      consumeExactProjection 4096 (UInt64.ofNat authority.allocation.frame)
          scalar.word[1]! scalar.word[14]! scalar.word[15]!
          (manifestWord authority.reserved.intervals authority.allocation.frame) =
        UInt64.ofNat authority.allocation.frame ∧
      claimed = BootMemoryMapFullProjectionABI.projection authority := by
  dsimp only
  have hscalar := authorizeCanonical_acceptance_scalar_agreement input
    lowStart lowLength imageStart imageLength pageStart pageLength
    descriptorStart descriptorLength stacksStart stacksLength
    guardStart guardLength entryStart entryLength usersStart usersLength
    infoStart infoLength owner claimed authority haccepted
  have hbinding := authorizeCanonical_acceptance_binding input
    lowStart lowLength imageStart imageLength pageStart pageLength
    descriptorStart descriptorLength stacksStart stacksLength
    guardStart guardLength entryStart entryLength usersStart usersLength
    infoStart infoLength owner claimed authority haccepted
  unfold ScalarTerminalProjectionAgrees at hscalar
  refine ⟨hscalar.2.2.1, hscalar.2.2.2.1, ?_,
    hbinding.2.2.2.2.2.2.2⟩
  · rw [hscalar.2.2.1, hscalar.2.2.2.2.1, hscalar.2.2.2.2.2]
    exact hbinding.2.2.2.2.2.2.1

/-- Equal immutable raw inputs and equal canonical manifest words cannot yield
different complete rich projections.  This is the extensional raw-byte
determinism statement consumed by later production-equivalence proofs. -/
theorem runCanonical_raw_bytes_extensional
    (firstInput secondInput : BootMemoryMapDecoder.Input)
    (lowStart lowLength imageStart imageLength pageStart pageLength
    descriptorStart descriptorLength stacksStart stacksLength
    guardStart guardLength entryStart entryLength usersStart usersLength
    infoStart infoLength : UInt64)
    (owner : FrameAllocator.OwnerId)
    (first second : BootMemoryMapFullProjectionABI.Authority)
    (hmagic : firstInput.magic = secondInput.magic)
    (hinfo : firstInput.infoAddress = secondInput.infoAddress)
    (hbytes : firstInput.bytes = secondInput.bytes)
    (hfirst :
      runCanonical firstInput lowStart lowLength imageStart imageLength pageStart pageLength
        descriptorStart descriptorLength stacksStart stacksLength
        guardStart guardLength entryStart entryLength usersStart usersLength
        infoStart infoLength owner = .ok first)
    (hsecond :
      runCanonical secondInput lowStart lowLength imageStart imageLength pageStart pageLength
        descriptorStart descriptorLength stacksStart stacksLength
        guardStart guardLength entryStart entryLength usersStart usersLength
        infoStart infoLength owner = .ok second) :
    BootMemoryMapFullProjectionABI.projection first =
      BootMemoryMapFullProjectionABI.projection second := by
  have hinput : firstInput = secondInput := by
    cases firstInput
    cases secondInput
    simp_all
  subst secondInput
  rw [hfirst] at hsecond
  injection hsecond with heq
  subst second
  rfl

end LeanOS.BootMemoryMapScalarRichEquivalence
