import LeanOS.BootMemoryMapDecoder
import LeanOS.BootReservation

/-!
# Generated-C full boot-memory projection

This hosted boundary executes the exact rich transition from immutable raw
Multiboot2 bytes through `BootMemoryMapDecoder.decode`,
`BootReservation.initializeAllocator`, and `FrameAllocator.allocate`.  It
serializes the complete `BootMemoryMapStreamPipeline.Projection`; it does not
reimplement decoding, normalization, reservation overlay, or selection.

The export is deliberately fixture-backed.  It supplies reproducible
generated-C evidence for the rich transition while remaining excluded from the
allocation-free production image.  Production consumption of this exact rich
result remains a separate integration step.
-/
namespace LeanOS.BootMemoryMapFullProjectionABI

open LeanOS
open LeanOS.BootMemoryMap
open LeanOS.BootMemoryMapDecoder

inductive Error where
  | decode (reason : BootMemoryMapDecoder.Error)
  | reservation (reason : BootReservation.Error)
  | allocation (reason : FrameAllocator.AllocationError)
  | internalSelectionInvariant
  | outputMutation
  deriving BEq, DecidableEq, Repr

structure Authority where
  input : Input
  manifest : List BootReservation.Reservation
  owner : FrameAllocator.OwnerId
  decoded : Decoded
  reserved : BootReservation.Result
  allocation : FrameAllocator.Allocation
  decodedBy : BootMemoryMapDecoder.decode input = .ok decoded
  decodedTraversal :
    BootMemoryMapDecoder.SuccessfulRichDecodeTraversal input decoded
  reservedBy :
    BootReservation.initializeAllocator decoded.handoff manifest = .ok reserved
  allocatedBy :
    FrameAllocator.allocate reserved.allocator owner = .ok allocation
  selectedUsable :
    usableFrameSound decoded.entries allocation.frame = true
  selectedWithinBound : allocation.frame < frameLimit
  earlierCandidatesRejected :
    ∀ candidate, candidate < allocation.frame →
      (usableFrameSound decoded.entries candidate &&
        !BootReservation.reservedBy reserved.intervals candidate) = false
  continuation : Except FrameAllocator.AllocationError FrameAllocator.Allocation
  continuedBy :
    FrameAllocator.allocate allocation.state owner = continuation

/-- The sole rich transition consumed by this ABI.  No parsed fields, stage
flags, normalized regions, reservation intervals, or selected frame are caller
inputs. -/
def run (input : Input) (manifest : List BootReservation.Reservation)
    (owner : FrameAllocator.OwnerId) : Except Error Authority :=
  match hdecode : BootMemoryMapDecoder.decode input with
  | .error reason => .error (.decode reason)
  | .ok decoded =>
      match hreserve :
          BootReservation.initializeAllocator decoded.handoff manifest with
      | .error reason => .error (.reservation reason)
      | .ok reserved =>
          match hallocate : FrameAllocator.allocate reserved.allocator owner with
          | .error reason => .error (.allocation reason)
          | .ok allocation =>
              if hsound : usableFrameSound decoded.entries allocation.frame then
                if hbound : allocation.frame < frameLimit then
                  if hfirst :
                      (List.range allocation.frame).all fun candidate =>
                        !(usableFrameSound decoded.entries candidate &&
                          !BootReservation.reservedBy reserved.intervals candidate)
                  then
                    let continuation :=
                      FrameAllocator.allocate allocation.state owner
                    .ok
                      { input, manifest, owner, decoded, reserved, allocation,
                        decodedBy := hdecode, reservedBy := hreserve,
                        decodedTraversal :=
                          BootMemoryMapDecoder.successful_decode_constructs_traversal
                            input decoded hdecode,
                        allocatedBy := hallocate, selectedUsable := hsound,
                        selectedWithinBound := hbound,
                        earlierCandidatesRejected := by
                          intro candidate hearlier
                          have hrejected :=
                            (List.all_eq_true.mp hfirst) candidate
                              (List.mem_range.mpr hearlier)
                          cases hu :
                              usableFrameSound decoded.entries candidate <;>
                            cases hr :
                              BootReservation.reservedBy reserved.intervals candidate <;>
                            simp_all,
                        continuation,
                        continuedBy := rfl }
                  else .error .internalSelectionInvariant
                else .error .internalSelectionInvariant
              else .error .internalSelectionInvariant

theorem run_functional input manifest owner first second
    (hfirst : run input manifest owner = first)
    (hsecond : run input manifest owner = second) : first = second := by
  rw [hfirst] at hsecond
  exact hsecond

structure Projection where
  entries : List RawEntry
  normalizedRegions : List FrameAllocator.Region
  intervals : List BootReservation.Interval
  reservedRegions : List FrameAllocator.Region
  selectedFrame : FrameAllocator.FrameId
  deriving BEq, DecidableEq

def projection (authority : Authority) : Projection :=
  { entries := authority.decoded.entries
    normalizedRegions := authority.reserved.firmware.regions
    intervals := authority.reserved.intervals
    reservedRegions := authority.reserved.regions
    selectedFrame := authority.allocation.frame }

def authorize (input : Input) (manifest : List BootReservation.Reservation)
    (owner : FrameAllocator.OwnerId) (claimed : Projection) :
    Except Error Authority := do
  let authority ← run input manifest owner
  if claimed = projection authority then pure authority else throw .outputMutation

theorem rejected_has_no_authority input manifest owner reason
    (h : run input manifest owner = .error reason) :
    (run input manifest owner).toOption = none := by
  rw [h]
  rfl

theorem accepted_authority_chain (authority : Authority)
    (_h : run authority.input authority.manifest authority.owner = .ok authority) :
    BootMemoryMapDecoder.decode authority.input = .ok authority.decoded ∧
      BootReservation.initializeAllocator authority.decoded.handoff authority.manifest =
        .ok authority.reserved ∧
      FrameAllocator.allocate authority.reserved.allocator authority.owner =
        .ok authority.allocation :=
  ⟨authority.decodedBy, authority.reservedBy, authority.allocatedBy⟩

/-- Every full-projection authority carries the recursive rich byte traversal
that produced its decoded handoff and entries.  This evidence is available
before the scalar terminal gate and does not depend on a claimed projection. -/
theorem accepted_decode_traversal (authority : Authority) :
    BootMemoryMapDecoder.SuccessfulRichDecodeTraversal
      authority.input authority.decoded :=
  authority.decodedTraversal

/-- The exact rich transition cannot replace any of its three authoritative
inputs when it constructs a successful result.  This projection lemma lets
proof-only production compositions bind raw bytes and the complete manifest
without unfolding the decoder or allocator. -/
theorem accepted_inputs (input : Input)
    (manifest : List BootReservation.Reservation) (owner : FrameAllocator.OwnerId)
    (authority : Authority) (h : run input manifest owner = .ok authority) :
    authority.input = input ∧ authority.manifest = manifest ∧ authority.owner = owner := by
  unfold run at h
  split at h <;> try contradiction
  next decoded hdecode =>
    split at h <;> try contradiction
    next reserved hreserve =>
      split at h <;> try contradiction
      next allocation hallocate =>
        split at h <;> try contradiction
        next hsound =>
          split at h <;> try contradiction
          next hbound =>
            split at h <;> try contradiction
            next hfirst =>
              injection h with hauthority
              subst authority
              exact ⟨rfl, rfl, rfl⟩

theorem accepted_selection_sound (authority : Authority)
    (_h : run authority.input authority.manifest authority.owner = .ok authority) :
    usableFrameSound authority.decoded.entries authority.allocation.frame = true ∧
      authority.allocation.frame < frameLimit ∧
      BootReservation.reservedBy authority.reserved.intervals
        authority.allocation.frame = false :=
  ⟨authority.selectedUsable, authority.selectedWithinBound,
    BootReservation.allocation_excludes_reservations authority.reserved authority.owner
      authority.allocation authority.allocatedBy⟩

theorem accepted_claim_is_canonical (input : Input)
    (manifest : List BootReservation.Reservation) (owner : FrameAllocator.OwnerId)
    (claimed : Projection) (authority : Authority)
    (h : authorize input manifest owner claimed = .ok authority) :
    claimed = projection authority := by
  unfold authorize at h
  cases hrun : run input manifest owner with
  | error reason =>
      rw [hrun] at h
      contradiction
  | ok canonical =>
      rw [hrun] at h
      change (if claimed = projection canonical then Except.ok canonical
        else Except.error Error.outputMutation) = Except.ok authority at h
      by_cases heq : claimed = projection canonical
      · rw [if_pos heq] at h
        injection h with hauthority
        rw [← hauthority]
        exact heq
      · rw [if_neg heq] at h
        contradiction

/-- Full authorization acceptance retains both halves of the boundary:
`run` produced the returned authority from the exact three authoritative
inputs, and every field of the caller-visible rich projection equals the
canonical projection of that authority.  Later production compositions can
use this lemma without unfolding the decoder, reservation overlay, allocator,
or projection comparison. -/
theorem authorize_acceptance_binding (input : Input)
    (manifest : List BootReservation.Reservation) (owner : FrameAllocator.OwnerId)
    (claimed : Projection) (authority : Authority)
    (h : authorize input manifest owner claimed = .ok authority) :
    run input manifest owner = .ok authority ∧
      claimed = projection authority := by
  unfold authorize at h
  cases hrun : run input manifest owner with
  | error reason =>
      rw [hrun] at h
      contradiction
  | ok canonical =>
      rw [hrun] at h
      change (if claimed = projection canonical then Except.ok canonical
        else Except.error Error.outputMutation) = Except.ok authority at h
      by_cases heq : claimed = projection canonical
      · rw [if_pos heq] at h
        injection h with hauthority
        subst authority
        exact ⟨rfl, heq⟩
      · rw [if_neg heq] at h
        contradiction

def abiVersion : UInt64 := 1
def accepted : UInt64 := 1
def rejected : UInt64 := 2

def decoderErrorCode : BootMemoryMapDecoder.Error → UInt64
  | .badMagic => 1
  | .unalignedInfo => 2
  | .bufferTooSmall => 3
  | .bufferTooLarge => 4
  | .truncatedField => 5
  | .advertisedSizeMismatch => 6
  | .nonzeroInfoReserved => 7
  | .tooManyTags => 8
  | .malformedTagSize => 9
  | .tagOutOfBounds => 10
  | .missingEndTag => 11
  | .misplacedEndTag => 12
  | .missingMemoryMap => 13
  | .duplicateMemoryMap => 14
  | .badEntrySize => 15
  | .unsupportedEntryVersion => 16
  | .tooManyEntries => 17
  | .nonzeroEntryReserved => 18
  | .zeroLengthEntry => 19
  | .entryAddressOverflow => 20
  | .typedHandoffRejected _ => 21
  | .internalBounds => 22
  | .infoAddressBelowMinimum => 23

def reservationErrorCode : BootReservation.Error → UInt64
  | .missingIdentity => 1
  | .duplicateIdentity => 2
  | .zeroLength => 3
  | .addressOverflow => 4
  | .outsidePhysicalLimit => 5
  | .tooManyReservations => 6
  | .inconsistentImage => 7
  | .ordinaryEntryOverlap => 8
  | .emptyOutput => 9
  | .normalizationInvariant => 10
  | .allocatorRejected => 11

def errorCode : Error → UInt64
  | .decode reason => 100 + decoderErrorCode reason
  | .reservation reason => 200 + reservationErrorCode reason
  | .allocation .exhausted => 301
  | .internalSelectionInvariant => 400
  | .outputMutation => 401

def memoryKindCode : MemoryKind → UInt64
  | .usable => 1
  | .reserved => 2
  | .acpiReclaimable => 3
  | .acpiNvs => 4
  | .badMemory => 5

def regionKindCode : FrameAllocator.RegionKind → UInt64
  | .usable => 1
  | .reserved => 2

def identityCode : BootReservation.Identity → UInt64
  | .lowMemory => 1
  | .loadedImage => 2
  | .pageTables => 3
  | .descriptorTables => 4
  | .kernelStacks => 5
  | .ordinaryEntryGuard => 6
  | .ordinaryEntryStack => 7
  | .embeddedUsers => 8
  | .multibootInfo => 9

def lifetimeCode : BootReservation.Lifetime → UInt64
  | .permanent => 1
  | .bootstrap => 2

def entryWord (entry : RawEntry) (field : Nat) : UInt64 :=
  match field with
  | 0 => entry.base.toUInt64
  | 1 => entry.length.toUInt64
  | _ => memoryKindCode entry.kind

def regionWord (region : FrameAllocator.Region) (field : Nat) : UInt64 :=
  match field with
  | 0 => region.start.toUInt64
  | 1 => region.count.toUInt64
  | _ => regionKindCode region.kind

def intervalWord (interval : BootReservation.Interval) (field : Nat) : UInt64 :=
  match field with
  | 0 => identityCode interval.identity
  | 1 => interval.firstFrame.toUInt64
  | 2 => interval.frameCount.toUInt64
  | _ => lifetimeCode interval.lifetime

/-- Accepted words:

* 0: ABI version
* 1: accepted status
* 2: zero error
* 3..8: total bytes, entry/normalized/interval/overlaid counts, selected frame
* 9..: every entry triple, normalized-region triple, interval quadruple, and
  overlaid-region triple, in that order

Rejected results expose only ABI version, rejected status, and the exact error
code.  Every other word is zero. -/
def projectionWord (authority : Authority) (word : Nat) : UInt64 :=
  if word == 0 then abiVersion
  else if word == 1 then accepted
  else if word == 2 then 0
  else if word == 3 then authority.input.bytes.length.toUInt64
  else if word == 4 then authority.decoded.entries.length.toUInt64
  else if word == 5 then authority.reserved.firmware.regions.length.toUInt64
  else if word == 6 then authority.reserved.intervals.length.toUInt64
  else if word == 7 then authority.reserved.regions.length.toUInt64
  else if word == 8 then authority.allocation.frame.toUInt64
  else
    let entryStart := 9
    let normalizedStart := entryStart + authority.decoded.entries.length * 3
    let intervalStart := normalizedStart + authority.reserved.firmware.regions.length * 3
    let reservedStart := intervalStart + authority.reserved.intervals.length * 4
    if word < normalizedStart then
      let relative := word - entryStart
      match authority.decoded.entries[relative / 3]? with
      | some entry => entryWord entry (relative % 3)
      | none => 0
    else if word < intervalStart then
      let relative := word - normalizedStart
      match authority.reserved.firmware.regions[relative / 3]? with
      | some region => regionWord region (relative % 3)
      | none => 0
    else if word < reservedStart then
      let relative := word - intervalStart
      match authority.reserved.intervals[relative / 4]? with
      | some interval => intervalWord interval (relative % 4)
      | none => 0
    else
      let relative := word - reservedStart
      match authority.reserved.regions[relative / 3]? with
      | some region => regionWord region (relative % 3)
      | none => 0

def resultWord (result : Except Error Authority)
    (word : UInt64) : UInt64 :=
  match result with
  | .ok authority => projectionWord authority word.toNat
  | .error reason =>
      if word == 0 then abiVersion
      else if word == 1 then rejected
      else if word == 2 then errorCode reason
      else 0

theorem accepted_result_words (authority : Authority) (word : UInt64) :
    resultWord (.ok authority) word = projectionWord authority word.toNat := by
  rfl

theorem accepted_result_is_exact_projection (authority : Authority) :
    projection authority =
      { entries := authority.decoded.entries
        normalizedRegions := authority.reserved.firmware.regions
        intervals := authority.reserved.intervals
        reservedRegions := authority.reserved.regions
        selectedFrame := authority.allocation.frame } := by
  exact rfl

theorem rejected_result_has_no_projection (reason : Error) (word : UInt64)
    (hzero : word ≠ 0) (hone : word ≠ 1) (htwo : word ≠ 2) :
    resultWord (.error reason : Except Error Authority) word = 0 := by
  simp [resultWord, hzero, hone, htwo]

namespace Fixtures

open BootMemoryMapDecoder.Fixtures

def identity : Nat := 0x1000

def richEntries : List (List UInt8) :=
  [entry 0 (14 * pageBytes) 1,
   entry (4 * pageBytes) pageBytes 2,
   entry (5 * pageBytes) pageBytes 99,
   entry (6 * pageBytes) pageBytes 3,
   entry (14 * pageBytes + 1) (pageBytes - 1) 1,
   entry 0 (14 * pageBytes) 1]

def richBytes : List UInt8 :=
  information (memoryMapTag richEntries ++ endTag)

def reversedBytes : List UInt8 :=
  information (memoryMapTag richEntries.reverse ++ endTag)

def missingEndBytes : List UInt8 :=
  information (memoryMapTag richEntries)

def truncatedBytes : List UInt8 :=
  richBytes.take (richBytes.length - 1)

def overflowingBytes : List UInt8 :=
  information (memoryMapTag [entry (wordLimit - 1) 2 1] ++ endTag)

def maximumEntriesBytes : List UInt8 :=
  information
    (memoryMapTag (List.replicate maxEntries (entry 0 (15 * pageBytes) 1)) ++ endTag)

def richRun (bytes : List UInt8) : Except Error Authority :=
  run { magic := multiboot2Magic, infoAddress := identity, bytes }
    BootReservation.twoSidedManifest 7

def mutatedRun : Except Error Authority :=
  match richRun richBytes with
  | .error reason => .error reason
  | .ok authority =>
      authorize authority.input authority.manifest authority.owner
        { projection authority with selectedFrame := authority.allocation.frame + 1 }

def fixtureResult (fixture : UInt64) : Except Error Authority :=
  if fixture == 0 then richRun richBytes
  else if fixture == 1 then richRun reversedBytes
  else if fixture == 2 then richRun missingEndBytes
  else if fixture == 3 then richRun overflowingBytes
  else if fixture == 4 then mutatedRun
  else if fixture == 5 then richRun maximumEntriesBytes
  else if fixture == 6 then richRun truncatedBytes
  else .error (.decode .bufferTooSmall)

example : (richRun richBytes).toOption.map projection = some
    { entries :=
        [{ base := 0, length := 14 * pageBytes, kind := .usable },
         { base := 4 * pageBytes, length := pageBytes, kind := .reserved },
         { base := 5 * pageBytes, length := pageBytes, kind := .reserved },
         { base := 6 * pageBytes, length := pageBytes, kind := .acpiReclaimable },
         { base := 14 * pageBytes + 1, length := pageBytes - 1, kind := .usable },
         { base := 0, length := 14 * pageBytes, kind := .usable }]
      normalizedRegions :=
        [{ start := 0, count := 4, kind := .usable },
         { start := 4, count := 3, kind := .reserved },
         { start := 7, count := 7, kind := .usable },
         { start := 14, count := 1, kind := .reserved }]
      intervals :=
        [{ identity := .lowMemory, firstFrame := 0, frameCount := 1,
           lifetime := .permanent },
         { identity := .loadedImage, firstFrame := 3, frameCount := 7,
           lifetime := .permanent },
         { identity := .pageTables, firstFrame := 3, frameCount := 1,
           lifetime := .permanent },
         { identity := .descriptorTables, firstFrame := 4, frameCount := 1,
           lifetime := .permanent },
         { identity := .kernelStacks, firstFrame := 5, frameCount := 1,
           lifetime := .permanent },
         { identity := .ordinaryEntryGuard, firstFrame := 8, frameCount := 1,
           lifetime := .permanent },
         { identity := .ordinaryEntryStack, firstFrame := 9, frameCount := 1,
           lifetime := .permanent },
         { identity := .embeddedUsers, firstFrame := 6, frameCount := 2,
           lifetime := .permanent },
         { identity := .multibootInfo, firstFrame := 10, frameCount := 2,
           lifetime := .bootstrap }]
      reservedRegions :=
        [{ start := 0, count := 1, kind := .reserved },
         { start := 1, count := 2, kind := .usable },
         { start := 3, count := 9, kind := .reserved },
         { start := 12, count := 2, kind := .usable },
         { start := 14, count := 1, kind := .reserved }]
      selectedFrame := 1 } := by
  native_decide

example :
    ((richRun richBytes).toOption.map fun authority =>
        (authority.reserved.firmware.regions, authority.reserved.regions,
          authority.allocation.frame)) =
      ((richRun reversedBytes).toOption.map fun authority =>
        (authority.reserved.firmware.regions, authority.reserved.regions,
          authority.allocation.frame)) := by
  native_decide

def errorOf {α : Type} : Except Error α → Option Error
  | .error reason => some reason
  | .ok _ => none

example : errorOf (fixtureResult 2) = some (.decode .missingEndTag) := by
  native_decide

example : errorOf (fixtureResult 3) = some (.decode .entryAddressOverflow) := by
  native_decide

example : errorOf (fixtureResult 4) = some .outputMutation := by
  native_decide

example : ((fixtureResult 5).toOption.map fun authority =>
    (authority.decoded.entries.length, authority.allocation.frame)) =
      some (maxEntries, 1) := by
  native_decide

example : errorOf (fixtureResult 6) = some (.decode .advertisedSizeMismatch) := by
  native_decide

end Fixtures

/-- Reproducible raw-corpus entry point for hosted generated-C/ELF replay. -/
@[export leanos_boot_full_projection_fixture_query]
def fixtureQuery (fixture word : UInt64) : UInt64 :=
  resultWord (Fixtures.fixtureResult fixture) word

end LeanOS.BootMemoryMapFullProjectionABI
