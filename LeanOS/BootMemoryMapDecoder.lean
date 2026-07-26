import LeanOS.BootMemoryMap

/-!
# Bounded Multiboot2 byte decoder

This module owns the model-side boundary between an immutable byte copy of a
Multiboot2 information structure and `BootMemoryMap.Handoff`.  Copying bytes
from physical memory remains outside the model.  Once copied, every load is
checked against the finite list and every accepted result carries evidence that
the existing typed handoff validator accepts exactly the decoded entries.
-/
namespace LeanOS.BootMemoryMapDecoder

open LeanOS.BootMemoryMap

structure Input where
  magic : Nat
  infoAddress : Nat
  bytes : List UInt8
  deriving BEq, DecidableEq, Repr

inductive Error where
  | badMagic
  | unalignedInfo
  | bufferTooSmall
  | bufferTooLarge
  | truncatedField
  | advertisedSizeMismatch
  | nonzeroInfoReserved
  | tooManyTags
  | malformedTagSize
  | tagOutOfBounds
  | missingEndTag
  | misplacedEndTag
  | missingMemoryMap
  | duplicateMemoryMap
  | badEntrySize
  | unsupportedEntryVersion
  | tooManyEntries
  | nonzeroEntryReserved
  | typedHandoffRejected (reason : BootMemoryMap.Error)
  | internalBounds
  deriving BEq, DecidableEq, Repr

private def readByte (bytes : List UInt8) (offset : Nat) : Except Error Nat :=
  match bytes[offset]? with
  | none => .error .truncatedField
  | some byte => .ok byte.toNat

private def readLEAux (bytes : List UInt8) (offset remaining factor acc : Nat) :
    Except Error Nat :=
  match remaining with
  | 0 => .ok acc
  | remaining + 1 => do
      let byte ← readByte bytes offset
      readLEAux bytes (offset + 1) remaining (factor * 256) (acc + byte * factor)

def readLE (bytes : List UInt8) (offset width : Nat) : Except Error Nat :=
  readLEAux bytes offset width 1 0

def readU32 (bytes : List UInt8) (offset : Nat) : Except Error Nat :=
  readLE bytes offset 4

def readU64 (bytes : List UInt8) (offset : Nat) : Except Error Nat :=
  readLE bytes offset 8

def memoryKind (kind : Nat) : MemoryKind :=
  match kind with
  | 1 => .usable
  | 3 => .acpiReclaimable
  | 4 => .acpiNvs
  | 5 => .badMemory
  | _ => .reserved

private def decodeEntries (bytes : List UInt8) (offset count : Nat) :
    Except Error (List RawEntry) :=
  match count with
  | 0 => .ok []
  | count + 1 => do
      let base ← readU64 bytes offset
      let length ← readU64 bytes (offset + 8)
      let kind ← readU32 bytes (offset + 16)
      let reserved ← readU32 bytes (offset + 20)
      if reserved != 0 then throw .nonzeroEntryReserved
      let rest ← decodeEntries bytes (offset + memoryMapEntrySize) count
      pure ({ base, length, kind := memoryKind kind } :: rest)

private def decodeTags (bytes : List UInt8) (total offset fuel : Nat)
    (sawMemoryMap : Bool) (tagsRev : List Tag) : Except Error (List Tag) := do
  if offset == total then throw .missingEndTag
  match fuel with
  | 0 => throw .tooManyTags
  | fuel + 1 =>
      if offset + 8 > total then throw .truncatedField
      let tagType ← readU32 bytes offset
      let tagSize ← readU32 bytes (offset + 4)
      if tagSize < 8 then throw .malformedTagSize
      if offset + tagSize > total then throw .tagOutOfBounds
      let advance := aligned8 tagSize
      if offset + advance > total then throw .tagOutOfBounds
      if tagType == 0 then
        if tagSize != 8 then throw .malformedTagSize
        if offset + advance != total then throw .misplacedEndTag
        if !sawMemoryMap then throw .missingMemoryMap
        pure (tagsRev.reverse ++ [.end 8])
      else if tagType == 6 then
        if sawMemoryMap then throw .duplicateMemoryMap
        if tagSize < memoryMapTagHeaderSize then throw .malformedTagSize
        let entrySize ← readU32 bytes (offset + 8)
        let entryVersion ← readU32 bytes (offset + 12)
        if entrySize != memoryMapEntrySize then throw .badEntrySize
        if entryVersion != 0 then throw .unsupportedEntryVersion
        let entryBytes := tagSize - memoryMapTagHeaderSize
        if entryBytes % entrySize != 0 then throw .malformedTagSize
        let entryCount := entryBytes / entrySize
        if entryCount > maxEntries then throw .tooManyEntries
        let entries ← decodeEntries bytes (offset + memoryMapTagHeaderSize) entryCount
        decodeTags bytes total (offset + advance) fuel true
          (.memoryMap tagSize entrySize entryVersion entries :: tagsRev)
      else
        decodeTags bytes total (offset + advance) fuel sawMemoryMap
          (.ignored tagSize :: tagsRev)

def withinBounds (handoff : Handoff) (entries : List RawEntry) : Bool :=
  handoff.totalSize ≤ maxTagBytes &&
    handoff.tags.length ≤ maxTags &&
    entries.length ≤ maxEntries

structure Decoded where
  handoff : Handoff
  entries : List RawEntry
  handoffValid : validateHandoff handoff = .ok entries
  bounds : withinBounds handoff entries = true

def decode (input : Input) : Except Error Decoded := do
  if input.magic != multiboot2Magic then throw .badMagic
  if input.infoAddress % 8 != 0 then throw .unalignedInfo
  if input.bytes.length < 16 then throw .bufferTooSmall
  if input.bytes.length > maxTagBytes then throw .bufferTooLarge
  let totalSize ← readU32 input.bytes 0
  let reserved ← readU32 input.bytes 4
  if totalSize != input.bytes.length then throw .advertisedSizeMismatch
  if totalSize % 8 != 0 then throw .advertisedSizeMismatch
  if reserved != 0 then throw .nonzeroInfoReserved
  let tags ← decodeTags input.bytes totalSize 8 maxTags false []
  let handoff : Handoff :=
    { magic := input.magic, infoAddress := input.infoAddress, totalSize, tags }
  match hvalid : validateHandoff handoff with
  | .error reason => throw (.typedHandoffRejected reason)
  | .ok entries =>
      if hbounds : withinBounds handoff entries then
        pure ⟨handoff, entries, hvalid, hbounds⟩
      else throw .internalBounds

theorem decode_functional (input : Input) (first second : Except Error Decoded)
    (hfirst : decode input = first) (hsecond : decode input = second) : first = second := by
  rw [hfirst] at hsecond
  exact hsecond

theorem accepted_handoff_valid (input : Input) (decoded : Decoded)
    (_h : decode input = .ok decoded) :
    validateHandoff decoded.handoff = .ok decoded.entries :=
  decoded.handoffValid

theorem accepted_within_bounds (input : Input) (decoded : Decoded)
    (_h : decode input = .ok decoded) :
    withinBounds decoded.handoff decoded.entries = true :=
  decoded.bounds

def decodeHandoff (input : Input) : Except Error Handoff :=
  (decode input).map (·.handoff)

theorem rejected_has_no_handoff (input : Input) (reason : Error)
    (h : decodeHandoff input = .error reason) :
    (decodeHandoff input).toOption = none := by
  rw [h]
  rfl

inductive PipelineError where
  | decode (reason : Error)
  | normalize (reason : BootMemoryMap.Error)
  deriving BEq, DecidableEq, Repr

def decodeAndNormalize (input : Input) : Except PipelineError Normalized := do
  match decode input with
  | .error reason => .error (.decode reason)
  | .ok decoded =>
      match normalize decoded.handoff with
      | .error reason => .error (.normalize reason)
      | .ok result => .ok result

theorem accepted_pipeline_has_handoff (input : Input) (result : Normalized)
    (h : decodeAndNormalize input = .ok result) :
    ∃ decoded, decode input = .ok decoded ∧ normalize decoded.handoff = .ok result := by
  unfold decodeAndNormalize at h
  cases hdecode : decode input with
  | error reason =>
      rw [hdecode] at h
      contradiction
  | ok decoded =>
      rw [hdecode] at h
      dsimp only at h
      cases hnormalize : normalize decoded.handoff with
      | error reason =>
          rw [hnormalize] at h
          contradiction
      | ok normalized =>
          rw [hnormalize] at h
          injection h with heq
          subst result
          exact ⟨decoded, rfl, hnormalize⟩

theorem rejected_pipeline_has_no_normalized (input : Input) (reason : PipelineError)
    (h : decodeAndNormalize input = .error reason) :
    (decodeAndNormalize input).toOption = none := by
  rw [h]
  rfl

namespace Fixtures

def byte (value : Nat) : UInt8 := UInt8.ofNat value

def encodeLE (width value : Nat) : List UInt8 :=
  (List.range width).map fun index => byte ((value / (256 ^ index)) % 256)

def u32 (value : Nat) : List UInt8 := encodeLE 4 value
def u64 (value : Nat) : List UInt8 := encodeLE 8 value
def zeroes (count : Nat) : List UInt8 := List.replicate count 0

def entry (base length kind : Nat) (reserved := 0) : List UInt8 :=
  u64 base ++ u64 length ++ u32 kind ++ u32 reserved

def tag (tagType : Nat) (payload : List UInt8) (paddingByte := byte 0) : List UInt8 :=
  let size := 8 + payload.length
  u32 tagType ++ u32 size ++ payload ++ List.replicate (aligned8 size - size) paddingByte

def memoryMapTag (entries : List (List UInt8)) (entrySize := memoryMapEntrySize)
    (entryVersion := 0) : List UInt8 :=
  tag 6 (u32 entrySize ++ u32 entryVersion ++ entries.flatten)

def endTag : List UInt8 := u32 0 ++ u32 8

def information (tags : List UInt8) (reserved := 0) : List UInt8 :=
  let total := 8 + tags.length
  u32 total ++ u32 reserved ++ tags

def sampleEntries : List (List UInt8) :=
  [entry 0x1000 0x4000 1, entry 0x2000 0x1000 2]

def sampleBytes : List UInt8 :=
  information (tag 42 [byte 0xaa] ++ memoryMapTag sampleEntries ++ endTag)

def sampleInput : Input :=
  { magic := multiboot2Magic, infoAddress := 0x1000, bytes := sampleBytes }

def sampleHandoff : Handoff :=
  { magic := multiboot2Magic, infoAddress := 0x1000, totalSize := sampleBytes.length,
    tags :=
      [.ignored 9,
       .memoryMap (memoryMapTagHeaderSize + memoryMapEntrySize * 2)
         memoryMapEntrySize 0
         [{ base := 0x1000, length := 0x4000, kind := .usable },
          { base := 0x2000, length := 0x1000, kind := .reserved }],
       .end 8] }

example : (decode sampleInput).toOption.map (·.handoff) = some sampleHandoff := by
  native_decide

example : (decodeAndNormalize sampleInput).toOption.map (·.regions) = some
    [{ start := 1, count := 1, kind := .usable },
     { start := 2, count := 1, kind := .reserved },
     { start := 3, count := 2, kind := .usable }] := by
  native_decide

def withBytes (bytes : List UInt8) : Input := { sampleInput with bytes }

def errorOf {α : Type} : Except Error α → Option Error
  | .error reason => some reason
  | .ok _ => none

def pipelineErrorOf {α : Type} : Except PipelineError α → Option PipelineError
  | .error reason => some reason
  | .ok _ => none

example : errorOf (decode (withBytes (sampleBytes.take (sampleBytes.length - 1)))) =
    some .advertisedSizeMismatch := by native_decide

example : errorOf (decode (withBytes
    (information (memoryMapTag sampleEntries ++ memoryMapTag sampleEntries ++ endTag)))) =
    some .duplicateMemoryMap := by native_decide

example : errorOf (decode (withBytes (information (memoryMapTag sampleEntries)))) =
    some .missingEndTag := by native_decide

example : errorOf (decode (withBytes
    (information (endTag ++ memoryMapTag sampleEntries ++ endTag)))) =
    some .misplacedEndTag := by native_decide

example : errorOf (decode (withBytes
    (information (memoryMapTag sampleEntries (entrySize := 32) ++ endTag)))) =
    some .badEntrySize := by native_decide

example : errorOf (decode (withBytes
    (information (memoryMapTag sampleEntries (entryVersion := 1) ++ endTag)))) =
    some .unsupportedEntryVersion := by native_decide

example : errorOf (decode (withBytes
    (information (memoryMapTag [entry 0 0x1000 1 1] ++ endTag)))) =
    some .nonzeroEntryReserved := by native_decide

example : ((decode (withBytes
    (information (tag 42 [byte 0xaa] (paddingByte := byte 1) ++
      memoryMapTag sampleEntries ++ endTag)))).toOption.map (·.handoff)) =
    some sampleHandoff := by native_decide

example : ((decode (withBytes
    (information (memoryMapTag [entry 0 0x1000 99] ++ endTag)))).toOption.map
      (·.entries)) =
    some [{ base := 0, length := 0x1000, kind := .reserved }] := by native_decide

example : errorOf
    (decode (withBytes (information (memoryMapTag sampleEntries ++ endTag) 1))) =
    some .nonzeroInfoReserved := by native_decide

def ignoredTags (count : Nat) : List UInt8 :=
  (List.replicate count (tag 42 [])).flatten

def repeatedEntries (count : Nat) : List (List UInt8) :=
  (List.range count).map fun frame => entry (frame * pageBytes) pageBytes 1

def repeatedEntryInput (count : Nat) : Input :=
  withBytes (information (memoryMapTag (repeatedEntries count) ++ endTag))

example : errorOf (decode (withBytes (zeroes (maxTagBytes + 1)))) =
    some .bufferTooLarge := by native_decide

example : errorOf
    (decode (withBytes (information (ignoredTags maxTags ++ endTag)))) =
    some .tooManyTags := by native_decide

example : errorOf (decode (withBytes
    (information (memoryMapTag (repeatedEntries (maxEntries + 1)) ++ endTag)))) =
    some .tooManyEntries := by native_decide

example : (decode (repeatedEntryInput 128)).toOption.map (·.entries.length) =
    some 128 := by native_decide

example : (decode (repeatedEntryInput 129)).toOption.map (·.entries.length) =
    some 129 := by native_decide

example : (decode (repeatedEntryInput 256)).toOption.map (·.entries.length) =
    some maxEntries := by native_decide

example : errorOf (decode (repeatedEntryInput 257)) =
    some .tooManyEntries := by native_decide

example : errorOf (decode (withBytes
    (information (u32 42 ++ u32 24 ++ endTag)))) =
    some .tagOutOfBounds := by native_decide

example : pipelineErrorOf (decodeAndNormalize (withBytes
    (information (memoryMapTag [entry (wordLimit - 1) 2 1] ++ endTag)))) =
    some (.normalize .addressOverflow) := by native_decide

example : pipelineErrorOf (decodeAndNormalize (withBytes
    (information (memoryMapTag [entry 0 0 1] ++ endTag)))) =
    some (.normalize .zeroLength) := by native_decide

end Fixtures

end LeanOS.BootMemoryMapDecoder
