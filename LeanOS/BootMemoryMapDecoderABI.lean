import LeanOS.BootMemoryMapDecoder

/-!
# Versioned generated-C projection for the boot handoff decoder

The freestanding boot image cannot yet host the boxed Lean result directly.
This query ABI lets hosted C replay one immutable byte buffer and compare every
accepted decoded entry and normalized region, or the exact typed rejection.
Queries are independent: callers cannot splice state from two buffers.
-/
namespace LeanOS.BootMemoryMapDecoderABI

open LeanOS.BootMemoryMap
open LeanOS.BootMemoryMapDecoder

def abiVersion : UInt64 := 1

def errorCode : BootMemoryMapDecoder.Error → UInt64
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
  | .missingEndTag => 12
  | .misplacedEndTag => 13
  | .missingMemoryMap => 14
  | .duplicateMemoryMap => 15
  | .badEntrySize => 16
  | .unsupportedEntryVersion => 17
  | .tooManyEntries => 18
  | .nonzeroEntryReserved => 19
  | .typedHandoffRejected _ => 20
  | .internalBounds => 21

def normalizeErrorCode : BootMemoryMap.Error → UInt64
  | .badMagic => 1
  | .unalignedInfo => 2
  | .malformedInfoSize => 3
  | .tooManyTags => 4
  | .tagBytesExceeded => 5
  | .malformedTagSize => 6
  | .missingEndTag => 7
  | .misplacedEndTag => 8
  | .missingMemoryMap => 9
  | .duplicateMemoryMap => 10
  | .badEntrySize => 11
  | .unsupportedEntryVersion => 12
  | .tooManyEntries => 13
  | .zeroLength => 14
  | .addressOverflow => 15
  | .expandedFramesExceeded => 16
  | .normalizedRegionsExceeded => 17
  | .normalizationInvariant => 18
  | .allocatorRejected => 19

def kindCode : MemoryKind → UInt64
  | .usable => 1
  | .reserved => 2
  | .acpiReclaimable => 3
  | .acpiNvs => 4
  | .badMemory => 5

def regionKindCode : FrameAllocator.RegionKind → UInt64
  | .usable => 1
  | .reserved => 2

def queryDecoded (decoded : Decoded) (normalized : Normalized) (query : Nat) : UInt64 :=
  if query == 0 then abiVersion
  else if query == 1 then 1
  else if query == 2 then decoded.handoff.totalSize.toUInt64
  else if query == 3 then decoded.entries.length.toUInt64
  else if query == 4 then normalized.regions.length.toUInt64
  else
    let entryWords := decoded.entries.length * 3
    if query < 5 + entryWords then
      let relative := query - 5
      match decoded.entries[relative / 3]? with
      | none => 0
      | some entry =>
          match relative % 3 with
          | 0 => entry.base.toUInt64
          | 1 => entry.length.toUInt64
          | _ => kindCode entry.kind
    else
      let relative := query - (5 + entryWords)
      match normalized.regions[relative / 3]? with
      | none => 0
      | some region =>
          match relative % 3 with
          | 0 => region.start.toUInt64
          | 1 => region.count.toUInt64
          | _ => regionKindCode region.kind

/-- Result words:

* 0: ABI version
* 1: status (`1` accepted, `2` decoder rejection, `3` normalizer rejection)
* accepted 2..4: total bytes, entry count, region count
* accepted 5..: triples for every entry, then triples for every region
* rejected 2: stable typed error code

All out-of-range queries return zero. -/
def query (magic infoAddress : UInt64) (bytes : ByteArray) (word : UInt64) : UInt64 :=
  let input : Input :=
    { magic := magic.toNat, infoAddress := infoAddress.toNat, bytes := bytes.data.toList }
  match decode input with
  | .error reason =>
      if word == 0 then abiVersion else if word == 1 then 2
      else if word == 2 then errorCode reason else 0
  | .ok decoded =>
      match normalize decoded.handoff with
      | .error reason =>
          if word == 0 then abiVersion else if word == 1 then 3
          else if word == 2 then normalizeErrorCode reason else 0
      | .ok normalized => queryDecoded decoded normalized word.toNat

@[export leanos_boot_handoff_query]
def exportedQuery (magic infoAddress : UInt64) (bytes : ByteArray) (word : UInt64) : UInt64 :=
  query magic infoAddress bytes word

theorem query_deterministic magic infoAddress bytes word first second
    (hfirst : query magic infoAddress bytes word = first)
    (hsecond : query magic infoAddress bytes word = second) : first = second := by
  rw [hfirst] at hsecond
  exact hsecond

theorem rejection_has_no_accepted_status magic infoAddress bytes reason
    (h : decode
      { magic := magic.toNat, infoAddress := infoAddress.toNat,
        bytes := bytes.data.toList } = .error reason) :
    query magic infoAddress bytes 1 = 2 := by
  simp [query, h]

namespace Fixtures

open BootMemoryMapDecoder.Fixtures

def magic : UInt64 := UInt64.ofNat multiboot2Magic
def sampleArray : ByteArray := ⟨sampleBytes.toArray⟩
def reversedBytes : List UInt8 :=
  information (tag 42 [byte 0xaa] ++ memoryMapTag sampleEntries.reverse ++ endTag)
def reversedArray : ByteArray := ⟨reversedBytes.toArray⟩

example : query magic 0x1000 sampleArray 0 = abiVersion := by native_decide
example : query magic 0x1000 sampleArray 1 = 1 := by native_decide
example : query magic 0x1000 sampleArray 3 = 2 := by native_decide
example : query magic 0x1000 sampleArray 4 = 3 := by native_decide
example : query magic 0x1000 sampleArray 5 = 0x1000 := by native_decide
example : query magic 0x1000 sampleArray 6 = 0x4000 := by native_decide
example : query magic 0x1000 sampleArray 7 = 1 := by native_decide
example : query magic 0x1000 sampleArray 11 = 1 := by native_decide
example : query magic 0x1000 sampleArray 12 = 1 := by native_decide
example : query magic 0x1000 sampleArray 19 = 1 := by native_decide
example : query magic 0x1000 sampleArray 20 = 0 := by native_decide

def truncatedArray : ByteArray := ⟨(sampleBytes.take (sampleBytes.length - 1)).toArray⟩
def paddingArray : ByteArray :=
  ⟨(information (tag 42 [byte 0xaa] (paddingByte := byte 1) ++
    memoryMapTag sampleEntries ++ endTag)).toArray⟩

example : query magic 0x1000 truncatedArray 1 = 2 := by native_decide
example : query magic 0x1000 truncatedArray 2 = 6 := by native_decide
example : query magic 0x1000 paddingArray 1 = 1 := by native_decide
example : query magic 0x1000 paddingArray 19 = 1 := by native_decide

end Fixtures

/-- The checked-in corpus entry point used by hosted generated-C replay.
Fixture identifiers select immutable raw byte arrays, never intermediate state. -/
@[export leanos_boot_handoff_fixture_query]
def fixtureQuery (fixture word : UInt64) : UInt64 :=
  let bytes :=
    if fixture == 0 then Fixtures.sampleArray
    else if fixture == 1 then Fixtures.reversedArray
    else if fixture == 2 then Fixtures.truncatedArray
    else Fixtures.paddingArray
  query Fixtures.magic 0x1000 bytes word

end LeanOS.BootMemoryMapDecoderABI
