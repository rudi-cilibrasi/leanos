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
  | .zeroLengthEntry => 20
  | .entryAddressOverflow => 21
  | .typedHandoffRejected _ => 22
  | .internalBounds => 23
  | .infoAddressBelowMinimum => 24

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

/-! ## Hosted replay of captured ACPI roots and physical table copies -/

private def rootDecodeErrorCode : AcpiRootDecoder.Error → UInt64
  | .handoffRejected reason => 200 + errorCode reason
  | .truncatedTag => 100
  | .malformedTagSize => 101
  | .tagOutOfBounds => 102
  | .missingEndTag => 103
  | .misplacedEndTag => 104
  | .tooManyTags => 105
  | .invalidSignature => 106
  | .unsupportedRevision => 107
  | .invalidRsdpLength => 108
  | .invalidLegacyChecksum => 109
  | .invalidExtendedChecksum => 110

private def rootSdtErrorCode : BootTopology.AcpiSdtError → UInt64
  | .truncatedHeader => 1
  | .invalidSignature => 2
  | .invalidLength => 3
  | .tableTooLarge => 4
  | .invalidChecksum => 5
  | .invalidRootPayloadAlignment => 6
  | .rootEntryOverflow => 7

private def rootFailureWord (code detail extra word : UInt64) : UInt64 :=
  if word == 1 then 2 else if word == 2 then code
  else if word == 3 then detail else if word == 4 then extra else 0

/-- Replay the captured handoff and physical ACPI copies through the existing
root decoder and authoritative topology model. The ordinary five-word topology
projection is retained. Decoder rejection words 3/4 additionally preserve root
SDT reasons and offending physical addresses. RSDP byte failures use 100..110,
wrapped handoff failures use 200 + the existing decoder code, and adapter
bounds use 300..305. No root or processor identity is synthesized here. -/
def capturedRootQuery (magic infoAddress : UInt64) (info rootBytes : ByteArray)
    (rootAddress : UInt64) (addresses : Array UInt64) (tables : Array ByteArray)
    (executingApicId word : UInt64) : UInt64 :=
  if word == 0 then abiVersion
  else if addresses.size > BootTopology.maxAcpiRootEntries ||
      tables.size > BootTopology.maxAcpiRootEntries then rootFailureWord 300 0 0 word
  else if addresses.size != tables.size then rootFailureWord 301 0 0 word
  else if rootBytes.size + (tables.foldl (fun n bytes => n + bytes.size) 0) > 1048576 then
    rootFailureWord 302 0 0 word
  else if rootBytes.size > BootTopology.maxAcpiSdtBytes ||
      tables.any (fun bytes => bytes.size > BootTopology.maxAcpiSdtBytes) then
    rootFailureWord 303 0 0 word
  else if executingApicId > 0xffffffff then rootFailureWord 304 0 0 word
  else if info.size > 65536 then rootFailureWord 305 0 0 word
  else
    match AcpiRootDecoder.decode
        { magic := magic.toNat, infoAddress := infoAddress.toNat,
          bytes := info.data.toList } with
    | .error reason => rootFailureWord (rootDecodeErrorCode reason) 0 0 word
    | .ok roots =>
      let copies := (addresses.toList.zip tables.toList).map (fun (address, bytes) =>
        ({ physicalAddress := address, bytes := bytes.data.toList } : BootTopology.CopiedAcpiSdt))
      match BootTopology.decodeAndAdmitAuthoritativeAcpiTopology roots
          { physicalAddress := rootAddress, bytes := rootBytes.data.toList }
          copies (UInt32.ofNat executingApicId.toNat) with
      | .error reason =>
        let detail := match reason with
          | .madtSelection (.root reason) => rootSdtErrorCode reason
          | .madtSelection (.untranslatedRootEntry address) => address
          | .madtSelection (.duplicateTranslation address) => address
          | .selectedRootAddressMismatch expected _ => expected
          | _ => 0
        let extra := match reason with
          | .selectedRootAddressMismatch _ actual => actual
          | _ => 0
        rootFailureWord (BootTopology.authoritativeAcpiTopologyErrorCode reason) detail extra word
      | .ok (.rejected reason) =>
        if word == 1 then 3 else if word == 2 then BootTopology.admissionErrorCode reason else 0
      | .ok (.accepted processor) =>
        if word == 1 then 1 else if word == 2 then processor.apicId.toUInt64
        else if word == 3 then if processor.enabled then 1 else 0
        else if word == 4 then if processor.onlineCapable then 1 else 0
        else 0

@[export leanos_boot_captured_root_query]
def exportedCapturedRootQuery (magic infoAddress : UInt64) (info rootBytes : ByteArray)
    (rootAddress : UInt64) (addresses : Array UInt64) (tables : Array ByteArray)
    (executingApicId word : UInt64) : UInt64 :=
  capturedRootQuery magic infoAddress info rootBytes rootAddress addresses tables executingApicId word

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
