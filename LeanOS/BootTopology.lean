import LeanOS.BootInterruptPhase

/-!
# Single-core boot-topology admission

This module is the first model slice for issue #182.  It consumes a bounded,
kernel-owned topology snapshot and admits only one enabled processor whose APIC
identity agrees with both the recorded BSP and the executing processor.

The snapshot decoder, firmware/CPUID reads, and machine enforcement remain
trusted integration boundaries.  In particular, this model does not claim to
control dormant application processors or x86 INIT/SIPI delivery.
-/

namespace LeanOS.BootTopology

def snapshotVersion : UInt64 := 1
def maxProcessors : Nat := 256

inductive Source where
  | acpiMadt
  | cpuidTopology
  deriving DecidableEq, Repr

structure Processor where
  apicId : UInt32
  enabled : Bool
  /-- ACPI MADT bit 1: firmware permits this disabled processor to be brought
  online.  The single-core admission policy rejects such latent processors
  rather than erasing them during normalization. -/
  onlineCapable : Bool
  deriving DecidableEq, Repr

structure Snapshot where
  source : Source
  version : UInt64
  bspId : UInt32
  executingId : UInt32
  processors : List Processor
  deriving DecidableEq, Repr

/-! ## Copied-handoff ACPI root selection -/

/-- The version-independent ACPI 1.0 identity shared by Multiboot2's old and
new RSDP tags.  The revision and checksum bytes necessarily differ between the
two encodings, so root coherence compares the exact OEM ID and RSDT address
after the decoder has validated each tag's signature and checksum. -/
structure AcpiLegacyRoot where
  oemId : List UInt8
  rsdtAddress : UInt32
  deriving BEq, DecidableEq, Repr

/-- Bounded ACPI root evidence projected from Multiboot2 tag 14 or tag 15.
The extended checksum, length, revision, and XSDT address remain mandatory
checks at the byte-decoder boundary before a `new` value may be constructed. -/
inductive RawAcpiRootTag where
  | old (legacy : AcpiLegacyRoot)
  | new (legacy : AcpiLegacyRoot) (xsdtAddress : UInt64)
  deriving BEq, DecidableEq, Repr

inductive AcpiRootSource where
  | oldRsdp
  | newRsdp
  deriving BEq, DecidableEq, Repr

structure AcpiRoot where
  source : AcpiRootSource
  legacy : AcpiLegacyRoot
  xsdtAddress : Option UInt64
  deriving BEq, DecidableEq, Repr

inductive AcpiRootError where
  | missingRoot
  | duplicateOldRoot
  | duplicateNewRoot
  | conflictingRoots
  deriving BEq, DecidableEq, Repr

private def collectAcpiRoots : List RawAcpiRootTag →
    Option AcpiLegacyRoot → Option (AcpiLegacyRoot × UInt64) →
    Except AcpiRootError (Option AcpiLegacyRoot ×
      Option (AcpiLegacyRoot × UInt64))
  | [], oldRoot, newRoot => .ok (oldRoot, newRoot)
  | .old legacy :: rest, oldRoot, newRoot =>
      match oldRoot with
      | some _ => .error .duplicateOldRoot
      | none => collectAcpiRoots rest (some legacy) newRoot
  | .new legacy xsdtAddress :: rest, oldRoot, newRoot =>
      match newRoot with
      | some _ => .error .duplicateNewRoot
      | none => collectAcpiRoots rest oldRoot (some (legacy, xsdtAddress))

/-- Select one authoritative ACPI root from the bounded copied handoff.
When firmware publishes both Multiboot2 ACPI tag forms, their complete checked
legacy portions must agree exactly; the newer root then carries the selected
XSDT address.  Duplicate or conflicting roots fail closed before MADT parsing. -/
def selectAcpiRoot (tags : List RawAcpiRootTag) :
    Except AcpiRootError AcpiRoot := do
  let (oldRoot, newRoot) ← collectAcpiRoots tags none none
  match oldRoot, newRoot with
  | none, none => .error .missingRoot
  | some legacy, none =>
      .ok { source := .oldRsdp, legacy, xsdtAddress := none }
  | none, some (legacy, xsdtAddress) =>
      .ok { source := .newRsdp, legacy, xsdtAddress := some xsdtAddress }
  | some oldLegacy, some (newLegacy, xsdtAddress) =>
      if oldLegacy == newLegacy then
        .ok { source := .newRsdp, legacy := newLegacy, xsdtAddress := some xsdtAddress }
      else
        .error .conflictingRoots

def repositoryLegacyRoot : AcpiLegacyRoot :=
  { oemId := [0x51, 0x45, 0x4d, 0x55, 0x20, 0x20]
    rsdtAddress := 0x000f5b70 }

theorem coherent_old_new_roots_select_new :
    selectAcpiRoot [
      .old repositoryLegacyRoot,
      .new repositoryLegacyRoot 0x00000000000f5c00
    ] = .ok {
      source := .newRsdp
      legacy := repositoryLegacyRoot
      xsdtAddress := some 0x00000000000f5c00
    } := by
  rfl

theorem coherent_root_selection_is_order_independent :
    selectAcpiRoot [
      .old repositoryLegacyRoot,
      .new repositoryLegacyRoot 0x00000000000f5c00
    ] = selectAcpiRoot [
      .new repositoryLegacyRoot 0x00000000000f5c00,
      .old repositoryLegacyRoot
    ] := by
  rfl

theorem conflicting_old_new_roots_rejected :
    selectAcpiRoot [
      .old repositoryLegacyRoot,
      .new { repositoryLegacyRoot with oemId := [0x42] }
        0x00000000000f5c00
    ] = .error .conflictingRoots := by
  rfl

theorem duplicate_new_roots_rejected :
    selectAcpiRoot [
      .new repositoryLegacyRoot 0x00000000000f5c00,
      .new repositoryLegacyRoot 0x00000000000f5c00
    ] = .error .duplicateNewRoot := by
  rfl

/-! ## Bounded ACPI system-description table validation -/

def acpiSdtHeaderLength : Nat := 36

inductive AcpiSdtError where
  | truncatedHeader
  | invalidSignature
  | invalidLength
  | invalidChecksum
  | invalidRootPayloadAlignment
  | rootEntryOverflow
  deriving BEq, DecidableEq, Repr

structure ValidAcpiSdt where
  signature : List UInt8
  length : Nat
  bytes : List UInt8
  deriving BEq, DecidableEq, Repr

inductive AcpiRootTableKind where
  | rsdt
  | xsdt
  deriving BEq, DecidableEq, Repr

def maxAcpiRootEntries : Nat := 256

private def rootTableSignature : AcpiRootTableKind → List UInt8
  | .rsdt => [0x52, 0x53, 0x44, 0x54]
  | .xsdt => [0x58, 0x53, 0x44, 0x54]

private def rootEntryWidth : AcpiRootTableKind → Nat
  | .rsdt => 4
  | .xsdt => 8

private def readSdtU32 (bytes : List UInt8) (offset : Nat) :
    Except AcpiSdtError Nat :=
  match bytes[offset]?, bytes[offset + 1]?, bytes[offset + 2]?, bytes[offset + 3]? with
  | some b0, some b1, some b2, some b3 =>
      .ok (b0.toNat + b1.toNat * 256 + b2.toNat * 65536 +
        b3.toNat * 16777216)
  | _, _, _, _ => .error .truncatedHeader

private def acpiChecksum (bytes : List UInt8) : Nat :=
  bytes.foldl (fun total byte => (total + byte.toNat) % 256) 0

/-- Validate one complete, bounded ACPI SDT copy before any root-entry or MADT
payload interpretation. Physical-address translation and choosing which root
entry names the authoritative MADT remain trusted machine-boundary work. -/
def validateAcpiSdt (expectedSignature bytes : List UInt8) :
    Except AcpiSdtError ValidAcpiSdt := do
  if bytes.length < acpiSdtHeaderLength then throw .truncatedHeader
  if expectedSignature.length != 4 || bytes.take 4 != expectedSignature then
    throw .invalidSignature
  let declaredLength ← readSdtU32 bytes 4
  if declaredLength < acpiSdtHeaderLength || declaredLength != bytes.length then
    throw .invalidLength
  if acpiChecksum bytes != 0 then throw .invalidChecksum
  pure { signature := bytes.take 4, length := declaredLength, bytes }

private def decodeRootAddress (bytes : List UInt8) : UInt64 :=
  UInt64.ofNat <| bytes.zipIdx.foldl
    (fun total pair => total + pair.1.toNat * 256 ^ pair.2) 0

private def decodeRootEntriesAux : Nat → Nat → List UInt8 → List UInt64
  | 0, _, _ => []
  | fuel + 1, width, bytes =>
      if bytes.isEmpty then []
      else decodeRootAddress (bytes.take width) ::
        decodeRootEntriesAux fuel width (bytes.drop width)

/-- Decode the complete aligned RSDT/XSDT physical-address vector after the
whole copied root table has passed signature, declared-length, and checksum
validation. Translating these addresses and selecting the unique APIC table
remain explicit trusted machine-boundary work. -/
def decodeAcpiRootEntries (kind : AcpiRootTableKind) (bytes : List UInt8) :
    Except AcpiSdtError (List UInt64) := do
  let table ← validateAcpiSdt (rootTableSignature kind) bytes
  let payload := table.bytes.drop acpiSdtHeaderLength
  let width := rootEntryWidth kind
  if payload.length % width != 0 then throw .invalidRootPayloadAlignment
  let count := payload.length / width
  if count > maxAcpiRootEntries then throw .rootEntryOverflow
  pure (decodeRootEntriesAux count width payload)

def acpiSdtErrorOf {α : Type} :
    Except AcpiSdtError α → Option AcpiSdtError
  | .error reason => some reason
  | .ok _ => none

private def sdtByte (value : Nat) : UInt8 := UInt8.ofNat value

private def encodeSdtU32 (value : Nat) : List UInt8 :=
  [sdtByte value, sdtByte (value / 256), sdtByte (value / 65536),
    sdtByte (value / 16777216)]

private def replaceSdtByte (bytes : List UInt8) (index : Nat) (value : UInt8) :
    List UInt8 :=
  bytes.take index ++ [value] ++ bytes.drop (index + 1)

private def encodeRootAddress (width : Nat) (value : Nat) : List UInt8 :=
  (List.range width).map (fun index => sdtByte (value / 256 ^ index))

def repositoryXsdtTableBytes : List UInt8 :=
  let payload := encodeRootAddress 8 0x000f6000 ++
    encodeRootAddress 8 0x000f7000
  let length := acpiSdtHeaderLength + payload.length
  let unchecked :=
    [sdtByte 0x58, sdtByte 0x53, sdtByte 0x44, sdtByte 0x54] ++
      encodeSdtU32 length ++ [sdtByte 1, sdtByte 0] ++
      List.replicate (acpiSdtHeaderLength - 10) (sdtByte 0) ++ payload
  replaceSdtByte unchecked 9 (sdtByte ((256 - acpiChecksum unchecked) % 256))

private def decodedRootEntriesMatch
    (result : Except AcpiSdtError (List UInt64)) (expected : List UInt64) : Bool :=
  match result with
  | .ok actual => actual == expected
  | .error _ => false

theorem repository_xsdt_entries_decoded :
    decodedRootEntriesMatch
      (decodeAcpiRootEntries .xsdt repositoryXsdtTableBytes)
      [0x000f6000, 0x000f7000] = true := by
  native_decide

theorem xsdt_payload_misalignment_rejected :
    acpiSdtErrorOf (decodeAcpiRootEntries .xsdt
      (let unchecked := repositoryXsdtTableBytes ++ [0]
       let resized := replaceSdtByte unchecked 4 (sdtByte unchecked.length)
       let zeroed := replaceSdtByte resized 9 0
       replaceSdtByte zeroed 9 (sdtByte ((256 - acpiChecksum zeroed) % 256)))) =
      some .invalidRootPayloadAlignment := by
  native_decide

def repositoryMadtTableBytes : List UInt8 :=
  let length := 52
  let unchecked :=
    [sdtByte 0x41, sdtByte 0x50, sdtByte 0x49, sdtByte 0x43] ++
      encodeSdtU32 length ++ [sdtByte 1, sdtByte 0] ++
      List.replicate (length - 10) (sdtByte 0)
  replaceSdtByte unchecked 9 (sdtByte ((256 - acpiChecksum unchecked) % 256))

theorem repository_madt_table_header_valid :
    (validateAcpiSdt [0x41, 0x50, 0x49, 0x43] repositoryMadtTableBytes).isOk =
      true := by
  native_decide

theorem truncated_sdt_header_rejected :
    acpiSdtErrorOf
      (validateAcpiSdt [0x41, 0x50, 0x49, 0x43] (List.replicate 35 0)) =
      some .truncatedHeader := by
  native_decide

theorem wrong_sdt_signature_rejected :
    acpiSdtErrorOf
      (validateAcpiSdt [0x58, 0x53, 0x44, 0x54] repositoryMadtTableBytes) =
      some .invalidSignature := by
  native_decide

theorem corrupt_sdt_checksum_rejected :
    acpiSdtErrorOf (validateAcpiSdt [0x41, 0x50, 0x49, 0x43]
      (replaceSdtByte repositoryMadtTableBytes 10 1)) =
      some .invalidChecksum := by
  native_decide

/-- Bounded input already copied from the selected MADT handoff.  The raw
record length and kind remain explicit so normalization cannot silently erase
truncation or admission-relevant unsupported entries. -/
inductive RawMadtRecord where
  | localApic (length : Nat) (apicId : UInt32) (enabled onlineCapable : Bool)
  /-- A fixed-length MADT record whose fields cannot add or enable a processor:
  I/O APIC (1), interrupt-source override (2), or local-APIC NMI (4). -/
  | topologyIrrelevant (kind : UInt8) (length : Nat)
  | unsupported (kind : UInt8) (length : Nat)
  deriving DecidableEq, Repr

inductive DecodeError where
  | truncatedHeader
  | truncatedRecord
  | invalidRecordLength
  | unsupportedRecordKind
  | processorOverflow
  deriving DecidableEq, Repr

def localApicRecordLength : Nat := 8

/-- Exact ACPI lengths for q35 MADT records that describe interrupt routing,
not processor presence or eligibility.  All other non-local-APIC kinds remain
fail closed, including processor-bearing x2APIC records. -/
private def topologyIrrelevantRecordLength : Nat → Option Nat
  | 1 => some 12 -- I/O APIC
  | 2 => some 10 -- interrupt-source override
  | 4 => some 6  -- local-APIC NMI routing
  | _ => none

private def byteAt : List UInt8 → Nat → Option Nat
  | [], _ => none
  | byte :: _, 0 => some byte.toNat
  | _ :: rest, offset + 1 => byteAt rest offset

private def requireByte (bytes : List UInt8) (offset : Nat)
    (error : DecodeError) : Except DecodeError Nat :=
  match byteAt bytes offset with
  | some byte => .ok byte
  | none => .error error

/-- Decode the bounded MADT entry stream.  Table discovery,
address translation, the fixed MADT header, and checksum validation remain at
the trusted machine boundary.  Entry framing and admission-relevant flags do
not; only fixed-length q35 interrupt-routing records are skipped. -/
def decodeMadtBytesAux : Nat → List UInt8 → Except DecodeError (List RawMadtRecord)
  | _, [] => .ok []
  | 0, _ => .error .processorOverflow
  | fuel + 1, bytes => do
      let kind ← requireByte bytes 0 .truncatedHeader
      let length ← requireByte bytes 1 .truncatedHeader
      if length < 2 then
        throw .invalidRecordLength
      if bytes.length < length then
        throw .truncatedRecord
      if kind == 0 then
        if length != localApicRecordLength then
          throw .invalidRecordLength
        let apicId ← requireByte bytes 3 .truncatedRecord
        let flag0 ← requireByte bytes 4 .truncatedRecord
        let flag1 ← requireByte bytes 5 .truncatedRecord
        let flag2 ← requireByte bytes 6 .truncatedRecord
        let flag3 ← requireByte bytes 7 .truncatedRecord
        let flags := flag0 + flag1 * 256 + flag2 * 65536 + flag3 * 16777216
        let rest ← decodeMadtBytesAux fuel (bytes.drop length)
        pure (.localApic length (UInt32.ofNat apicId)
          (flags % 2 == 1) ((flags / 2) % 2 == 1) :: rest)
      else
        match topologyIrrelevantRecordLength kind with
        | some expectedLength =>
            if length != expectedLength then
              throw .invalidRecordLength
            let rest ← decodeMadtBytesAux fuel (bytes.drop length)
            pure (.topologyIrrelevant (UInt8.ofNat kind) length :: rest)
        | none => throw .unsupportedRecordKind

def decodeMadtBytes (bytes : List UInt8) : Except DecodeError (List RawMadtRecord) :=
  decodeMadtBytesAux bytes.length bytes

def decodeProcessor : RawMadtRecord → Except DecodeError Processor
  | .localApic length apicId enabled onlineCapable =>
      if length < localApicRecordLength then
        .error .truncatedRecord
      else if length != localApicRecordLength then
        .error .invalidRecordLength
      else
        .ok { apicId, enabled, onlineCapable }
  | .topologyIrrelevant _ _ => .error .unsupportedRecordKind
  | .unsupported _ _ => .error .unsupportedRecordKind

private def decodeProcessors : List RawMadtRecord → Except DecodeError (List Processor)
  | [] => .ok []
  | .localApic length apicId enabled onlineCapable :: rest => do
      let processor ← decodeProcessor (.localApic length apicId enabled onlineCapable)
      let processors ← decodeProcessors rest
      pure (processor :: processors)
  | .topologyIrrelevant _ _ :: rest => decodeProcessors rest
  | .unsupported _ _ :: _ => .error .unsupportedRecordKind

/-- The normalizer is the only constructor in this module that attaches the
ACPI-MADT source/version provenance to decoded processor records.  BSP and
executing IDs remain trusted machine inputs until the integration slice lands. -/
def normalizeMadtRecords (records : List RawMadtRecord)
    (bspId executingId : UInt32) : Except DecodeError Snapshot := do
  let processors ← decodeProcessors records
  if processors.length > maxProcessors then
    throw .processorOverflow
  pure {
    source := .acpiMadt
    version := snapshotVersion
    bspId
    executingId
    processors
  }

def repositoryMadtRecords : List RawMadtRecord :=
  [.localApic localApicRecordLength 0 true false]

inductive Error where
  | unsupportedSource
  | unsupportedVersion
  | tooManyProcessors
  | duplicateApicId
  | onlineCapableProcessor
  | noEnabledProcessor
  | multipleEnabledProcessors
  | bspMismatch
  deriving DecidableEq, Repr

inductive Result where
  | accepted (processor : Processor)
  | rejected (reason : Error)
  deriving DecidableEq, Repr

def uniqueApicIds : List Processor → Bool
  | [] => true
  | processor :: rest =>
      !rest.any (fun other => other.apicId == processor.apicId) && uniqueApicIds rest

def admit (snapshot : Snapshot) : Result :=
  if snapshot.source != .acpiMadt then
    .rejected .unsupportedSource
  else if snapshot.version != snapshotVersion then
    .rejected .unsupportedVersion
  else if snapshot.processors.length > maxProcessors then
    .rejected .tooManyProcessors
  else if !uniqueApicIds snapshot.processors then
    .rejected .duplicateApicId
  else if snapshot.processors.any (fun processor =>
      !processor.enabled && processor.onlineCapable) then
    .rejected .onlineCapableProcessor
  else
    match snapshot.processors.filter (fun processor => processor.enabled) with
    | [] => .rejected .noEnabledProcessor
    | [processor] =>
        if processor.apicId == snapshot.bspId &&
            snapshot.executingId == snapshot.bspId then
          .accepted processor
        else
          .rejected .bspMismatch
    | _ => .rejected .multipleEnabledProcessors

/-- Admission through the decoder-produced snapshot.  Callers cannot relabel
arbitrary processor records with ACPI provenance along this path. -/
def decodeAndAdmitMadt (records : List RawMadtRecord)
    (bspId executingId : UInt32) : Except DecodeError Result := do
  let snapshot ← normalizeMadtRecords records bspId executingId
  pure (admit snapshot)

def decodeAndAdmitMadtBytes (bytes : List UInt8)
    (bspId executingId : UInt32) : Except DecodeError Result := do
  let records ← decodeMadtBytes bytes
  decodeAndAdmitMadt records bspId executingId

def repositoryMadtBytes : List UInt8 :=
  [0, 8, 0, 0, 1, 0, 0, 0]

theorem empty_madt_entry_region_decodes :
    decodeMadtBytes [] = .ok [] := by
  rfl

theorem truncated_madt_entry_header_rejected :
    decodeMadtBytes [0] = .error .truncatedHeader := by
  rfl

theorem truncated_madt_entry_body_rejected :
    decodeMadtBytes [0, 8, 0, 0, 1] = .error .truncatedRecord := by
  rfl

theorem zero_length_madt_entry_rejected :
    decodeMadtBytes [0, 0] = .error .invalidRecordLength := by
  rfl

theorem unsupported_raw_madt_entry_rejected :
    decodeMadtBytes [9, 2] = .error .unsupportedRecordKind := by
  rfl

def mixedQ35MadtBytes : List UInt8 :=
  [0, 8, 0, 0, 1, 0, 0, 0,
   1, 12, 0, 0, 0, 0, 192, 254, 0, 0, 0, 0,
   2, 10, 0, 0, 2, 0, 0, 0, 0, 0,
   4, 6, 255, 0, 1, 0]

/-- The ordinary mixed q35 entry stream reaches admission while preserving the
sole processor record and skipping only fixed-length interrupt routing data. -/
def acceptedProcessorMatches (result : Except DecodeError Result)
    (apicId : UInt32) : Bool :=
  match result with
  | .ok (.accepted processor) =>
      processor.apicId == apicId && processor.enabled && !processor.onlineCapable
  | _ => false

def rejectedWith (result : Except DecodeError Result) (reason : Error) : Bool :=
  match result with
  | .ok (.rejected actual) => actual == reason
  | _ => false

def decodeFailedWith (result : Except DecodeError Result)
    (reason : DecodeError) : Bool :=
  match result with
  | .error actual => actual == reason
  | _ => false

theorem mixed_q35_madt_bytes_admitted :
    acceptedProcessorMatches (decodeAndAdmitMadtBytes mixedQ35MadtBytes 0 0) 0 = true := by
  native_decide

theorem malformed_q35_io_apic_length_rejected :
    decodeMadtBytes [1, 2] = .error .invalidRecordLength := by
  rfl

theorem topology_affecting_x2apic_record_rejected :
    decodeMadtBytes [9, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] =
      .error .unsupportedRecordKind := by
  rfl

theorem duplicate_madt_byte_apic_ids_rejected :
    decodeAndAdmitMadtBytes
      [0, 8, 0, 0, 1, 0, 0, 0,
       0, 8, 0, 0, 0, 0, 0, 0] 0 0 =
      .ok (.rejected .duplicateApicId) := by
  set_option maxRecDepth 100000 in
    rfl

theorem disabled_madt_byte_processor_does_not_expand_enabled_set :
    acceptedProcessorMatches (decodeAndAdmitMadtBytes
      [0, 8, 0, 0, 1, 0, 0, 0,
       0, 8, 1, 1, 0, 0, 0, 0] 0 0) 0 = true := by
  native_decide

theorem online_capable_madt_byte_processor_rejected :
    rejectedWith (decodeAndAdmitMadtBytes
      [0, 8, 0, 0, 1, 0, 0, 0,
       0, 8, 1, 1, 2, 0, 0, 0] 0 0) .onlineCapableProcessor = true := by
  native_decide

theorem two_enabled_madt_byte_processors_rejected :
    rejectedWith (decodeAndAdmitMadtBytes
      [0, 8, 0, 0, 1, 0, 0, 0,
       0, 8, 1, 1, 1, 0, 0, 0] 0 0) .multipleEnabledProcessors = true := by
  native_decide

theorem maximum_madt_byte_apic_id_admitted :
    acceptedProcessorMatches (decodeAndAdmitMadtBytes
      [0, 8, 0, 255, 1, 0, 0, 0] 255 255) 255 = true := by
  native_decide

theorem truncated_madt_byte_record_rejected_before_admission :
    decodeAndAdmitMadtBytes [0, 8, 0, 0, 1] 0 0 =
      .error .truncatedRecord := by
  rfl

def overflowMadtBytes : List UInt8 :=
  (List.replicate (maxProcessors + 1) repositoryMadtBytes).flatten

theorem processor_overflow_madt_bytes_rejected_before_admission :
    decodeFailedWith (decodeAndAdmitMadtBytes overflowMadtBytes 0 0)
      .processorOverflow = true := by
  native_decide

theorem repository_madt_records_admitted :
    decodeAndAdmitMadt repositoryMadtRecords 0 0 =
      .ok (.accepted { apicId := 0, enabled := true, onlineCapable := false }) := by
  rfl

theorem truncated_madt_record_rejected_before_admission :
    decodeAndAdmitMadt [.localApic 7 0 true false] 0 0 =
      .error .truncatedRecord := by
  rfl

theorem oversized_madt_record_rejected_before_admission :
    decodeAndAdmitMadt [.localApic 9 0 true false] 0 0 =
      .error .invalidRecordLength := by
  rfl

theorem unsupported_madt_record_rejected_before_admission :
    decodeAndAdmitMadt [.unsupported 9 16] 0 0 =
      .error .unsupportedRecordKind := by
  rfl

def overflowMadtRecords : List RawMadtRecord :=
  List.replicate (maxProcessors + 1)
    (.localApic localApicRecordLength 0 true false)

theorem processor_overflow_rejected_before_admission :
    decodeAndAdmitMadt overflowMadtRecords 0 0 = .error .processorOverflow := by
  set_option maxRecDepth 4096 in
    rfl

theorem duplicate_decoded_apic_ids_rejected :
    decodeAndAdmitMadt [
      .localApic localApicRecordLength 0 true false,
      .localApic localApicRecordLength 0 false false
    ] 0 0 = .ok (.rejected .duplicateApicId) := by
  rfl

theorem reordered_enabled_processors_rejected :
    decodeAndAdmitMadt [
      .localApic localApicRecordLength 1 true false,
      .localApic localApicRecordLength 0 true false
    ] 0 0 = .ok (.rejected .multipleEnabledProcessors) := by
  rfl

theorem disabled_online_capable_decoded_processor_rejected :
    decodeAndAdmitMadt [
      .localApic localApicRecordLength 0 true false,
      .localApic localApicRecordLength 1 false true
    ] 0 0 = .ok (.rejected .onlineCapableProcessor) := by
  rfl

theorem maximum_apic_id_admitted :
    decodeAndAdmitMadt [
      .localApic localApicRecordLength 4294967295 true false
    ] 4294967295 4294967295 =
      .ok (.accepted {
        apicId := 4294967295
        enabled := true
        onlineCapable := false
      }) := by
  rfl

theorem admit_deterministic (snapshot : Snapshot) (first second : Result)
    (hfirst : admit snapshot = first) (hsecond : admit snapshot = second) :
    first = second := by
  rw [← hfirst, ← hsecond]

/-- Admission exposes the exact singleton enabled-processor premise consumed by
the repository's single-core models, including agreement between the recorded
BSP and the processor executing the admission check. -/
theorem accepted_implies_single_enabled_bsp (snapshot : Snapshot) (processor : Processor)
    (haccepted : admit snapshot = .accepted processor) :
    snapshot.processors.filter (fun candidate => candidate.enabled) = [processor] ∧
      processor.apicId = snapshot.bspId ∧
      snapshot.executingId = snapshot.bspId := by
  unfold admit at haccepted
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  generalize henabled : snapshot.processors.filter (fun candidate => candidate.enabled) =
      enabled at haccepted ⊢
  cases enabled with
  | nil => simp at haccepted
  | cons head tail =>
      cases tail with
      | nil =>
          by_cases hids : head.apicId = snapshot.bspId ∧
              snapshot.executingId = snapshot.bspId
          · simp [hids] at haccepted
            subst processor
            exact ⟨rfl, hids⟩
          · simp [hids] at haccepted
      | cons next rest => simp at haccepted

def repositorySingleCore : Snapshot :=
  { source := .acpiMadt
    version := snapshotVersion
    bspId := 0
    executingId := 0
    processors := [{ apicId := 0, enabled := true, onlineCapable := false }] }

theorem repository_madt_records_normalize :
    normalizeMadtRecords repositoryMadtRecords 0 0 = .ok repositorySingleCore := by
  rfl

theorem repository_single_core_nonvacuous :
    admit repositorySingleCore =
      .accepted { apicId := 0, enabled := true, onlineCapable := false } := by
  decide

def twoEnabledProcessors : Snapshot :=
  { source := .acpiMadt
    version := snapshotVersion
    bspId := 0
    executingId := 0
    processors := [
      { apicId := 0, enabled := true, onlineCapable := false },
      { apicId := 1, enabled := true, onlineCapable := false }
    ] }

theorem two_enabled_processors_rejected :
    admit twoEnabledProcessors = .rejected .multipleEnabledProcessors := by
  decide

def duplicateBsp : Snapshot :=
  { source := .acpiMadt
    version := snapshotVersion
    bspId := 0
    executingId := 0
    processors := [
      { apicId := 0, enabled := true, onlineCapable := false },
      { apicId := 0, enabled := false, onlineCapable := false }
    ] }

theorem duplicate_bsp_rejected :
    admit duplicateBsp = .rejected .duplicateApicId := by
  decide

def unsupportedSnapshotSource : Snapshot :=
  { repositorySingleCore with source := .cpuidTopology }

theorem unsupported_snapshot_source_rejected :
    admit unsupportedSnapshotSource = .rejected .unsupportedSource := by
  decide

def unsupportedSnapshotVersion : Snapshot :=
  { repositorySingleCore with version := 0 }

theorem unsupported_snapshot_version_rejected :
    admit unsupportedSnapshotVersion = .rejected .unsupportedVersion := by
  decide

def zeroEnabledProcessors : Snapshot :=
  { source := .acpiMadt
    version := snapshotVersion
    bspId := 0
    executingId := 0
    processors := [{ apicId := 0, enabled := false, onlineCapable := false }] }

theorem zero_enabled_processors_rejected :
    admit zeroEnabledProcessors = .rejected .noEnabledProcessor := by
  decide

def disabledOnlineCapableProcessor : Snapshot :=
  { source := .acpiMadt
    version := snapshotVersion
    bspId := 0
    executingId := 0
    processors := [
      { apicId := 0, enabled := true, onlineCapable := false },
      { apicId := 1, enabled := false, onlineCapable := true }
    ] }

theorem disabled_online_capable_processor_rejected :
    admit disabledOnlineCapableProcessor = .rejected .onlineCapableProcessor := by
  decide

def mismatchedExecutingProcessor : Snapshot :=
  { repositorySingleCore with executingId := 1 }

theorem mismatched_executing_processor_rejected :
    admit mismatchedExecutingProcessor = .rejected .bspMismatch := by
  decide

/-! ## Pre-runtime fail-stop composition -/

/-- Topology admission is consumed while the bootstrap64 table owns entry.
The existing boot-interrupt `terminal` phase is reused as the irreversible
pre-CPL3 latch rather than inventing a second notion of terminal execution. -/
inductive AdmissionFailure where
  | decode (reason : DecodeError)
  | policy (reason : Error)
  | wrongPhase
  deriving DecidableEq, Repr

structure AdmissionState where
  phase : BootInterruptPhase.Phase
  failure : Option AdmissionFailure := none
  singleCoreAdmitted : Bool := false
  runtimeInitialized : Bool := false
  returnAuthorityArmed : Bool := false
  /-- Model observation only. Real INIT/SIPI delivery remains an x86/QEMU
  assumption at the trusted boundary. -/
  apStartIssued : Bool := false
  deriving DecidableEq, Repr

def admissionInitial : AdmissionState :=
  { phase := .bootstrap64 }

private def haltAdmission (state : AdmissionState)
    (failure : AdmissionFailure) : AdmissionState :=
  { state with
    phase := .terminal
    failure := some failure
    runtimeInitialized := false
    returnAuthorityArmed := false }

/-- Consume only the decoder-produced result. Every decoder or policy rejection
enters the existing terminal boot phase before runtime initialization or return
authority can be published. -/
def consumeAdmission (state : AdmissionState)
    (result : Except DecodeError Result) : AdmissionState :=
  match state.failure with
  | some _ => state
  | none =>
      if state.phase != .bootstrap64 then
        haltAdmission state .wrongPhase
      else
        match result with
        | .error reason => haltAdmission state (.decode reason)
        | .ok (.rejected reason) => haltAdmission state (.policy reason)
        | .ok (.accepted _) => { state with singleCoreAdmitted := true }

/-- The topology business state embedded in the actual boot publication state. -/
abbrev BootAdmissionState := BootInterruptPhase.State AdmissionState

def bootAdmissionInitial : BootAdmissionState :=
  { phase := .bootstrap64, business := admissionInitial }

/-- Consume topology evidence and latch the real boot state on every rejection. -/
def consumeBootAdmission (state : BootAdmissionState)
    (result : Except DecodeError Result) : BootAdmissionState :=
  match state.latched with
  | some _ => state
  | none =>
      let business :=
        if state.phase != .bootstrap64 || state.business.phase != .bootstrap64 then
          haltAdmission state.business .wrongPhase
        else
          consumeAdmission state.business result
      let next := { state with business }
      match business.failure with
      | some _ => (BootInterruptPhase.rejectTopology next).state
      | none => next

/-- The only topology-aware runtime publication transition.  It refuses to
publish the runtime IDT until decoder-produced admission has been consumed in
the coherent bootstrap64 phase.  On success it advances the outer boot phase
and its embedded business phase atomically. -/
def publishAdmittedRuntime (state : BootAdmissionState)
    (prerequisites : BootInterruptPhase.RuntimePrerequisites) :
    BootInterruptPhase.StepResult AdmissionState :=
  match state.latched with
  | some record => { state, outcome := .alreadyTerminal record }
  | none =>
      if state.phase != .bootstrap64 || state.business.phase != .bootstrap64 ||
          state.business.singleCoreAdmitted != true then
        BootInterruptPhase.rejectTopology state
      else
        let published := BootInterruptPhase.publish state (.publishRuntime prerequisites)
        match published.outcome with
        | .published .runtime =>
            { state := { published.state with business := { published.state.business with
                phase := .runtime
                runtimeInitialized := true } }
              outcome := published.outcome }
        | _ => published

theorem runtime_publication_requires_admission state prerequisites
    (hpublished : (publishAdmittedRuntime state prerequisites).outcome =
      .published .runtime) :
    state.phase = .bootstrap64 ∧
      state.business.phase = .bootstrap64 ∧
      state.business.singleCoreAdmitted = true := by
  cases hlatched : state.latched with
  | some record =>
      simp [publishAdmittedRuntime, hlatched] at hpublished
  | none =>
      by_cases hphase : state.phase = .bootstrap64
      · by_cases hbusiness : state.business.phase = .bootstrap64
        · by_cases hadmitted : state.business.singleCoreAdmitted = true
          · exact ⟨hphase, hbusiness, hadmitted⟩
          · simp [publishAdmittedRuntime, hlatched, hphase, hbusiness, hadmitted,
              BootInterruptPhase.rejectTopology] at hpublished
        · simp [publishAdmittedRuntime, hlatched, hphase, hbusiness,
            BootInterruptPhase.rejectTopology] at hpublished
      · simp [publishAdmittedRuntime, hlatched, hphase,
          BootInterruptPhase.rejectTopology] at hpublished

theorem publication_without_admission_is_terminal :
    let result := publishAdmittedRuntime bootAdmissionInitial ⟨true, true, true⟩
    result.state.phase = .terminal ∧
      result.state.latched.isSome = true ∧
      result.state.returnAuthorityArmed = false := by
  decide

theorem decoded_rejection_latches_real_boot_state (reason : DecodeError) :
    let state := consumeBootAdmission bootAdmissionInitial (.error reason)
    ∃ record,
      state.phase = .terminal ∧
        state.latched = some record ∧
        state.returnAuthorityArmed = false ∧
        state.business.failure = some (.decode reason) := by
  simp [consumeBootAdmission, bootAdmissionInitial, consumeAdmission,
    admissionInitial, haltAdmission, BootInterruptPhase.rejectTopology]

theorem policy_rejection_latches_real_boot_state (reason : Error) :
    let state := consumeBootAdmission bootAdmissionInitial (.ok (.rejected reason))
    ∃ record,
      state.phase = .terminal ∧
        state.latched = some record ∧
        state.returnAuthorityArmed = false ∧
        state.business.failure = some (.policy reason) := by
  simp [consumeBootAdmission, bootAdmissionInitial, consumeAdmission,
    admissionInitial, haltAdmission, BootInterruptPhase.rejectTopology]

theorem boot_rejection_blocks_publication_suffix (state : BootAdmissionState)
    (record : BootInterruptPhase.EarlyHaltRecord)
    (operations : List BootInterruptPhase.Operation)
    (hlatched : state.latched = some record) :
    BootInterruptPhase.run state operations = state :=
  BootInterruptPhase.terminal_suffix_absorbing state record operations hlatched

inductive RuntimeOperation where
  | initialize
  | armUserReturn
  | dispatch
  deriving DecidableEq, Repr

/-- The admitted runtime vocabulary has no AP-start operation. Initialization
and user-return publication remain fail closed until the immutable admission
premise is present. -/
def runtimeStep (state : AdmissionState)
    (operation : RuntimeOperation) : AdmissionState :=
  match state.failure with
  | some _ => state
  | none =>
      if state.singleCoreAdmitted != true then
        haltAdmission state (.policy .noEnabledProcessor)
      else
        match operation with
        | .initialize =>
            { state with phase := .runtime, runtimeInitialized := true }
        | .armUserReturn =>
            if state.phase == .runtime && state.runtimeInitialized then
              { state with returnAuthorityArmed := true }
            else
              haltAdmission state .wrongPhase
        | .dispatch => state

def runRuntime : AdmissionState → List RuntimeOperation → AdmissionState
  | state, [] => state
  | state, operation :: rest => runRuntime (runtimeStep state operation) rest

theorem decoded_rejection_is_pre_cpl3_terminal (reason : DecodeError) :
    let state := consumeAdmission admissionInitial (.error reason)
    state.phase = .terminal ∧
      state.failure = some (.decode reason) ∧
      state.runtimeInitialized = false ∧
      state.returnAuthorityArmed = false := by
  simp [consumeAdmission, admissionInitial, haltAdmission]

theorem policy_rejection_is_pre_cpl3_terminal (reason : Error) :
    let state := consumeAdmission admissionInitial (.ok (.rejected reason))
    state.phase = .terminal ∧
      state.failure = some (.policy reason) ∧
      state.runtimeInitialized = false ∧
      state.returnAuthorityArmed = false := by
  simp [consumeAdmission, admissionInitial, haltAdmission]

theorem admission_failure_absorbing (state : AdmissionState)
    (reason : AdmissionFailure) (operations : List RuntimeOperation)
    (hfailure : state.failure = some reason) :
    runRuntime state operations = state := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation rest ih =>
      simp only [runRuntime]
      have hstep : runtimeStep state operation = state := by
        simp [runtimeStep, hfailure]
      rw [hstep]
      exact ih state hfailure

theorem repository_admission_publishes_single_core_premise :
    (consumeAdmission admissionInitial
      (decodeAndAdmitMadt repositoryMadtRecords 0 0)).singleCoreAdmitted = true := by
  rfl

set_option linter.unusedSimpArgs false in
theorem runtime_preserves_single_core_admission (state : AdmissionState)
    (operation : RuntimeOperation)
    (hadmitted : state.singleCoreAdmitted = true) :
    (runtimeStep state operation).singleCoreAdmitted = true := by
  cases hfailure : state.failure with
  | some reason => simp [runtimeStep, hfailure, hadmitted]
  | none =>
      cases operation <;> simp only [runtimeStep, hfailure]
      all_goals split <;> simp_all [haltAdmission] <;> split <;> simp_all [haltAdmission]

set_option linter.unusedSimpArgs false in
theorem runtime_cannot_publish_ap_start (state : AdmissionState)
    (operation : RuntimeOperation) (hnotStarted : state.apStartIssued = false) :
    (runtimeStep state operation).apStartIssued = false := by
  cases hfailure : state.failure with
  | some reason => simp [runtimeStep, hfailure, hnotStarted]
  | none =>
      cases operation <;> simp only [runtimeStep, hfailure]
      all_goals split <;> simp_all [haltAdmission] <;> split <;> simp_all [haltAdmission]

theorem run_runtime_preserves_single_core_admission (state : AdmissionState)
    (operations : List RuntimeOperation)
    (hadmitted : state.singleCoreAdmitted = true) :
    (runRuntime state operations).singleCoreAdmitted = true := by
  induction operations generalizing state with
  | nil => exact hadmitted
  | cons operation rest ih =>
      apply ih
      exact runtime_preserves_single_core_admission state operation hadmitted

theorem run_runtime_cannot_publish_ap_start (state : AdmissionState)
    (operations : List RuntimeOperation)
    (hnotStarted : state.apStartIssued = false) :
    (runRuntime state operations).apStartIssued = false := by
  induction operations generalizing state with
  | nil => exact hnotStarted
  | cons operation rest ih =>
      apply ih
      exact runtime_cannot_publish_ap_start state operation hnotStarted

/-! ## Hosted generated-code replay ABI -/

def topologyAbiVersion : UInt64 := 1

def decodeErrorCode : DecodeError → UInt64
  | .truncatedHeader => 1
  | .truncatedRecord => 2
  | .invalidRecordLength => 3
  | .unsupportedRecordKind => 4
  | .processorOverflow => 5

def admissionErrorCode : Error → UInt64
  | .unsupportedSource => 1
  | .unsupportedVersion => 2
  | .tooManyProcessors => 3
  | .duplicateApicId => 4
  | .onlineCapableProcessor => 5
  | .noEnabledProcessor => 6
  | .multipleEnabledProcessors => 7
  | .bspMismatch => 8

/-- Stable result words for hosted generated-C differential replay:

* 0: ABI version
* 1: status (`1` accepted, `2` decoder rejection, `3` policy rejection)
* 2: accepted APIC ID or stable typed error code
* 3..4: accepted enabled and online-capable flags

Out-of-range words are zero. -/
def topologyQuery (bytes : ByteArray) (bspId executingId word : UInt64) : UInt64 :=
  if word == 0 then topologyAbiVersion
  else
    match decodeAndAdmitMadtBytes bytes.data.toList
      (UInt32.ofNat bspId.toNat) (UInt32.ofNat executingId.toNat) with
    | .error reason =>
        if word == 1 then 2 else if word == 2 then decodeErrorCode reason else 0
    | .ok (.rejected reason) =>
        if word == 1 then 3 else if word == 2 then admissionErrorCode reason else 0
    | .ok (.accepted processor) =>
        if word == 1 then 1
        else if word == 2 then processor.apicId.toUInt64
        else if word == 3 then if processor.enabled then 1 else 0
        else if word == 4 then if processor.onlineCapable then 1 else 0
        else 0

@[export leanos_boot_topology_query]
def exportedTopologyQuery
    (bytes : ByteArray) (bspId executingId word : UInt64) : UInt64 :=
  topologyQuery bytes bspId executingId word

def topologyFixture (fixture : UInt64) : List UInt8 × UInt64 × UInt64 :=
  if fixture == 0 then (mixedQ35MadtBytes, 0, 0)
  else if fixture == 1 then
    ([0, 8, 0, 0, 1, 0, 0, 0, 0, 8, 1, 1, 1, 0, 0, 0], 0, 0)
  else if fixture == 2 then
    ([0, 8, 0, 0, 1, 0, 0, 0, 0, 8, 1, 1, 2, 0, 0, 0], 0, 0)
  else if fixture == 3 then
    ([0, 8, 0, 0, 1, 0, 0, 0, 0, 8, 1, 0, 0, 0, 0, 0], 0, 0)
  else if fixture == 4 then ([0, 8, 0, 255, 1, 0, 0, 0], 255, 255)
  else if fixture == 5 then ([0, 8, 0, 0, 1], 0, 0)
  else if fixture == 6 then ([9, 2], 0, 0)
  else if fixture == 7 then ([0, 8, 0, 1, 1, 0, 0, 0], 0, 0)
  else if fixture == 8 then (repositoryMadtBytes, 1, 0)
  else (repositoryMadtBytes, 0, 1)

@[export leanos_boot_topology_fixture_query]
def topologyFixtureQuery (fixture word : UInt64) : UInt64 :=
  let selected := topologyFixture fixture
  topologyQuery ⟨selected.1.toArray⟩ selected.2.1 selected.2.2 word

end LeanOS.BootTopology
