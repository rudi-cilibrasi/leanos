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
/-- Platform copy bound for one complete ACPI system-description table.  This
matches the existing 64-KiB immutable boot-handoff budget, so validation never
scans an attacker-declared multi-gigabyte table. -/
def maxAcpiSdtBytes : Nat := 65536

inductive AcpiSdtError where
  | truncatedHeader
  | invalidSignature
  | invalidLength
  | tableTooLarge
  | invalidChecksum
  | invalidRootPayloadAlignment
  | rootEntryOverflow
  deriving BEq, DecidableEq, Repr

structure ValidAcpiSdt where
  signature : List UInt8
  length : Nat
  bytes : List UInt8
  lengthBounded : length ≤ maxAcpiSdtBytes

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
  if hlarge : declaredLength > maxAcpiSdtBytes then
    throw .tableTooLarge
  else
    if acpiChecksum bytes != 0 then throw .invalidChecksum
    pure {
      signature := bytes.take 4
      length := declaredLength
      bytes
      lengthBounded := Nat.le_of_not_gt hlarge
    }

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

private def madtTableBytesOfLength (length : Nat) : List UInt8 :=
  let unchecked :=
    [sdtByte 0x41, sdtByte 0x50, sdtByte 0x49, sdtByte 0x43] ++
      encodeSdtU32 length ++ [sdtByte 1, sdtByte 0] ++
      List.replicate (length - 10) (sdtByte 0)
  replaceSdtByte unchecked 9 (sdtByte ((256 - acpiChecksum unchecked) % 256))

def repositoryMadtTableBytes : List UInt8 :=
  madtTableBytesOfLength 52

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

theorem maximum_sdt_length_accepted :
    (validateAcpiSdt [0x41, 0x50, 0x49, 0x43]
      (madtTableBytesOfLength maxAcpiSdtBytes)).isOk = true := by
  native_decide

theorem sdt_length_above_platform_bound_rejected :
    acpiSdtErrorOf (validateAcpiSdt [0x41, 0x50, 0x49, 0x43]
      (madtTableBytesOfLength (maxAcpiSdtBytes + 1))) =
      some .tableTooLarge := by
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

/-- A complete MADT has the common 36-byte SDT header followed by the
8-byte MADT-local APIC address/flags header. -/
def acpiMadtHeaderLength : Nat := 44

/-- Preserve whether a complete-table admission failure came from the ACPI
envelope, the fixed MADT header, or the bounded entry decoder. -/
inductive CompleteMadtError where
  | sdt (reason : AcpiSdtError)
  | truncatedMadtHeader
  | entry (reason : DecodeError)
  deriving DecidableEq, Repr

/-- Decode one validated complete MADT into the exact snapshot consumed by
admission.  The fixed MADT header is never exposed as an entry stream. -/
def decodeCompleteMadtSnapshot (bytes : List UInt8)
    (bspId executingId : UInt32) : Except CompleteMadtError Snapshot :=
  match validateAcpiSdt [0x41, 0x50, 0x49, 0x43] bytes with
  | .error reason => .error (.sdt reason)
  | .ok table =>
      if table.length < acpiMadtHeaderLength then
        .error .truncatedMadtHeader
      else
        match decodeMadtBytes (table.bytes.drop acpiMadtHeaderLength) with
        | .error reason => .error (.entry reason)
        | .ok records =>
            match normalizeMadtRecords records bspId executingId with
            | .error reason => .error (.entry reason)
            | .ok snapshot => .ok snapshot

/-- Validate and admit one complete copied MADT.  Only an exact APIC SDT with
a bounded declared length and valid checksum reaches admission. -/
def decodeAndAdmitCompleteMadt (bytes : List UInt8)
    (bspId executingId : UInt32) : Except CompleteMadtError Result := do
  let snapshot ← decodeCompleteMadtSnapshot bytes bspId executingId
  pure (admit snapshot)

def repositoryMadtBytes : List UInt8 :=
  [0, 8, 0, 0, 1, 0, 0, 0]

private def madtTableWithEntries (entries : List UInt8) : List UInt8 :=
  let length := acpiMadtHeaderLength + entries.length
  let unchecked :=
    [sdtByte 0x41, sdtByte 0x50, sdtByte 0x49, sdtByte 0x43] ++
      encodeSdtU32 length ++ [sdtByte 1, sdtByte 0] ++
      List.replicate (acpiMadtHeaderLength - 10) (sdtByte 0) ++ entries
  replaceSdtByte unchecked 9 (sdtByte ((256 - acpiChecksum unchecked) % 256))

def repositoryCompleteMadtBytes : List UInt8 :=
  madtTableWithEntries repositoryMadtBytes

/-! ## Root-table translation and unique MADT selection -/

/-- One immutable table copy paired with the physical address carried by the
validated RSDT/XSDT.  Producing these copies remains machine-boundary work;
selection and ambiguity rejection below are model-owned. -/
structure CopiedAcpiSdt where
  physicalAddress : UInt64
  bytes : List UInt8
  deriving BEq, DecidableEq, Repr

inductive MadtSelectionError where
  | root (reason : AcpiSdtError)
  | untranslatedRootEntry (address : UInt64)
  | duplicateTranslation (address : UInt64)
  | missingMadt
  | duplicateMadt
  deriving BEq, DecidableEq, Repr

private def translateRootEntry (copies : List CopiedAcpiSdt)
    (address : UInt64) : Except MadtSelectionError CopiedAcpiSdt :=
  match copies.filter (fun copy => copy.physicalAddress == address) with
  | [] => .error (.untranslatedRootEntry address)
  | [copy] => .ok copy
  | _ => .error (.duplicateTranslation address)

private def translateRootEntries (copies : List CopiedAcpiSdt) :
    List UInt64 → Except MadtSelectionError (List CopiedAcpiSdt)
  | [] => .ok []
  | address :: rest => do
      let copy ← translateRootEntry copies address
      let translated ← translateRootEntries copies rest
      pure (copy :: translated)

/-- Decode the bounded root vector, require one translation for every address,
and select exactly one APIC/MADT copy.  Missing translations and duplicate
address associations fail before the complete-table admission pipeline. -/
def selectUniqueCompleteMadt (kind : AcpiRootTableKind) (rootBytes : List UInt8)
    (copies : List CopiedAcpiSdt) : Except MadtSelectionError (List UInt8) := do
  let addresses ← match decodeAcpiRootEntries kind rootBytes with
    | .ok entries => pure entries
    | .error reason => throw (.root reason)
  let translated ← translateRootEntries copies addresses
  match translated.filter (fun copy =>
      copy.bytes.take 4 == [0x41, 0x50, 0x49, 0x43]) with
  | [] => .error .missingMadt
  | [madt] => .ok madt.bytes
  | _ => .error .duplicateMadt

def repositoryCopiedAcpiTables : List CopiedAcpiSdt := [
  { physicalAddress := 0x000f6000, bytes := repositoryCompleteMadtBytes },
  { physicalAddress := 0x000f7000, bytes := repositoryXsdtTableBytes }
]

private def selectedMadtMatches
    (result : Except MadtSelectionError (List UInt8))
    (expected : List UInt8) : Bool :=
  match result with
  | .ok bytes => bytes == expected
  | .error _ => false

private def madtSelectionFailedWith
    (result : Except MadtSelectionError (List UInt8))
    (expected : MadtSelectionError) : Bool :=
  match result with
  | .ok _ => false
  | .error reason => reason == expected

theorem repository_unique_madt_selected :
    selectedMadtMatches
      (selectUniqueCompleteMadt .xsdt repositoryXsdtTableBytes
        repositoryCopiedAcpiTables) repositoryCompleteMadtBytes = true := by
  native_decide

theorem untranslated_root_entry_rejected :
    madtSelectionFailedWith
      (selectUniqueCompleteMadt .xsdt repositoryXsdtTableBytes [
        { physicalAddress := 0x000f6000, bytes := repositoryCompleteMadtBytes }
      ]) (.untranslatedRootEntry 0x000f7000) = true := by
  native_decide

theorem duplicate_madt_translation_rejected :
    madtSelectionFailedWith
      (selectUniqueCompleteMadt .xsdt repositoryXsdtTableBytes [
        { physicalAddress := 0x000f6000, bytes := repositoryCompleteMadtBytes },
        { physicalAddress := 0x000f7000, bytes := repositoryCompleteMadtBytes }
      ]) .duplicateMadt = true := by
  native_decide

/-! ## Authoritative root-to-admission pipeline -/

/-- Failures from the single typed ACPI topology pipeline retain the boundary
that rejected the input.  In particular, root selection and physical-address
agreement cannot be skipped by supplying an otherwise valid MADT directly. -/
inductive AuthoritativeAcpiTopologyError where
  | rsdp (reason : AcpiRootError)
  | selectedRootAddressMismatch (expected actual : UInt64)
  | madtSelection (reason : MadtSelectionError)
  | completeMadt (reason : CompleteMadtError)
  deriving DecidableEq, Repr

private def selectedRootTable (root : AcpiRoot) :
    AcpiRootTableKind × UInt64 :=
  match root.xsdtAddress with
  | some address => (.xsdt, address)
  | none => (.rsdt, root.legacy.rsdtAddress.toUInt64)

/-- Decode the exact snapshot selected by the authoritative ACPI path.  Exposing
this typed intermediate lets security claims state their singleton conclusion
over the same root-selected MADT that reached admission. -/
def decodeAuthoritativeAcpiTopologySnapshot
    (rootTags : List RawAcpiRootTag) (rootCopy : CopiedAcpiSdt)
    (tableCopies : List CopiedAcpiSdt) (executingApicId : UInt32) :
    Except AuthoritativeAcpiTopologyError Snapshot := do
  let root ← match selectAcpiRoot rootTags with
    | .ok selected => pure selected
    | .error reason => throw (.rsdp reason)
  let selected := selectedRootTable root
  if rootCopy.physicalAddress != selected.2 then
    throw (.selectedRootAddressMismatch selected.2 rootCopy.physicalAddress)
  let madtBytes ← match selectUniqueCompleteMadt selected.1 rootCopy.bytes tableCopies with
    | .ok bytes => pure bytes
    | .error reason => throw (.madtSelection reason)
  match decodeCompleteMadtSnapshot madtBytes executingApicId executingApicId with
  | .ok snapshot => pure snapshot
  | .error reason => throw (.completeMadt reason)

/-- Start at decoded old/new RSDP evidence, require the copied root table to
match the exact selected RSDT/XSDT physical address, translate every advertised
entry exactly once, select one MADT, and admit the exact decoded snapshot.  The
executing APIC ID is a single trusted machine observation and therefore
supplies both the recorded BSP and executing identity. -/
def decodeAndAdmitAuthoritativeAcpiTopology
    (rootTags : List RawAcpiRootTag) (rootCopy : CopiedAcpiSdt)
    (tableCopies : List CopiedAcpiSdt) (executingApicId : UInt32) :
    Except AuthoritativeAcpiTopologyError Result := do
  let snapshot ← decodeAuthoritativeAcpiTopologySnapshot rootTags rootCopy
    tableCopies executingApicId
  pure (admit snapshot)

def repositoryAcpiRootTags : List RawAcpiRootTag := [
  .old repositoryLegacyRoot,
  .new repositoryLegacyRoot 0x00000000000f5c00
]

def repositoryXsdtCopy : CopiedAcpiSdt :=
  { physicalAddress := 0x00000000000f5c00, bytes := repositoryXsdtTableBytes }

private def authoritativeTopologyAcceptedProcessorMatches
    (result : Except AuthoritativeAcpiTopologyError Result)
    (apicId : UInt32) : Bool :=
  match result with
  | .ok (.accepted processor) =>
      processor.apicId == apicId && processor.enabled && !processor.onlineCapable
  | _ => false

private def authoritativeRsdpFailedWith
    (result : Except AuthoritativeAcpiTopologyError Result)
    (expected : AcpiRootError) : Bool :=
  match result with
  | .error (.rsdp actual) => actual == expected
  | _ => false

private def authoritativeRootAddressMismatchMatches
    (result : Except AuthoritativeAcpiTopologyError Result)
    (expected actual : UInt64) : Bool :=
  match result with
  | .error (.selectedRootAddressMismatch observedExpected observedActual) =>
      observedExpected == expected && observedActual == actual
  | _ => false

theorem repository_authoritative_acpi_topology_admitted :
    authoritativeTopologyAcceptedProcessorMatches
      (decodeAndAdmitAuthoritativeAcpiTopology repositoryAcpiRootTags
        repositoryXsdtCopy repositoryCopiedAcpiTables 0) 0 = true := by
  native_decide

theorem missing_rsdp_cannot_bypass_authoritative_pipeline :
    authoritativeRsdpFailedWith
      (decodeAndAdmitAuthoritativeAcpiTopology [] repositoryXsdtCopy
        repositoryCopiedAcpiTables 0) .missingRoot = true := by
  native_decide

theorem wrong_selected_root_copy_cannot_reach_admission :
    authoritativeRootAddressMismatchMatches
      (decodeAndAdmitAuthoritativeAcpiTopology repositoryAcpiRootTags
        { repositoryXsdtCopy with physicalAddress := 0x00000000000f5c08 }
        repositoryCopiedAcpiTables 0)
      0x00000000000f5c00 0x00000000000f5c08 = true := by
  native_decide

def completeMadtAcceptedProcessorMatches
    (result : Except CompleteMadtError Result) (apicId : UInt32) : Bool :=
  match result with
  | .ok (.accepted processor) =>
      processor.apicId == apicId && processor.enabled && !processor.onlineCapable
  | _ => false

def completeMadtFailedWith (result : Except CompleteMadtError Result)
    (reason : CompleteMadtError) : Bool :=
  match result with
  | .error actual => actual == reason
  | _ => false

theorem repository_complete_madt_admitted :
    completeMadtAcceptedProcessorMatches
      (decodeAndAdmitCompleteMadt repositoryCompleteMadtBytes 0 0) 0 = true := by
  native_decide

theorem complete_madt_wrong_signature_rejected :
    completeMadtFailedWith
      (decodeAndAdmitCompleteMadt
        (replaceSdtByte repositoryCompleteMadtBytes 0 (sdtByte 0x58)) 0 0)
      (.sdt .invalidSignature) = true := by
  native_decide

theorem complete_madt_declared_length_mismatch_rejected :
    completeMadtFailedWith
      (decodeAndAdmitCompleteMadt
        (replaceSdtByte repositoryCompleteMadtBytes 4 (sdtByte 44)) 0 0)
      (.sdt .invalidLength) = true := by
  native_decide

theorem complete_madt_bad_checksum_rejected :
    completeMadtFailedWith
      (decodeAndAdmitCompleteMadt
        (replaceSdtByte repositoryCompleteMadtBytes 10 (sdtByte 1)) 0 0)
      (.sdt .invalidChecksum) = true := by
  native_decide

theorem complete_madt_truncated_fixed_header_rejected :
    completeMadtFailedWith
      (decodeAndAdmitCompleteMadt (madtTableBytesOfLength 40) 0 0)
      .truncatedMadtHeader = true := by
  native_decide

theorem complete_madt_entry_error_preserves_provenance :
    completeMadtFailedWith
      (decodeAndAdmitCompleteMadt
        (madtTableWithEntries [0, 8, 0, 0, 1]) 0 0)
      (.entry .truncatedRecord) = true := by
  native_decide

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
  | completeMadt (reason : CompleteMadtError)
  | authoritativeAcpi (reason : AuthoritativeAcpiTopologyError)
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

/-- Consume the complete-table pipeline without collapsing ACPI-envelope,
fixed-header, and MADT-entry failures into one decoder error. -/
def consumeCompleteBootAdmission (state : BootAdmissionState)
    (result : Except CompleteMadtError Result) : BootAdmissionState :=
  match state.latched with
  | some _ => state
  | none =>
      let business :=
        if state.phase != .bootstrap64 || state.business.phase != .bootstrap64 then
          haltAdmission state.business .wrongPhase
        else
          match result with
          | .error reason => haltAdmission state.business (.completeMadt reason)
          | .ok admitted => consumeAdmission state.business (.ok admitted)
      let next := { state with business }
      match business.failure with
      | some _ => (BootInterruptPhase.rejectTopology next).state
      | none => next

/-- Consume only the root-selected authoritative ACPI result, preserving which
boundary rejected it before entering the real terminal boot phase. -/
def consumeAuthoritativeBootAdmission (state : BootAdmissionState)
    (result : Except AuthoritativeAcpiTopologyError Result) : BootAdmissionState :=
  match state.latched with
  | some _ => state
  | none =>
      let business :=
        if state.phase != .bootstrap64 || state.business.phase != .bootstrap64 then
          haltAdmission state.business .wrongPhase
        else
          match result with
          | .error reason => haltAdmission state.business (.authoritativeAcpi reason)
          | .ok admitted => consumeAdmission state.business (.ok admitted)
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

def completeMadtErrorCode : CompleteMadtError → UInt64
  | .entry reason => decodeErrorCode reason
  | .truncatedMadtHeader => 6
  | .sdt .truncatedHeader => 7
  | .sdt .invalidSignature => 8
  | .sdt .invalidLength => 9
  | .sdt .tableTooLarge => 10
  | .sdt .invalidChecksum => 11
  | .sdt .invalidRootPayloadAlignment => 12
  | .sdt .rootEntryOverflow => 13

def authoritativeAcpiTopologyErrorCode : AuthoritativeAcpiTopologyError → UInt64
  | .rsdp .missingRoot => 20
  | .rsdp .duplicateOldRoot => 21
  | .rsdp .duplicateNewRoot => 22
  | .rsdp .conflictingRoots => 23
  | .selectedRootAddressMismatch _ _ => 24
  | .madtSelection (.root _) => 25
  | .madtSelection (.untranslatedRootEntry _) => 26
  | .madtSelection (.duplicateTranslation _) => 27
  | .madtSelection .missingMadt => 28
  | .madtSelection .duplicateMadt => 29
  | .completeMadt reason => 32 + completeMadtErrorCode reason

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

def completeTopologyQuery (bytes : ByteArray)
    (bspId executingId word : UInt64) : UInt64 :=
  if word == 0 then topologyAbiVersion
  else
    match decodeAndAdmitCompleteMadt bytes.data.toList
      (UInt32.ofNat bspId.toNat) (UInt32.ofNat executingId.toNat) with
    | .error reason =>
        if word == 1 then 2 else if word == 2 then completeMadtErrorCode reason else 0
    | .ok (.rejected reason) =>
        if word == 1 then 3 else if word == 2 then admissionErrorCode reason else 0
    | .ok (.accepted processor) =>
        if word == 1 then 1
        else if word == 2 then processor.apicId.toUInt64
        else if word == 3 then if processor.enabled then 1 else 0
        else if word == 4 then if processor.onlineCapable then 1 else 0
        else 0

def authoritativeTopologyQuery
    (rootTags : List RawAcpiRootTag) (rootCopy : CopiedAcpiSdt)
    (tableCopies : List CopiedAcpiSdt) (executingApicId word : UInt64) : UInt64 :=
  if word == 0 then topologyAbiVersion
  else
    match decodeAndAdmitAuthoritativeAcpiTopology rootTags rootCopy tableCopies
      (UInt32.ofNat executingApicId.toNat) with
    | .error reason =>
        if word == 1 then 2
        else if word == 2 then authoritativeAcpiTopologyErrorCode reason
        else 0
    | .ok (.rejected reason) =>
        if word == 1 then 3 else if word == 2 then admissionErrorCode reason else 0
    | .ok (.accepted processor) =>
        if word == 1 then 1
        else if word == 2 then processor.apicId.toUInt64
        else if word == 3 then if processor.enabled then 1 else 0
        else if word == 4 then if processor.onlineCapable then 1 else 0
        else 0

private def pairMachineTableCopies : List UInt64 → List ByteArray →
    Option (List CopiedAcpiSdt)
  | [], [] => some []
  | address :: addresses, bytes :: tables => do
      let rest ← pairMachineTableCopies addresses tables
      pure ({ physicalAddress := address, bytes := bytes.data.toList } :: rest)
  | _, _ => none

/-- Allocation-free scalar seed for the production copied-table stream.

The one-MiB aggregate cap matches the kernel arena. Each complete SDT consumes
its eight-byte-aligned length, and overflow is rejected before the caller may
advance its immutable copy cursor. Result words are version/status/error/next
cursor; errors 43 and 44 denote aggregate exhaustion and invalid SDT length. -/
def machineAcpiCopyBudgetQuery
    (currentOffset tableLength word : UInt64) : UInt64 :=
  if word == 0 then 1
  else if tableLength < 36 || tableLength > UInt64.ofNat maxAcpiSdtBytes then
    if word == 1 then 2 else if word == 2 then 44 else 0
  else
    let paddedLength := ((tableLength + 7) / 8) * 8
    let capacity : UInt64 := 1024 * 1024
    if paddedLength < tableLength || currentOffset % 8 != 0 ||
        currentOffset > capacity ||
        paddedLength > capacity - currentOffset then
      if word == 1 then 2 else if word == 2 then 43 else 0
    else if word == 1 then 1
    else if word == 3 then currentOffset + paddedLength
    else 0

@[export leanos_boot_machine_acpi_copy_budget_query]
def exportedMachineAcpiCopyBudgetQuery
    (currentOffset tableLength word : UInt64) : UInt64 :=
  machineAcpiCopyBudgetQuery currentOffset tableLength word

theorem machine_acpi_copy_budget_exact_capacity_accepted :
    machineAcpiCopyBudgetQuery (1024 * 1024 - 65536) 65536 3 =
      1024 * 1024 := by
  native_decide

theorem machine_acpi_copy_budget_exhaustion_rejected :
    machineAcpiCopyBudgetQuery (1024 * 1024 - 65528) 65536 2 = 43 := by
  native_decide

theorem machine_acpi_copy_budget_forged_cursor_rejected :
    machineAcpiCopyBudgetQuery (1024 * 1024 + 1) 36 2 = 43 := by
  native_decide

theorem machine_acpi_copy_budget_misaligned_cursor_rejected :
    machineAcpiCopyBudgetQuery 1 36 2 = 43 := by
  native_decide

theorem machine_acpi_copy_budget_invalid_length_rejected :
    machineAcpiCopyBudgetQuery 0 65537 2 = 44 := by
  native_decide

/-- One allocation-free transition for the production ACPI copy stream.

The caller must feed the returned next-byte and next-copy cursors into the
next transition.  The generated transition binds every exposed chunk to its
physical table address and declared length, rejects reordered/partial steps,
and advances the aggregate copy arena only on the exact terminal chunk.
Errors 45, 46, and 47 denote an invalid table address, byte cursor, and
terminal marker respectively. -/
def machineAcpiCopyStreamStepQuery
    (currentCopyOffset currentTableAddress currentByteOffset tableAddress
      tableLength byteOffset chunk terminal word : UInt64) : UInt64 :=
  let budgetStatus := machineAcpiCopyBudgetQuery currentCopyOffset tableLength 1
  let budgetError := machineAcpiCopyBudgetQuery currentCopyOffset tableLength 2
  let badAddress := currentTableAddress == 0 ||
    currentTableAddress > 0xffffffff || tableAddress != currentTableAddress
  let badOffset := currentByteOffset % 8 != 0 ||
    currentByteOffset >= tableLength || byteOffset != currentByteOffset
  let shouldTerminate := byteOffset + 8 >= tableLength
  let badTerminal := terminal > 1 || ((terminal == 1) != shouldTerminate)
  let error :=
    if budgetStatus != 1 then budgetError
    else if badAddress then 45
    else if badOffset then 46
    else if badTerminal then 47
    else 0
  if word == 0 then 1
  else if word == 1 then if error == 0 then 1 else 2
  else if word == 2 then error
  else if error != 0 then 0
  else if word == 3 then tableAddress
  else if word == 4 then
    if shouldTerminate then tableLength else byteOffset + 8
  else if word == 5 then
    if shouldTerminate then
      machineAcpiCopyBudgetQuery currentCopyOffset tableLength 3
    else currentCopyOffset
  else if word == 6 then chunk
  else 0

@[export leanos_boot_machine_acpi_copy_stream_step_query]
def exportedMachineAcpiCopyStreamStepQuery
    (currentCopyOffset currentTableAddress currentByteOffset tableAddress
      tableLength byteOffset chunk terminal word : UInt64) : UInt64 :=
  machineAcpiCopyStreamStepQuery currentCopyOffset currentTableAddress
    currentByteOffset tableAddress tableLength byteOffset chunk terminal word

theorem machine_acpi_copy_stream_partial_step_retains_copy_cursor :
    machineAcpiCopyStreamStepQuery 0 0x000f6000 0 0x000f6000 44 0
      0x1122334455667788 0 5 = 0 := by
  native_decide

theorem machine_acpi_copy_stream_terminal_step_advances_copy_cursor :
    machineAcpiCopyStreamStepQuery 0 0x000f6000 40 0x000f6000 44 40
      0xaabbccdd 1 5 = 48 := by
  native_decide

theorem machine_acpi_copy_stream_forged_terminal_rejected :
    machineAcpiCopyStreamStepQuery 0 0x000f6000 0 0x000f6000 44 0 0 1 2 = 47 := by
  native_decide

theorem machine_acpi_copy_stream_truncated_final_chunk_rejected :
    machineAcpiCopyStreamStepQuery 0 0x000f6000 32 0x000f6000 44 32 0 1 2 =
      47 := by
  native_decide

theorem machine_acpi_copy_stream_missing_final_marker_rejected :
    machineAcpiCopyStreamStepQuery 0 0x000f6000 40 0x000f6000 44 40 0 0 2 =
      47 := by
  native_decide

theorem machine_acpi_copy_stream_reordered_address_rejected :
    machineAcpiCopyStreamStepQuery 0 0x000f6000 0 0x000f7000 44 0 0 0 2 =
      45 := by
  native_decide

theorem machine_acpi_copy_stream_unaligned_physical_address_accepted :
    machineAcpiCopyStreamStepQuery 0 0x000f6004 0 0x000f6004 44 0
      0x1122334455667788 0 2 = 0 := by
  native_decide

theorem machine_acpi_copy_stream_reordered_byte_rejected :
    machineAcpiCopyStreamStepQuery 0 0x000f6000 8 0x000f6000 44 16 0 0 2 =
      46 := by
  native_decide

/-- Advance the advertised-table sequence only after one complete copied SDT.

The caller must carry `currentOrdinal` from the returned word 3 into the next
step.  This makes a skipped or replayed table ordinal observable and binds the
final-table marker to the exact advertised count.  Errors 48 and 49 denote an
ordinal/count mismatch and a missing/forged final-table marker respectively. -/
def machineAcpiCopySequenceStepQuery
    (currentOrdinal advertisedCount tableOrdinal tableComplete finalTable
      word : UInt64) : UInt64 :=
  let badOrdinal := advertisedCount == 0 ||
    advertisedCount > UInt64.ofNat maxAcpiRootEntries ||
    currentOrdinal >= advertisedCount || tableOrdinal != currentOrdinal ||
    tableComplete != 1
  let shouldFinish := currentOrdinal + 1 == advertisedCount
  let badFinal := finalTable > 1 || ((finalTable == 1) != shouldFinish)
  let error := if badOrdinal then 48 else if badFinal then 49 else 0
  if word == 0 then 1
  else if word == 1 then if error == 0 then 1 else 2
  else if word == 2 then error
  else if error != 0 then 0
  else if word == 3 then currentOrdinal + 1
  else 0

@[export leanos_boot_machine_acpi_copy_sequence_step_query]
def exportedMachineAcpiCopySequenceStepQuery
    (currentOrdinal advertisedCount tableOrdinal tableComplete finalTable
      word : UInt64) : UInt64 :=
  machineAcpiCopySequenceStepQuery currentOrdinal advertisedCount tableOrdinal
    tableComplete finalTable word

theorem machine_acpi_copy_sequence_exact_terminal_accepted :
    machineAcpiCopySequenceStepQuery 1 2 1 1 1 3 = 2 := by
  native_decide

theorem machine_acpi_copy_sequence_duplicate_ordinal_rejected :
    machineAcpiCopySequenceStepQuery 1 2 0 1 1 2 = 48 := by
  native_decide

theorem machine_acpi_copy_sequence_missing_ordinal_rejected :
    machineAcpiCopySequenceStepQuery 1 3 2 1 0 2 = 48 := by
  native_decide

theorem machine_acpi_copy_sequence_forged_final_rejected :
    machineAcpiCopySequenceStepQuery 0 2 0 1 1 2 = 49 := by
  native_decide

theorem machine_acpi_copy_sequence_missing_final_rejected :
    machineAcpiCopySequenceStepQuery 1 2 1 1 0 2 = 49 := by
  native_decide

/-! ### Allocation-free complete-MADT envelope stream -/

/-- Consume one exact byte from the selected immutable MADT copy.

The caller carries words 3--5 (next byte, declared length, and checksum) into
the next transition.  The generated transition, rather than C, recognizes the
`APIC` signature, reconstructs the complete 32-bit declared length, requires
the exact 44-byte-or-larger bounded extent, binds the terminal marker to the
last byte, and accepts the envelope only when the whole-table checksum is
zero.  Result status is 1 while active, 2 on rejection, and 3 on the exact
terminal byte.  Errors 55 through 59 denote malformed state/order, signature,
declared length, checksum, and terminal-marker failures respectively. -/
def machineMadtEnvelopeByteStepQuery
    (currentOffset declaredLength checksum tableLength byteOffset byteValue
      terminal word : UInt64) : UInt64 :=
  let malformedState := currentOffset != byteOffset || byteValue > 0xff ||
    checksum > 0xff || declaredLength > 0xffffffff ||
    tableLength < UInt64.ofNat acpiMadtHeaderLength ||
    tableLength > UInt64.ofNat maxAcpiSdtBytes || byteOffset >= tableLength
  let signatureError :=
    (byteOffset == 0 && byteValue != 0x41) ||
    (byteOffset == 1 && byteValue != 0x50) ||
    (byteOffset == 2 && byteValue != 0x49) ||
    (byteOffset == 3 && byteValue != 0x43)
  let lengthShift := (byteOffset - 4) * 8
  let nextDeclaredLength :=
    if byteOffset >= 4 && byteOffset <= 7 then
      declaredLength ||| (byteValue <<< lengthShift)
    else declaredLength
  let lengthError := byteOffset == 7 && nextDeclaredLength != tableLength
  let shouldTerminate := byteOffset + 1 == tableLength
  let terminalError := terminal > 1 || ((terminal == 1) != shouldTerminate)
  let nextChecksum := (checksum + byteValue) % 256
  let checksumError := shouldTerminate && nextChecksum != 0
  let error :=
    if malformedState then 55
    else if signatureError then 56
    else if lengthError then 57
    else if terminalError then 59
    else if checksumError then 58
    else 0
  if word == 0 then 1
  else if word == 1 then
    if error != 0 then 2 else if shouldTerminate then 3 else 1
  else if word == 2 then error
  else if error != 0 then 0
  else if word == 3 then byteOffset + 1
  else if word == 4 then nextDeclaredLength
  else if word == 5 then nextChecksum
  else if word == 6 then byteValue
  else 0

@[export leanos_boot_machine_madt_envelope_byte_step_query]
def exportedMachineMadtEnvelopeByteStepQuery
    (currentOffset declaredLength checksum tableLength byteOffset byteValue
      terminal word : UInt64) : UInt64 :=
  machineMadtEnvelopeByteStepQuery currentOffset declaredLength checksum
    tableLength byteOffset byteValue terminal word

theorem machine_madt_envelope_first_signature_byte_accepted :
    machineMadtEnvelopeByteStepQuery 0 0 0 52 0 0x41 0 3 = 1 := by
  native_decide

theorem machine_madt_envelope_wrong_signature_rejected :
    machineMadtEnvelopeByteStepQuery 0 0 0 52 0 0x58 0 2 = 56 := by
  native_decide

theorem machine_madt_envelope_declared_length_mismatch_rejected :
    machineMadtEnvelopeByteStepQuery 7 52 0 52 7 1 0 2 = 57 := by
  native_decide

theorem machine_madt_envelope_early_terminal_rejected :
    machineMadtEnvelopeByteStepQuery 8 52 0 52 8 1 1 2 = 59 := by
  native_decide

theorem machine_madt_envelope_exact_terminal_checksum_accepted :
    machineMadtEnvelopeByteStepQuery 51 52 255 52 51 1 1 1 = 3 := by
  native_decide

/-! ### Allocation-free local-APIC record stream -/

/-- Consume one byte of an exact eight-byte MADT local-APIC record.

This is the first entry-framing transition after the complete envelope gate.
The caller carries words 3--6 (record offset, declared record length, APIC ID,
and flags). The generated transition binds kind zero and length eight, decodes
the APIC ID and little-endian flags, requires the exact terminal byte, and
admits only an enabled, non-online-capable processor. Result status is 1 while
active, 2 on rejection, and 3 on exact record completion. Errors 60 through 64
denote malformed state/order, record kind, record length, terminal-marker, and
processor-flag failures respectively. -/
def machineMadtLocalApicByteStepQuery
    (currentOffset recordOffset recordLength apicId flags byteOffset byteValue
      terminal word : UInt64) : UInt64 :=
  let malformedState := currentOffset != byteOffset || recordOffset > 7 ||
    recordLength > 8 || apicId > 0xff || flags > 0xffffffff ||
    byteValue > 0xff
  let kindError := recordOffset == 0 && byteValue != 0
  let nextRecordLength := if recordOffset == 1 then byteValue else recordLength
  let lengthError := recordOffset == 1 && nextRecordLength != 8
  let nextApicId := if recordOffset == 3 then byteValue else apicId
  let flagsShift := (recordOffset - 4) * 8
  let nextFlags :=
    if recordOffset >= 4 then flags ||| (byteValue <<< flagsShift) else flags
  let shouldTerminate := recordOffset == 7
  let terminalError := terminal > 1 || ((terminal == 1) != shouldTerminate)
  let flagsError := shouldTerminate &&
    ((nextFlags &&& 1) != 1 || (nextFlags &&& 2) != 0)
  let error :=
    if malformedState then 60
    else if kindError then 61
    else if lengthError then 62
    else if terminalError then 63
    else if flagsError then 64
    else 0
  if word == 0 then 1
  else if word == 1 then
    if error != 0 then 2 else if shouldTerminate then 3 else 1
  else if word == 2 then error
  else if error != 0 then 0
  else if word == 3 then recordOffset + 1
  else if word == 4 then nextRecordLength
  else if word == 5 then nextApicId
  else if word == 6 then nextFlags
  else if word == 7 then byteValue
  else 0

@[export leanos_boot_machine_madt_local_apic_byte_step_query]
def exportedMachineMadtLocalApicByteStepQuery
    (currentOffset recordOffset recordLength apicId flags byteOffset byteValue
      terminal word : UInt64) : UInt64 :=
  machineMadtLocalApicByteStepQuery currentOffset recordOffset recordLength
    apicId flags byteOffset byteValue terminal word

theorem machine_madt_local_apic_kind_accepted :
    machineMadtLocalApicByteStepQuery 44 0 0 0 0 44 0 0 1 = 1 := by
  native_decide

theorem machine_madt_x2apic_kind_rejected :
    machineMadtLocalApicByteStepQuery 44 0 0 0 0 44 9 0 2 = 61 := by
  native_decide

theorem machine_madt_local_apic_length_rejected :
    machineMadtLocalApicByteStepQuery 45 1 0 0 0 45 7 0 2 = 62 := by
  native_decide

theorem machine_madt_local_apic_online_capable_rejected :
    machineMadtLocalApicByteStepQuery 51 7 8 0 3 51 0 1 2 = 64 := by
  native_decide

theorem machine_madt_local_apic_exact_record_accepted :
    machineMadtLocalApicByteStepQuery 51 7 8 0 1 51 0 1 1 = 3 := by
  native_decide

/-! ### Allocation-free topology-irrelevant MADT record stream -/

/-- Consume one byte from a fixed-width q35 MADT record that cannot add a CPU.

The accepted kinds are I/O APIC (1, length 12), interrupt-source override
(2, length 10), and local-APIC NMI (4, length 6). The generated transition
binds both kind and exact width and therefore cannot skip x2APIC or an unknown
variable-width record. Errors 65--68 denote malformed state/order,
unsupported kind, wrong fixed length, and terminal-marker mismatch. -/
def machineMadtIrrelevantRecordByteStepQuery
    (currentOffset recordOffset recordKind recordLength byteOffset byteValue
      terminal word : UInt64) : UInt64 :=
  let malformedState := currentOffset != byteOffset || recordOffset > 11 ||
    recordKind > 0xff || recordLength > 12 || byteValue > 0xff ||
    (recordOffset > 1 && (recordLength == 0 || recordOffset >= recordLength))
  let nextRecordKind := if recordOffset == 0 then byteValue else recordKind
  let kindError := recordOffset == 0 &&
    nextRecordKind != 1 && nextRecordKind != 2 && nextRecordKind != 4
  let expectedLength :=
    if nextRecordKind == 1 then 12
    else if nextRecordKind == 2 then 10
    else if nextRecordKind == 4 then 6
    else 0
  let nextRecordLength := if recordOffset == 1 then byteValue else recordLength
  let lengthError := recordOffset == 1 && nextRecordLength != expectedLength
  let shouldTerminate := nextRecordLength != 0 &&
    recordOffset + 1 == nextRecordLength
  let terminalError := terminal > 1 || ((terminal == 1) != shouldTerminate)
  let error :=
    if malformedState then 65
    else if kindError then 66
    else if lengthError then 67
    else if terminalError then 68
    else 0
  if word == 0 then 1
  else if word == 1 then
    if error != 0 then 2 else if shouldTerminate then 3 else 1
  else if word == 2 then error
  else if error != 0 then 0
  else if word == 3 then recordOffset + 1
  else if word == 4 then nextRecordKind
  else if word == 5 then nextRecordLength
  else if word == 6 then byteValue
  else 0

@[export leanos_boot_machine_madt_irrelevant_record_byte_step_query]
def exportedMachineMadtIrrelevantRecordByteStepQuery
    (currentOffset recordOffset recordKind recordLength byteOffset byteValue
      terminal word : UInt64) : UInt64 :=
  machineMadtIrrelevantRecordByteStepQuery currentOffset recordOffset
    recordKind recordLength byteOffset byteValue terminal word

theorem machine_madt_io_apic_kind_accepted :
    machineMadtIrrelevantRecordByteStepQuery 52 0 0 0 52 1 0 4 = 1 := by
  native_decide

theorem machine_madt_io_apic_wrong_length_rejected :
    machineMadtIrrelevantRecordByteStepQuery 53 1 1 0 53 10 0 2 = 67 := by
  native_decide

theorem machine_madt_x2apic_not_skippable :
    machineMadtIrrelevantRecordByteStepQuery 52 0 0 0 52 9 0 2 = 66 := by
  native_decide

theorem machine_madt_local_apic_nmi_exact_terminal_accepted :
    machineMadtIrrelevantRecordByteStepQuery 57 5 4 6 57 0 1 1 = 3 := by
  native_decide

/-! ### Allocation-free complete MADT entry stream -/

/-- Consume the complete entry region of one envelope-validated MADT.

The caller carries only the words emitted by the preceding transition.  Four
64-bit limbs retain the complete 256-bit local-APIC-ID set without allocation.
The generated transition binds record kind and width, permits disabled legacy
local-APIC records without counting them, rejects online-capable processors,
rejects duplicate APIC IDs (including disabled duplicates), and authorizes the
terminal byte only when exactly one enabled APIC ID equals the executing APIC
ID.  Fixed-width q35 interrupt-routing records are consumed but cannot affect
the processor set.  x2APIC and every unknown/variable-width kind fail closed.

Result status is 1 while active, 2 on rejection, and 3 on exact complete-table
admission. Errors 69--76 denote malformed state/order, unsupported kind, wrong
record width, truncated entry region, online-capable processor, duplicate APIC
ID, non-singleton enabled set, and executing-APIC mismatch.  Result words are
ABI/status/error followed by the complete next state. -/
def machineMadtEntryStreamByteStepQuery
    (currentOffset recordOffset recordKind recordLength apicId flags
      enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue word : UInt64) : UInt64 :=
  let malformedState := currentOffset != byteOffset || byteOffset < 44 ||
    byteOffset >= tableLength || tableLength < 44 ||
    tableLength > UInt64.ofNat maxAcpiSdtBytes || recordOffset > 11 ||
    recordKind > 0xff || recordLength > 12 || apicId > 0xff ||
    flags > 0xffffffff || enabledCount > 256 || admittedApicId > 256 ||
    executingApicId > 0xff || byteValue > 0xff
  let nextKind := if recordOffset == 0 then byteValue else recordKind
  let kindError := recordOffset == 0 && nextKind != 0 && nextKind != 1 &&
    nextKind != 2 && nextKind != 4
  let expectedLength :=
    if nextKind == 0 then 8
    else if nextKind == 1 then 12
    else if nextKind == 2 then 10
    else if nextKind == 4 then 6
    else 0
  let nextLength := if recordOffset == 1 then byteValue else recordLength
  let lengthError := recordOffset == 1 && nextLength != expectedLength
  let nextApicId :=
    if nextKind == 0 && recordOffset == 3 then byteValue else apicId
  let flagsShift := (recordOffset - 4) * 8
  let nextFlags :=
    if nextKind == 0 && recordOffset >= 4 then
      flags ||| (byteValue <<< flagsShift)
    else flags
  let recordComplete := nextLength != 0 && recordOffset + 1 == nextLength
  let tableComplete := byteOffset + 1 == tableLength
  let truncationError := tableComplete && !recordComplete
  let onlineCapableError := recordComplete && nextKind == 0 &&
    (nextFlags &&& 2) != 0
  let seenIndex := nextApicId / 64
  let seenBit := (1 : UInt64) <<< (nextApicId % 64)
  let duplicate := recordComplete && nextKind == 0 &&
    ((seenIndex == 0 && (seen0 &&& seenBit) != 0) ||
     (seenIndex == 1 && (seen1 &&& seenBit) != 0) ||
     (seenIndex == 2 && (seen2 &&& seenBit) != 0) ||
     (seenIndex == 3 && (seen3 &&& seenBit) != 0))
  let enabled := recordComplete && nextKind == 0 && (nextFlags &&& 1) != 0
  let nextEnabledCount := if enabled then enabledCount + 1 else enabledCount
  let nextAdmittedApicId :=
    if enabled && enabledCount == 0 then nextApicId else admittedApicId
  let nextSeen0 :=
    if recordComplete && nextKind == 0 && seenIndex == 0 then seen0 ||| seenBit
    else seen0
  let nextSeen1 :=
    if recordComplete && nextKind == 0 && seenIndex == 1 then seen1 ||| seenBit
    else seen1
  let nextSeen2 :=
    if recordComplete && nextKind == 0 && seenIndex == 2 then seen2 ||| seenBit
    else seen2
  let nextSeen3 :=
    if recordComplete && nextKind == 0 && seenIndex == 3 then seen3 ||| seenBit
    else seen3
  let singletonError := tableComplete && recordComplete &&
    nextEnabledCount != 1
  let executingError := tableComplete && recordComplete &&
    nextEnabledCount == 1 && nextAdmittedApicId != executingApicId
  let error :=
    if malformedState then 69
    else if kindError then 70
    else if lengthError then 71
    else if truncationError then 72
    else if onlineCapableError then 73
    else if duplicate then 74
    else if singletonError then 75
    else if executingError then 76
    else 0
  if word == 0 then 1
  else if word == 1 then
    if error != 0 then 2 else if tableComplete then 3 else 1
  else if word == 2 then error
  else if error != 0 then 0
  else if word == 3 then byteOffset + 1
  else if word == 4 then if recordComplete then 0 else recordOffset + 1
  else if word == 5 then if recordComplete then 0 else nextKind
  else if word == 6 then if recordComplete then 0 else nextLength
  else if word == 7 then if recordComplete then 0 else nextApicId
  else if word == 8 then if recordComplete then 0 else nextFlags
  else if word == 9 then nextEnabledCount
  else if word == 10 then nextAdmittedApicId
  else if word == 11 then nextSeen0
  else if word == 12 then nextSeen1
  else if word == 13 then nextSeen2
  else if word == 14 then nextSeen3
  else if word == 15 then byteValue
  else 0

@[export leanos_boot_machine_madt_entry_stream_byte_step_query]
def exportedMachineMadtEntryStreamByteStepQuery
    (currentOffset recordOffset recordKind recordLength apicId flags
      enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue word : UInt64) : UInt64 :=
  machineMadtEntryStreamByteStepQuery currentOffset recordOffset recordKind
    recordLength apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3
    tableLength executingApicId byteOffset byteValue word

theorem machine_madt_entry_stream_first_local_apic_byte_accepted :
    machineMadtEntryStreamByteStepQuery
      44 0 0 0 0 0 0 256 0 0 0 0 52 0 44 0 1 = 1 := by
  native_decide

theorem machine_madt_entry_stream_x2apic_rejected :
    machineMadtEntryStreamByteStepQuery
      44 0 0 0 0 0 0 256 0 0 0 0 52 0 44 9 2 = 70 := by
  native_decide

theorem machine_madt_entry_stream_duplicate_apic_rejected :
    machineMadtEntryStreamByteStepQuery
      59 7 0 8 0 1 1 0 1 0 0 0 60 0 59 0 2 = 74 := by
  native_decide

theorem machine_madt_entry_stream_single_enabled_terminal_admitted :
    machineMadtEntryStreamByteStepQuery
      51 7 0 8 0 1 0 256 0 0 0 0 52 0 51 0 1 = 3 := by
  native_decide

theorem machine_madt_entry_stream_wrong_executing_apic_rejected :
    machineMadtEntryStreamByteStepQuery
      51 7 0 8 1 1 0 256 0 0 0 0 52 0 51 0 2 = 76 := by
  native_decide

/-! ### Allocation-free machine topology terminal gate -/

/-- Final fixed-width gate for the production topology stream.

The scalar arguments are the terminal words carried from the generated root,
copy-sequence, unique-MADT, and complete-admission transitions.  This function
does not replace those byte-consuming transitions: it prevents C from
publishing runtime after a partial copy, a root-address substitution, a
missing/duplicate MADT, a rejected admission, or an executing-APIC mismatch.

Result words are ABI/status/error/admitted APIC ID.  Errors 50 through 54 name
root binding, incomplete copy sequence, non-unique MADT, rejected admission,
and executing-APIC mismatch respectively. -/
def machineTopologyAdmissionResultQuery
    (selectedKind selectedAddress copiedRootAddress advertisedCount
      completedCopies madtCount admissionStatus admissionDetail
      admittedApicId executingApicId word : UInt64) : UInt64 :=
  let error :=
    if (selectedKind != 1 && selectedKind != 2) || selectedAddress == 0 ||
        copiedRootAddress != selectedAddress then 50
    else if advertisedCount == 0 ||
        advertisedCount > UInt64.ofNat maxAcpiRootEntries ||
        completedCopies != advertisedCount then 51
    else if madtCount != 1 then 52
    else if admissionStatus != 1 || admissionDetail != 0 then 53
    else if admittedApicId > 255 || admittedApicId != executingApicId then 54
    else 0
  if word == 0 then 1
  else if word == 1 then if error == 0 then 1 else 2
  else if word == 2 then error
  else if word == 3 && error == 0 then admittedApicId
  else 0

@[export leanos_boot_machine_topology_admission_result_query]
def exportedMachineTopologyAdmissionResultQuery
    (selectedKind selectedAddress copiedRootAddress advertisedCount
      completedCopies madtCount admissionStatus admissionDetail
      admittedApicId executingApicId word : UInt64) : UInt64 :=
  machineTopologyAdmissionResultQuery selectedKind selectedAddress
    copiedRootAddress advertisedCount completedCopies madtCount admissionStatus
    admissionDetail admittedApicId executingApicId word

theorem machine_topology_admission_result_exact_state_accepted :
    machineTopologyAdmissionResultQuery 2 0xf5c00 0xf5c00 2 2 1 1 0 0 0 1 = 1 := by
  native_decide

theorem machine_topology_admission_result_incomplete_copy_rejected :
    machineTopologyAdmissionResultQuery 2 0xf5c00 0xf5c00 2 1 1 1 0 0 0 2 = 51 := by
  native_decide

theorem machine_topology_admission_result_duplicate_madt_rejected :
    machineTopologyAdmissionResultQuery 2 0xf5c00 0xf5c00 2 2 2 1 0 0 0 2 = 52 := by
  native_decide

theorem machine_topology_admission_result_forged_executing_apic_rejected :
    machineTopologyAdmissionResultQuery 2 0xf5c00 0xf5c00 2 2 1 1 0 0 1 2 = 54 := by
  native_decide

/-- Stable generated boundary for production's immutable ACPI copies.

The machine adapter supplies the selected root kind/address emitted by the
generated Multiboot2 decoder, one byte copy for that root, one address/byte
pair for every advertised table, and the executing APIC ID observed directly
with CPUID. The 256-copy cap matches `maxAcpiRootEntries`; count drift and an
unknown selected-root kind fail closed before table selection.

Result words use the ordinary topology ABI. Boundary failures use codes 40
(root kind), 41 (copy-count mismatch), and 42 (copy-count overflow); typed
root/MADT failures retain `authoritativeAcpiTopologyErrorCode`. -/
def machineAuthoritativeTopologyQuery
    (selectedKind selectedAddress : UInt64) (rootBytes : ByteArray)
    (tableAddresses : Array UInt64) (tableBytes : Array ByteArray)
    (executingApicId word : UInt64) : UInt64 :=
  if word == 0 then topologyAbiVersion
  else if tableAddresses.size > maxAcpiRootEntries ||
      tableBytes.size > maxAcpiRootEntries then
    if word == 1 then 2 else if word == 2 then 42 else 0
  else
    match pairMachineTableCopies tableAddresses.toList tableBytes.toList with
    | none => if word == 1 then 2 else if word == 2 then 41 else 0
    | some copies =>
        let kind :=
          if selectedKind == 1 then some AcpiRootTableKind.rsdt
          else if selectedKind == 2 then some AcpiRootTableKind.xsdt
          else none
        match kind with
        | none => if word == 1 then 2 else if word == 2 then 40 else 0
        | some rootKind =>
            let rootCopy : CopiedAcpiSdt := {
              physicalAddress := selectedAddress
              bytes := rootBytes.data.toList
            }
            match selectUniqueCompleteMadt rootKind rootCopy.bytes copies with
            | .error reason =>
                if word == 1 then 2
                else if word == 2 then
                  authoritativeAcpiTopologyErrorCode (.madtSelection reason)
                else 0
            | .ok madt =>
                match decodeAndAdmitCompleteMadt madt
                    (UInt32.ofNat executingApicId.toNat)
                    (UInt32.ofNat executingApicId.toNat) with
                | .error reason =>
                    if word == 1 then 2
                    else if word == 2 then
                      authoritativeAcpiTopologyErrorCode (.completeMadt reason)
                    else 0
                | .ok (.rejected reason) =>
                    if word == 1 then 3
                    else if word == 2 then admissionErrorCode reason
                    else 0
                | .ok (.accepted processor) =>
                    if word == 1 then 1
                    else if word == 2 then processor.apicId.toUInt64
                    else if word == 3 then if processor.enabled then 1 else 0
                    else if word == 4 then
                      if processor.onlineCapable then 1 else 0
                    else 0

def exportedMachineAuthoritativeTopologyQuery
    (selectedKind selectedAddress : UInt64) (rootBytes : ByteArray)
    (tableAddresses : Array UInt64) (tableBytes : Array ByteArray)
    (executingApicId word : UInt64) : UInt64 :=
  machineAuthoritativeTopologyQuery selectedKind selectedAddress rootBytes
    tableAddresses tableBytes executingApicId word

theorem repository_machine_topology_query_admitted :
    machineAuthoritativeTopologyQuery 2 0x00000000000f5c00
      ⟨repositoryXsdtTableBytes.toArray⟩
      #[0x000f6000, 0x000f7000]
      #[⟨repositoryCompleteMadtBytes.toArray⟩,
        ⟨repositoryXsdtTableBytes.toArray⟩] 0 1 = 1 := by
  native_decide

theorem machine_topology_copy_count_mismatch_rejected :
    machineAuthoritativeTopologyQuery 2 0x00000000000f5c00
      ⟨repositoryXsdtTableBytes.toArray⟩ #[0x000f6000] #[] 0 2 = 41 := by
  native_decide

theorem machine_topology_copy_count_overflow_rejected :
    machineAuthoritativeTopologyQuery 2 0x00000000000f5c00
      ⟨repositoryXsdtTableBytes.toArray⟩
      (Array.replicate (maxAcpiRootEntries + 1) 0) #[] 0 2 = 42 := by
  native_decide

theorem machine_topology_byte_copy_count_overflow_rejected :
    machineAuthoritativeTopologyQuery 2 0x00000000000f5c00
      ⟨repositoryXsdtTableBytes.toArray⟩ #[]
      (Array.replicate (maxAcpiRootEntries + 1) ByteArray.empty) 0 2 = 42 := by
  native_decide

theorem machine_topology_unknown_root_kind_rejected :
    machineAuthoritativeTopologyQuery 3 0x00000000000f5c00
      ⟨repositoryXsdtTableBytes.toArray⟩
      #[0x000f6000, 0x000f7000]
      #[⟨repositoryCompleteMadtBytes.toArray⟩,
        ⟨repositoryXsdtTableBytes.toArray⟩] 0 2 = 40 := by
  native_decide

theorem repository_machine_topology_forged_executing_apic_rejected :
    machineAuthoritativeTopologyQuery 2 0x00000000000f5c00
      ⟨repositoryXsdtTableBytes.toArray⟩
      #[0x000f6000, 0x000f7000]
      #[⟨repositoryCompleteMadtBytes.toArray⟩,
        ⟨repositoryXsdtTableBytes.toArray⟩] 1 1 = 3 := by
  native_decide

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
  let complete :=
    if fixture == 10 then
      replaceSdtByte repositoryCompleteMadtBytes 0 (sdtByte 0x58)
    else if fixture == 11 then
      replaceSdtByte repositoryCompleteMadtBytes 4 (sdtByte 44)
    else if fixture == 12 then
      replaceSdtByte repositoryCompleteMadtBytes 10 (sdtByte 1)
    else if fixture == 13 then
      madtTableBytesOfLength 40
    else
      madtTableWithEntries selected.1
  if fixture < 14 then
    completeTopologyQuery ⟨complete.toArray⟩ selected.2.1 selected.2.2 word
  else
    let conflictingTags : List RawAcpiRootTag := [
      .old repositoryLegacyRoot,
      .new { repositoryLegacyRoot with oemId := [0x42] } 0x00000000000f5c00
    ]
    let wrongRootCopy :=
      { repositoryXsdtCopy with physicalAddress := 0x00000000000f5c08 }
    let missingTranslation : List CopiedAcpiSdt := [
      { physicalAddress := 0x000f6000, bytes := repositoryCompleteMadtBytes }
    ]
    let duplicateTranslation : List CopiedAcpiSdt := [
      { physicalAddress := 0x000f6000, bytes := repositoryCompleteMadtBytes },
      { physicalAddress := 0x000f6000, bytes := repositoryCompleteMadtBytes },
      { physicalAddress := 0x000f7000, bytes := repositoryXsdtTableBytes }
    ]
    let missingMadt : List CopiedAcpiSdt := [
      { physicalAddress := 0x000f6000, bytes := repositoryXsdtTableBytes },
      { physicalAddress := 0x000f7000, bytes := repositoryXsdtTableBytes }
    ]
    let duplicateMadt : List CopiedAcpiSdt := [
      { physicalAddress := 0x000f6000, bytes := repositoryCompleteMadtBytes },
      { physicalAddress := 0x000f7000, bytes := repositoryCompleteMadtBytes }
    ]
    if fixture == 14 then
      authoritativeTopologyQuery repositoryAcpiRootTags repositoryXsdtCopy
        repositoryCopiedAcpiTables 0 word
    else if fixture == 15 then
      authoritativeTopologyQuery conflictingTags repositoryXsdtCopy
        repositoryCopiedAcpiTables 0 word
    else if fixture == 16 then
      authoritativeTopologyQuery repositoryAcpiRootTags wrongRootCopy
        repositoryCopiedAcpiTables 0 word
    else if fixture == 17 then
      authoritativeTopologyQuery repositoryAcpiRootTags repositoryXsdtCopy
        missingTranslation 0 word
    else if fixture == 18 then
      authoritativeTopologyQuery repositoryAcpiRootTags repositoryXsdtCopy
        duplicateTranslation 0 word
    else if fixture == 19 then
      authoritativeTopologyQuery repositoryAcpiRootTags repositoryXsdtCopy
        missingMadt 0 word
    else
      authoritativeTopologyQuery repositoryAcpiRootTags repositoryXsdtCopy
        duplicateMadt 0 word

end LeanOS.BootTopology
