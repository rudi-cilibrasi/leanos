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

/-- Bounded input already copied from the selected MADT handoff.  The raw
record length and kind remain explicit so normalization cannot silently erase
truncation or admission-relevant unsupported entries. -/
inductive RawMadtRecord where
  | localApic (length : Nat) (apicId : UInt32) (enabled onlineCapable : Bool)
  | unsupported (kind : UInt8) (length : Nat)
  deriving DecidableEq, Repr

inductive DecodeError where
  | truncatedRecord
  | invalidRecordLength
  | unsupportedRecordKind
  | processorOverflow
  deriving DecidableEq, Repr

def localApicRecordLength : Nat := 8

def decodeProcessor : RawMadtRecord → Except DecodeError Processor
  | .localApic length apicId enabled onlineCapable =>
      if length < localApicRecordLength then
        .error .truncatedRecord
      else if length != localApicRecordLength then
        .error .invalidRecordLength
      else
        .ok { apicId, enabled, onlineCapable }
  | .unsupported _ _ => .error .unsupportedRecordKind

/-- The normalizer is the only constructor in this module that attaches the
ACPI-MADT source/version provenance to decoded processor records.  BSP and
executing IDs remain trusted machine inputs until the integration slice lands. -/
def normalizeMadtRecords (records : List RawMadtRecord)
    (bspId executingId : UInt32) : Except DecodeError Snapshot := do
  if records.length > maxProcessors then
    throw .processorOverflow
  let processors ← records.mapM decodeProcessor
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

end LeanOS.BootTopology
