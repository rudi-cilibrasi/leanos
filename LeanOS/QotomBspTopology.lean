import LeanOS.BootTopology

/-!
# Qotom BSP topology candidate

The captured J1900 topology advertises four enabled processors. This module
checks that exact topology independently of q35's single-core policy. A
`Witness` establishes only the processor observation: it is deliberately not
runtime authority or a claim that firmware left the other processors dormant.

The authoritative ACPI decoder remains the only raw-table entry point. Memory,
PCI, interrupt routing (including MADT NMI fields), AP dormancy, final-object
AP-start exclusion, and the complete versioned platform witness remain separate
requirements before this candidate can authorize physical execution.
-/

namespace LeanOS.QotomBspTopology

open BootTopology

/-- Exact captured processor order and flags; do not normalize away changed
firmware observations or disabled/online-capable records. -/
def processors : List Processor :=
  [0, 2, 4, 6].map fun id =>
    { apicId := id, enabled := true, onlineCapable := false }

def baseline : Snapshot :=
  { source := .acpiMadt
    version := snapshotVersion
    bspId := 0
    executingId := 0
    processors }

inductive Error where
  | unsupportedSource
  | unsupportedVersion
  | tooManyProcessors
  | duplicateApicId
  | noEnabledProcessor
  | wrongBsp
  | processorInventoryMismatch
  deriving DecidableEq, Repr

/-- A topology-only witness retains the complete observation and its equality
with the named baseline, rather than just a boolean admission flag. -/
structure Witness where
  observed : Snapshot
  matchesBaseline : observed = baseline

/-- Bounds and structural failures retain stable reasons before exact inventory
matching. This policy does not call or weaken `BootTopology.admit`. -/
def check (snapshot : Snapshot) : Except Error Witness :=
  if snapshot.source != .acpiMadt then .error .unsupportedSource
  else if snapshot.version != snapshotVersion then .error .unsupportedVersion
  else if snapshot.processors.length > maxProcessors then .error .tooManyProcessors
  else if !uniqueApicIds snapshot.processors then .error .duplicateApicId
  else if !(snapshot.processors.any fun p => p.enabled) then .error .noEnabledProcessor
  else if snapshot.bspId != 0 || snapshot.executingId != 0 then .error .wrongBsp
  else if h : snapshot = baseline then .ok ⟨snapshot, h⟩
  else .error .processorInventoryMismatch

inductive PipelineError where
  | acpi (reason : AuthoritativeAcpiTopologyError)
  | topology (reason : Error)
  deriving DecidableEq, Repr

/-- Root selection, copy-address binding and complete MADT validation must all
succeed before checking the Qotom processor inventory. -/
def checkAuthoritative (tags : List RawAcpiRootTag) (root : CopiedAcpiSdt)
    (tables : List CopiedAcpiSdt) (executingApicId : UInt32) :
    Except PipelineError Witness := do
  let snapshot ← match decodeAuthoritativeAcpiTopologySnapshot tags root tables
      executingApicId with
    | .error reason => throw (.acpi reason)
    | .ok snapshot => pure snapshot
  match check snapshot with
  | .error reason => throw (.topology reason)
  | .ok witness => pure witness

/-- Acceptance retains the exact caller observation; it cannot substitute a
known-good baseline for a mismatching snapshot. -/
theorem check_preserves_observation (snapshot : Snapshot) (witness : Witness)
    (accepted : check snapshot = .ok witness) : witness.observed = snapshot := by
  unfold check at accepted
  split at accepted <;> try simp_all
  split at accepted <;> try simp_all
  split at accepted <;> try simp_all
  split at accepted <;> try simp_all
  split at accepted <;> try simp_all
  split at accepted <;> try simp_all
  split at accepted <;> try simp_all

  rw [← accepted]

/-- Every possible candidate witness carries all processor fields together. -/
theorem witness_has_complete_baseline (witness : Witness) :
    witness.observed = baseline := witness.matchesBaseline

theorem witness_binds_executing_bsp (witness : Witness) :
    witness.observed.executingId = 0 ∧ witness.observed.bspId = 0 := by
  rw [witness.matchesBaseline]
  decide

theorem witness_enumerates_four_enabled_processors (witness : Witness) :
    witness.observed.processors = processors ∧
    witness.observed.processors.length = 4 ∧
    witness.observed.processors.all (fun p => p.enabled && !p.onlineCapable) = true := by
  rw [witness.matchesBaseline]
  decide

/-- A four-processor candidate can never masquerade as q35 single-core
admission. The existing rejection meaning is preserved exactly. -/
theorem witness_still_rejected_by_single_core (witness : Witness) :
    BootTopology.admit witness.observed = .rejected .multipleEnabledProcessors := by
  rw [witness.matchesBaseline]
  decide

private def failure (snapshot : Snapshot) : Option Error :=
  match check snapshot with
  | .error reason => some reason
  | .ok _ => none

theorem baseline_candidate_accepted : (check baseline).isOk = true := by native_decide

theorem wrong_source_rejected :
    failure { baseline with source := .cpuidTopology } = some .unsupportedSource := by
  native_decide

theorem wrong_version_rejected :
    failure { baseline with version := 2 } = some .unsupportedVersion := by native_decide

theorem wrong_executing_bsp_rejected :
    failure { baseline with executingId := 2 } = some .wrongBsp := by native_decide

theorem wrong_recorded_bsp_rejected :
    failure { baseline with bspId := 2 } = some .wrongBsp := by native_decide

theorem duplicate_processor_rejected :
    failure { baseline with processors := processors ++ processors } =
      some .duplicateApicId := by native_decide

theorem missing_processors_rejected :
    failure { baseline with processors := [] } = some .noEnabledProcessor := by
  native_decide

theorem missing_one_processor_rejected :
    failure { baseline with processors := processors.take 3 } =
      some .processorInventoryMismatch := by native_decide

theorem changed_processor_order_rejected :
    failure { baseline with processors := processors.reverse } =
      some .processorInventoryMismatch := by native_decide

theorem disabled_ap_rejected :
    failure { baseline with processors := processors.map (fun p =>
      if p.apicId == 2 then { p with enabled := false } else p) } =
      some .processorInventoryMismatch := by native_decide

theorem online_capable_ap_rejected :
    failure { baseline with processors := processors.map (fun p =>
      if p.apicId == 2 then { p with onlineCapable := true } else p) } =
      some .processorInventoryMismatch := by native_decide

theorem exceeded_bound_rejected_before_duplicates :
    failure { baseline with processors := (List.replicate (maxProcessors + 1)
      { apicId := 0, enabled := true, onlineCapable := false }) } =
      some .tooManyProcessors := by native_decide

theorem q35_cannot_supply_qotom_topology :
    failure repositorySingleCore = some .processorInventoryMismatch := by native_decide

/-! ## Authoritative-path fixtures

These tables are synthetic and use the existing repository root addresses.
They exercise policy composition, not the physical Qotom handoff.
-/

private def syntheticMadt : List UInt8 :=
  let entries : List UInt8 := [0, 2, 4, 6].flatMap fun id =>
    [0, 8, id, id, 1, 0, 0, 0]
  let header := repositoryCompleteMadtBytes.take 44
  let unchecked := (header ++ entries).zipIdx.map fun (byte, index) =>
    if index == 4 then UInt8.ofNat (44 + entries.length)
    else if index == 9 then 0 else byte
  let checksum := unchecked.foldl (fun sum byte => sum + byte) (0 : UInt8)
  unchecked.zipIdx.map fun (byte, index) => if index == 9 then 0 - checksum else byte

private def syntheticTables : List CopiedAcpiSdt :=
  repositoryCopiedAcpiTables.map fun table =>
    if table.physicalAddress == 0x000f6000 then { table with bytes := syntheticMadt }
    else table

private def pipelineFailure (tags : List RawAcpiRootTag) (root : CopiedAcpiSdt)
    (tables : List CopiedAcpiSdt) (executing : UInt32 := 0) : Option PipelineError :=
  match checkAuthoritative tags root tables executing with
  | .ok _ => none
  | .error reason => some reason

theorem authoritative_synthetic_four_cpu_candidate_accepted :
    (checkAuthoritative repositoryAcpiRootTags repositoryXsdtCopy
      syntheticTables 0).isOk = true := by native_decide

theorem missing_root_cannot_reach_candidate :
    pipelineFailure [] repositoryXsdtCopy syntheticTables =
      some (.acpi (.rsdp .missingRoot)) := by native_decide

theorem wrong_root_address_cannot_reach_candidate :
    pipelineFailure repositoryAcpiRootTags
      { repositoryXsdtCopy with physicalAddress := 0x000f5c08 } syntheticTables =
      some (.acpi (.selectedRootAddressMismatch 0x000f5c00 0x000f5c08)) := by
  native_decide

theorem missing_translation_cannot_reach_candidate :
    pipelineFailure repositoryAcpiRootTags repositoryXsdtCopy [] =
      some (.acpi (.madtSelection (.untranslatedRootEntry 0x000f6000))) := by
  native_decide

theorem duplicate_translation_cannot_reach_candidate :
    pipelineFailure repositoryAcpiRootTags repositoryXsdtCopy
      (syntheticTables ++ syntheticTables) =
      some (.acpi (.madtSelection (.duplicateTranslation 0x000f6000))) := by
  native_decide

theorem damaged_madt_cannot_reach_candidate :
    pipelineFailure repositoryAcpiRootTags repositoryXsdtCopy
      (syntheticTables.map fun table =>
        if table.physicalAddress == 0x000f6000 then
          { table with bytes := table.bytes.zipIdx.map fun (byte, index) =>
              if index == 9 then byte + 1 else byte }
        else table) = some (.acpi (.completeMadt (.sdt .invalidChecksum))) := by
  native_decide

theorem authoritative_wrong_executing_bsp_rejected :
    pipelineFailure repositoryAcpiRootTags repositoryXsdtCopy syntheticTables 2 =
      some (.topology .wrongBsp) := by native_decide

theorem authoritative_q35_cannot_supply_candidate :
    pipelineFailure repositoryAcpiRootTags repositoryXsdtCopy repositoryCopiedAcpiTables =
      some (.topology .processorInventoryMismatch) := by native_decide

/-- Hardware observation from the same executing CPU as the ACPI snapshot.
Read fidelity and temporal binding remain caller obligations. -/
structure BootstrapObservation where
  cpuidEdx : UInt32
  readAvailable : Bool
  apicBase : UInt64
  executingId : UInt32
  deriving DecidableEq, Repr

/-- Exact architectural state observed on Qotom. Pinning the complete register
also rejects changed APIC base, disabled APIC, x2APIC and reserved bits. -/
def expectedApicBase : UInt64 := 0xfee00900

/-- The topology witness alone does not prove the architectural BSP flag. -/
def BootstrapValid (topology : Witness) (observation : BootstrapObservation) : Prop :=
  observation.readAvailable = true ∧
  observation.cpuidEdx &&& 0x220 = 0x220 ∧
  observation.executingId = topology.observed.executingId ∧
  observation.apicBase = expectedApicBase

instance (topology : Witness) (observation : BootstrapObservation) :
    Decidable (BootstrapValid topology observation) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

inductive BootstrapError where
  | unavailable
  | missingFeatures
  | executingIdMismatch
  | notBootstrapProcessor
  | unsupportedApicState
  deriving DecidableEq, Repr

structure BootstrapWitness (topology : Witness) where
  observed : BootstrapObservation
  valid : BootstrapValid topology observed

/-- Reject observed missing features/role and identity disagreement before the
remaining complete-register mismatch. No baseline observation is substituted. -/
def bindBootstrap (topology : Witness) (observation : BootstrapObservation) :
    Except BootstrapError (BootstrapWitness topology) :=
  if h : BootstrapValid topology observation then .ok ⟨observation, h⟩
  else if !observation.readAvailable then .error .unavailable
  else if observation.cpuidEdx &&& 0x220 != 0x220 then .error .missingFeatures
  else if observation.executingId != topology.observed.executingId then .error .executingIdMismatch
  else if observation.apicBase &&& 0x100 == 0 then .error .notBootstrapProcessor
  else .error .unsupportedApicState

inductive BootstrapPipelineError where
  | topology (reason : PipelineError)
  | bootstrap (reason : BootstrapError)
  deriving DecidableEq, Repr

structure BootstrapEntryWitness where
  topology : Witness
  bootstrap : BootstrapWitness topology

/-- Compose the existing authoritative table decoder with the architectural
BSP observation. This remains a candidate, not runtime or AP-dormancy authority. -/
def checkBootstrapAuthoritative (tags : List RawAcpiRootTag) (root : CopiedAcpiSdt)
    (tables : List CopiedAcpiSdt) (executingApicId : UInt32)
    (observation : BootstrapObservation) : Except BootstrapPipelineError BootstrapEntryWitness := do
  let topology ← (checkAuthoritative tags root tables executingApicId).mapError .topology
  let bootstrap ← (bindBootstrap topology observation).mapError .bootstrap
  pure ⟨topology, bootstrap⟩

theorem bootstrap_preserves_observation (topology : Witness)
    (observation : BootstrapObservation) (witness : BootstrapWitness topology)
    (accepted : bindBootstrap topology observation = .ok witness) :
    witness.observed = observation := by
  unfold bindBootstrap at accepted
  split at accepted
  · cases accepted; rfl
  · split at accepted <;> try simp_all
    split at accepted <;> try simp_all
    split at accepted <;> try simp_all
    split at accepted <;> try simp_all

theorem bootstrap_binds_executing_id (topology : Witness)
    (witness : BootstrapWitness topology) : witness.observed.executingId = 0 := by
  rw [witness.valid.2.2.1, topology.matchesBaseline]
  rfl

theorem bootstrap_requires_msr_and_apic (topology : Witness)
    (witness : BootstrapWitness topology) :
    witness.observed.readAvailable = true ∧ witness.observed.cpuidEdx &&& 0x220 = 0x220 :=
  ⟨witness.valid.1, witness.valid.2.1⟩

theorem bootstrap_requires_architectural_bsp (topology : Witness)
    (witness : BootstrapWitness topology) : witness.observed.apicBase &&& 0x100 = 0x100 := by
  rw [witness.valid.2.2.2]
  decide

theorem bootstrap_acceptance_iff_valid (topology : Witness)
    (observation : BootstrapObservation) :
    (∃ witness, bindBootstrap topology observation = .ok witness) ↔
      BootstrapValid topology observation := by
  constructor
  · rintro ⟨witness, accepted⟩
    have same := bootstrap_preserves_observation topology observation witness accepted
    rw [← same]
    exact witness.valid
  · intro valid
    exact ⟨⟨observation, valid⟩, by simp [bindBootstrap, valid]⟩

theorem bootstrap_entry_remains_multicore (entry : BootstrapEntryWitness) :
    BootTopology.admit entry.topology.observed = .rejected .multipleEnabledProcessors :=
  witness_still_rejected_by_single_core entry.topology

end LeanOS.QotomBspTopology
