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

structure Processor where
  apicId : UInt32
  enabled : Bool
  deriving DecidableEq, Repr

structure Snapshot where
  version : UInt64
  bspId : UInt32
  executingId : UInt32
  processors : List Processor
  deriving DecidableEq, Repr

inductive Error where
  | unsupportedVersion
  | tooManyProcessors
  | duplicateApicId
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
  if snapshot.version != snapshotVersion then
    .rejected .unsupportedVersion
  else if snapshot.processors.length > maxProcessors then
    .rejected .tooManyProcessors
  else if !uniqueApicIds snapshot.processors then
    .rejected .duplicateApicId
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
  split at haccepted <;> simp_all [Bool.and_eq_true]
  split at haccepted <;> simp_all
  split at haccepted <;> simp_all
  split at haccepted <;> simp_all
  split at haccepted <;> simp_all

def repositorySingleCore : Snapshot :=
  { version := snapshotVersion
    bspId := 0
    executingId := 0
    processors := [{ apicId := 0, enabled := true }] }

theorem repository_single_core_nonvacuous :
    admit repositorySingleCore = .accepted { apicId := 0, enabled := true } := by
  decide

def twoEnabledProcessors : Snapshot :=
  { version := snapshotVersion
    bspId := 0
    executingId := 0
    processors := [
      { apicId := 0, enabled := true },
      { apicId := 1, enabled := true }
    ] }

theorem two_enabled_processors_rejected :
    admit twoEnabledProcessors = .rejected .multipleEnabledProcessors := by
  decide

def duplicateBsp : Snapshot :=
  { version := snapshotVersion
    bspId := 0
    executingId := 0
    processors := [
      { apicId := 0, enabled := true },
      { apicId := 0, enabled := false }
    ] }

theorem duplicate_bsp_rejected :
    admit duplicateBsp = .rejected .duplicateApicId := by
  decide

def unsupportedSnapshotVersion : Snapshot :=
  { repositorySingleCore with version := 0 }

theorem unsupported_snapshot_version_rejected :
    admit unsupportedSnapshotVersion = .rejected .unsupportedVersion := by
  decide

def zeroEnabledProcessors : Snapshot :=
  { version := snapshotVersion
    bspId := 0
    executingId := 0
    processors := [{ apicId := 0, enabled := false }] }

theorem zero_enabled_processors_rejected :
    admit zeroEnabledProcessors = .rejected .noEnabledProcessor := by
  decide

def mismatchedExecutingProcessor : Snapshot :=
  { repositorySingleCore with executingId := 1 }

theorem mismatched_executing_processor_rejected :
    admit mismatchedExecutingProcessor = .rejected .bspMismatch := by
  decide

end LeanOS.BootTopology
