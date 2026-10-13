import LeanOS.Oracle.Composite

/-!
# Oracle corpus: frame budget

Issue 112's canonical frame-budget sequence and its hostile encodings, on the
stateful composite dispatcher.
-/
namespace LeanOS.Oracle

open LeanOS
set_option maxRecDepth 4096

/-- Issue-112's canonical budget sequence and hostile encodings use the same
stateful export as the mixed composite trace. -/
def budgetVectors : List Vector := [
  composite "frame-budget.a-allocate" 0x4001 0x4001 10 0 0 0,
  composite "frame-budget.a-at-limit" 0x4101 0x4101 11 1 0 0,
  composite "frame-budget.select-b" 0x4201 0x4201 0 0 0 0,
  composite "frame-budget.b-peer-allocate" 0x4301 0x4301 20 0 0 0,
  composite "frame-budget.terminate-a" 0x4401 0x4401 0 0 0 0,
  composite "frame-budget.b-fresh-publication" 0x4501 0x4501 21 1 0 0,
  composite "frame-budget.stale-a-handle-denied" 0x4601 0x4601 0x10000 0 0 0,
  composite "frame-budget.complete" 0x4701 0x4701 0 0 0 0,
  composite "frame-budget.release-a" 0x4101 0x4801 0 0 0 0,
  composite "frame-budget.repeated-release" 0x4901 0x4901 0 0 0 0,
  composite "frame-budget.release-complete" 0x4a01 0x4a01 0 0 0 0,
  composite "frame-budget.repeated-a-retry" 0x4201 0x4101 11 1 0 0,
  composite "frame-budget.occupied-slot" 0x4101 0x4001 10 0 0 0,
  composite "frame-budget.repeated-termination" 0x4501 0x4401 0 0 0 0,
  composite "frame-budget.aggregate-global-inconsistency" 0x4c01 0x4301 20 0 0 0,
  composite "frame-budget.malformed-budget-state" 0x4002 0x4001 10 0 0 0,
  composite "frame-budget.caller-context-forgery" 0x4201 0x4201 1 2 0 0,
  composite "frame-budget.user-selects-charge-owner" 0x4001 0x4001 10 0 1 0,
  composite "frame-budget.stale-generation" 0x4601 0x4601 0x20000 0 0 0,
  composite "frame-budget.output-state-replay" 0x4101 0x4301 20 0 0 0,
  composite "frame-budget.cross-trace-splice" 0x1001 0x4501 21 1 0 0,
  composite "frame-budget.unknown-operation" 0x4001 0x3f01 0 0 0 0,
  composite "frame-budget.reserved-command" 0x4001 0x5001 0 0 0 0,
  composite "frame-budget.maximum-words" 0xffffffffffffffff 0xffffffffffffffff
    0xffffffffffffffff 0xffffffffffffffff 0xffffffffffffffff 0xffffffffffffffff]

/-- A malformed budget-state ABI version is rejected before range routing, so
the differential corpus cannot silently bless a continuity misclassification. -/
theorem malformed_budget_state_is_wrong_version :
    (budgetVectors[15]).id = "frame-budget.malformed-budget-state" ∧
    (budgetVectors[15]).expected = 0xff01 := by
  native_decide

theorem hosted_budget_canonical_sequence :
    FrameBudgetScenario.run .initial FrameBudgetScenario.canonicalCommands =
      some .complete :=
  FrameBudgetScenario.canonical_sequence_complete

end LeanOS.Oracle
