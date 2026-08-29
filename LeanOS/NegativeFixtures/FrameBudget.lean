import LeanOS.FrameBudgetScenario

open LeanOS

namespace LeanOS.NegativeFixtures.FrameBudget

/- A budget-exhausted retry cannot both reject and mutate authoritative state. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  let before := FrameBudgetScenario.materialize FrameBudgetScenario.StateId.aAllocated;
  (FrameBudget.allocate before.budget before.currentSubject 11 1).result =
      FrameBudget.Result.rejected FrameBudget.AllocationError.budgetExhausted ∧
    FrameBudget.usage (FrameBudget.allocate before.budget before.currentSubject 11 1).state 0 ≠
      FrameBudget.usage before.budget 0
is false
-/
#guard_msgs in
example :
    let before := FrameBudgetScenario.materialize .aAllocated
    (FrameBudget.allocate before.budget before.currentSubject 11 1).result =
        .rejected .budgetExhausted ∧
      FrameBudget.usage
          (FrameBudget.allocate before.budget before.currentSubject 11 1).state 0 ≠
        FrameBudget.usage before.budget 0 := by
  native_decide

/- A pending retirement cannot publish before its invalidation acknowledgement. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  (FrameBudgetScenario.publishFreshAfterRetirement FrameBudgetScenario.retirementPrepared).accepted = true
is false
-/
#guard_msgs in
example :
    (FrameBudgetScenario.publishFreshAfterRetirement
      FrameBudgetScenario.retirementPrepared).accepted = true := by
  native_decide

end LeanOS.NegativeFixtures.FrameBudget
