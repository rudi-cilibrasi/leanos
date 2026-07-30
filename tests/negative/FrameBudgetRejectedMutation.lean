import LeanOS.FrameBudgetScenario

open LeanOS

/- A budget-exhausted retry cannot both reject and mutate the authoritative
state. This deliberately false fixture protects the rejection-atomicity proof
from being weakened into a result-only claim. -/
example :
    let before := FrameBudgetScenario.materialize .aAllocated
    (FrameBudget.allocate before.budget before.currentSubject 11 1).result =
        .rejected .budgetExhausted ∧
      FrameBudget.usage
          (FrameBudget.allocate before.budget before.currentSubject 11 1).state 0 ≠
        FrameBudget.usage before.budget 0 := by
  native_decide
