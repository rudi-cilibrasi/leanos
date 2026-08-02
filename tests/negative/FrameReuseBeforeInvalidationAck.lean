import LeanOS.FrameBudgetScenario

open LeanOS

/- A pending retirement cannot publish the fresh mapping before its exact
invalidation acknowledgement. This deliberately false fixture protects the
release/acknowledgement/scrub/republication ordering claim. -/
example :
    (FrameBudgetScenario.publishFreshAfterRetirement
      FrameBudgetScenario.retirementPrepared).accepted = true := by
  native_decide
