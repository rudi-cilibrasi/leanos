import LeanOS.CompositeUnwinding

open LeanOS LeanOS.FailStop LeanOS.CompositeObservation LeanOS.CompositeUnwinding

/- The global capability-identity counter breaks step consistency.  The
observer's delegation into its own row draws the new capability's identity
from the global counter, so it is not in `ownStepConsistent`, and the step
consistency theorem cannot be instantiated for it.
`Channels.identity_counter_step_inconsistent` proves the claim would be
false. -/
example (plan : BootPageTablePlan.Plan) :
    LowEquiv 2
      (authoritativeGate (Channels.seed plan) (.ordinary Channels.delegateToSelf)).state
      (authoritativeGate (Channels.shifted plan) (.ordinary Channels.delegateToSelf)).state :=
  own_step_consistent (Channels.seed_ownStep_shifted plan) Channels.delegateToSelf rfl
