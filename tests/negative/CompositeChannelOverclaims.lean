import LeanOS.CompositeSwitchedChannels

open LeanOS LeanOS.FailStop LeanOS.CompositeObservation LeanOS.CompositeUnwinding
open LeanOS.CompositeOwnSteps LeanOS.CompositeChannels

/- The channel theorems of `LeanOS.CompositeChannels` and
`LeanOS.CompositeSwitchedChannels` justify each exclusion
from the extended consistency families.  Every example below overclaims one of
them and must fail to type-check. -/

/- Terminating another subject reveals whether it was issued, so it is not in
`ownOutputConsistentCounter`; `terminate_output_inconsistent` proves the claim
would be false. -/
example (plan : BootPageTablePlan.Plan) :
    (authoritativeGate (seed plan) (.ordinary (.terminateSubject 3))).result =
      (authoritativeGate (created plan) (.ordinary (.terminateSubject 3))).result :=
  own_output_consistent_counter (seed_created plan) (.terminateSubject 3) rfl

/- Terminating another subject cancels the observer's pending offers, so it is
not in `ownStepConsistentCounter`; `terminate_step_inconsistent` proves the
claim would be false. -/
example (plan : BootPageTablePlan.Plan) :
    LowEquiv 2 (authoritativeGate (offered plan) (.ordinary (.terminateSubject 3))).state
      (authoritativeGate (offeredCreated plan) (.ordinary (.terminateSubject 3))).state :=
  own_step_consistent_counter (offered_offeredCreated plan) (.terminateSubject 3) rfl

/- The identity counter is a public input: states that differ in it do not
satisfy `OwnStepCounter`, and `offer_counter_step_inconsistent` shows the
offer would otherwise be step inconsistent. -/
example (plan : BootPageTablePlan.Plan) :
    OwnStepCounter 2 (seed plan) (Channels.shifted plan) :=
  { toOwnStep := Channels.seed_ownStep_shifted plan, counter := rfl }

/- Subtree revocation of the observer's own slot depends on a derivation it
cannot see, so it is not in `ownStepConsistentCounter`;
`CompositeSwitchedChannels.revokeSubtree_own_step_inconsistent` proves the
claim would be false. -/
example (plan : BootPageTablePlan.Plan)
    (hplan : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan) :
    LowEquiv 2
      (authoritativeGate (CompositeSwitchedChannels.runFrom plan
        CompositeSwitchedChannels.leftTrace)
        (.ordinary CompositeSwitchedChannels.ownSubtree)).state
      (authoritativeGate (CompositeSwitchedChannels.runFrom plan
        CompositeSwitchedChannels.rightTrace)
        (.ordinary CompositeSwitchedChannels.ownSubtree)).state :=
  own_step_consistent_counter (CompositeSwitchedChannels.derivation_pair plan hplan)
    CompositeSwitchedChannels.ownSubtree rfl

/- The observer's timer switch replies with the next subject's registers, so
it is not in `ownOutputConsistentCounter`;
`CompositeSwitchedChannels.resumePreempt_output_inconsistent` proves the claim
would be false. -/
example (plan : BootPageTablePlan.Plan)
    (hplan : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan) :
    (authoritativeGate (CompositeSwitchedChannels.runFrom plan
        CompositeSwitchedChannels.preemptLeftTrace)
        (.ordinary CompositeSwitchedChannels.preempt)).result =
      (authoritativeGate (CompositeSwitchedChannels.runFrom plan
        CompositeSwitchedChannels.preemptRightTrace)
        (.ordinary CompositeSwitchedChannels.preempt)).result :=
  own_output_consistent_counter
    (CompositeSwitchedChannels.resumePreempt_output_inconsistent plan hplan).1
    CompositeSwitchedChannels.preempt rfl
