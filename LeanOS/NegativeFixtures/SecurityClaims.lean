import LeanOS.SecurityClaims

open LeanOS

namespace LeanOS.NegativeFixtures.SecurityClaims

-- The non-vacuity witness must include a genuinely accepted transition.
/--
error: Type mismatch
  SecurityClaims.initial_transition_witness
has type
  KernelTransition.WellFormed KernelTransition.initialState ∧
    (KernelTransition.transition KernelTransition.initialState KernelTransition.Command.initialize).result =
      KernelTransition.Result.accepted
but is expected to have type
  KernelTransition.WellFormed KernelTransition.initialState ∧
    (KernelTransition.transition KernelTransition.initialState KernelTransition.Command.unsupported).result =
      KernelTransition.Result.accepted
-/
#guard_msgs in
example :
    KernelTransition.WellFormed KernelTransition.initialState ∧
      (KernelTransition.transition KernelTransition.initialState .unsupported).result = .accepted := by
  exact SecurityClaims.initial_transition_witness

end LeanOS.NegativeFixtures.SecurityClaims
