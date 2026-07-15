import LeanOS.SecurityClaims

open LeanOS

/- The non-vacuity witness must include a genuinely accepted transition. -/
example :
    KernelTransition.WellFormed KernelTransition.initialState ∧
      (KernelTransition.transition KernelTransition.initialState .unsupported).result = .accepted := by
  exact SecurityClaims.initial_transition_witness
