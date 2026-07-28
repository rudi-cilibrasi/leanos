import LeanOS.FailStop

open LeanOS

namespace LeanOS.FailStop

-- The weaker legacy runtime invariant cannot establish the folded
-- authoritative preservation contract because it omits deferred-cancellation
-- and blocking-context classification.
example state operation
    (hstate : RuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeGate state operation).state := by
  have hstrong : AuthoritativeRuntimeWellFormed state := hstate
  exact authoritativeGate_preserves_authoritativeRuntimeWellFormed
    state operation hstrong

end LeanOS.FailStop
