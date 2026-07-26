import LeanOS.FailStop

open LeanOS

namespace LeanOS.FailStop

-- The folded authoritative invariant alone does not yet discharge the
-- operation-local dormant-cancellation compatibility obligation.  This
-- fixture must keep failing until every public constructor has a derived law.
example state operation
    (hstate : AuthoritativeRuntimeWellFormed state) :
    AuthoritativeRuntimeWellFormed
      (authoritativeGate state operation).state := by
  exact authoritativeGate_preserves_authoritativeRuntimeWellFormed
    state operation hstate

end LeanOS.FailStop
