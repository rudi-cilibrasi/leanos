import LeanOS.FailStop

open LeanOS

namespace LeanOS.FailStop

-- The old wrapper merely assumed the preservation conclusion.  It must not
-- satisfy the independently typed operation-compatibility premise.
def TautologicalAuthoritativeContract (state : CompositeState)
    (operation : AuthoritativeOperation) : Prop :=
  AuthoritativeRuntimeWellFormed state →
    AuthoritativeRuntimeWellFormed (authoritativeGate state operation).state

example state operation
    (htautology : TautologicalAuthoritativeContract state operation) :
    AuthoritativeOperationCompatible state operation := by
  exact htautology

end LeanOS.FailStop
