import LeanOS.BootPageTablePlan
import LeanOS.VTdBootPlan

namespace LeanOS.NegativeFixtures.BootPlans

namespace PageTables

open LeanOS.BootPageTablePlan

/- The accepted plan is an opaque proof-carrying value outside its defining
module. A live-table consumer must not be able to substitute ancestor fields
and reconstruct a plan whose proofs describe a different compiled layout. -/
/--
error: invalid {...} notation, constructor for `Plan` is marked as private
-/
#guard_msgs in
def substituteCompiledLayout (plan : Plan) : Plan :=
  { plan with
    compiledAncestors :=
      { plan.compiledAncestors with
        subjectA :=
          { plan.compiledAncestors.subjectA with
            pdpt := plan.compiledAncestors.subjectA.pd } }
    liveTableFrames := layoutFrames plan.roots
      { plan.compiledAncestors with
        subjectA :=
          { plan.compiledAncestors.subjectA with
            pdpt := plan.compiledAncestors.subjectA.pd } } }

end PageTables

namespace VTd

open LeanOS.VTdBootPlan

/- An accepted VT-d plan is an opaque proof-carrying value outside its defining
module. A live-unit consumer must not be able to substitute a present context
entry and reconstruct a plan whose deny-all proofs describe the empty
projection. -/
/--
error: invalid {...} notation, constructor for `Plan` is marked as private
-/
#guard_msgs in
def forgePresentContext (plan : Plan) : Plan :=
  { plan with
    contexts := { present := true, domain := 1, addressWidth := 1,
                  secondLevelFrame := 4 } :: plan.contexts.tail }

end VTd

end LeanOS.NegativeFixtures.BootPlans
