import LeanOS.BootPageTablePlan

open LeanOS.BootPageTablePlan

/- The accepted plan is an opaque proof-carrying value outside its defining
module.  A live-table consumer must not be able to substitute ancestor fields
and reconstruct a plan whose proofs describe a different compiled layout. -/
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
