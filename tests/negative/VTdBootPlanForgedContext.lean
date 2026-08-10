import LeanOS.VTdBootPlan

open LeanOS.VTdBootPlan

/- An accepted VT-d plan is an opaque proof-carrying value outside its defining
module.  A live-unit consumer must not be able to substitute a present context
entry and reconstruct a plan whose deny-all proofs still describe the empty
projection. -/
def forgePresentContext (plan : Plan) : Plan :=
  { plan with
    contexts := { present := true, domain := 1, addressWidth := 1,
                  secondLevelFrame := 4 } :: plan.contexts.tail }
