import LeanOS.FaultDispatch

open LeanOS
open LeanOS.FaultDispatch

/- A protection-class error cannot authorize containment when the active walk
predicts a non-present denial. -/
example :
    pageFaultAgreementWitnessContained
      (pageFaultAgreementWitnessRecord 5 50) = true := by
  native_decide
