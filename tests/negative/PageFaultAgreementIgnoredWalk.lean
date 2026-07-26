import LeanOS.FaultDispatch

open LeanOS
open LeanOS.FaultDispatch

/- Ignoring the active plan/live-mapping disagreement would misclassify this
planned user-text page as an ordinary non-present subject denial. -/
example :
    pageFaultAgreementWitnessContained
      (pageFaultAgreementWitnessRecord 4 100) = true := by
  native_decide
