import LeanOS.FaultDispatch

open LeanOS
open LeanOS.FaultDispatch

/- An architectural RSVD indication is an integrity failure, never ordinary
subject cleanup. -/
example :
    pageFaultAgreementWitnessContained
      (pageFaultAgreementWitnessRecord 12 50) = true := by
  native_decide
