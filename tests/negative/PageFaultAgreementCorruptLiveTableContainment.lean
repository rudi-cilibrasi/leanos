import LeanOS.FaultDispatch

open LeanOS
open LeanOS.FaultDispatch

/- This must not type-check: a reserved-bit violation decoded from the live
CR3-bound report is an integrity failure, never ordinary subject cleanup. -/
example : pageFaultReservedLiveTableContained = true := by
  native_decide
