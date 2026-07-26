import LeanOS.FaultDispatch

open LeanOS
open LeanOS.FaultDispatch

/- A mapped object whose monotonic issuance bit is clear is stale generation
state and cannot authorize ordinary subject containment. -/
example : pageFaultAgreementUnissuedObjectContained = true := by
  native_decide
