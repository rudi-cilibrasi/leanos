import LeanOS.FaultDispatch

open LeanOS
open LeanOS.FaultDispatch

/- A page absent from both the boot plan and virtual mapping cannot authorize
containment while the parallel lifecycle still maps it to a stale object. -/
example : pageFaultAgreementStaleLifecycleContained = true := by
  native_decide
