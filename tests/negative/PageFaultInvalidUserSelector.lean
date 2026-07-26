import LeanOS.InterruptEntry

open LeanOS InterruptEntry

/-- A saved user selector outside the reviewed codec profile cannot decode. -/
example :
    validCanonicalPageFault { canonicalPageFaultExample with cs := 7 } = true := by
  native_decide
