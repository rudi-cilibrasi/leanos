import LeanOS.InterruptEntry

open LeanOS InterruptEntry

/-- The canonical inbound record cannot erase its kernel entry-stack identity. -/
example :
    validCanonicalPageFault
      { canonicalPageFaultExample with stackIdentity := 0 } = true := by
  native_decide
