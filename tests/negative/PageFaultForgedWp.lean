import LeanOS.InterruptEntry

open LeanOS InterruptEntry

/-- Serialized WP cannot authorize against an independently trusted WP=true. -/
example :
    (authorizeCanonicalPageFault
      (encodeCanonicalPageFault
        { canonicalPageFaultExample with controlsCode := 14 })
      canonicalPageFaultExampleContext ()).authorized =
        some { canonicalPageFaultExample with controlsCode := 14 } := by
  native_decide
