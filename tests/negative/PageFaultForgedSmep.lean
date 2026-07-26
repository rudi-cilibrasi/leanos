import LeanOS.InterruptEntry

open LeanOS InterruptEntry

/-- Serialized SMEP cannot authorize against trusted SMEP=true. -/
example :
    (authorizeCanonicalPageFault
      (encodeCanonicalPageFault
        { canonicalPageFaultExample with controlsCode := 11 })
      canonicalPageFaultExampleContext ()).authorized =
        some { canonicalPageFaultExample with controlsCode := 11 } := by
  native_decide
