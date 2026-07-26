import LeanOS.InterruptEntry

open LeanOS InterruptEntry

/-- Serialized SMAP cannot authorize against trusted SMAP=true. -/
example :
    (authorizeCanonicalPageFault
      (encodeCanonicalPageFault
        { canonicalPageFaultExample with controlsCode := 7 })
      canonicalPageFaultExampleContext ()).authorized =
        some { canonicalPageFaultExample with controlsCode := 7 } := by
  native_decide
