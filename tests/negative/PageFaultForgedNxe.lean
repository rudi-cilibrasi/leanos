import LeanOS.InterruptEntry

open LeanOS InterruptEntry

/-- Serialized NXE cannot authorize against an independently trusted NXE=true. -/
example :
    (authorizeCanonicalPageFault
      (encodeCanonicalPageFault
        { canonicalPageFaultExample with controlsCode := 13 })
      canonicalPageFaultExampleContext ()).authorized =
        some { canonicalPageFaultExample with controlsCode := 13 } := by
  native_decide
