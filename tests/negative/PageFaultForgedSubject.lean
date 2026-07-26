import LeanOS.InterruptEntry

open LeanOS InterruptEntry

/-- Serialized subject identity cannot replace the trusted current subject. -/
example :
    (authorizeCanonicalPageFault
      (encodeCanonicalPageFault
        { canonicalPageFaultExample with currentSubject := 2 })
      canonicalPageFaultExampleContext ()).authorized =
        some { canonicalPageFaultExample with currentSubject := 2 } := by
  native_decide
