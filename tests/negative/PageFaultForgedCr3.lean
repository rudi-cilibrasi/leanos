import LeanOS.InterruptEntry

open LeanOS InterruptEntry

/-- Serialized CR3 cannot replace the independently trusted active root. -/
example :
    (authorizeCanonicalPageFault
      (encodeCanonicalPageFault
        { canonicalPageFaultExample with activeCr3 := 0x2000 })
      canonicalPageFaultExampleContext ()).authorized =
        some { canonicalPageFaultExample with activeCr3 := 0x2000 } := by
  native_decide
