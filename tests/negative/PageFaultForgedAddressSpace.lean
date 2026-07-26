import LeanOS.InterruptEntry

open LeanOS InterruptEntry

/-- Serialized address-space identity cannot replace trusted containment state. -/
example :
    (authorizeCanonicalPageFault
      (encodeCanonicalPageFault
        { canonicalPageFaultExample with activeAddressSpace := 2 })
      canonicalPageFaultExampleContext ()).authorized =
        some { canonicalPageFaultExample with activeAddressSpace := 2 } := by
  native_decide
