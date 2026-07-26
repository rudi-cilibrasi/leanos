import LeanOS.InterruptEntry

open LeanOS InterruptEntry

/-- An impossible noncanonical saved instruction pointer cannot decode. -/
example :
    validCanonicalPageFault
      { canonicalPageFaultExample with rip := 0x0000800000000000 } = true := by
  native_decide
