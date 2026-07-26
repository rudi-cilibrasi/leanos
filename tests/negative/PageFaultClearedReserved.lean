import LeanOS.InterruptEntry

open LeanOS InterruptEntry

/-- Clearing the architectural RSVD indication would admit a corrupt walk. -/
example : (decodePageFaultError 12).isOk = true := by
  native_decide
