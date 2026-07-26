import LeanOS.InterruptEntry

open LeanOS InterruptEntry

/-- The selected profile cannot silently truncate PK (bit five). -/
example : (decodePageFaultError 36).isOk = true := by
  native_decide
