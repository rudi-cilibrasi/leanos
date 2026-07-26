import LeanOS.InterruptEntry

open LeanOS InterruptEntry

-- Dropping the post-halt return suffix must be detected as an incomplete trace inventory.
example : nmiTraceInventory.dropLast = nmiTraceInventory := by
  native_decide
