import LeanOS.InterruptEntry

open LeanOS InterruptEntry

/-- A codec/authorizer that drops CR2 would equate distinct canonical pages. -/
example :
    pageFaultDemo 4 0x400123 0 0x10000101 123 =
      pageFaultDemo 4 0x401123 0 0x10000101 123 := by
  native_decide
