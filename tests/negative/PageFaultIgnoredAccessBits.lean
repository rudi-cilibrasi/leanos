import LeanOS.InterruptEntry

open LeanOS InterruptEntry

/-- W/R and I/D are architectural inputs, not ignorable labels. -/
example :
    pageFaultDemo 4 0x400123 0 0x10000101 123 =
      pageFaultDemo 6 0x400123 0 0x10000101 123 ∧
    pageFaultDemo 4 0x400123 0 0x10000101 123 =
      pageFaultDemo 20 0x400123 0 0x10000101 123 := by
  native_decide
