import LeanOS.InterruptEntry

open LeanOS InterruptEntry

namespace LeanOS.NegativeFixtures.PageFaultError

/- A codec/authorizer that drops CR2 would equate distinct canonical pages. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  pageFaultDemo 4 4194595 0 268435713 123 = pageFaultDemo 4 4198691 0 268435713 123
is false
-/
#guard_msgs in
example :
    pageFaultDemo 4 0x400123 0 0x10000101 123 =
      pageFaultDemo 4 0x401123 0 0x10000101 123 := by
  native_decide

/- W/R and I/D are architectural inputs, not ignorable labels. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  pageFaultDemo 4 4194595 0 268435713 123 = pageFaultDemo 6 4194595 0 268435713 123 ∧
    pageFaultDemo 4 4194595 0 268435713 123 = pageFaultDemo 20 4194595 0 268435713 123
is false
-/
#guard_msgs in
example :
    pageFaultDemo 4 0x400123 0 0x10000101 123 =
      pageFaultDemo 6 0x400123 0 0x10000101 123 ∧
    pageFaultDemo 4 0x400123 0 0x10000101 123 =
      pageFaultDemo 20 0x400123 0 0x10000101 123 := by
  native_decide

/- Clearing the architectural RSVD indication would admit a corrupt walk. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  (decodePageFaultError 12).isOk = true
is false
-/
#guard_msgs in
example : (decodePageFaultError 12).isOk = true := by
  native_decide

/- The selected profile cannot silently truncate PK (bit five). -/
/--
error: Tactic `native_decide` evaluated that the proposition
  (decodePageFaultError 36).isOk = true
is false
-/
#guard_msgs in
example : (decodePageFaultError 36).isOk = true := by
  native_decide

end LeanOS.NegativeFixtures.PageFaultError
