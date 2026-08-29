import LeanOS.InterruptEntry

open LeanOS InterruptEntry

namespace LeanOS.NegativeFixtures.PageFaultProvenance

/- A saved user selector outside the reviewed codec profile is rejected. -/
/- error: cs := 7, flags := -/
#guard_msgs (substring := true) in
example :
    validCanonicalPageFault { canonicalPageFaultExample with cs := 7 } = true := by
  native_decide

/- A noncanonical saved instruction pointer is rejected. -/
/- error: rip := 140737488355328, cs := -/
#guard_msgs (substring := true) in
example :
    validCanonicalPageFault
      { canonicalPageFaultExample with rip := 0x0000800000000000 } = true := by
  native_decide

/- The inbound record cannot erase its kernel entry-stack identity. -/
/- error: stackIdentity := 0, reserved := -/
#guard_msgs (substring := true) in
example :
    validCanonicalPageFault
      { canonicalPageFaultExample with stackIdentity := 0 } = true := by
  native_decide

end LeanOS.NegativeFixtures.PageFaultProvenance
