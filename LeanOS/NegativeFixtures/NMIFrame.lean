import LeanOS.InterruptEntry

open LeanOS InterruptEntry

namespace LeanOS.NegativeFixtures.NMIFrame

-- The IST-switch frame structurally requires the saved RIP word.
/--
error: Fields missing: `rip`

Hint: Add missing fields:
  
  ̲ ̲ ̲ ̲ ̲r̲i̲p̲ ̲:̲=̲ ̲_̲
-/
#guard_msgs in
private def missingRip : RawNmiFrame :=
  { cs := 0x23
    flags := 0x202
    rsp := 0x500ff8
    ss := 0x1b
    canonicalRip := true
    canonicalRsp := true }

end LeanOS.NegativeFixtures.NMIFrame
