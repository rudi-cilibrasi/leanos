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

-- The IST-switch frame structurally requires the saved CS word.
/--
error: Fields missing: `cs`

Hint: Add missing fields:
  
  ̲ ̲ ̲ ̲ ̲c̲s̲ ̲:̲=̲ ̲_̲
-/
#guard_msgs in
private def missingCs : RawNmiFrame :=
  { rip := 0x400100
    flags := 0x202
    rsp := 0x500ff8
    ss := 0x1b
    canonicalRip := true
    canonicalRsp := true }

-- The IST-switch frame structurally requires the saved RFLAGS word.
/--
error: Fields missing: `flags`

Hint: Add missing fields:
  
  ̲ ̲ ̲ ̲ ̲f̲l̲a̲g̲s̲ ̲:̲=̲ ̲_̲
-/
#guard_msgs in
private def missingFlags : RawNmiFrame :=
  { rip := 0x400100
    cs := 0x23
    rsp := 0x500ff8
    ss := 0x1b
    canonicalRip := true
    canonicalRsp := true }

-- An IST-switch frame structurally requires the saved RSP word.
/--
error: Fields missing: `rsp`

Hint: Add missing fields:
  
  ̲ ̲ ̲ ̲ ̲r̲s̲p̲ ̲:̲=̲ ̲_̲
-/
#guard_msgs in
private def missingRsp : RawNmiFrame :=
  { rip := 0x400100
    cs := 0x23
    flags := 0x202
    ss := 0x1b
    canonicalRip := true
    canonicalRsp := true }

-- An IST-switch frame structurally requires the saved SS word.
/--
error: Fields missing: `ss`

Hint: Add missing fields:
  
  ̲ ̲ ̲ ̲ ̲s̲s̲ ̲:̲=̲ ̲_̲
-/
#guard_msgs in
private def missingSs : RawNmiFrame :=
  { rip := 0x400100
    cs := 0x23
    flags := 0x202
    rsp := 0x500ff8
    canonicalRip := true
    canonicalRsp := true }

end LeanOS.NegativeFixtures.NMIFrame
