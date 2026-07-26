import LeanOS.InterruptEntry

open LeanOS InterruptEntry

-- The IST-switch frame structurally requires the saved RIP word.
private def missingRip : RawNmiFrame :=
  { cs := 0x23
    flags := 0x202
    rsp := 0x500ff8
    ss := 0x1b
    canonicalRip := true
    canonicalRsp := true }
