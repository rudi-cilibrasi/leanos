import LeanOS.InterruptEntry

open LeanOS InterruptEntry

-- An IST-switch frame structurally requires the saved RSP word.
private def missingRsp : RawNmiFrame :=
  { rip := 0x400100
    cs := 0x23
    flags := 0x202
    ss := 0x1b
    canonicalRip := true
    canonicalRsp := true }
