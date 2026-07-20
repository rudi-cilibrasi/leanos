import LeanOS.InterruptEntry

open LeanOS InterruptEntry

-- The IST-switch frame structurally requires the saved RFLAGS word.
private def missingFlags : RawNmiFrame :=
  { rip := 0x400100
    cs := 0x23
    rsp := 0x500ff8
    ss := 0x1b
    canonicalRip := true
    canonicalRsp := true }
