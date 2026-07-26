import LeanOS.InterruptEntry

open LeanOS InterruptEntry

-- An IST-switch frame structurally requires the saved SS word.
private def missingSs : RawNmiFrame :=
  { rip := 0x400100
    cs := 0x23
    flags := 0x202
    rsp := 0x500ff8
    canonicalRip := true
    canonicalRsp := true }
