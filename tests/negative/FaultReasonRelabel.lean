import LeanOS.FaultDispatch

open LeanOS FaultDispatch InterruptEntry

private def divideFrame : NormalizedFrame :=
  { vector := 0
    purpose := .userFault
    origin := .user
    errorCode := none
    rip := 0x400100
    cs := 0x23
    flags := 0x202
    userRsp := some 0x500ff8
    userSs := some 0x1b
    currentSubject := 1
    activeAddressSpace := 1
    activeCr3 := 0
    stackIdentity := 1 }

-- A divide-error frame must never satisfy the breakpoint class gate: no
-- untrusted word may relabel one contained reason as another.
example : validUserFaultFor .breakpoint divideFrame = true := by
  native_decide
