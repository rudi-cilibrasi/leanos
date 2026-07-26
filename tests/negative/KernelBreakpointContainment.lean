import LeanOS.InterruptEntry

open LeanOS InterruptEntry

private def kernelBreakpoint : RawEntry :=
  { boundVector := 3
    boundStub := 3
    errorCode := none
    restartClass := .followingBoundary
    frame := .samePrivilege 0x100000 0x08 0x202
    frameBytes := 24
    frameAddress := 0x800000
    acCleared := true
    dfCleared := true }

private def kernelContext : KernelContext :=
  { currentSubject := 1
    activeAddressSpace := 1
    activeCr3 := 0
    stackIdentity := 1
    stackFirst := 0x800000
    stackPastLast := 0x804000
    entryActive := false }

-- A same-privilege breakpoint must never normalize to an accepted containment
-- record; the user-only origin policy makes it a terminal rejection.
example : normalize kernelBreakpoint kernelContext =
    .accepted (makeNormalized breakpointEntry kernelBreakpoint kernelContext) := by
  native_decide
