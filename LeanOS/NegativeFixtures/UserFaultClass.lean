import LeanOS.FaultDispatch

open LeanOS FaultDispatch InterruptEntry

namespace LeanOS.NegativeFixtures.UserFaultClass

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

/- An untrusted frame cannot relabel one contained fault reason as another. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  validUserFaultFor ContainedReason.breakpoint divideFrame = true
is false
-/
#guard_msgs in
example : validUserFaultFor .breakpoint divideFrame = true := by
  native_decide

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

/- Same-privilege breakpoints cannot become accepted containment records. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  normalize kernelBreakpoint kernelContext =
    Result.accepted (makeNormalized breakpointEntry kernelBreakpoint kernelContext)
is false
-/
#guard_msgs in
example : normalize kernelBreakpoint kernelContext =
    .accepted (makeNormalized breakpointEntry kernelBreakpoint kernelContext) := by
  native_decide

private def softwareDivideManifest : List ManifestEntry :=
  manifest.map (fun entry => if entry.vector = 0 then { entry with dpl := 3 } else entry)

/- Vector zero must not become a CPL3 software-callable gate. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  validateManifest softwareDivideManifest = true
is false
-/
#guard_msgs in
example : validateManifest softwareDivideManifest = true := by
  native_decide

private def alternateBreakpointManifest : List ManifestEntry :=
  manifest.map (fun entry => if entry.vector = 3 then { entry with dpl := 0 } else entry)

/- The reviewed breakpoint descriptor cannot be replaced by an alternate DPL. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  validateManifest alternateBreakpointManifest = true
is false
-/
#guard_msgs in
example : validateManifest alternateBreakpointManifest = true := by
  native_decide

end LeanOS.NegativeFixtures.UserFaultClass
