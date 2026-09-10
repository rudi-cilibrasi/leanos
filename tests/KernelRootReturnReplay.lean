import LeanOS.KernelRootReturn

open LeanOS LeanOS.Interrupt LeanOS.KernelRootReturn LeanOS.X86PageTable

private def request : UserReturnRequest :=
  { hardware :=
      { vector := 0, errorCode := 0, savedPrivilege := .user,
        instructionPointer := 0x400000, stackPointer := 0x501000,
        codeSelector := 0x23, stackSelector := 0x1b, flags := 0x202,
        canonicalInstructionPointer := true, canonicalStackPointer := true,
        flagsAllowed := true }
    purpose := .schedulerRestore
    frameSubject := 1, frameAddressSpace := 11, frameCr3 := 0x1000
    expectedSubject := 1, expectedAddressSpace := 11, expectedCr3 := 0x1000
    executionMode := .running
    lifecycle :=
      { capabilities :=
          { subjects := fun s => s = 1, objects := fun _ => false,
            kinds := fun _ => none, slots := fun _ _ => none }
        issuedSubjects := fun s => s = 1, ownedMemory := fun _ => none
        addressOwner := fun s => if s = 11 then some 1 else none
        mapping := fun _ _ => none, endpointOwner := fun _ => none
        mailbox := fun _ => none, frameOwner := fun _ => none
        freeFrame := fun _ => true, runnable := fun s => s = 1, current := some 1 }
    codeRegion := ⟨0x400000, 0x401000⟩, stackRegion := ⟨0x500000, 0x501000⟩
    flags :=
      { interruptEnable := true, direction := false, alignmentCheck := false,
        nestedTask := false, virtual8086 := false, ioPrivilegeLevel := 0,
        reservedAllowed := true } }

private def table : PageTable :=
  { pml4 := { present := true, writable := true, user := true }
    pdpt := { present := true, writable := true, user := true }
    pd := { present := true, writable := true, user := true }
    leaf := fun _ => none }
private def context : Context :=
  { closedRoot := 0x2000, activeRoot := 0x2000
    current := { table, cache := [] }
    controls := { pcid := false, globalPages := false }
    interruptsEnabled := false
    tables := fun root => if root = 0x1000 then some table else none }
private def rejects (ctx : Context) (req : UserReturnRequest) (reason : Error) : Bool :=
  match prepare ctx req with
  | .error actual => actual == reason
  | .ok _ => false

private def checks : List Bool :=
  [ (match prepare context request with
      | .error _ => false
      | .ok plan => plan.targetRoot == 0x1000 && plan.effect == .reloadRoot &&
          plan.after.cache.isEmpty && plan.request.hardware.stackPointer == 0x501000)
  , rejects { context with activeRoot := 0x1000 } request .notClosed
  , rejects { context with interruptsEnabled := true } request .interruptsEnabled
  , rejects { context with controls := { pcid := true, globalPages := false } }
      request .unsupportedControls
  , rejects { context with controls := { pcid := false, globalPages := true } }
      request .unsupportedControls
  , rejects context { request with expectedCr3 := 0 } .invalidRoot
  , rejects context { request with expectedCr3 := 0x1001 } .invalidRoot
  , rejects context { request with expectedCr3 := 0x2000 } .invalidRoot
  , rejects context { request with frameCr3 := 0x3000 } (.returnRejected .wrongCr3)
  , rejects context { request with frameSubject := 2 } (.returnRejected .staleSubject)
  , rejects context { request with frameAddressSpace := 12 } (.returnRejected .wrongAddressSpace)
  , rejects { context with tables := fun _ => none } request .missingTable
  , advance .awaitingReload .iretCompleted == .terminal
  , advance (advance .awaitingReload .reloadVerified) .iretCompleted == .user
  , advance (advance .awaitingReload .reloadVerified) .interrupted == .terminal
  , advance (advance .awaitingReload .reloadFailed) .iretCompleted == .terminal ]

example : checks.all id = true := by rfl

def main : IO Unit := do
  if checks.all id then IO.println s!"Kernel root return replay: {checks.length} checks PASS"
  else throw (IO.userError "kernel root return replay failed")
