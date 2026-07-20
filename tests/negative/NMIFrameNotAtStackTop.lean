import LeanOS.InterruptEntry

open LeanOS InterruptEntry

private def context : NmiContext :=
  { currentSubject := 1
    activeAddressSpace := 1
    activeCr3 := 0x1000
    stackIdentity := nmiStackIdentity
    stackFirst := nmiStackFirst
    stackPastLast := nmiStackPastLast
    interruptedMode := .running }

private def raw : RawNmiEntry :=
  { descriptor := nmiEntry
    boundStub := nmiVector
    errorCode := none
    frame := ⟨0x400100, 0x23, 0x202, 0x500ff8, 0x1b, true, true⟩
    claimedOrigin := .user
    frameBytes := 40
    frameAddress := 0x903fc8
    acCleared := true
    dfCleared := true }

-- An 8-mod-16 frame still fails unless its fifth word ends at stackPastLast.
example : normalizeNmi raw context 1 1 = .accepted (makeNormalizedNmi raw context) := by
  native_decide
