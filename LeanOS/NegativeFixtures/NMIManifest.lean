import LeanOS.InterruptEntry

open LeanOS InterruptEntry

namespace LeanOS.NegativeFixtures.NMIManifest

private def dpl3Nmi : ManifestEntry :=
  { nmiEntry with dpl := 3 }

/--
error: Tactic `native_decide` evaluated that the proposition
  validateTerminalManifest [dpl3Nmi] = true
is false
-/
#guard_msgs in
example : validateTerminalManifest [dpl3Nmi] = true := by
  native_decide

/--
error: Tactic `native_decide` evaluated that the proposition
  nmiTraceInventory.dropLast = nmiTraceInventory
is false
-/
#guard_msgs in
example : nmiTraceInventory.dropLast = nmiTraceInventory := by
  native_decide

private def manifestWithNmi : List ManifestEntry :=
  nmiEntry :: manifest

/--
error: Tactic `native_decide` evaluated that the proposition
  validateManifest manifestWithNmi = true
is false
-/
#guard_msgs in
example : validateManifest manifestWithNmi = true := by
  native_decide

private def ist0Nmi : ManifestEntry :=
  { nmiEntry with ist := 0 }

/--
error: Tactic `native_decide` evaluated that the proposition
  validateTerminalManifest [ist0Nmi] = true
is false
-/
#guard_msgs in
example : validateTerminalManifest [ist0Nmi] = true := by
  native_decide

private def ist1Nmi : ManifestEntry :=
  { nmiEntry with ist := 1 }

/--
error: Tactic `native_decide` evaluated that the proposition
  validateTerminalManifest [ist1Nmi] = true
is false
-/
#guard_msgs in
example : validateTerminalManifest [ist1Nmi] = true := by
  native_decide

private def diagnosticNmi : ManifestEntry :=
  { nmiEntry with purpose := .diagnosticRecovery }

/--
error: Tactic `native_decide` evaluated that the proposition
  validateTerminalManifest [diagnosticNmi] = true
is false
-/
#guard_msgs in
example : validateTerminalManifest [diagnosticNmi] = true := by
  native_decide

private def containmentNmi : ManifestEntry :=
  { nmiEntry with purpose := .userFault }

/--
error: Tactic `native_decide` evaluated that the proposition
  validateTerminalManifest [containmentNmi] = true
is false
-/
#guard_msgs in
example : validateTerminalManifest [containmentNmi] = true := by
  native_decide

private def schedulerNmi : ManifestEntry :=
  { nmiEntry with purpose := .timer }

/--
error: Tactic `native_decide` evaluated that the proposition
  validateTerminalManifest [schedulerNmi] = true
is false
-/
#guard_msgs in
example : validateTerminalManifest [schedulerNmi] = true := by
  native_decide

private def context : NmiContext :=
  { currentSubject := 1
    activeAddressSpace := 1
    activeCr3 := 0x1000
    stackIdentity := nmiStackIdentity
    stackFirst := nmiAbstractStackFirst
    stackPastLast := nmiAbstractStackPastLast
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

/--
error: Tactic `native_decide` evaluated that the proposition
  normalizeNmi raw context 1 1 = NmiResult.accepted (makeNormalizedNmi raw context)
is false
-/
#guard_msgs in
example : normalizeNmi raw context 1 1 = .accepted (makeNormalizedNmi raw context) := by
  native_decide

end LeanOS.NegativeFixtures.NMIManifest
