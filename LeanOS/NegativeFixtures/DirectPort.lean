import LeanOS.DirectPortContainment

namespace LeanOS.NegativeFixtures.DirectPort

open LeanOS DirectPortIO DirectPortContainment

private def exposed : Controls :=
  { selectedControls with ioBitmapPresent := true }

private def exposedState : DirectPortIO.State :=
  { controls := exposed, devices := ⟨0, 0, 0, 0⟩ }

private def serialRequest : PortOperation :=
  { port := 0x3f8, direction := .output, width := .byte, value := 65 }

/- An exposed user bitmap cannot be relabeled as the accepted #GP denial state. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  executeUser exposedState exposed serialRequest = { state := exposedState, result := Result.userDeniedGP }
is false
-/
#guard_msgs in
example : executeUser exposedState exposed serialRequest =
    { state := exposedState, result := .userDeniedGP } := by
  native_decide

private def selectedState : DirectPortIO.State :=
  { controls := selectedControls, devices := ⟨0, 0, 0, 0⟩ }

private def wrongPurpose : KernelRequest :=
  { purpose := .debugExit
    operation := { port := 0x3f8, direction := .output, width := .byte, value := 1 } }

/- A serial port paired with the debug-exit purpose is not ambient authority. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  (executeKernel selectedState selectedControls wrongPurpose).result = Result.kernelAccepted
is false
-/
#guard_msgs in
example : (executeKernel selectedState selectedControls wrongPurpose).result =
    .kernelAccepted := by
  native_decide

private def wrongWidth : KernelRequest :=
  { purpose := .serial
    operation := { port := 0x3f8, direction := .output, width := .word, value := 1 } }

/- A partial-width mismatch does not inherit byte-wide serial authority. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  (executeKernel selectedState selectedControls wrongWidth).result = Result.kernelAccepted
is false
-/
#guard_msgs in
example : (executeKernel selectedState selectedControls wrongWidth).result =
    .kernelAccepted := by
  native_decide

private def exposedDevices : DirectPortIO.State :=
  { witnessDevices with
    controls := { selectedControls with ioBitmapPresent := true } }

/- The composed containment theorem must retain its deny-all control premise. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  (containDeniedPort exposedDevices exposedDevices.controls serialProbe witnessSchedule witnessEntry).port.result =
    Result.userDeniedGP
is false
-/
#guard_msgs in
example :
    (containDeniedPort exposedDevices exposedDevices.controls serialProbe
      witnessSchedule witnessEntry).port.result = .userDeniedGP := by
  native_decide

/- A user-origin request cannot be used to prove any modeled device mutation. -/
/--
error: Type mismatch
  user_request_preserves_device_state state live request
has type
  (executeUser state live request).state.devices = state.devices
but is expected to have type
  (executeUser state live request).state.devices ≠ state.devices
-/
#guard_msgs in
example (state : DirectPortIO.State) (live : Controls) (request : PortOperation) :
    (executeUser state live request).state.devices ≠ state.devices := by
  exact user_request_preserves_device_state state live request

end LeanOS.NegativeFixtures.DirectPort
