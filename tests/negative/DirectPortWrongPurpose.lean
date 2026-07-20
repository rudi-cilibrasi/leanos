import LeanOS.DirectPortIO

open LeanOS DirectPortIO

private def state : State :=
  { controls := selectedControls, devices := ⟨0, 0, 0, 0⟩ }

private def wrong : KernelRequest :=
  { purpose := .debugExit
    operation := { port := 0x3f8, direction := .output, width := .byte, value := 1 } }

-- A serial port paired with the debug-exit purpose is not ambient authority.
example : (executeKernel state selectedControls wrong).result = .kernelAccepted := by
  native_decide
