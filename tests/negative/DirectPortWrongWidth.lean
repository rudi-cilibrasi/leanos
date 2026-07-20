import LeanOS.DirectPortIO

open LeanOS DirectPortIO

private def state : State :=
  { controls := selectedControls, devices := ⟨0, 0, 0, 0⟩ }

private def wrong : KernelRequest :=
  { purpose := .serial
    operation := { port := 0x3f8, direction := .output, width := .word, value := 1 } }

-- A partial-width mismatch does not inherit the byte-wide serial authority.
example : (executeKernel state selectedControls wrong).result = .kernelAccepted := by
  native_decide
