import LeanOS.DirectPortIO

open LeanOS DirectPortIO

private def exposed : Controls :=
  { selectedControls with ioBitmapPresent := true }

private def state : State :=
  { controls := exposed, devices := ⟨0, 0, 0, 0⟩ }

private def request : PortOperation :=
  { port := 0x3f8, direction := .output, width := .byte, value := 65 }

-- An exposed user bitmap cannot be relabeled as the accepted #GP denial state.
example : executeUser state exposed request = { state, result := .userDeniedGP } := by
  native_decide
