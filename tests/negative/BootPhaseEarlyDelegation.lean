import LeanOS.BootInterruptPhase

open LeanOS BootInterruptPhase

-- A bootstrap-phase vector-2 event cannot be delegated to an ordinary runtime
-- handler before the runtime IDT is published.
example :
    (dispatch (α := UInt64) { phase := .bootstrap64, business := 0x5a }
      ⟨2, false, false⟩).outcome = .runtimeDelegated 2 := by
  native_decide
