import LeanOS.BootInterruptPhase

open LeanOS BootInterruptPhase

-- The runtime manifest cannot be published before the TSS is loaded.
example :
    (publish (α := UInt64) { phase := .bootstrap64, business := 0x5a }
      (.publishRuntime ⟨false, true, true⟩)).outcome = .published .runtime := by
  native_decide
