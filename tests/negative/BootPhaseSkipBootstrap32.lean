import LeanOS.BootInterruptPhase

open LeanOS BootInterruptPhase

-- The 64-bit bootstrap table cannot be published before the 32-bit one:
-- skipping a chain step must fail closed rather than advance the phase.
example :
    (publish (α := UInt64) { phase := .inherited, business := 0x5a }
      .publishBootstrap64).outcome = .published .bootstrap64 := by
  native_decide
