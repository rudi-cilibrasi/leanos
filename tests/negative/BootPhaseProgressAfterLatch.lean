import LeanOS.BootInterruptPhase

open LeanOS BootInterruptPhase

-- After an early terminal latch, a publication cannot resume the chain.
example :
    (publish (α := UInt64)
      { phase := .terminal, latched := some canonicalLatchRecord, business := 0x5a }
      .publishBootstrap32).state.phase = .bootstrap32 := by
  native_decide
