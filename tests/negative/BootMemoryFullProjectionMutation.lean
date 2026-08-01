import LeanOS.BootMemoryMapFullProjectionABI

open LeanOS.BootMemoryMapFullProjectionABI

/- A substituted selected frame must never be reported as accepted authority. -/
example : fixtureQuery 4 1 = accepted := by
  native_decide
