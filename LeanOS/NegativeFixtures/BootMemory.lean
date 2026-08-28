import LeanOS.BootMemoryMapFullProjectionABI

namespace LeanOS.NegativeFixtures.BootMemory

open LeanOS.BootMemoryMapFullProjectionABI

/- A substituted selected frame must never be reported as accepted authority. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  fixtureQuery 4 1 = accepted
is false
-/
#guard_msgs in
example : fixtureQuery 4 1 = accepted := by
  native_decide

end LeanOS.NegativeFixtures.BootMemory
