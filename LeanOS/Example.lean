/-!
# Bootstrap proof example

This module checks the initial project wiring; it is not the Phase 1 kernel
transition model. `boundedSuccessor` is executable Lean code, and the theorem
below proves only the stated upper bound in Lean's natural-number model. It
makes no claim about generated native code or the boot boundary described by
ADR 0001.
-/

namespace LeanOS.Example

/-- Increment `value`, capped at `limit`. -/
def boundedSuccessor (limit value : Nat) : Nat :=
  min (value + 1) limit

/-- The bounded successor never exceeds its supplied limit. -/
theorem boundedSuccessor_le (limit value : Nat) :
    boundedSuccessor limit value ≤ limit := by
  exact Nat.min_le_right _ _

example : boundedSuccessor 5 2 = 3 := by decide
example : boundedSuccessor 5 5 = 5 := by decide

end LeanOS.Example
