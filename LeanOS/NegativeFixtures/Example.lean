import LeanOS.Example

namespace LeanOS.NegativeFixtures.Example

-- A successor at the bound must remain clamped instead of advancing past it.
/--
error: Tactic `rfl` failed: The left-hand side
  Example.boundedSuccessor 3 3
is not definitionally equal to the right-hand side
  4

⊢ Example.boundedSuccessor 3 3 = 4
-/
#guard_msgs in
example : LeanOS.Example.boundedSuccessor 3 3 = 4 := by
  rfl

end LeanOS.NegativeFixtures.Example
