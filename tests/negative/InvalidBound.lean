import LeanOS.Example

-- This deliberately false claim must be rejected by the pinned Lean checker.
example : LeanOS.Example.boundedSuccessor 3 3 = 4 := by
  rfl
