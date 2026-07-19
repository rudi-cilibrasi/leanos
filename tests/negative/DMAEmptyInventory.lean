import LeanOS.DMAQuarantine

open LeanOS DMAQuarantine

-- The advertised acceptance invariant cannot be witnessed by an empty list.
example (accepted : AcceptedSnapshot) (hempty : accepted.snapshot.functions = []) : False := by
  have hnonempty := accepted_nonempty accepted
  rw [hempty] at hnonempty
  exact hnonempty
