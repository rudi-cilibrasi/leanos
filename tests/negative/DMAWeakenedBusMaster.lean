import LeanOS.DMAQuarantine

open LeanOS DMAQuarantine

-- Dropping the clear-bit conclusion does not satisfy the stable source fact.
example (accepted : AcceptedSnapshot) (function : FunctionState)
    (hmember : function ∈ accepted.snapshot.functions)
    (hpresent : function.status = .present) : busMasterEnabled function = true := by
  exact (accepted_unassigned_busMaster_disabled accepted function hmember hpresent).2
