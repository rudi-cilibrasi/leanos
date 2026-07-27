import LeanOS.DMAQuarantine

open LeanOS DMAQuarantine

private def staleSnapshot : Snapshot :=
  { q35Snapshot with version := 0 }

-- Fixed-width typed serialization does not validate a snapshot or supply
-- issue #105's future canonical composite-state decoder.
example : (encodeSnapshot staleSnapshot).isSome = true →
    (validate staleSnapshot).isAccepted = true := by
  intro _hencoded
  native_decide
