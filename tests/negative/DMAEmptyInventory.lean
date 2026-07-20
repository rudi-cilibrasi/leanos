import LeanOS.DMAQuarantine

open LeanOS DMAQuarantine

private def emptySnapshot : Snapshot :=
  { version := snapshotVersion
    topologyVersion := q35TopologyVersion
    functions := [] }

-- Validation must reject an empty function inventory.
example : (validate emptySnapshot).isAccepted = true := by
  native_decide
