import LeanOS.DMAQuarantine

namespace LeanOS.NegativeFixtures.DMAQuarantine

open LeanOS DMAQuarantine

private def emptySnapshot : Snapshot :=
  { version := snapshotVersion
    topologyVersion := q35TopologyVersion
    functions := [] }

/- Validation must reject an empty function inventory. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  (validate emptySnapshot).isAccepted = true
is false
-/
#guard_msgs in
example : (validate emptySnapshot).isAccepted = true := by
  native_decide

/- A bus-master-enabled control observation cannot continue. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  (runtimeGate q35Runtime (PublicOperation.observeControl q35BusMasterBitFlipSnapshot)).result = RuntimeResult.continued
is false
-/
#guard_msgs in
example :
    (runtimeGate q35Runtime (.observeControl q35BusMasterBitFlipSnapshot)).result =
      .continued := by
  native_decide

private def staleSnapshot : Snapshot :=
  { q35Snapshot with version := 0 }

/- Encoding does not validate a stale snapshot. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  (validate staleSnapshot).isAccepted = true
is false
-/
#guard_msgs in
example : (encodeSnapshot staleSnapshot).isSome = true ->
    (validate staleSnapshot).isAccepted = true := by
  intro _hencoded
  native_decide

end LeanOS.NegativeFixtures.DMAQuarantine
