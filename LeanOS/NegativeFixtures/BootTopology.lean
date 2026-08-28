import LeanOS.BootTopology

namespace LeanOS.NegativeFixtures.BootTopology

open LeanOS.BootTopology

/- A scalar "one expected CPU" promise cannot admit an observed two-CPU snapshot. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  admit twoEnabledProcessors = Result.accepted { apicId := 0, enabled := true, onlineCapable := false }
is false
-/
#guard_msgs in
example : admit twoEnabledProcessors =
    .accepted { apicId := 0, enabled := true, onlineCapable := false } := by
  native_decide

/- Deduplicating APIC IDs before policy evaluation cannot satisfy admission. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  admit duplicateBsp = Result.accepted { apicId := 0, enabled := true, onlineCapable := false }
is false
-/
#guard_msgs in
example : admit duplicateBsp =
    .accepted { apicId := 0, enabled := true, onlineCapable := false } := by
  native_decide

/- A caller-selected BSP cannot override the independently observed executing ID. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  admit mismatchedExecutingProcessor = Result.accepted { apicId := 0, enabled := true, onlineCapable := false }
is false
-/
#guard_msgs in
example : admit mismatchedExecutingProcessor =
    .accepted { apicId := 0, enabled := true, onlineCapable := false } := by
  native_decide

private def admitted : AdmissionState :=
  (consumeBootAdmission bootAdmissionInitial
    (decodeAndAdmitMadt repositoryMadtRecords 0 0)).business

/- The finite runtime vocabulary cannot erase the published admission premise. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  (runRuntime admitted [RuntimeOperation.initialize, RuntimeOperation.dispatch]).singleCoreAdmitted = false
is false
-/
#guard_msgs in
example : (runRuntime admitted [.initialize, .dispatch]).singleCoreAdmitted = false := by
  native_decide

end LeanOS.NegativeFixtures.BootTopology
