import LeanOS.UserFaultContainmentVocabulary

open LeanOS
open LeanOS.DirectPortContainment
open LeanOS.UserFaultContainmentVocabulary

namespace LeanOS.NegativeFixtures.SharedContainment

/- The typed contained reason is bound to the manifest vector and cannot be
substituted: a real CPL3 divide-error entry dispatches with the divide-error
reason, never the breakpoint reason. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  (FaultDispatch.dispatch witnessSchedule divideErrorEntry).action =
    FaultDispatch.Action.dispatch InterruptEntry.ContainedReason.breakpoint witnessSurvivorContext
is false
-/
#guard_msgs in
example :
    (FaultDispatch.dispatch witnessSchedule divideErrorEntry).action =
      .dispatch .breakpoint witnessSurvivorContext := by
  native_decide

end LeanOS.NegativeFixtures.SharedContainment
