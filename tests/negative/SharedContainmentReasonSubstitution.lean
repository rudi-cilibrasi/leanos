import LeanOS.UserFaultContainmentVocabulary

open LeanOS
open LeanOS.DirectPortContainment
open LeanOS.UserFaultContainmentVocabulary

/- The typed contained reason is bound to the manifest vector and cannot be
substituted: a real CPL3 divide-error entry dispatches with the divide-error
reason, never the breakpoint reason, so this relabeled claim is false on the
concrete shared pre-state. -/
example :
    (FaultDispatch.dispatch witnessSchedule divideErrorEntry).action =
      .dispatch .breakpoint witnessSurvivorContext := by
  native_decide
