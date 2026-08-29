import LeanOS.VTdBootPlan

namespace LeanOS.NegativeFixtures.VTdBootPlan

open LeanOS.VTdBootPlan

/- The v1 boot plan is deny-all: an assigned device-domain state is rejected. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  (match
      compile
        (let __src := sampleInput;
        { state := IOMMU.assignedState, rootTableFrame := __src.rootTableFrame,
          contextTableFrame := __src.contextTableFrame, cpuTableFrames := __src.cpuTableFrames,
          reservationResult := __src.reservationResult }) with
    | Except.ok a => true
    | Except.error a => false) =
    true
is false
-/
#guard_msgs in
example : (match compile { sampleInput with state := LeanOS.IOMMU.assignedState } with
    | .ok _ => true | .error _ => false) = true := by
  native_decide

/- A surprise present context entry must fail generated-snapshot validation. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  (match compile sampleInput with
    | Except.ok plan =>
      (validateDecodedUnit plan
          (let __src := expectedDecodedUnit plan;
          { versionRegister := __src.versionRegister, capabilityRegister := __src.capabilityRegister,
            extendedCapabilityRegister := __src.extendedCapabilityRegister, globalStatus := __src.globalStatus,
            faultStatus := __src.faultStatus, rootTableAddress := __src.rootTableAddress, rootWords := __src.rootWords,
            contextWords := (expectedDecodedUnit plan).contextWords.set 0 (UInt64.ofNat (12 * 4096 + 1)) })).isOk
    | Except.error a => false) =
    true
is false
-/
#guard_msgs in
example : (match compile sampleInput with
    | .ok plan =>
        (validateDecodedUnit plan
          { expectedDecodedUnit plan with
            contextWords := (expectedDecodedUnit plan).contextWords.set 0
              (UInt64.ofNat (12 * 4096 + 1)) }).isOk
    | .error _ => false) = true := by
  native_decide

end LeanOS.NegativeFixtures.VTdBootPlan
