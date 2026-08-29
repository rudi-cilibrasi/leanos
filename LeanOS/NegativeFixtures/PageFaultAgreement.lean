import LeanOS.FaultDispatch

open LeanOS FaultDispatch

namespace LeanOS.NegativeFixtures.PageFaultAgreement

/- A protection error cannot contain a walk that predicts non-presence. -/
/- error: Tactic `native_decide` evaluated that the proposition -/
#guard_msgs (substring := true) in
example :
    pageFaultAgreementWitnessContained
      (pageFaultAgreementWitnessRecord 5 50) = true := by
  native_decide

/- Ignoring a plan/live-walk disagreement cannot authorize containment. -/
/- error: Tactic `native_decide` evaluated that the proposition -/
#guard_msgs (substring := true) in
example :
    pageFaultAgreementWitnessContained
      (pageFaultAgreementWitnessRecord 4 100) = true := by
  native_decide

/- An architectural reserved-bit violation is an integrity failure. -/
/- error: Tactic `native_decide` evaluated that the proposition -/
#guard_msgs (substring := true) in
example :
    pageFaultAgreementWitnessContained
      (pageFaultAgreementWitnessRecord 12 50) = true := by
  native_decide

/- A caller-selected address space cannot replace the active one. -/
/- error: Tactic `native_decide` evaluated that the proposition -/
#guard_msgs (substring := true) in
example :
    let forged :=
      { pageFaultAgreementWitnessRecord 4 50 with activeAddressSpace := 2 }
    pageFaultAgreementWitnessContained forged = true := by
  native_decide

/- Stale lifecycle state cannot authorize ordinary containment. -/
/- error: Tactic `native_decide` evaluated that the proposition -/
#guard_msgs (substring := true) in
example : pageFaultAgreementStaleLifecycleContained = true := by
  native_decide

/- An unissued mapped object is stale generation state. -/
/- error: Tactic `native_decide` evaluated that the proposition -/
#guard_msgs (substring := true) in
example : pageFaultAgreementUnissuedObjectContained = true := by
  native_decide

/- A corrupt live table is an integrity failure, not subject cleanup. -/
/- error: Tactic `native_decide` evaluated that the proposition -/
#guard_msgs (substring := true) in
example : pageFaultReservedLiveTableContained = true := by
  native_decide

end LeanOS.NegativeFixtures.PageFaultAgreement
