import LeanOS.DirectPortContainment

open LeanOS
open LeanOS.DirectPortContainment

/- The composed containment claim's accepted deny-all control hypothesis is
load-bearing: with an exposed I/O bitmap the user path is a malformed-policy
rejection rather than the modeled `#GP(0)` denial, so the denial conclusion is
false on this concrete stored-control state. -/
private def exposedDevices : DirectPortIO.State :=
  { witnessDevices with
    controls := { DirectPortIO.selectedControls with ioBitmapPresent := true } }

example :
    (containDeniedPort exposedDevices exposedDevices.controls serialProbe
      witnessSchedule witnessEntry).port.result = .userDeniedGP := by
  native_decide
