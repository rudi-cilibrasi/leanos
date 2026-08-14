import LeanOS.BootTopology

open LeanOS.BootTopology

/- A scalar "one expected CPU" promise cannot admit an observed two-CPU snapshot. -/
example : admit twoEnabledProcessors =
    .accepted { apicId := 0, enabled := true, onlineCapable := false } := by
  native_decide
