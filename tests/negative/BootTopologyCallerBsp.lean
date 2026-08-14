import LeanOS.BootTopology

open LeanOS.BootTopology

/- A caller-selected BSP cannot override the independently observed executing ID. -/
example : admit mismatchedExecutingProcessor =
    .accepted { apicId := 0, enabled := true, onlineCapable := false } := by
  native_decide
