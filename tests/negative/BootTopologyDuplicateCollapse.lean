import LeanOS.BootTopology

open LeanOS.BootTopology

/- Deduplicating APIC IDs before policy evaluation cannot satisfy admission. -/
example : admit duplicateBsp =
    .accepted { apicId := 0, enabled := true, onlineCapable := false } := by
  native_decide
