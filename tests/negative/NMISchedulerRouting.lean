import LeanOS.InterruptEntry

open LeanOS InterruptEntry

private def schedulerNmi : ManifestEntry :=
  { nmiEntry with purpose := .timer }

-- The terminal gate must not route NMI through timer scheduling.
example : validateTerminalManifest [schedulerNmi] = true := by
  native_decide
