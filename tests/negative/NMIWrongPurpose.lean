import LeanOS.InterruptEntry

open LeanOS InterruptEntry

private def diagnosticNmi : ManifestEntry :=
  { nmiEntry with purpose := .diagnosticRecovery }

-- NMI entry cannot be repurposed as an ordinary diagnostic recovery path.
example : validateTerminalManifest [diagnosticNmi] = true := by
  native_decide
