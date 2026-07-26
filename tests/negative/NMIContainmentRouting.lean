import LeanOS.InterruptEntry

open LeanOS InterruptEntry

private def containmentNmi : ManifestEntry :=
  { nmiEntry with purpose := .userFault }

-- The terminal gate must not route NMI through ordinary user containment.
example : validateTerminalManifest [containmentNmi] = true := by
  native_decide
