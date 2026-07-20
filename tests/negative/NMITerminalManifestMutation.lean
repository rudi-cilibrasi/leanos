import LeanOS.InterruptEntry

open LeanOS InterruptEntry

private def dpl3Nmi : ManifestEntry :=
  { nmiEntry with dpl := 3 }

-- A user-callable terminal descriptor must never validate as the NMI manifest.
example : validateTerminalManifest [dpl3Nmi] = true := by
  native_decide
