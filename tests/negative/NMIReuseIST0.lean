import LeanOS.InterruptEntry

open LeanOS InterruptEntry

private def ist0Nmi : ManifestEntry :=
  { nmiEntry with ist := 0 }

-- The terminal NMI may not reuse the ordinary non-IST entry stack.
example : validateTerminalManifest [ist0Nmi] = true := by
  native_decide
