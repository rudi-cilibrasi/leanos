import LeanOS.InterruptEntry

open LeanOS InterruptEntry

private def ist1Nmi : ManifestEntry :=
  { nmiEntry with ist := 1 }

-- The terminal NMI may not reuse the double-fault IST1 stack.
example : validateTerminalManifest [ist1Nmi] = true := by
  native_decide
