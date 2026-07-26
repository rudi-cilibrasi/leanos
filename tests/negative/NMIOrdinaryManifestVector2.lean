import LeanOS.InterruptEntry

open LeanOS InterruptEntry

private def manifestWithNmi : List ManifestEntry :=
  nmiEntry :: manifest

-- Adding vector 2 must not produce a valid ordinary-handler manifest.
example : validateManifest manifestWithNmi = true := by
  native_decide
