import LeanOS.InterruptEntry

open LeanOS InterruptEntry

private def softwareDivideManifest : List ManifestEntry :=
  manifest.map (fun entry => if entry.vector = 0 then { entry with dpl := 3 } else entry)

-- Making vector 0 a CPL3 software-callable INT n gate must not revalidate the
-- ordinary manifest.
example : validateManifest softwareDivideManifest = true := by
  native_decide
