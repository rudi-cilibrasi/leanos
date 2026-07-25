import LeanOS.InterruptEntry

open LeanOS InterruptEntry

private def alternateBreakpointManifest : List ManifestEntry :=
  manifest.map (fun entry => if entry.vector = 3 then { entry with dpl := 0 } else entry)

-- Any DPL/type combination other than the reviewed DPL3 interrupt-gate
-- breakpoint descriptor must be rejected by manifest validation.
example : validateManifest alternateBreakpointManifest = true := by
  native_decide
