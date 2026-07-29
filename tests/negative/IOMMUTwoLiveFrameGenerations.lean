import LeanOS.IOMMU

open LeanOS IOMMU

-- Memory is keyed by physical FrameId.  Two simultaneously live lifetime
-- records may not share that key, even when their generations differ.
def twoLiveGenerationsCore : Core :=
  { emptyCore with
    frames := sampleFrames ++
      [{ sampleFrames.head! with handle := ⟨0, 2⟩, owner := 1 }] }

example : validateCore twoLiveGenerationsCore = true := by
  native_decide
