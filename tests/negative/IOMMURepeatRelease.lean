import LeanOS.IOMMU

open LeanOS IOMMU

def releasedFrameState : State :=
  (gate tornDownState (.releaseFrame ⟨0, 1⟩)).state

-- A retired lifetime cannot be released again through the same stale handle.
example :
    (gate releasedFrameState (.releaseFrame ⟨0, 1⟩)).isAccepted = true := by
  native_decide
