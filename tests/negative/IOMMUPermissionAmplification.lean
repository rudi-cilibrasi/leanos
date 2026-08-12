import LeanOS.IOMMU

open LeanOS IOMMU

-- Read-only authority cannot be amplified to read-write.
example :
    (gate readOnlyState
      (.attenuate ⟨mapping0, 0, 16, readWrite⟩)).isAccepted = true := by
  native_decide
