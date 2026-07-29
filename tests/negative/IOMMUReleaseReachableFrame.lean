import LeanOS.IOMMU

open LeanOS IOMMU

-- A live DMA mapping prevents release of its backing lifetime.
example :
    (gate readOnlyState (.releaseFrame ⟨0, 1⟩)).isAccepted = true := by
  native_decide
