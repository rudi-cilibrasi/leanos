import LeanOS.IOMMU

open LeanOS IOMMU

-- The only readable view is IOVA [0,16); an observation outside it rejects.
example :
    (deviceRead readOnlyState { readRequest with iova := 16 }).isObserved = true := by
  native_decide
