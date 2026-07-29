import LeanOS.IOMMU

open LeanOS IOMMU

-- A successful translation carries the exact kernel-bound domain equality.
example (translation : Translation state request direction) :
    translation.mapping.domain ≠ translation.assignment.domain := by
  exact translation.domainBound
