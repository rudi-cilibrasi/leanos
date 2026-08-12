import LeanOS.IOMMU

open LeanOS IOMMU

-- A public grant has no physical-frame field.  Backing identity must resolve
-- through the current owner's capability slot.
def forgedGrant : GrantRequest :=
  { assignment := assignment0
    capability := ⟨0, 1⟩
    iova := 0
    capabilityOffset := 0
    length := 16
    permission := readOnly
    frame := ⟨7, 99⟩ }
