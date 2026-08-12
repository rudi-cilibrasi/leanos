import LeanOS.IOMMU

open LeanOS IOMMU

-- Object 10 is authoritatively bound to frame lifetime ⟨0,1⟩.  Same-owner
-- frame ⟨1,1⟩ must not become DMA authority for that capability.
def sameOwnerWrongFrameCore : Core :=
  { emptyCore with
    capabilities :=
      [{ sampleCapabilities.head! with frame := ⟨1, 1⟩ }] }

example : validateCore sameOwnerWrongFrameCore = true := by
  native_decide
