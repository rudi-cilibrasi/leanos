import LeanOS.IOMMU

open LeanOS IOMMU

-- The source binding is a required field of every successful translation
-- witness; it cannot be omitted from a replacement observation rule.
def omittedSource (state : State) (request : TransferRequest)
    (assignment : Assignment) (mapping : Mapping) (frame : Frame) :
    Translation state request .read :=
  { assignment := assignment
    mapping := mapping
    frame := frame }
