import LeanOS.IOMMU

open LeanOS IOMMU

-- A translation-shaped record is not a device observation.  Every published
-- read view must carry the exact bytes and the successful `deviceRead` result.
def fabricatedReadView (state : State) (request : TransferRequest)
    (translation : Translation state request .read) :
    AuthorizedReadView state :=
  { request := request
    translation := translation }
