import LeanOS.Oracle.Vector
import LeanOS.IOTLB

/-!
# Oracle corpus: IOTLB publication

The filled-cache IOTLB publication trace with its stale-ticket and wrong-scope
rows, checked against the cache model.
-/
namespace LeanOS.Oracle

open LeanOS
set_option maxRecDepth 4096

private def iotlbPublication (id : String)
    (action ticket source domain mapping iova : UInt64) : Vector :=
  { id, adapter := "IOTLB.scalar",
    words := [action, ticket, source, domain, mapping, iova],
    expected := IOMMU.IOTLB.iotlbPublicationDemo
      action ticket source domain mapping iova }

/-- The first hosted IOTLB corpus keeps one exact filled-cache trace together
with stale-ticket and every lifetime-bearing scope mismatch. -/
def iotlbPublicationVectors : List Vector := [
  iotlbPublication "iotlb.observe-filled" 0 0 0 0 0 0,
  iotlbPublication "iotlb.prepare-retains-live" 1 0 0 0 0 0,
  iotlbPublication "iotlb.reject-stale-ticket" 2 6 1 3 4 0x1000,
  iotlbPublication "iotlb.reject-wrong-source" 2 7 9 3 4 0x1000,
  iotlbPublication "iotlb.reject-wrong-domain" 2 7 1 9 4 0x1000,
  iotlbPublication "iotlb.reject-wrong-mapping" 2 7 1 3 9 0x1000,
  iotlbPublication "iotlb.reject-wrong-iova" 2 7 1 3 4 0x2000,
  iotlbPublication "iotlb.ack-exact" 2 7 1 3 4 0x1000,
  iotlbPublication "iotlb.reject-completion-replay" 3 7 1 3 4 0x1000]

private def iotlbPublicationAdapterAgrees (vector : Vector) : Bool :=
  match vector.adapter, vector.words with
  | "IOTLB.scalar", [action, ticket, source, domain, mapping, iova] =>
      IOMMU.IOTLB.iotlbPublicationDemo action ticket source domain mapping iova =
        vector.expected
  | _, _ => true

theorem hosted_iotlb_publication_adapter_agrees :
    iotlbPublicationVectors.all
      iotlbPublicationAdapterAgrees = true := by
  native_decide

end LeanOS.Oracle
