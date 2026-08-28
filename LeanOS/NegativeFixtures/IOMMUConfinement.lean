import LeanOS.IOMMU

namespace LeanOS.NegativeFixtures.IOMMUConfinement

open LeanOS IOMMU

/- A public grant cannot inject a caller-selected physical-frame identity. -/
/--
error: `frame` is not a field of structure `GrantRequest`
-/
#guard_msgs in
def forgedGrant : GrantRequest :=
  { assignment := assignment0
    capability := ⟨0, 1⟩
    iova := 0
    capabilityOffset := 0
    length := 16
    permission := readOnly
    frame := ⟨7, 99⟩ }

/- A successful translation carries the exact kernel-bound domain equality. -/
/--
error: Type mismatch
  translation.domainBound
has type
  translation.mapping.domain = translation.assignment.domain
but is expected to have type
  translation.mapping.domain ≠ translation.assignment.domain
-/
#guard_msgs in
example (translation : Translation state request direction) :
    translation.mapping.domain ≠ translation.assignment.domain := by
  exact translation.domainBound

/- A successful translation witness must retain every source-binding proof. -/
/--
error: Fields missing: `assignmentFound`, `mappingFound`, `frameFound`, `sourceBound`
-/
#guard_msgs (substring := true) in
def omittedSource (state : State) (request : TransferRequest)
    (assignment : Assignment) (mapping : Mapping) (frame : Frame) :
    Translation state request .read :=
  { assignment := assignment
    mapping := mapping
    frame := frame }

/- A published read view must carry both bytes and the successful observation. -/
/--
error: Fields missing: `bytes`, `observed`
-/
#guard_msgs (substring := true) in
def fabricatedReadView (state : State) (request : TransferRequest)
    (translation : Translation state request .read) :
    AuthorizedReadView state :=
  { request := request
    translation := translation }

end LeanOS.NegativeFixtures.IOMMUConfinement
