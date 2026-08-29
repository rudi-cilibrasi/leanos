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

private def releasedFrameState : State :=
  (gate tornDownState (.releaseFrame ⟨0, 1⟩)).state

/- A retired lifetime cannot be released again through the same stale handle. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  (gate releasedFrameState (Operation.releaseFrame { frame := 0, generation := 1 })).isAccepted = true
is false
-/
#guard_msgs in
example :
    (gate releasedFrameState (.releaseFrame ⟨0, 1⟩)).isAccepted = true := by
  native_decide

/- Read-only authority cannot be amplified to read-write. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  (gate readOnlyState
        (Operation.attenuate { mapping := mapping0, offset := 0, length := 16, permission := readWrite })).isAccepted =
    true
is false
-/
#guard_msgs in
example :
    (gate readOnlyState
      (.attenuate ⟨mapping0, 0, 16, readWrite⟩)).isAccepted = true := by
  native_decide

/- An observation outside the only readable IOVA window rejects. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  (deviceRead readOnlyState
        (let __src := readRequest;
        { source := __src.source, assignmentGeneration := __src.assignmentGeneration, iova := 16,
          length := __src.length })).isObserved =
    true
is false
-/
#guard_msgs in
example :
    (deviceRead readOnlyState { readRequest with iova := 16 }).isObserved = true := by
  native_decide

/- A live DMA mapping prevents release of its backing lifetime. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  (gate readOnlyState (Operation.releaseFrame { frame := 0, generation := 1 })).isAccepted = true
is false
-/
#guard_msgs in
example :
    (gate readOnlyState (.releaseFrame ⟨0, 1⟩)).isAccepted = true := by
  native_decide

/- Local kernel and IOMMU invariants cannot replace cross-projection coherence. -/
/--
error: Application type mismatch: The argument
  hiommu
has type
  state.iommu.Invariant
but is expected to have type
  state.iommu.Invariant ∧ state.Coherent
in the application
  ⟨hkernel, hiommu⟩
-/
#guard_msgs in
example (state : AuthoritativeExtension)
    (hkernel : FailStop.AuthoritativeRuntimeWellFormed state.kernel)
    (hiommu : state.iommu.Invariant) :
    (gatedByKernel state ⟨hkernel, hiommu⟩
      (.grant readOnlyGrant)).isAccepted = true := by
  native_decide

private def sameOwnerWrongFrameCore : Core :=
  { emptyCore with
    capabilities :=
      [{ sampleCapabilities.head! with frame := ⟨1, 1⟩ }] }

/- Same ownership cannot substitute a different frame lifetime. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  validateCore sameOwnerWrongFrameCore = true
is false
-/
#guard_msgs in
example : validateCore sameOwnerWrongFrameCore = true := by
  native_decide

private def reassignedState : State :=
  (gate tornDownState (.assign ⟨0⟩)).state

/- A retired assignment generation cannot authorize a reused device slot. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  (deviceRead reassignedState readRequest).isObserved = true
is false
-/
#guard_msgs in
example : (deviceRead reassignedState readRequest).isObserved = true := by
  native_decide

private def twoLiveGenerationsCore : Core :=
  { emptyCore with
    frames := sampleFrames ++
      [{ sampleFrames.head! with handle := ⟨0, 2⟩, owner := 1 }] }

/- Two live generations cannot share one physical frame identity. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  validateCore twoLiveGenerationsCore = true
is false
-/
#guard_msgs in
example : validateCore twoLiveGenerationsCore = true := by
  native_decide

end LeanOS.NegativeFixtures.IOMMUConfinement
