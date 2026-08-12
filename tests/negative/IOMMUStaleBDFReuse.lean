import LeanOS.IOMMU

open LeanOS IOMMU

def reassignedState : State :=
  (gate tornDownState (.assign ⟨0⟩)).state

-- Reusing a device slot receives a fresh assignment/domain generation.  The
-- retired generation-one request cannot authorize the replacement.
example : (deviceRead reassignedState readRequest).isObserved = true := by
  native_decide
