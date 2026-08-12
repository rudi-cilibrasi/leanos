import LeanOS.IOMMU

open LeanOS IOMMU

-- A conjunction of the two local invariants cannot invoke the public grant
-- gate: the exact kernel/IOMMU pair must carry cross-projection coherence.
example (state : AuthoritativeExtension)
    (hkernel : FailStop.AuthoritativeRuntimeWellFormed state.kernel)
    (hiommu : state.iommu.Invariant) :
    (gatedByKernel state ⟨hkernel, hiommu⟩
      (.grant readOnlyGrant)).isAccepted = true := by
  native_decide
