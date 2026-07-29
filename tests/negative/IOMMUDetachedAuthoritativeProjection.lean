import LeanOS.IOMMU

open LeanOS IOMMU

-- A conjunction of the two local invariants is no longer enough: the kernel
-- and IOMMU projections must also satisfy the cross-projection coherence law.
example (state : AuthoritativeExtension)
    (hkernel : FailStop.AuthoritativeRuntimeWellFormed state.kernel)
    (hiommu : state.iommu.Invariant) :
    state.Invariant :=
  ⟨hkernel, hiommu⟩
