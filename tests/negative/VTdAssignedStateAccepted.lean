import LeanOS.VTdBootPlan

open LeanOS.VTdBootPlan

-- The v1 boot plan is deny-all: a device-domain state carrying a live
-- assignment must not compile into an accepted VT-d boot plan.
example : (match compile { sampleInput with state := LeanOS.IOMMU.assignedState } with
    | .ok _ => true | .error _ => false) = true := by native_decide
