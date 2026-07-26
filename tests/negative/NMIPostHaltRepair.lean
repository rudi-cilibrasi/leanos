import LeanOS.FailStop

open LeanOS FailStop

-- Post-halt input cannot repair even an incoherent privileged cleanup bit.
example state record raw context
    (hhalted : state.mode = .halted record)
    (hcopy : state.copyOverride = true) :
    (dispatchNmi state raw context).state.copyOverride = false := by
  rw [halted_nmi_absorbing state record raw context hhalted]
  simp [hcopy]
