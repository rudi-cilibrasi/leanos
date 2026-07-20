import LeanOS.FailStop

open LeanOS FailStop

-- A repeated NMI must not clear an existing halt latch.
example state record raw context
    (hhalted : state.mode = .halted record) :
    (dispatchNmi state raw context).state.mode = .running := by
  rw [halted_nmi_absorbing state record raw context hhalted]
  simp [hhalted]
