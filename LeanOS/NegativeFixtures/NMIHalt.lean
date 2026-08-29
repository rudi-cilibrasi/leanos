import LeanOS.FailStop

open LeanOS FailStop

namespace LeanOS.NegativeFixtures.NMIHalt

-- A repeated NMI must not clear an existing halt latch.
/--
error: unsolved goals
state : State
record : HaltRecord
raw : InterruptEntry.RawNmiEntry
context : InterruptEntry.NmiContext
hhalted : state.mode = Mode.halted record
⊢ False
-/
#guard_msgs in
example state record raw context
    (hhalted : state.mode = .halted record) :
    (dispatchNmi state raw context).state.mode = .running := by
  rw [halted_nmi_absorbing state record raw context hhalted]
  simp [hhalted]

-- Post-halt input cannot repair even an incoherent privileged cleanup bit.
/--
error: unsolved goals
state : State
record : HaltRecord
raw : InterruptEntry.RawNmiEntry
context : InterruptEntry.NmiContext
hhalted : state.mode = Mode.halted record
hcopy : state.copyOverride = true
⊢ False
-/
#guard_msgs in
example state record raw context
    (hhalted : state.mode = .halted record)
    (hcopy : state.copyOverride = true) :
    (dispatchNmi state raw context).state.copyOverride = false := by
  rw [halted_nmi_absorbing state record raw context hhalted]
  simp [hcopy]

end LeanOS.NegativeFixtures.NMIHalt
