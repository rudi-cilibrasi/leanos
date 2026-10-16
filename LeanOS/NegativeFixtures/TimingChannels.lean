import LeanOS.TimingBudget

open LeanOS.TimingChannels LeanOS.TimingBudget

namespace LeanOS.NegativeFixtures.TimingChannels

/- Issue #576, ADR 0028.  Each claim below would reopen a timing channel the
ADR closes; the kernel refutes every one. -/

/- The refusal tells the live peer (word 3) from a subject never issued
(word 10). -/
/--
error: Tactic `decide` proved that the proposition
  crossSubjectRefusal 1 2 3 ≠ crossSubjectRefusal 1 2 10
is false
-/
#guard_msgs in
example : crossSubjectRefusal 1 2 3 ≠ crossSubjectRefusal 1 2 10 := by
  decide

/- A padded reply whose work fits its budget leaves before the budget. -/
/--
error: Tactic `decide` proved that the proposition
  ∃ work, work < 11 ∧ departure 0 work 10 < 10
is false
-/
#guard_msgs in
example : ∃ work < 11, departure 0 work 10 < 10 := by
  decide

/- Some CR4 the validated user return accepts leaves RDTSC or RDPMC usable at
CPL3: TSD clear, or PCE set. -/
/--
error: Tactic `decide` proved that the proposition
  ∃ cr4,
    cr4 ∈ [3145728, 3145732, 3145988, 3145984] ∧ userReturnClockControls cr4 = true ∧ userCounterFaults cr4 3 = false
is false
-/
#guard_msgs in
example : ∃ cr4 ∈ [(0x300000 : UInt64), 0x300004, 0x300104, 0x300100],
    userReturnClockControls cr4 = true ∧ userCounterFaults cr4 3 = false := by
  decide

end LeanOS.NegativeFixtures.TimingChannels
