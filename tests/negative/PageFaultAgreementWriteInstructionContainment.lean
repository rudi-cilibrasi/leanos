import LeanOS.FaultDispatch

open LeanOS
open LeanOS.FaultDispatch

/- An error word cannot describe one access as both a write and an instruction
fetch; that impossible encoding must never reach ordinary containment. -/
example : pageFaultImpossibleWriteInstructionContained = true := by
  have hfalse : pageFaultImpossibleWriteInstructionContained = false := by
    unfold pageFaultImpossibleWriteInstructionContained
    rw [page_fault_write_instruction_is_absorbing_fatal.1]
  exact hfalse
