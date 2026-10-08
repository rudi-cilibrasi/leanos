import LeanOS.Refinement.CSubset
import LeanOS.KernelTransition

/-!
# Rung 3 for `leanos_boot_transition` (issue #470, ADR 0023)

`bootTransitionC` is the C function the pinned Lean toolchain emits for the
`@[export leanos_boot_transition]` adapter, as extracted from the generated
`KernelTransition.c` by `scripts/extract-generated-c.py`. The build re-runs
the extractor and fails if the emitted C no longer matches this AST.

Under the C-subset semantics of `LeanOS.Refinement.CSubset`, calling it on any
two 64-bit words returns exactly `KernelTransition.bootTransition`, and so,
on encoded states, the model's encoded result. The theorem does not cover the
calling convention, the compiler, the linker, the boot path or QEMU.
-/
namespace LeanOS.Refinement.BootTransitionC

open LeanOS.Refinement.CSubset LeanOS.KernelTransition

-- BEGIN GENERATED AST
def bootTransitionC : Func :=
  { params := ["v_state_567_", "v_command_568_"]
    body := [
      (.decl .u64 "v___x_569_"),
      (.decl .u8 "v___y_571_"),
      (.decl .u8 "v___x_573_"),
      (.assign "v___x_569_" (.lit 0)),
      (.assign "v___x_573_" (.decEq (.var "v_state_567_") (.var "v___x_569_"))),
      (.ifZero "v___x_573_" [(.assign "v___y_571_" (.var "v___x_573_")), (.goto "v___jp_570_")] [(.decl .u64 "v___x_574_"), (.decl .u8 "v___x_575_"), (.assign "v___x_574_" (.lit 1)), (.assign "v___x_575_" (.decEq (.var "v_command_568_") (.var "v___x_574_"))), (.assign "v___y_571_" (.var "v___x_575_")), (.goto "v___jp_570_")]),
      (.block "v___jp_570_" [(.ifZero "v___y_571_" [(.ret (.var "v___x_569_"))] [(.decl .u64 "v___x_572_"), (.assign "v___x_572_" (.lit 1)), (.ret (.var "v___x_572_"))])])] }
-- END GENERATED AST

/-- Rung 3: the emitted C computes the Lean adapter on every pair of words. -/
theorem bootTransitionC_refines (state command : UInt64) :
    call bootTransitionC [state, command] = some (bootTransition state command) := by
  by_cases hs : state = 0 <;> by_cases hc : command = 1 <;>
    simp [call, bootTransitionC, runBody, execList, findLabel, evalExpr, Env.get?,
      Env.ty?, truncate, bootTransition, hs, hc] <;> decide

/-- On every encoded model state the emitted C returns the model's encoded
result for the decoded command. -/
theorem bootTransitionC_refines_transition (state : State) (command : UInt64) :
    call bootTransitionC [encodeState state, command] =
      some (encodeResult (transition state (decodeCommand command)).result) := by
  rw [bootTransitionC_refines, bootTransition_agrees]

end LeanOS.Refinement.BootTransitionC
