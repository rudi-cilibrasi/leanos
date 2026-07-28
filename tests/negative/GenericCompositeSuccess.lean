import LeanOS.FailStop

open LeanOS

namespace LeanOS.FailStop

/-! A wrapper that erases every operation-specific completed reply cannot
satisfy the authoritative gate's accepted-result soundness contract. -/

inductive GenericGateResult where
  | accepted
  | rejectedBusy
  | rejectedHalted

def genericGateResult : AuthoritativeGateResult → GenericGateResult
  | .completed _ => .accepted
  | .rejectedBusy => .rejectedBusy
  | .rejectedHalted _ => .rejectedHalted

example state operation reply
    (hgeneric :
      genericGateResult (authoritativeGate state operation).result =
        .accepted) :
    (authoritativeGate state operation).result = .completed reply := by
  exact hgeneric

end LeanOS.FailStop
