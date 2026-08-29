import LeanOS.StaleTranslation

open LeanOS.StaleTranslation
open LeanOS.TLB

namespace LeanOS.NegativeFixtures.StaleTranslation

/- A cache cannot preserve access to a retired frame after an accepted unmap. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  Option.map (fun result => result.fst) (access (step filled (Request.unmap 0 1 7)).state 7 ctx).toOption = some 4
is false
-/
#guard_msgs in
example : (access (step filled (.unmap 0 1 7)).state 7 ctx).toOption.map
    (fun result => result.1) = some 4 := by
  native_decide

/- An accepted unmap cannot report an effect for a caller-chosen page. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  (step filled (Request.unmap 0 1 7)).effect = Effect.page 1 8
is false
-/
#guard_msgs in
example : (step filled (.unmap 0 1 7)).effect = .page 1 8 := by
  native_decide

/- An untrusted subject cannot invalidate another subject's mapping. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  (step filled (Request.unmap 1 1 7)).accepted = true
is false
-/
#guard_msgs in
example : (step filled (.unmap 1 1 7)).accepted = true := by
  native_decide

end LeanOS.NegativeFixtures.StaleTranslation
