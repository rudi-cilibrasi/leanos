import LeanOS.SmapWindowPlan

open LeanOS.SmapWindowPlan

/- A copy window that drops `clac` reaches `popfq` and `ret` with the AC
window still open, so the plan check must reject it. -/
example : acSafe (copyBody.erase .clac) = true := by decide
