import LeanOS.StaleTranslation

open LeanOS.StaleTranslation

-- An accepted unmap must invalidate exactly the requested page.  Claiming the
-- effect names a different page (here page 8 instead of the checked page 7) is
-- false: the effect is spliced from checked kernel state, not attacker choice.
example : (step filled (.unmap 0 1 7)).effect = .page 1 8 := by
  native_decide
