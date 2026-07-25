import LeanOS.StaleTranslation

open LeanOS.StaleTranslation

-- Untrusted arguments cannot invalidate another subject's page: subject 1 does
-- not own address space 1, so its unmap request must be rejected and inert.
-- Claiming it is accepted is false.
example : (step filled (.unmap 1 1 7)).accepted = true := by
  native_decide
