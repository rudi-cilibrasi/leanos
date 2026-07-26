import LeanOS.StaleTranslation

open LeanOS.StaleTranslation
open LeanOS.TLB

-- A cache that trusts a stale hit after the PTE is cleared without invalidation
-- would still reach the retired frame 4.  This fixture asserts the *safe* honest
-- access still succeeds through the stale hit, which is false: the authoritative
-- access rewalks and denies it.  Any design that dropped the invalidation and
-- trusted the cache is therefore rejected by the model.
example : (access (step filled (.unmap 0 1 7)).state 7 ctx).toOption.map
    (fun result => result.1) = some 4 := by
  native_decide
