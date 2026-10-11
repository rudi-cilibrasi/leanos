import LeanOS.CompositeFullChannels

open LeanOS LeanOS.FailStop LeanOS.CompositeSwitchedChannels LeanOS.CompositeFullView

/- `#542` proved that subtree revocation of the observer's own capability is
step inconsistent (`CompositeSwitchedChannels.revokeSubtree_own_step_inconsistent`):
two runs the view cannot tell apart differ only in a derivation, and revoking
the subtree cancels the transfer pending on the observer's endpoint in one run
only.  That derivation is the observer's revocation authority, and the full
view contains it.  Restating the old premise for the full view must fail: on
the canonical sample plan the kernel evaluates the two runs' authority to
different lineages. -/
example :
    (match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
      | .ok plan => extra 2 (runFrom plan leftTrace) == extra 2 (runFrom plan rightTrace)
      | .error _ => false) = true := by
  decide +kernel
