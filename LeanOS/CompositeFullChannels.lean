import LeanOS.CompositeFullTrace

/-!
# The subtree-revocation channel is inside the full view

`CompositeSwitchedChannels.revokeSubtree_own_step_inconsistent` is the record
of the channel: two runs the observer's view cannot tell apart, after which
revoking the subtree of its own capability cancels the sealed transfer pending
on its endpoint in one run only.  The difference is a derivation the view
leaves out: in one run the offered capability descends from the observer's own
capability, in the other from subject 1's root.

That derivation is the observer's revocation authority, and the full view
contains it (`LeanOS.CompositeFullView`): on the same pair the lineage of the
offered transfer differs, so the two runs are not fully low-equivalent
(`revokeSubtree_own_closed`), and `CompositeFullIsolation.full_step` covers
the revocation for every pair that is.
-/
namespace LeanOS.CompositeFullChannels

open LeanOS
open LeanOS.FailStop
open LeanOS.CompositeSwitchedChannels
open LeanOS.CompositeFullView

/-- The full view tells the subtree pair apart. -/
def facts (plan : BootPageTablePlan.Plan) : Bool :=
  extra 2 (runFrom plan leftTrace) != extra 2 (runFrom plan rightTrace)

set_option maxRecDepth 100000 in
/-- **Kernel evaluation on the canonical sample plan.** -/
theorem facts_sample :
    (match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
      | .ok plan => facts plan
      | .error _ => false) = true := by
  decide +kernel

theorem facts_of_compile {plan : BootPageTablePlan.Plan}
    (hplan : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan) :
    facts plan = true := by
  have h := facts_sample
  rw [hplan] at h
  exact h

/-- **The subtree-revocation channel is closed**: the pair on which the
observer's own subtree revocation was step inconsistent is not fully
low-equivalent, because the lineage of the offered transfer is part of the
observer's authority. -/
theorem revokeSubtree_own_closed (plan : BootPageTablePlan.Plan)
    (hplan : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan) :
    ¬ FullLowEquiv 2 (runFrom plan leftTrace) (runFrom plan rightTrace) := by
  intro hfull
  have h := facts_of_compile hplan
  simp only [facts, hfull.extra, bne_self_eq_false] at h
  cases h

end LeanOS.CompositeFullChannels
