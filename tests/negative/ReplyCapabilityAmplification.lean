import LeanOS.NotifyReply

open LeanOS NotifyReply

/- A weakened no-amplification claim — a reply capability could name a
subject other than the caller — must not follow from the creation theorem. -/
example (sys : System) (t : Transition) (server : Capability.SubjectId) (r : Nat)
    (rc : ReplyCap) (hnew : (step sys t).1.replies server r = some rc)
    (hold : sys.replies server r ≠ some rc) :
    ∃ slot, t = .call server slot := by
  exact reply_created_only_by_call sys t server r rc hnew hold
