import LeanOS.NotifyReply

open LeanOS NotifyReply

/- A model in which a reply capability can be copied must be rejected:
`copyReply` is a typed refusal that leaves the system unchanged. -/
example (sys : System) (server : Capability.SubjectId) (r : Nat)
    (destination : Capability.SubjectId) :
    (step sys (.copyReply server r destination)).2 = .accepted := by
  exact copyReply_rejected sys server r destination
