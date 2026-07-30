import LeanOS.FailStop

open LeanOS

/- A rejected machine acknowledgement cannot mutate any authoritative runtime
projection. This deliberately contradictory fixture protects the public
current-unmap completion stutter theorem. -/
example state ack
    (hrejected :
      (FailStop.authoritativeAcknowledgeCurrentUnmap state ack).accepted =
        false) :
    (FailStop.authoritativeAcknowledgeCurrentUnmap state ack).state ≠ state := by
  exact
    (FailStop.authoritativeAcknowledgeCurrentUnmap_rejected_inert
      state ack hrejected).1
