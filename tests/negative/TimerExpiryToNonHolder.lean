import LeanOS.SecurityClaims

open LeanOS

/- The PIT expiry must reach only the timer-capability holder.  A weakened
capability claim in which the expiry interrupt also signals a subject that
does not hold the timer capability must not follow from the footprint
theorem, which says such a subject's expiry bits are unchanged. -/
example (sys : TimerServer.System) (s : TimerServer.SubjectId)
    (hs : sys.auth.timerHolder ≠ some s) :
    (TimerServer.step sys .expire).1.expiries s = sys.expiries s + 1 := by
  exact (TimerServer.expire_footprint sys).2.2.2.2.2.2 s hs
