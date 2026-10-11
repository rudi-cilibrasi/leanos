import LeanOS.CompositeRegisterChannels

open LeanOS LeanOS.FailStop LeanOS.CompositeChannels LeanOS.CompositeSwitchedChannels
open LeanOS.CompositeRegisterChannels

/- `#542` proved that the replies of the observer's timer switch, blocking send
and wait cancellation carried another subject's saved registers
(`CompositeRegisterChannels.legacy_replies_leaked` keeps that record).  The
replies now name a subject only.  Restating the old channel theorems of the
new replies must fail: on the canonical sample plan the kernel evaluates both
sides to the same reply. -/

/- The observer's timer switch no longer reveals the next subject's
registers. -/
example :
    (match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
      | .ok plan =>
          reply (runFrom plan preemptLeftTrace) preempt !=
            reply (runFrom plan preemptRightTrace) preempt
      | .error _ => false) = true := by
  decide +kernel

/- The observer's waking blocking send no longer reveals the woken subject's
registers. -/
example :
    (match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
      | .ok plan =>
          (authoritativeGate (runFrom plan blockedLeftTrace) blockingSend).result !=
            (authoritativeGate (runFrom plan blockedRightTrace) blockingSend).result
      | .error _ => false) = true := by
  decide +kernel
