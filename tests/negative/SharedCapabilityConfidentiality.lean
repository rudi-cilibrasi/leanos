import LeanOS.CompositeObservation

open LeanOS LeanOS.FailStop LeanOS.CompositeObservation

/- A capability shared with the observer breaks composite local respect.
Subject 1 revokes the subtree of its endpoint capability; the observer's
capability was derived from it, so the observer's row changes.  The operation
is not silent, so the composite unwinding theorem cannot certify that the
observer's view is unchanged. -/
example (base : CompositeState) :
    LowEquiv 0 (authoritativeGate (Evidence.composite base 7) Evidence.sharedRevoke).state
      (Evidence.composite base 7) :=
  authoritativeGate_silent_observe 0 (Evidence.composite base 7) Evidence.sharedRevoke rfl
