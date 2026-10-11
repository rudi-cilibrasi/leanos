import LeanOS.SecurityClaims

open LeanOS

/- After the parent terminates a child and spawns a new one, possibly into the
same child-table slot, the old control word is stale: terminating through it
is rejected and leaves the state unchanged.  A weakened claim in which the old
word still reaches the new child (its termination changes the state) must not
follow from SC-SPAWN-STALE-CHILD. -/
example (state : FailStop.CompositeState) (word : UInt64) (child returned : Nat)
    (accounting : FailStop.ChildAccountingWellFormed state)
    (terminated : (FailStop.terminateChild state word).result = .terminated child returned)
    (request : FailStop.SpawnRequest)
    (same : FailStop.spawnParent
        (FailStop.childGate (FailStop.terminateChild state word).state (.spawn request)).state =
      FailStop.spawnParent state) :
    (FailStop.terminateChild
        (FailStop.childGate (FailStop.terminateChild state word).state (.spawn request)).state
        word).state ≠
      (FailStop.childGate (FailStop.terminateChild state word).state (.spawn request)).state := by
  exact (SecurityClaims.spawn_stale_child_control state word child returned accounting terminated
    request 1 same).2.2.2
