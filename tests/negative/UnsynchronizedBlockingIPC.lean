import LeanOS.FailStop

open LeanOS

/-! A blocking store cannot be replaced independently of the authoritative
composite scheduler while retaining the blocking-IPC coherence claim. -/

def driftBlockingScheduler (state : FailStop.CompositeState)
    (scheduler : Scheduler.State) : FailStop.CompositeState :=
  { state with blockingIPC := { state.blockingIPC with scheduler } }

example (state : FailStop.CompositeState) (scheduler : Scheduler.State)
    (hcoherent : state.BlockingIPCCoherent) :
    (driftBlockingScheduler state scheduler).BlockingIPCCoherent := by
  exact hcoherent
