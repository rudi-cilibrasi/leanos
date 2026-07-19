import LeanOS.DMAQuarantine

open LeanOS DMAQuarantine

-- A changed observed control snapshot cannot be reported as continued.
example (state : RuntimeState) (snapshot : Snapshot)
    (hrunning : state.mode = .running) (hchanged : snapshot ≠ state.accepted.snapshot) :
    (runtimeGate state (.observeControl snapshot)).result = .continued := by
  exact changed_control_is_fatal state snapshot hrunning hchanged
