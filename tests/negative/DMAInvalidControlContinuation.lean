import LeanOS.DMAQuarantine

open LeanOS DMAQuarantine

-- A bus-master-enabled control observation is invalid and cannot continue.
example :
    (runtimeGate q35Runtime (.observeControl q35BusMasterBitFlipSnapshot)).result =
      .continued := by
  native_decide
