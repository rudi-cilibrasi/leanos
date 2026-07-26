import LeanOS.FailStop

open LeanOS

-- A changed PCI control observation cannot retain the authoritative global
-- DMA quarantine invariant.
example (state : FailStop.CompositeState)
    (hinvariant : state.DMAQuarantined) :
    ({ state with
      dmaObserved := DMAQuarantine.q35BusMasterBitFlipSnapshot } :
      FailStop.CompositeState).DMAQuarantined := by
  exact hinvariant
