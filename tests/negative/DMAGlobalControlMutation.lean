import LeanOS.FailStop

open LeanOS

-- A changed PCI control observation cannot retain the authoritative global
-- DMA quarantine invariant.
example (state : FailStop.CompositeState)
    (hinvariant : FailStop.RuntimeWellFormed state) :
    ({ state with
      dmaObserved := DMAQuarantine.q35BusMasterBitFlipSnapshot } :
      FailStop.CompositeState).DMAQuarantined := by
  exact hinvariant.dmaQuarantined
