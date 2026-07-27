import LeanOS.DMAQuarantine

open LeanOS DMAQuarantine

-- DeviceContract is integrity-only. It permits distinct device-read
-- observations and therefore cannot prove device-read confidentiality.
example :
    ({ observedByte := 0 } : DeviceReadObservation) =
      ({ observedByte := 1 } : DeviceReadObservation) := by
  exact (device_contract_allows_distinct_reads
    q35Snapshot q35Functions[1]!.bdf zeroMemoryProjection).2
