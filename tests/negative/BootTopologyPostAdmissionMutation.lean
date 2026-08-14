import LeanOS.BootTopology

open LeanOS.BootTopology

def admitted : AdmissionState :=
  (consumeBootAdmission bootAdmissionInitial
    (decodeAndAdmitMadt repositoryMadtRecords 0 0)).business

/- The finite runtime vocabulary cannot erase the published admission premise. -/
example : (runRuntime admitted [.initialize, .dispatch]).singleCoreAdmitted = false := by
  native_decide
