import LeanOS.FaultDispatch

open LeanOS
open LeanOS.FaultDispatch

/- CR2 cannot make a snapshot naming a non-active address space authoritative;
the kernel-selected state remains active on address space 1. -/
example :
    let forged :=
      { pageFaultAgreementWitnessRecord 4 50 with activeAddressSpace := 2 }
    pageFaultAgreementWitnessContained forged = true := by
  native_decide
