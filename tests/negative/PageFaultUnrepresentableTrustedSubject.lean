import LeanOS.InterruptEntry

open LeanOS InterruptEntry

/-- A trusted `Nat` subject outside the canonical identity word domain cannot
alias the encoded subject after truncation modulo `2^64`. -/
example :
    (authorizeCanonicalPageFault
      (encodeCanonicalPageFault canonicalPageFaultExample)
      { canonicalPageFaultExampleContext with
        entry :=
          { canonicalPageFaultExampleContext.entry with
            currentSubject := 2 ^ 64 + 1 } }
      ()).authorized = some canonicalPageFaultExample := by
  native_decide
