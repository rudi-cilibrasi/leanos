import LeanOS.InterruptEntry
import LeanOS.X86PageTable

open LeanOS InterruptEntry

namespace LeanOS.NegativeFixtures.PageFaultProvenance

/- A caller-selected execute tag cannot relabel a raw user-read error word. -/
/- error: Tactic `native_decide` evaluated that the proposition -/
#guard_msgs (substring := true) in
example :
    (DecodedPageFaultError.mk false false true false).accessKind =
        X86PageTable.AccessKind.execute := by
  native_decide

/- Serialized subject identity cannot replace the trusted current subject. -/
/- error: Tactic `native_decide` evaluated that the proposition -/
#guard_msgs (substring := true) in
example :
    (authorizeCanonicalPageFault
      (encodeCanonicalPageFault
        { canonicalPageFaultExample with currentSubject := 2 })
      canonicalPageFaultExampleContext ()).authorized =
        some { canonicalPageFaultExample with currentSubject := 2 } := by
  native_decide

/- Serialized address-space identity cannot replace trusted containment state. -/
/- error: Tactic `native_decide` evaluated that the proposition -/
#guard_msgs (substring := true) in
example :
    (authorizeCanonicalPageFault
      (encodeCanonicalPageFault
        { canonicalPageFaultExample with activeAddressSpace := 2 })
      canonicalPageFaultExampleContext ()).authorized =
        some { canonicalPageFaultExample with activeAddressSpace := 2 } := by
  native_decide

/- Trusted identities outside the canonical word domain cannot alias after truncation. -/
/- error: Tactic `native_decide` evaluated that the proposition -/
#guard_msgs (substring := true) in
example :
    (authorizeCanonicalPageFault
      (encodeCanonicalPageFault canonicalPageFaultExample)
      { canonicalPageFaultExampleContext with
        entry :=
          { canonicalPageFaultExampleContext.entry with
            currentSubject := 2 ^ 64 + 1 } }
      ()).authorized = some canonicalPageFaultExample := by
  native_decide

/- Trusted address-space identities outside the word domain cannot alias. -/
/- error: Tactic `native_decide` evaluated that the proposition -/
#guard_msgs (substring := true) in
example :
    (authorizeCanonicalPageFault
      (encodeCanonicalPageFault canonicalPageFaultExample)
      { canonicalPageFaultExampleContext with
        entry :=
          { canonicalPageFaultExampleContext.entry with
            activeAddressSpace := 2 ^ 64 + 1 } }
      ()).authorized = some canonicalPageFaultExample := by
  native_decide

/- Serialized CR3 cannot replace the independently trusted active root. -/
/- error: Tactic `native_decide` evaluated that the proposition -/
#guard_msgs (substring := true) in
example :
    (authorizeCanonicalPageFault
      (encodeCanonicalPageFault
        { canonicalPageFaultExample with activeCr3 := 0x2000 })
      canonicalPageFaultExampleContext ()).authorized =
        some { canonicalPageFaultExample with activeCr3 := 0x2000 } := by
  native_decide

/- Serialized control bits cannot replace independently trusted controls. -/
/- error: Tactic `native_decide` evaluated that the proposition -/
#guard_msgs (substring := true) in
example :
    (authorizeCanonicalPageFault
      (encodeCanonicalPageFault
        { canonicalPageFaultExample with controlsCode := 14 })
      canonicalPageFaultExampleContext ()).authorized =
        some { canonicalPageFaultExample with controlsCode := 14 } := by
  native_decide

/- error: Tactic `native_decide` evaluated that the proposition -/
#guard_msgs (substring := true) in
example :
    (authorizeCanonicalPageFault
      (encodeCanonicalPageFault
        { canonicalPageFaultExample with controlsCode := 13 })
      canonicalPageFaultExampleContext ()).authorized =
        some { canonicalPageFaultExample with controlsCode := 13 } := by
  native_decide

/- error: Tactic `native_decide` evaluated that the proposition -/
#guard_msgs (substring := true) in
example :
    (authorizeCanonicalPageFault
      (encodeCanonicalPageFault
        { canonicalPageFaultExample with controlsCode := 11 })
      canonicalPageFaultExampleContext ()).authorized =
        some { canonicalPageFaultExample with controlsCode := 11 } := by
  native_decide

/- error: Tactic `native_decide` evaluated that the proposition -/
#guard_msgs (substring := true) in
example :
    (authorizeCanonicalPageFault
      (encodeCanonicalPageFault
        { canonicalPageFaultExample with controlsCode := 7 })
      canonicalPageFaultExampleContext ()).authorized =
        some { canonicalPageFaultExample with controlsCode := 7 } := by
  native_decide

/- A saved user selector outside the reviewed codec profile is rejected. -/
/- error: Tactic `native_decide` evaluated that the proposition -/
#guard_msgs (substring := true) in
example :
    validCanonicalPageFault { canonicalPageFaultExample with cs := 7 } = true := by
  native_decide

/- A noncanonical saved instruction pointer is rejected. -/
/- error: Tactic `native_decide` evaluated that the proposition -/
#guard_msgs (substring := true) in
example :
    validCanonicalPageFault
      { canonicalPageFaultExample with rip := 0x0000800000000000 } = true := by
  native_decide

/- The inbound record cannot erase its kernel entry-stack identity. -/
/- error: Tactic `native_decide` evaluated that the proposition -/
#guard_msgs (substring := true) in
example :
    validCanonicalPageFault
      { canonicalPageFaultExample with stackIdentity := 0 } = true := by
  native_decide

end LeanOS.NegativeFixtures.PageFaultProvenance
