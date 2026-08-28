import LeanOS.BootInterruptPhase

namespace LeanOS.NegativeFixtures.BootPhase

open LeanOS BootInterruptPhase

/- The 64-bit table cannot be published before the 32-bit table. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  (publish { phase := Phase.inherited, business := 90 } TableLoad.publishBootstrap64).outcome =
    Outcome.published Phase.bootstrap64
is false
-/
#guard_msgs in
example :
    (publish (α := UInt64) { phase := .inherited, business := 0x5a }
      .publishBootstrap64).outcome = .published .bootstrap64 := by
  native_decide

/- Runtime publication requires a loaded TSS. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  (publish { phase := Phase.bootstrap64, business := 90 }
        (TableLoad.publishRuntime
          { tssLoaded := false, istStacksInitialized := true, gatesMatchRuntimeManifest := true })).outcome =
    Outcome.published Phase.runtime
is false
-/
#guard_msgs in
example :
    (publish (α := UInt64) { phase := .bootstrap64, business := 0x5a }
      (.publishRuntime ⟨false, true, true⟩)).outcome = .published .runtime := by
  native_decide

/- A terminal latch cannot resume the publication chain. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  (publish { phase := Phase.terminal, latched := some canonicalLatchRecord, business := 90 }
          TableLoad.publishBootstrap32).state.phase =
    Phase.bootstrap32
is false
-/
#guard_msgs in
example :
    (publish (α := UInt64)
      { phase := .terminal, latched := some canonicalLatchRecord, business := 0x5a }
      .publishBootstrap32).state.phase = .bootstrap32 := by
  native_decide

/- Bootstrap vector 2 cannot delegate before the runtime IDT is published. -/
/--
error: Tactic `native_decide` evaluated that the proposition
  (dispatch { phase := Phase.bootstrap64, business := 90 }
        { vector := 2, hasErrorCode := false, fromUser := false }).outcome =
    Outcome.runtimeDelegated 2
is false
-/
#guard_msgs in
example :
    (dispatch (α := UInt64) { phase := .bootstrap64, business := 0x5a }
      ⟨2, false, false⟩).outcome = .runtimeDelegated 2 := by
  native_decide

end LeanOS.NegativeFixtures.BootPhase
