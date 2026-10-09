import LeanOS.FailStop.Scheduler

/-!
# Fail-stop composite: preemption and interrupt faults

Resumable preemption switches, fatal and contained hardware interrupts, and
inbound interrupt cleanup preserve the runtime invariant.
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

private theorem schedulerSelectNext_preserves_capabilities scheduler :
    (Scheduler.selectNext scheduler).state.lifecycle.capabilities =
      scheduler.lifecycle.capabilities := by
  unfold Scheduler.selectNext
  split <;> try simp [Scheduler.reject]
  all_goals split <;> simp [Scheduler.reject]

theorem schedulerTick_preserves_capabilities scheduler :
    (Scheduler.tick scheduler).state.lifecycle.capabilities =
      scheduler.lifecycle.capabilities := by
  unfold Scheduler.tick Scheduler.yield
  split
  · simp [Scheduler.reject]
  next subject hcurrent =>
    split
    · simp [Scheduler.reject]
    · let staged : Scheduler.State :=
        { scheduler with
          ready := scheduler.ready ++ [subject]
          lifecycle := { scheduler.lifecycle with current := none } }
      generalize hselect : Scheduler.selectNext staged = outcome
      cases outcome with
      | mk next result =>
          cases result with
          | rejected reason => simp [Scheduler.reject]
          | accepted context =>
              have hcapabilities : next.lifecycle.capabilities =
                  staged.lifecycle.capabilities := by
                have hstate := congrArg
                  (fun outcome => outcome.state.lifecycle.capabilities) hselect
                rw [schedulerSelectNext_preserves_capabilities] at hstate
                exact hstate.symm
              simpa [staged] using hcapabilities

private theorem resumeSwitch_preserves_capabilities (state : CompositeState) frame registers
    (hcoherent : state.Coherent) :
    ((ResumablePreemption.switch state.resumable state.execution.core frame registers).state.scheduler.lifecycle.capabilities) =
      state.lifecycle.capabilities := by
  have hprojection : state.resumable.scheduler.lifecycle.capabilities =
      state.lifecycle.capabilities := by
    rw [hcoherent.2.2.2.2.2.2.2.1, hcoherent.2.1]
  simp only [ResumablePreemption.switch]
  split <;> try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals
    rw [schedulerTick_preserves_capabilities]
    exact hprojection

private theorem resumeSwitch_preserves_virtualMemory (state : CompositeState) frame registers
    (hcoherent : state.Coherent) :
    ((ResumablePreemption.switch state.resumable state.execution.core frame registers).state.translations.virtual) =
      state.virtualMemory := by
  have hprojection : state.resumable.translations.virtual = state.virtualMemory := by
    exact hcoherent.2.2.2.2.2.2.2.2.1
  simp only [ResumablePreemption.switch]
  split <;> try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals split <;>
    try simpa [ResumablePreemption.reject, ResumablePreemption.halt] using hprojection
  all_goals simpa [TLB.switch] using hprojection

theorem resumeSwitch_halted_preserves_scheduler state interrupt frame registers
    (hhalted : (ResumablePreemption.switch state interrupt frame registers).state.halted = true) :
    (ResumablePreemption.switch state interrupt frame registers).state.scheduler =
      state.scheduler := by
  simp only [ResumablePreemption.switch] at hhalted ⊢
  split <;> try simp_all [ResumablePreemption.reject]
  split <;> try simp_all [ResumablePreemption.reject, ResumablePreemption.halt]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> try simp_all [ResumablePreemption.reject]
  all_goals split <;> simp_all [ResumablePreemption.reject]

/-- Publishing a nonterminal save/select/restore result preserves every
runtime projection.  The resumable model owns the scheduler and translation
updates; this boundary republishes those authoritative views without changing
capability authority, IPC mailboxes, or transfer state. -/
private theorem installResumable_nonfatal_preserves_runtimeWellFormed state next
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hnext : ResumablePreemption.WellFormed next)
    (hcapabilities : next.scheduler.lifecycle.capabilities =
      state.lifecycle.capabilities)
    (hvirtual : next.translations.virtual = state.virtualMemory)
    (hhalted : next.halted = false) :
    RuntimeWellFormed (installResumable state next) := by
  rcases hstate with
    ⟨hcoherent, hexecution, _hlifecycle, hcapabilityWellFormed,
      hvirtualWellFormed, hipc, _hscheduler, hpreemption, _hresumable,
      htransfers, _hterminal, _hlive⟩
  rcases hcoherent with
    ⟨_hexecutionLifecycle, hschedulerLifecycle, _hpreemptionScheduler,
      hcapabilitiesLifecycle, hmemoryCapabilities, hipcVirtual,
      hipcCapabilities, _hresumableScheduler, _htranslationVirtual,
      htransferEndpoints, _hauthority, hdeadMailbox, hliveSender⟩
  have hscheduler' : Scheduler.WellFormed next.scheduler := hnext.1
  have hlifecycle' : SubjectLifecycle.WellFormed next.scheduler.lifecycle :=
    hscheduler'.1
  have hexecution' : WellFormed
      { state.execution with
        core := { state.execution.core with
          lifecycle := next.scheduler.lifecycle
          context := match next.scheduler.lifecycle.current with
            | some subject => { state.execution.core.context with
                currentSubject := subject, activeAddressSpace := subject }
            | none => state.execution.core.context }
        returnAuthorityArmed := false } := by
    refine ⟨?_, by simp, ?_⟩
    · exact hlifecycle'
    · cases hcurrent : next.scheduler.lifecycle.current <;>
        simpa [hcurrent, hmode] using hexecution.2.2
  have hpreemption' : Preemption.WellFormed
      { state.preemption with scheduler := next.scheduler } :=
    ⟨hscheduler', hpreemption.2⟩
  have hipc' : IPCSyscall.WellFormed
      { state.ipc with virtualMemory := state.virtualMemory } := by
    rw [← hipcVirtual]
    exact hipc
  have hcoherent' : (installResumable state next).Coherent := by
    simp [CompositeState.Coherent, installResumable, hvirtual, hcapabilities,
      hmemoryCapabilities, hipcCapabilities, htransferEndpoints,
      hdeadMailbox, hliveSender]
    refine ⟨?_, ?_, ?_⟩
    · intro subject hcurrent
      simp [hcurrent]
    · intro object hdead
      exact hdeadMailbox object (by simp [hdead])
    · exact hliveSender
  refine ⟨hcoherent', hexecution', hlifecycle', ?_, ?_, ?_, hscheduler',
    hpreemption', hnext, htransfers, ?_, ?_⟩
  · simpa [installResumable, hcapabilities, hcapabilitiesLifecycle] using
      hcapabilityWellFormed
  · simpa [installResumable, hvirtual] using hvirtualWellFormed
  · simpa [installResumable, hvirtual] using hipc'
  · simp [installResumable, hhalted, hmode]
  · exact ⟨by simp [installResumable], ⟨⟨rfl, rfl⟩, _hlive.2.2⟩⟩

/-- Every nonfatal resumable preemption step preserves the complete global
runtime invariant.  This includes successful save/select/restore as well as
all typed, state-preserving precondition failures; attacker-controlled frame
and register payloads cannot desynchronize the selected execution identity. -/
theorem gate_resumePreempt_nonfatal_preserves_runtimeWellFormed state frame registers
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hhalted : (ResumablePreemption.switch state.resumable state.execution.core
      frame registers).state.halted = false) :
    RuntimeWellFormed (gate state (.resumePreempt frame registers)).state := by
  have hnext := ResumablePreemption.switch_preserves_wellFormed
    state.resumable state.execution.core frame registers
      hstate.2.2.2.2.2.2.2.2.1
  have hcapabilities := resumeSwitch_preserves_capabilities state frame registers
    hstate.1
  have hvirtual := resumeSwitch_preserves_virtualMemory state frame registers
    hstate.1
  have hpublished := installResumable_nonfatal_preserves_runtimeWellFormed state
    (ResumablePreemption.switch state.resumable state.execution.core frame registers).state
    hstate hmode hnext hcapabilities hvirtual hhalted
  cases herror : (ResumablePreemption.switch state.resumable state.execution.core
      frame registers).error with
  | none => simpa [gate, hmode, applyOperation, herror] using hpublished
  | some reason =>
      cases reason <;> simp [gate, hmode, applyOperation, herror, hhalted, hstate]

private theorem resumeSwitch_halted_requires_fatal_dispatch state frame registers
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hhalted : (ResumablePreemption.switch state.resumable state.execution.core
      frame registers).state.halted = true) :
    ∃ reason, (Interrupt.dispatchHardware state.execution.core frame).action =
      .fatal reason := by
  have hresumable : state.resumable.halted = false := by
    cases hvalue : state.resumable.halted with
    | false => rfl
    | true =>
        obtain ⟨record, hrecord⟩ := hstate.2.2.2.2.2.2.2.2.2.2.1.mp hvalue
        rw [hmode] at hrecord
        contradiction
  simp only [ResumablePreemption.switch, hresumable, Bool.false_eq_true, ite_false]
    at hhalted
  generalize hdispatch : Interrupt.dispatchHardware state.execution.core frame = outcome
    at hhalted
  cases outcome with
  | mk next action =>
      cases action with
      | fatal reason =>
          exact ⟨reason, rfl⟩
      | contained subject =>
          simp [ResumablePreemption.reject, hresumable] at hhalted
      | timer =>
          simp only at hhalted
          split at hhalted <;> try simp_all [ResumablePreemption.reject]
          all_goals split at hhalted <;> try simp_all [ResumablePreemption.reject]
          all_goals split at hhalted <;> try simp_all [ResumablePreemption.reject]
          all_goals split at hhalted <;> try simp_all [ResumablePreemption.reject]
          all_goals split at hhalted <;> try simp_all [ResumablePreemption.reject]
          all_goals split at hhalted <;> try simp_all [ResumablePreemption.reject]
          all_goals split at hhalted <;> try simp_all [ResumablePreemption.reject]
          all_goals split at hhalted <;> try simp_all [ResumablePreemption.reject]
          all_goals split at hhalted <;> try simp_all [ResumablePreemption.reject]
          all_goals split at hhalted <;> try simp_all [ResumablePreemption.reject]
          all_goals split at hhalted <;> simp_all [ResumablePreemption.reject]
      | syscall =>
          simp [ResumablePreemption.reject, hresumable] at hhalted
      | rejected reason =>
          simp [ResumablePreemption.reject, hresumable] at hhalted

private theorem resumeSwitch_halted_state_eq state frame registers
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hhalted : (ResumablePreemption.switch state.resumable state.execution.core
      frame registers).state.halted = true) :
    (ResumablePreemption.switch state.resumable state.execution.core frame registers).state =
      { state.resumable with halted := true } := by
  obtain ⟨reason, hfatal⟩ := resumeSwitch_halted_requires_fatal_dispatch
    state frame registers hstate hmode hhalted
  have hresumable : state.resumable.halted = false := by
    cases hvalue : state.resumable.halted with
    | false => rfl
    | true =>
        obtain ⟨record, hrecord⟩ := hstate.2.2.2.2.2.2.2.2.2.2.1.mp hvalue
        rw [hmode] at hrecord
        contradiction
  simp [ResumablePreemption.switch, hresumable, hfatal, ResumablePreemption.halt]

private theorem fatalInterrupt_dispatchHardware_halts execution frame reason
    (hmode : execution.mode = .running)
    (hentry : execution.core.context.entryActive = false)
    (hfatal : (Interrupt.dispatchHardware execution.core frame).action = .fatal reason) :
    ∃ record, (dispatchHardware execution frame).state.mode = .halted record := by
  simp only [dispatchHardware, hmode, beginEntry, finishEntry, activeEntry]
  have hprepared :
      { execution.core with context :=
        { execution.core.context with entryActive := false } } = execution.core := by
    cases hcore : execution.core with
    | mk lifecycle context =>
        cases hcontext : context with
        | mk current space stack active => simp_all
  rw [hprepared]
  generalize hdispatch : Interrupt.dispatchHardware execution.core frame = outcome
    at hfatal ⊢
  cases outcome with
  | mk next action =>
      cases action <;> simp_all [halt]

private theorem dispatchHardware_preserves_wellFormed_internal state frame
    (hstate : WellFormed state) :
    WellFormed (dispatchHardware state frame).state := by
  rcases hstate with ⟨hlifecycle, hbound, hmodeWellFormed⟩
  change SubjectLifecycle.WellFormed state.core.lifecycle at hlifecycle
  cases hmode : state.mode with
  | handling active =>
      simp only [hmode] at hmodeWellFormed
      simpa [dispatchHardware, hmode, halt, WellFormed, Interrupt.WellFormed] using
        And.intro hlifecycle hmodeWellFormed.2
  | halted record =>
      simpa [dispatchHardware, hmode, WellFormed, Interrupt.WellFormed] using
        And.intro hlifecycle (And.intro hbound hmodeWellFormed)
  | running =>
      simp only [hmode] at hmodeWellFormed
      simp only [dispatchHardware, hmode, beginEntry, finishEntry, activeEntry]
      unfold Interrupt.dispatchHardware
      cases hvector : Interrupt.decodeVector frame.vector with
      | none => simpa [hvector, halt, WellFormed, Interrupt.WellFormed] using hlifecycle
      | some vector =>
          cases vector with
          | pageFault =>
              cases frame.savedPrivilege with
              | kernel =>
                  simpa [hvector, halt, WellFormed, Interrupt.WellFormed] using hlifecycle
              | user =>
                  simpa [hvector, WellFormed, Interrupt.WellFormed] using
                    SubjectLifecycle.terminateState_preserves_wellFormed
                      state.core.lifecycle state.core.context.currentSubject hlifecycle
          | timer => simpa [hvector, WellFormed, Interrupt.WellFormed] using hlifecycle
          | syscall =>
              cases frame.savedPrivilege <;>
                simpa [hvector, WellFormed, Interrupt.WellFormed] using hlifecycle

private theorem dispatchHardware_fatal_halts state frame reason
    (hfatal : (dispatchHardware state frame).action = .fatal reason) :
    ∃ record, (dispatchHardware state frame).state.mode = .halted record := by
  cases hmode : state.mode with
  | handling active =>
      simp [dispatchHardware, hmode, halt] at hfatal ⊢
  | halted record =>
      simp [dispatchHardware, hmode] at hfatal
  | running =>
      simp only [dispatchHardware, hmode, beginEntry, finishEntry, activeEntry] at hfatal ⊢
      generalize hdispatch : Interrupt.dispatchHardware
        { state.core with context := { state.core.context with entryActive := false } }
        frame = outcome at hfatal ⊢
      cases outcome with
      | mk next action => cases action <;> simp_all [halt]

private theorem interruptDispatch_ordinary_state state frame
    (hordinary : (Interrupt.dispatchHardware state frame).action = .timer ∨
      (Interrupt.dispatchHardware state frame).action = .syscall ∨
      ∃ reason, (Interrupt.dispatchHardware state frame).action = .rejected reason) :
    (Interrupt.dispatchHardware state frame).state = state := by
  unfold Interrupt.dispatchHardware at hordinary ⊢
  by_cases hentry : state.context.entryActive
  · simp [hentry] at hordinary
  · simp only [hentry, Bool.false_eq_true, ↓reduceIte] at hordinary ⊢
    cases hvector : Interrupt.decodeVector frame.vector with
    | none => simp [hvector] at hordinary
    | some vector =>
        cases vector with
        | pageFault =>
            cases hprivilege : frame.savedPrivilege <;>
              simp [hvector, hprivilege] at hordinary
        | timer => simp [hvector]
        | syscall =>
            cases hprivilege : frame.savedPrivilege <;>
              simp [hvector, hprivilege] at hordinary ⊢

private theorem dispatchHardware_ordinary_state state frame
    (hmode : state.mode = .running)
    (hentry : state.core.context.entryActive = false)
    (hordinary : (dispatchHardware state frame).action = .timer ∨
      (dispatchHardware state frame).action = .syscall ∨
      ∃ reason, (dispatchHardware state frame).action = .rejected reason) :
    (dispatchHardware state frame).state =
      { state with returnAuthorityArmed := false, copyOverride := false } := by
  simp only [dispatchHardware, hmode, beginEntry, finishEntry, activeEntry] at hordinary ⊢
  have hprepared :
      { state.core with context := { state.core.context with entryActive := false } } =
        state.core := by
    cases hcore : state.core with
    | mk lifecycle context =>
        cases hcontext : context with
        | mk current space stack active => simp_all
  rw [hprepared] at hordinary ⊢
  generalize hdispatch : Interrupt.dispatchHardware state.core frame = outcome
    at hordinary ⊢
  cases outcome with
  | mk next action =>
      cases action with
      | fatal reason => simp [halt] at hordinary
      | contained subject => simp at hordinary
      | timer =>
          have hcore := interruptDispatch_ordinary_state state.core frame
            (Or.inl (by rw [hdispatch]))
          simp_all
      | syscall =>
          have hcore := interruptDispatch_ordinary_state state.core frame
            (Or.inr (Or.inl (by rw [hdispatch])))
          simp_all
      | rejected reason =>
          have hcore := interruptDispatch_ordinary_state state.core frame
            (Or.inr (Or.inr ⟨reason, by rw [hdispatch]⟩))
          simp_all

/-- Closing the kernel-owned copy window changes no component of the global
runtime invariant. -/
private theorem closeCopyWindow_preserves_runtimeWellFormed state
    (hstate : RuntimeWellFormed state) :
    RuntimeWellFormed
      { state with execution := { state.execution with copyOverride := false } } := by
  unfold RuntimeWellFormed CompositeState.Coherent WellFormed ReturnAuthorityBound
    CompositeState.ReturnPlanLive CompositeState.BlockingIPCCoherent at hstate ⊢
  simpa using hstate

/-- Completed ordinary inbound entry clears transient return and copy
authority without changing any authoritative subsystem state. -/
private theorem clearInboundAuthority_preserves_runtimeWellFormed state
    (hstate : RuntimeWellFormed state) :
    RuntimeWellFormed
      { state with execution :=
          { state.execution with returnAuthorityArmed := false, copyOverride := false } } := by
  have hclosed := closeCopyWindow_preserves_runtimeWellFormed state hstate
  unfold RuntimeWellFormed CompositeState.Coherent WellFormed at hclosed ⊢
  rcases hclosed with
    ⟨hcoherent, ⟨hcore, _hbound, hentry⟩, hlifecycle, hcapabilities,
      hvirtual, hipc, hscheduler, hpreemption, hresumable, htransfers,
      hterminal, hlive⟩
  exact ⟨hcoherent, ⟨hcore, by simp, hentry⟩, hlifecycle, hcapabilities,
    hvirtual, hipc, hscheduler, hpreemption, hresumable, htransfers,
    hterminal, ⟨by simp, by simpa [CompositeState.BlockingIPCCoherent] using hlive.2⟩⟩

private theorem installResumable_fatal_preserves_runtimeWellFormed state entry
    (hstate : RuntimeWellFormed state)
    (hentry : WellFormed entry)
    (hentryMode : ∃ record, entry.mode = .halted record) :
    RuntimeWellFormed
      (installResumable { state with execution := entry }
        { state.resumable with halted := true }) := by
  rcases hstate with
    ⟨hcoherent, _hexecution, hlifecycle, hcapabilityWellFormed,
      hvirtualWellFormed, hipc, hschedulerWellFormed, hpreemption, _hresumable,
      htransfers, _hterminal, _hlive⟩
  rcases hcoherent with
    ⟨hexecutionLifecycle, hschedulerLifecycle, hpreemptionScheduler,
      hcapabilitiesLifecycle, hmemoryCapabilities, hipcVirtual,
      hipcCapabilities, hresumableScheduler, htranslationVirtual,
      htransferEndpoints, hauthority, hdeadMailbox, hliveSender⟩
  rcases hentry with ⟨_hentryCore, _hentryBound, hentryWellFormed⟩
  obtain ⟨record, hrecord⟩ := hentryMode
  have hentryExecution : WellFormed
      { entry with
        core := { entry.core with
          lifecycle := state.resumable.scheduler.lifecycle
          context := match state.resumable.scheduler.lifecycle.current with
            | some subject => { entry.core.context with
                currentSubject := subject, activeAddressSpace := subject }
            | none => entry.core.context }
        returnAuthorityArmed := false } := by
    refine ⟨?_, by simp, ?_⟩
    · simpa [Interrupt.WellFormed, hresumableScheduler, hschedulerLifecycle] using
        hlifecycle
    · rw [hrecord]
      cases hcurrent : state.resumable.scheduler.lifecycle.current <;>
        simpa [hcurrent, hrecord] using hentryWellFormed
  have hipc' : IPCSyscall.WellFormed
      { state.ipc with virtualMemory := state.virtualMemory } := by
    rw [← hipcVirtual]
    exact hipc
  have hcoherent' :
      (installResumable { state with execution := entry }
        { state.resumable with halted := true }).Coherent := by
    simp [CompositeState.Coherent, installResumable, hresumableScheduler,
      htranslationVirtual, hschedulerLifecycle, hcapabilitiesLifecycle, hmemoryCapabilities,
      hipcCapabilities, htransferEndpoints, hdeadMailbox, hliveSender]
    refine ⟨?_, ?_, ?_⟩
    · intro subject hcurrent
      simp [hcurrent]
    · intro object hdead
      exact hdeadMailbox object (by simpa [hschedulerLifecycle] using hdead)
    · intro object envelope hmailbox
      exact hliveSender object envelope hmailbox
  refine ⟨hcoherent', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htransfers, ?_, ?_⟩
  · exact hentryExecution
  · simpa [installResumable, hresumableScheduler, hschedulerLifecycle] using hlifecycle
  · simpa [installResumable, hresumableScheduler, hschedulerLifecycle,
      hcapabilitiesLifecycle] using
      hcapabilityWellFormed
  · simpa [installResumable, htranslationVirtual] using hvirtualWellFormed
  · simpa [installResumable, htranslationVirtual] using hipc'
  · simpa [installResumable, hresumableScheduler] using hschedulerWellFormed
  · simpa [installResumable, hresumableScheduler, Preemption.WellFormed] using
      (And.intro hschedulerWellFormed hpreemption.2)
  · simpa [installResumable] using
      (ResumablePreemption.wellFormed_set_halted state.resumable true).2 _hresumable
  · simp [installResumable, hrecord]
  · exact ⟨by simp [installResumable], ⟨⟨rfl, rfl⟩, _hlive.2.2⟩⟩

/-- A resumable-model fatal entry latches the same typed composite fail-stop
mode while freezing the scheduler, context bank, translations, IPC, and
authority projections. -/
theorem gate_resumePreempt_fatal_preserves_runtimeWellFormed state frame registers
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hhalted : (ResumablePreemption.switch state.resumable state.execution.core
      frame registers).state.halted = true) :
    RuntimeWellFormed (gate state (.resumePreempt frame registers)).state := by
  obtain ⟨reason, hfatal⟩ := resumeSwitch_halted_requires_fatal_dispatch
    state frame registers hstate hmode hhalted
  have hentryActive : state.execution.core.context.entryActive = false := by
    simpa [hmode] using hstate.2.1.2.2
  have hentryMode := fatalInterrupt_dispatchHardware_halts state.execution frame reason
    hmode hentryActive hfatal
  have hentryWellFormed : WellFormed (dispatchHardware state.execution frame).state := by
    rcases hstate.2.1 with ⟨hlifecycle, hbound, hmodeWellFormed⟩
    simp only [hmode] at hmodeWellFormed
    simp only [dispatchHardware, hmode, beginEntry, finishEntry, activeEntry]
    unfold Interrupt.dispatchHardware
    cases hvector : Interrupt.decodeVector frame.vector with
    | none => simpa [hvector, halt, WellFormed, Interrupt.WellFormed] using hlifecycle
    | some vector =>
        cases vector with
        | pageFault =>
            cases frame.savedPrivilege with
            | kernel =>
                simpa [hvector, halt, WellFormed, Interrupt.WellFormed] using hlifecycle
            | user =>
                simpa [hvector, WellFormed, Interrupt.WellFormed] using
                  SubjectLifecycle.terminateState_preserves_wellFormed
                    state.execution.core.lifecycle
                    state.execution.core.context.currentSubject hlifecycle
        | timer => simpa [hvector, WellFormed, Interrupt.WellFormed] using hlifecycle
        | syscall =>
            cases frame.savedPrivilege <;>
              simpa [hvector, WellFormed, Interrupt.WellFormed] using hlifecycle
  have hnext := resumeSwitch_halted_state_eq state frame registers hstate hmode hhalted
  have herror := ResumablePreemption.halted_reports_fatalEntry
    state.resumable state.execution.core frame registers hhalted
  have hpublished := installResumable_fatal_preserves_runtimeWellFormed state
    (dispatchHardware state.execution frame).state
    hstate hentryWellFormed hentryMode
  simpa [gate, hmode, applyOperation, herror, hhalted, hnext] using hpublished

/-- Resumable preemption is now a complete composite operation family:
successful switches, typed nonfatal rejection, fatal latching, and outer-gate
absorption all preserve the global runtime invariant. -/
theorem resumePreempt_operationPreservesRuntimeWellFormed frame registers :
    OperationPreservesRuntimeWellFormed (.resumePreempt frame registers) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hhalted : (ResumablePreemption.switch state.resumable
        state.execution.core frame registers).state.halted
    · exact gate_resumePreempt_nonfatal_preserves_runtimeWellFormed
        state frame registers hstate hmode hhalted
    · exact gate_resumePreempt_fatal_preserves_runtimeWellFormed
        state frame registers hstate hmode hhalted
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.resumePreempt frame registers) hstate hmode

/-- An accepted authoritative root switch preserves the global invariant and
publishes the no-PCID full-cache action modeled by `TLB.switch`. -/
theorem gate_resumePreempt_accepted_flushes_translations
    state frame registers
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : (ResumablePreemption.switch state.resumable
      state.execution.core frame registers).error = none) :
    RuntimeWellFormed (gate state (.resumePreempt frame registers)).state ∧
      (gate state (.resumePreempt frame registers)).state.resumable.translations.entries = [] := by
  have hpreserved :=
    resumePreempt_operationPreservesRuntimeWellFormed frame registers state hstate
  refine ⟨hpreserved, ?_⟩
  have hflush :=
    ResumablePreemption.switch_accepted_flushes_translations
      state.resumable state.execution.core frame registers haccepted
  simpa [gate, hmode, applyOperation, haccepted, installResumable] using hflush

/-! ### Inbound interrupt preservation -/

theorem publishInterruptCleanup_preserves_runtimeWellFormed
    state subject (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running) :
    RuntimeWellFormed (publishInterruptCleanup state subject) := by
  have hcleaned := installTerminatedResumable_cleanup_preserves_runtimeWellFormed
    state subject hstate hmode
  have hclosed := closeCopyWindow_preserves_runtimeWellFormed
    (installTerminatedResumable state
      (ResumablePreemption.cleanupSubject state.resumable subject)) hcleaned
  rcases hclosed with
    ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
      hscheduler, hpreemption, hresumable, htransfers, hhalted, hlive, _hblocking,
      hportControls⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [publishInterruptCleanup, CompositeState.Coherent] using hcoherent
  · simpa [publishInterruptCleanup] using hexecution
  · simpa [publishInterruptCleanup] using hlifecycle
  · simpa [publishInterruptCleanup] using hcapabilities
  · simpa [publishInterruptCleanup] using hvirtual
  · simpa [publishInterruptCleanup] using hipc
  · simpa [publishInterruptCleanup] using hscheduler
  · simpa [publishInterruptCleanup] using hpreemption
  · simpa [publishInterruptCleanup] using hresumable
  · simpa [publishInterruptCleanup] using htransfers
  · simpa [publishInterruptCleanup] using hhalted
  · simpa [publishInterruptCleanup, CompositeState.ReturnPlanLive] using hlive
  · simp [publishInterruptCleanup, CompositeState.BlockingIPCCoherent,
      BlockingIPCContext.detachInvalidated, installTerminatedResumable]
  · simpa [publishInterruptCleanup, installTerminatedResumable] using hportControls

/-- Every normalized hardware frame is a complete composite operation family.
Contained user faults reuse authoritative termination cleanup, fatal entry
synchronizes both halt latches, and ordinary timer/syscall/rejection entry only
closes transient return/copy authority.  No branch repairs an unrelated
projection of an invalid pre-state. -/
theorem interrupt_operationPreservesRuntimeWellFormed frame :
    OperationPreservesRuntimeWellFormed (.interrupt frame) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · have hentryActive : state.execution.core.context.entryActive = false := by
      simpa [hmode] using hstate.2.1.2.2
    let entry := dispatchHardware state.execution frame
    have hentryWellFormed : WellFormed entry.state := by
      exact dispatchHardware_preserves_wellFormed_internal
        state.execution frame hstate.2.1
    cases haction : entry.action with
    | contained subject =>
        have hpublished := publishInterruptCleanup_preserves_runtimeWellFormed
          state subject hstate hmode
        by_cases hcurrent : state.lifecycle.current = some subject
        · simpa [gate, hmode, applyOperation, entry, haction, hcurrent] using hpublished
        · simpa [gate, hmode, applyOperation, entry, haction, hcurrent] using hstate
    | fatal reason =>
        have hentryMode : ∃ record, entry.state.mode = .halted record := by
          apply dispatchHardware_fatal_halts state.execution frame reason
          simpa [entry] using haction
        have hpublished := installResumable_fatal_preserves_runtimeWellFormed
          state entry.state hstate hentryWellFormed hentryMode
        simpa [gate, hmode, applyOperation, entry, haction] using hpublished
    | timer =>
        have hordinary := dispatchHardware_ordinary_state state.execution frame
          hmode hentryActive (Or.inl (by simpa [entry] using haction))
        have hcleared := clearInboundAuthority_preserves_runtimeWellFormed state hstate
        simpa [gate, hmode, applyOperation, entry, haction, hordinary] using hcleared
    | syscall =>
        have hordinary := dispatchHardware_ordinary_state state.execution frame
          hmode hentryActive (Or.inr (Or.inl (by simpa [entry] using haction)))
        have hcleared := clearInboundAuthority_preserves_runtimeWellFormed state hstate
        simpa [gate, hmode, applyOperation, entry, haction, hordinary] using hcleared
    | rejected reason =>
        have hordinary := dispatchHardware_ordinary_state state.execution frame
          hmode hentryActive (Or.inr (Or.inr ⟨reason, by simpa [entry] using haction⟩))
        have hcleared := clearInboundAuthority_preserves_runtimeWellFormed state hstate
        simpa [gate, hmode, applyOperation, entry, haction, hordinary] using hcleared
    | alreadyHalted record =>
        have hnotAlready := dispatchHardware_running_not_alreadyHalted
          state.execution frame record hmode
        exact False.elim (hnotAlready (by simpa [entry] using haction))
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.interrupt frame) hstate hmode

end LeanOS.FailStop
