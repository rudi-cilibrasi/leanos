import LeanOS.CompositeOwnTermination
import LeanOS.CompositeSwitchedChannels

/-!
# Composite unwinding: the observer's timer switch and return path

**The scheduler's state as a public input.**  The claim treats the scheduler's
choice as a public input.  A timer switch and a blocking handoff make that
choice from the scheduler's bookkeeping, which this module therefore makes
public as a whole (`KernelPublic`):

* the ready queue and its capacity;
* which subjects hold a saved context in the resumable bank, and its capacity;
* the waiter-queue capacity of the blocking store.

The capacities are boot configuration.  None of these fields holds another
subject's data: the bank's contexts themselves (frames and registers) stay
hidden; only their owners are public.

**The observer's timer switch** (`resumePreempt` while the observer is
scheduled).  Under `AuthoritativeRuntimeWellFormed` its whole decision is a
function of the frame, the latch, the observer, and `KernelPublic`
(`switch_decision`): every check that reads hidden state (the incoming
context's validity, the bank entry of the observer itself, the active address
space) is decided by the invariant.  The switch then changes only the
scheduled subject in the observer's view (`observe_installResumable_current`),
so it is step and output consistent (`own_step_resumePreempt`,
`own_output_resumePreempt`).  The reply names the next subject only (the
2026-10-10 amendment).

**The return path.**  `selectUserReturn` replies with a constant
(`own_output_selectUserReturn`).  `userReturn` either accepts or latches a
fatal halt; when neither run halts both accept (`own_output_userReturn`), so
the only difference is the termination channel, which the claim excludes.
-/
namespace LeanOS.CompositeOwnSwitch

open LeanOS
open LeanOS.FailStop
open LeanOS.CompositeObservation
open LeanOS.CompositeUnwinding
open LeanOS.CompositeOwnSteps
open LeanOS.CompositeLocalRespect
open LeanOS.CompositeOwnTermination
set_option linter.unusedSimpArgs false

/-- The scheduler's bookkeeping, treated as a public input. -/
structure KernelPublic (left right : CompositeState) : Prop where
  ready : left.scheduler.ready = right.scheduler.ready
  capacity : left.scheduler.capacity = right.scheduler.capacity
  bank : left.resumable.contexts.map (·.owner) = right.resumable.contexts.map (·.owner)
  bankCapacity : left.resumable.capacity = right.resumable.capacity
  waiterCapacity : left.blockingIPC.waiterCapacity = right.blockingIPC.waiterCapacity

theorem KernelPublic.schedulerPublic {left right : CompositeState}
    (h : KernelPublic left right) : SchedulerPublic left right :=
  ⟨h.ready, h.capacity⟩

/-! ## The round-robin step -/

theorem tick_full (scheduler : Scheduler.State) (current : Nat)
    (hcurrent : scheduler.lifecycle.current = some current)
    (hfull : scheduler.ready.length = scheduler.capacity) :
    Scheduler.tick scheduler = { state := scheduler, result := .rejected .queueFull } := by
  unfold Scheduler.tick Scheduler.yield
  simp [hcurrent, hfull, Scheduler.reject]

/-- The round-robin step of a well-formed scheduler with a current subject
and room in its queue: the head of the queue, with the current subject
appended, is scheduled. -/
theorem tick_of_current (scheduler : Scheduler.State) (current : Nat)
    (hwf : Scheduler.WellFormed scheduler)
    (hcurrent : scheduler.lifecycle.current = some current)
    (hroom : scheduler.ready.length ≠ scheduler.capacity)
    (head : Nat) (rest : List Nat) (hlist : scheduler.ready ++ [current] = head :: rest) :
    Scheduler.tick scheduler =
      { state := { scheduler with
          ready := rest
          lifecycle := { scheduler.lifecycle with current := some head } }
        result := .accepted (some ⟨head, head⟩) } := by
  obtain ⟨_, _, _, hreadyValid, hcurrentValid⟩ := hwf
  have hmem : head ∈ scheduler.ready ++ [current] := by rw [hlist]; exact List.mem_cons_self
  have hown : scheduler.lifecycle.addressOwner head = some head := by
    have hsome : Scheduler.ownsAddressSpace scheduler head ≠ none := by
      rw [List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hmem | rfl
      · exact (hreadyValid head hmem).2.2
      · exact (hcurrentValid head hcurrent).2.2.1
    unfold Scheduler.ownsAddressSpace at hsome
    split at hsome
    · assumption
    · contradiction
  unfold Scheduler.tick Scheduler.yield
  simp only [hcurrent, hroom, ↓reduceIte, hlist]
  simp [Scheduler.selectNext, Scheduler.ownsAddressSpace, hown]

/-! ## The switch decision -/

/-- The decision of a timer switch away from the scheduled subject `current`:
the subject restored and the error, as a function of public data. -/
def switchDecision (action : Interrupt.Action) (frameValid : Bool) (ready : List Nat)
    (capacity : Nat) (owners : List Nat) (bankCapacity : Nat) (current : Nat) :
    Option Nat × Option ResumablePreemption.Error :=
  match action with
  | .fatal _ => (none, some .fatalEntry)
  | .timer =>
      if frameValid = false then (none, some .malformedIncoming)
      else if bankCapacity ≤ owners.length then (none, some .bankFull)
      else if ready.length = capacity then (none, some .schedulerRejected)
      else
        match ready ++ [current] with
        | [] => (none, some .noDestination)
        | head :: _ => if head ∈ owners then (some head, none) else (none, some .noDestination)
  | _ => (none, some .nonTimer)

theorem contextFor_some_iff (contexts : List ResumablePreemption.Context) (subject : Nat) :
    (ResumablePreemption.contextFor contexts subject).isSome = true ↔
      subject ∈ contexts.map (·.owner) := by
  simp only [ResumablePreemption.contextFor, List.find?_isSome, List.mem_map, beq_iff_eq]

/-- **The switch decision is public.**  For a well-formed bank whose scheduled
subject is the interrupted context's subject, the restored subject and the
error of a resumable switch are `switchDecision` of the hardware action, the
frame's validity, and the public scheduler bookkeeping. -/
theorem switch_decision (resumable : ResumablePreemption.State) (core : Interrupt.State)
    (frame : Interrupt.HardwareFrame) (registers : ResumablePreemption.Registers)
    (current : Nat)
    (hwf : ResumablePreemption.WellFormed resumable)
    (hcurrent : resumable.scheduler.lifecycle.current = some current)
    (hsubject : core.context.currentSubject = current)
    (hspace : core.context.activeAddressSpace = current)
    (hhalted : resumable.halted = false) :
    ((ResumablePreemption.switch resumable core frame registers).restored.map (·.owner),
      (ResumablePreemption.switch resumable core frame registers).error) =
      switchDecision (Interrupt.dispatchHardware core frame).action
        (Interrupt.validSavedUserFrame frame) resumable.scheduler.ready
        resumable.scheduler.capacity (resumable.contexts.map (·.owner)) resumable.capacity
        current := by
  obtain ⟨hscheduler, _hlength, _hunique, hvalid, habsent, _hready, htranslation, _hvirtual,
    _hkinds, _htlb⟩ := hwf
  have hactive : resumable.translations.active = some current := by
    have := htranslation.2
    rw [hcurrent] at this
    exact this
  have hownCurrent : resumable.scheduler.lifecycle.addressOwner current = some current := by
    have hsome := (hscheduler.2.2.2.2 current hcurrent).2.2.1
    unfold Scheduler.ownsAddressSpace at hsome
    split at hsome
    · assumption
    · contradiction
  have hvirtualOwner : resumable.translations.virtual.owner current = some current := by
    rw [htranslation.1]; exact hownCurrent
  have hnoSave : ResumablePreemption.contextFor resumable.contexts current = none :=
    habsent current hcurrent
  unfold ResumablePreemption.switch switchDecision
  simp only [hhalted]
  generalize haction : (Interrupt.dispatchHardware core frame).action = action
  cases action
  all_goals try (simp [ResumablePreemption.reject, ResumablePreemption.halt]; done)
  by_cases hframe : Interrupt.validSavedUserFrame frame = false
  · simp [hframe, ResumablePreemption.reject]
  have hframeTrue : Interrupt.validSavedUserFrame frame = true := by simpa using hframe
  simp only [hframeTrue, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hcurrent,
    hsubject, hspace, hactive, hvirtualOwner, hnoSave, Option.isSome_none, bne_self_eq_false,
    Bool.or_self, ne_eq, not_true_eq_false, or_self]
  by_cases hbank : resumable.capacity ≤ resumable.contexts.length
  · simp [hbank, ResumablePreemption.reject]
  simp only [hbank, ↓reduceIte, List.length_map]
  by_cases hfull : resumable.scheduler.ready.length = resumable.scheduler.capacity
  · rw [tick_full _ current hcurrent hfull]
    simp [hfull, ResumablePreemption.reject]
  simp only [hfull, ↓reduceIte]
  obtain ⟨head, rest, hlist⟩ :
      ∃ head rest, resumable.scheduler.ready ++ [current] = head :: rest := by
    cases h : resumable.scheduler.ready ++ [current] with
    | nil => simp at h
    | cons head rest => exact ⟨head, rest, rfl⟩
  rw [tick_of_current _ current hscheduler hcurrent hfull head rest hlist]
  simp only [hlist]
  cases hfind : ResumablePreemption.contextFor resumable.contexts head with
  | none =>
      have hnot : head ∉ resumable.contexts.map (·.owner) := by
        intro hmem
        have := (contextFor_some_iff resumable.contexts head).2 hmem
        rw [hfind] at this
        cases this
      simp [hnot, ResumablePreemption.reject]
  | some destination =>
      have hmem : head ∈ resumable.contexts.map (·.owner) :=
        (contextFor_some_iff resumable.contexts head).1 (by rw [hfind]; rfl)
      have hdmem : destination ∈ resumable.contexts := List.mem_of_find?_eq_some hfind
      have hdowner : destination.owner = head := by
        have := List.find?_some hfind
        simpa using this
      obtain ⟨hdframe, hdspace, hdlive, hdrunnable, hdaddress⟩ := hvalid destination hdmem
      have hdvirtual : resumable.translations.virtual.owner destination.addressSpace =
          some destination.owner := by
        rw [htranslation.1]; exact hdaddress
      simp only [hdspace, hdowner] at hdlive hdrunnable hdaddress hdvirtual
      simp [hmem, hdframe, hdspace, hdowner, hdlive, hdrunnable, hdvirtual, hdaddress]

/-- An accepted round-robin yield changes only the scheduled subject of the
lifecycle. -/
theorem yield_accepted_lifecycle (scheduler : Scheduler.State)
    (selected : Scheduler.TrustedContext)
    (haccepted : (Scheduler.yield scheduler).result = .accepted (some selected)) :
    (Scheduler.yield scheduler).state.lifecycle =
      { scheduler.lifecycle with current := some selected.currentSubject } := by
  revert haccepted
  unfold Scheduler.yield Scheduler.selectNext
  repeat' split
  all_goals simp_all [Scheduler.reject]
  intro h
  subst h
  rfl

/-- On success the switch schedules exactly the restored subject, with the
lifecycle otherwise unchanged, and keeps the virtual-memory translation. -/
theorem switch_success_state (resumable : ResumablePreemption.State) (core : Interrupt.State)
    (frame : Interrupt.HardwareFrame) (registers : ResumablePreemption.Registers)
    (restored : ResumablePreemption.Context)
    (hrestored : (ResumablePreemption.switch resumable core frame registers).restored =
      some restored) :
    (ResumablePreemption.switch resumable core frame registers).state.scheduler.lifecycle =
        { resumable.scheduler.lifecycle with current := some restored.owner } ∧
      (ResumablePreemption.switch resumable core frame registers).state.translations.virtual =
        resumable.translations.virtual := by
  refine ⟨?_, CompositeSwitchedChannels.switch_translations_virtual resumable core frame
    registers⟩
  revert hrestored
  unfold ResumablePreemption.switch
  generalize htick : Scheduler.tick resumable.scheduler = scheduled
  rcases scheduled with ⟨next, (_ | selected) | reason⟩
  all_goals
    repeat' split
  all_goals simp [ResumablePreemption.reject, ResumablePreemption.halt]
  cases hctx : ResumablePreemption.contextFor resumable.contexts selected.currentSubject with
  | none => simp
  | some destination =>
      simp only
      split
      · simp
      · rename_i hcheck
        intro h
        simp only [Option.some.injEq] at h
        subst h
        simp only [not_or, Decidable.not_not] at hcheck
        have hlifecycle := yield_accepted_lifecycle resumable.scheduler selected
          (by rw [show Scheduler.yield resumable.scheduler = Scheduler.tick resumable.scheduler
            from rfl, htick])
        rw [show Scheduler.yield resumable.scheduler = Scheduler.tick resumable.scheduler
          from rfl, htick] at hlifecycle
        simp only at hlifecycle ⊢
        rw [hlifecycle, hcheck.1.1.1.1.1.2]

theorem switch_restored_of_error (resumable : ResumablePreemption.State)
    (core : Interrupt.State) (frame : Interrupt.HardwareFrame)
    (registers : ResumablePreemption.Registers)
    (herror : (ResumablePreemption.switch resumable core frame registers).error = none) :
    (ResumablePreemption.switch resumable core frame registers).restored.isSome = true := by
  revert herror
  unfold ResumablePreemption.switch
  generalize Scheduler.tick resumable.scheduler = scheduled
  rcases scheduled with ⟨next, (_ | selected) | reason⟩
  all_goals
    simp only
    repeat' split
  all_goals simp [ResumablePreemption.reject, ResumablePreemption.halt]

/-! ## The view after a switch -/

/-- Installing a bank whose scheduler differs only in the scheduled subject,
with the same virtual-memory translation, changes only the scheduled subject
in every view. -/
theorem observe_installResumable_current (observer : Nat) (state : CompositeState)
    (resumable : ResumablePreemption.State) (current : Option Nat)
    (hcoherent : state.Coherent)
    (hlifecycle : resumable.scheduler.lifecycle = { state.lifecycle with current })
    (hvirtual : resumable.translations.virtual = state.virtualMemory) :
    observe observer (installResumable state resumable) =
      { observe observer state with scheduled := current } := by
  have hcapabilities := capabilities_eq_lifecycle hcoherent
  simp only [observe, installResumable, hlifecycle, hvirtual, row, objectView, backing,
    ← hcapabilities]

/-! ## The observer's timer switch -/

/-- The public data of a switch, from the composite state. -/
def switchDecisionOf (state : CompositeState) (observer : Nat) (frame : Interrupt.HardwareFrame) :
    Option Nat × Option ResumablePreemption.Error :=
  switchDecision (Interrupt.dispatchHardware state.execution.core frame).action
    (Interrupt.validSavedUserFrame frame) state.scheduler.ready state.scheduler.capacity
    (state.resumable.contexts.map (·.owner)) state.resumable.capacity observer

theorem switch_decision_of {observer : Nat} {state : CompositeState}
    (hstate : RuntimeWellFormed state) (hcurrent : state.lifecycle.current = some observer)
    (hmode : state.execution.mode = .running) (frame : Interrupt.HardwareFrame)
    (registers : ResumablePreemption.Registers) :
    ((ResumablePreemption.switch state.resumable state.execution.core frame
        registers).restored.map (·.owner),
      (ResumablePreemption.switch state.resumable state.execution.core frame registers).error) =
      switchDecisionOf state observer frame := by
  have hcoherent := hstate.1
  have hresumableScheduler : state.resumable.scheduler = state.scheduler :=
    hcoherent.2.2.2.2.2.2.2.1
  have hhalted : state.resumable.halted = false := by
    cases h : state.resumable.halted
    · rfl
    · obtain ⟨record, hrecord⟩ := hstate.2.2.2.2.2.2.2.2.2.2.1.1 h
      rw [hmode] at hrecord
      cases hrecord
  obtain ⟨hsubject, hspace⟩ := actor_of_current hcoherent hcurrent
  have h := switch_decision state.resumable state.execution.core frame registers observer
    hstate.2.2.2.2.2.2.2.2.1 (by rw [resumable_lifecycle hcoherent]; exact hcurrent)
    hsubject hspace hhalted
  rw [h, hresumableScheduler]
  rfl

/-- Two states of an `OwnStep` pair with public scheduler bookkeeping make the
same switch decision. -/
theorem switchDecisionOf_eq {observer : Nat} {left right : CompositeState}
    (h : OwnStep observer left right) (hpublic : KernelPublic left right)
    (hmode : left.execution.mode = .running) (frame : Interrupt.HardwareFrame) :
    switchDecisionOf left observer frame = switchDecisionOf right observer frame := by
  have hentry : left.execution.core.context.entryActive = false := by
    have := h.leftWF.2.1.2.2
    rw [hmode] at this
    exact this
  have hentryRight : right.execution.core.context.entryActive = false := by
    have := h.rightWF.2.1.2.2
    rw [← h.mode, hmode] at this
    exact this
  have haction := interrupt_action_eq left.execution.core right.execution.core frame
    (hentry.trans hentryRight.symm) (h.leftActor.1.trans h.rightActor.1.symm)
  simp only [switchDecisionOf, haction, hpublic.ready, hpublic.capacity, hpublic.bank,
    hpublic.bankCapacity]

/-- The observer's view after its own switch: the scheduled subject is the
restored one when the switch succeeds, and the view is otherwise unchanged. -/
theorem observe_apply_resumePreempt_own {observer : Nat} {state : CompositeState}
    (hstate : RuntimeWellFormed state) (frame : Interrupt.HardwareFrame)
    (registers : ResumablePreemption.Registers) :
    observe observer (applyOperation state (.resumePreempt frame registers)) =
      match (ResumablePreemption.switch state.resumable state.execution.core frame
          registers).error with
      | none =>
          { observe observer state with
            scheduled := (ResumablePreemption.switch state.resumable state.execution.core frame
              registers).restored.map (·.owner) }
      | some _ => observe observer state := by
  have hcoherent := hstate.1
  simp only [applyOperation]
  generalize houtcome : ResumablePreemption.switch state.resumable state.execution.core frame
    registers = outcome
  rcases outcome with ⟨resumable, restored, error⟩
  cases error with
  | none =>
      simp only
      cases restored with
      | none =>
          have := switch_restored_of_error state.resumable state.execution.core frame
            registers (by rw [houtcome])
          rw [houtcome] at this
          simp at this
      | some context =>
          obtain ⟨hlifecycle, hvirtual⟩ := switch_success_state state.resumable
            state.execution.core frame registers context (by rw [houtcome])
          rw [houtcome] at hlifecycle hvirtual
          simp only at hlifecycle hvirtual
          rw [resumable_lifecycle hcoherent] at hlifecycle
          exact observe_installResumable_current observer state resumable _ hcoherent
            hlifecycle (hvirtual.trans (translations_eq hcoherent))
  | some reason =>
      simp only
      have herror : (ResumablePreemption.switch state.resumable state.execution.core frame
          registers).error.isSome = true := by rw [houtcome]; rfl
      obtain ⟨hscheduler, htranslations⟩ := switch_error_frame _ _ _ _ herror
      rw [houtcome] at hscheduler htranslations
      split
      · split
        · exact observe_installResumable observer _ _
            (resumable_lifecycle (state := state) hcoherent)
            (capabilities_eq_lifecycle (state := state) hcoherent)
            (translations_eq (state := state) hcoherent) hscheduler (by rw [htranslations])
        · rfl
      · rfl
      · simp_all

/-- **Step consistency of the observer's timer switch**, with the scheduler's
bookkeeping public. -/
theorem own_step_resumePreempt {observer : Nat} {left right : CompositeState}
    (h : OwnStep observer left right) (hpublic : KernelPublic left right)
    (frame : Interrupt.HardwareFrame) (registers : ResumablePreemption.Registers) :
    LowEquiv observer
      (authoritativeGate left (.ordinary (.resumePreempt frame registers))).state
      (authoritativeGate right (.ordinary (.resumePreempt frame registers))).state := by
  rw [authoritativeGate_ordinary_state, authoritativeGate_ordinary_state]
  cases hmode : left.execution.mode with
  | handling entry =>
      have hright : right.execution.mode = .handling entry := h.mode ▸ hmode
      simp only [gate, hmode, hright]
      exact h.low
  | halted record =>
      have hright : right.execution.mode = .halted record := h.mode ▸ hmode
      simp only [gate, hmode, hright]
      exact h.low
  | running =>
      have hright : right.execution.mode = .running := h.mode ▸ hmode
      simp only [gate, hmode, hright]
      have hdecision := (switch_decision_of h.leftWF h.current hmode frame registers).trans
        ((switchDecisionOf_eq h hpublic hmode frame).trans
          (switch_decision_of h.rightWF h.rightCurrent hright frame registers).symm)
      simp only [Prod.mk.injEq] at hdecision
      unfold LowEquiv
      rw [observe_apply_resumePreempt_own h.leftWF, observe_apply_resumePreempt_own h.rightWF,
        hdecision.1, hdecision.2, h.low]

/-- **Output consistency of the observer's timer switch**, with the scheduler's
bookkeeping public: the reply is the restored subject and the error, both
public. -/
theorem own_output_resumePreempt {observer : Nat} {left right : CompositeState}
    (h : OwnStep observer left right) (hpublic : KernelPublic left right)
    (frame : Interrupt.HardwareFrame) (registers : ResumablePreemption.Registers) :
    (authoritativeGate left (.ordinary (.resumePreempt frame registers))).result =
      (authoritativeGate right (.ordinary (.resumePreempt frame registers))).result := by
  cases hmode : left.execution.mode with
  | handling entry =>
      have hright : right.execution.mode = .handling entry := h.mode ▸ hmode
      simp [authoritativeGate, hmode, hright]
  | halted record =>
      have hright : right.execution.mode = .halted record := h.mode ▸ hmode
      simp [authoritativeGate, hmode, hright]
  | running =>
      apply authoritativeGate_result_of_reply left right _ (not_nmi_of rfl) h.mode
      have hdecision := (switch_decision_of h.leftWF h.current hmode frame registers).trans
        ((switchDecisionOf_eq h hpublic hmode frame).trans
          (switch_decision_of h.rightWF h.rightCurrent (h.mode ▸ hmode) frame registers).symm)
      simp only [Prod.mk.injEq] at hdecision
      simp only [operationReply, hdecision.1, hdecision.2]

/-! ## The return path -/

/-- **Return-authority selection replies with a constant.** -/
theorem own_output_selectUserReturn {observer : Nat} {left right : CompositeState}
    (h : OwnStep observer left right) (purpose : Interrupt.ReturnPurpose) :
    (authoritativeGate left (.ordinary (.selectUserReturn purpose))).result =
      (authoritativeGate right (.ordinary (.selectUserReturn purpose))).result :=
  authoritativeGate_result_of_reply left right _ (not_nmi_of rfl) h.mode rfl

/-- A user return from a running latch accepts in place or latches a fatal
halt. -/
theorem completeUserReturn_running (execution : FailStop.State)
    (request : Interrupt.UserReturnRequest) (hrun : execution.mode = .running) :
    (∃ attested, (completeUserReturn execution request).action = .accepted attested ∧
        (completeUserReturn execution request).state = execution) ∨
      (∃ record, (completeUserReturn execution request).action = .fatal record ∧
        (completeUserReturn execution request).state.mode = .halted record) := by
  unfold completeUserReturn
  simp only [hrun]
  split
  · exact .inr ⟨_, rfl, rfl⟩
  · split
    · exact .inl ⟨_, rfl, rfl⟩
    · exact .inr ⟨_, rfl, rfl⟩

/-- The latch has not halted. -/
def Continues (state : CompositeState) : Prop :=
  ∀ record, state.execution.mode ≠ .halted record

/-- **The user return differs only by halting.**  When neither run's user
return halts the machine, both accept: every rejection of a user return
latches a fatal halt, so the only observable difference is the termination
channel, which the claim excludes. -/
theorem own_output_userReturn {observer : Nat} {left right : CompositeState}
    (h : OwnStep observer left right) (request : Interrupt.UserReturnRequest)
    (hleft : Continues (authoritativeGate left (.ordinary (.userReturn request))).state)
    (hright : Continues (authoritativeGate right (.ordinary (.userReturn request))).state) :
    (authoritativeGate left (.ordinary (.userReturn request))).result =
      (authoritativeGate right (.ordinary (.userReturn request))).result := by
  have accepted : ∀ state : CompositeState, state.execution.mode = .running →
      Continues (authoritativeGate state (.ordinary (.userReturn request))).state →
      operationReply state (.userReturn request) = .userReturn .accepted := by
    intro state hrun hcontinues
    have hgate : (authoritativeGate state (.ordinary (.userReturn request))).state =
        applyOperation state (.userReturn request) := by
      simp [authoritativeGate, hrun, applyAuthoritativeOperation]
    rw [hgate] at hcontinues
    simp only [applyOperation] at hcontinues
    simp only [operationReply]
    generalize hexecution : (if state.ReturnPlanLive then state.execution
      else { state.execution with returnAuthorityArmed := false }) = execution at hcontinues ⊢
    have hmode : execution.mode = .running := by
      rw [← hexecution]; split <;> exact hrun
    rcases completeUserReturn_running execution request hmode with
      ⟨attested, haction, _⟩ | ⟨record, haction, hhalted⟩
    · rw [haction]
    · rw [haction] at hcontinues ⊢
      simp only at hcontinues
      exact absurd hhalted (hcontinues record)
  cases hmode : left.execution.mode with
  | handling entry =>
      have hrightMode : right.execution.mode = .handling entry := h.mode ▸ hmode
      simp [authoritativeGate, hmode, hrightMode]
  | halted record =>
      have hrightMode : right.execution.mode = .halted record := h.mode ▸ hmode
      simp [authoritativeGate, hmode, hrightMode]
  | running =>
      apply authoritativeGate_result_of_reply left right _ (not_nmi_of rfl) h.mode
      rw [accepted left hmode hleft, accepted right (h.mode ▸ hmode) hright]

end LeanOS.CompositeOwnSwitch
