import LeanOS.CompositeLocalRespect

/-!
# Composite unwinding: the observer's own termination and kernel entries

When the scheduled observer terminates itself (`terminateSubject` of itself or
`terminateCurrent`), or a contained fault terminates it, everything it could
see disappears: its row is emptied, it owns no address space, nothing is
scheduled, and it waits on nothing.  Its view after the step is therefore a
function of two fields of its view before it, the slot capacity and its
blocking completion (`deadView`), so the step is step consistent
(`own_step_terminate_self`, `own_step_terminateCurrent`).

Kernel entries depend on the observer only through the scheduled subject and
the fail-stop mode.  An interrupt's classification reads the frame, the mode,
and the current subject; a contained fault terminates the observer as above,
and every other classification leaves its view unchanged.  So interrupts are
step and output consistent (`own_step_interrupt`, `own_output_interrupt`), and
an NMI, which only latches the halt, is output consistent
(`own_output_nmi`).

These theorems need the blocking-store well-formedness that
`AuthoritativeRuntimeWellFormed` carries: the scheduled observer waits on no
endpoint.
-/
namespace LeanOS.CompositeOwnTermination

open LeanOS
open LeanOS.FailStop
open LeanOS.CompositeObservation
open LeanOS.CompositeUnwinding
open LeanOS.CompositeOwnSteps
set_option linter.unusedSimpArgs false

/-- The view of a terminated observer with the given slot capacity and
blocking completion. -/
def deadView (capacity : Nat) (completion : Option BlockingIPC.Completion) : View :=
  { scheduled := none
    live := false
    capacity
    row := List.replicate capacity none
    named := List.replicate capacity none
    owns := fun _ => false
    mappings := fun _ _ => none
    waitingOn := none
    completion }

theorem observe_dead (observer : Nat) (state : CompositeState)
    (hcurrent : state.lifecycle.current = none)
    (hlive : state.capabilities.subjects observer = false)
    (hslots : ∀ slot, state.capabilities.slots observer slot = none)
    (howner : ∀ space, state.virtualMemory.owner space ≠ some observer)
    (hwaiting : state.blockingIPC.waiterEndpoint observer = none) :
    observe observer state =
      deadView (state.capabilities.slotCapacity observer)
        (state.blockingIPC.completion observer) := by
  have hrow : row state observer =
      List.replicate (state.capabilities.slotCapacity observer) none := by
    have hfun : state.capabilities.slots observer = fun _ => none := funext hslots
    simp only [row, Capability.capabilitySpace, hfun]
    rw [List.map_const', List.length_range]
  simp only [observe, deadView, hcurrent, hlive, hrow, hwaiting]
  congr 1
  · simp
  · funext space
    simp [howner space]
  · funext space page
    simp [howner space]

/-- The scheduled observer of a well-formed blocking store waits on no
endpoint. -/
theorem not_waiting {observer : Nat} {state : CompositeState}
    (hstate : AuthoritativeRuntimeWellFormed state)
    (hcurrent : state.lifecycle.current = some observer) :
    state.blockingIPC.waiterEndpoint observer = none := by
  have hblocking : BlockingIPC.WellFormed state.blockingIPC := hstate.right.1.1.1
  cases hwait : state.blockingIPC.waiterEndpoint observer with
  | none => rfl
  | some endpoint =>
      exfalso
      obtain ⟨_, _, hwaiters, _, hindex, _⟩ := hblocking
      have hmem := (hindex endpoint observer).2 hwait
      have hnot := (hwaiters endpoint observer hmem).2.2.2.2.2.1
      apply hnot
      rw [blockingCurrent_eq (blockingCoherent_of hstate), hcurrent]

/-- Self-removal from the blocking store keeps a non-waiting subject's index
and completion. -/
theorem terminate_self_blocking (context : BlockingIPCContext.State) (subject : Nat)
    (hwait : context.ipc.waiterEndpoint subject = none) :
    (BlockingIPCContext.terminate context subject).ipc.waiterEndpoint subject = none ∧
      (BlockingIPCContext.terminate context subject).ipc.completion subject =
        context.ipc.completion subject := by
  unfold BlockingIPCContext.terminate
  split
  · exact ⟨hwait, rfl⟩
  · simp only [BlockingIPC.terminate]
    split
    · exact ⟨hwait, rfl⟩
    · simp [BlockingIPC.cancelSubject, hwait]

/-- The fields of a self-cleanup that the view reads, for both termination
paths. -/
theorem cleanup_self_fields {observer : Nat} {state : CompositeState}
    (hstate : AuthoritativeRuntimeWellFormed state)
    (hcurrent : state.lifecycle.current = some observer) :
    let resumable := ResumablePreemption.cleanupSubject state.resumable observer
    let selfRemoved := BlockingIPCContext.terminate state.blockingIPCContext observer
    let detached := BlockingIPCContext.detachInvalidated selfRemoved state.deferredCancels
      resumable.scheduler
    resumable.scheduler.lifecycle.current = none ∧
      resumable.scheduler.lifecycle.capabilities.subjects observer = false ∧
      resumable.scheduler.lifecycle.capabilities.slotCapacity observer =
        state.capabilities.slotCapacity observer ∧
      (∀ slot, resumable.scheduler.lifecycle.capabilities.slots observer slot = none) ∧
      (∀ space, resumable.translations.virtual.owner space ≠ some observer) ∧
      detached.1.ipc.waiterEndpoint observer = none ∧
      detached.1.ipc.completion observer = state.blockingIPC.completion observer := by
  intro resumable selfRemoved detached
  have hlifecycle := resumable_lifecycle (coherent_of hstate)
  have hcaps := capabilities_eq_lifecycle (coherent_of hstate)
  obtain ⟨hwait, hcompletion⟩ := terminate_self_blocking state.blockingIPCContext observer
    (not_waiting hstate hcurrent)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [resumable, ResumablePreemption.cleanupSubject, SubjectLifecycle.terminateState,
      hlifecycle, hcurrent]
  · simp [resumable, ResumablePreemption.cleanupSubject,
      ResumablePreemption.retireOwnedAddressSpaces, SubjectLifecycle.terminateState,
      SubjectLifecycle.terminatedCapabilities, SubjectLifecycle.setBool]
  · simp [resumable, ResumablePreemption.cleanupSubject,
      ResumablePreemption.retireOwnedAddressSpaces, SubjectLifecycle.terminateState,
      SubjectLifecycle.terminatedCapabilities, hlifecycle, hcaps]
  · intro slot
    simp only [resumable, ResumablePreemption.cleanupSubject,
      ResumablePreemption.retireOwnedAddressSpaces, SubjectLifecycle.terminateState,
      SubjectLifecycle.terminatedCapabilities]
    split
    · rfl
    · rename_i capability hslot
      split at hslot
      · cases hslot
      · rename_i original _
        simp at hslot
  · intro space
    simp only [resumable, ResumablePreemption.cleanupSubject, SubjectLifecycle.terminateState]
    split
    · simp
    · assumption
  · simp only [detached, selfRemoved, BlockingIPCContext.detachInvalidated, hwait]
  · simp only [detached, selfRemoved, BlockingIPCContext.detachInvalidated]
    exact hcompletion

theorem observe_installTerminatedSubject_self {observer : Nat} {state : CompositeState}
    (hstate : AuthoritativeRuntimeWellFormed state)
    (hcurrent : state.lifecycle.current = some observer) :
    observe observer (installTerminatedSubject state observer
      (ResumablePreemption.cleanupSubject state.resumable observer)) =
      deadView (state.capabilities.slotCapacity observer)
        (state.blockingIPC.completion observer) := by
  obtain ⟨hcur, hlive, hcap, hslots, howner, hwait, hcompletion⟩ :=
    cleanup_self_fields hstate hcurrent
  rw [observe_dead]
  · simp only [installTerminatedSubject, installTerminatedResumable, hcap, hcompletion]
  · exact hcur
  · exact hlive
  · exact hslots
  · exact howner
  · exact hwait

theorem observe_publishInterruptCleanup_self {observer : Nat} {state : CompositeState}
    (hstate : AuthoritativeRuntimeWellFormed state)
    (hcurrent : state.lifecycle.current = some observer) :
    observe observer (publishInterruptCleanup state observer) =
      deadView (state.capabilities.slotCapacity observer)
        (state.blockingIPC.completion observer) := by
  obtain ⟨hcur, hlive, hcap, hslots, howner, hwait, hcompletion⟩ :=
    cleanup_self_fields hstate hcurrent
  rw [observe_dead]
  · simp only [publishInterruptCleanup, installTerminatedResumable, hcap, hcompletion]
  · exact hcur
  · exact hlive
  · exact hslots
  · exact howner
  · exact hwait

/-! ## Self-termination -/

theorem terminate_self_accepted {observer : Nat} {state : CompositeState}
    (hstate : RuntimeWellFormed state) (hcurrent : state.lifecycle.current = some observer) :
    (SubjectLifecycle.terminate state.lifecycle observer).result = .accepted := by
  rcases hstate with ⟨hcoherent, _, _, _, _, _, hscheduler, _⟩
  have hcurrent' : state.scheduler.lifecycle.current = some observer := by
    rw [hcoherent.2.1]
    exact hcurrent
  have hlive := (hscheduler.2.2.2.2 observer hcurrent').1
  have hissued := hscheduler.1.1 observer hlive
  rw [hcoherent.2.1] at hlive hissued
  simp [SubjectLifecycle.terminate, hlive, hissued]

theorem apply_terminate_self {observer : Nat} {state : CompositeState}
    (hstate : RuntimeWellFormed state) (hcurrent : state.lifecycle.current = some observer) :
    applyOperation state (.terminateSubject observer) =
      installTerminatedSubject state observer
        (ResumablePreemption.cleanupSubject state.resumable observer) := by
  simp only [applyOperation, terminate_self_accepted hstate hcurrent]

theorem apply_terminateCurrent_self {observer : Nat} {state : CompositeState}
    (hstate : RuntimeWellFormed state) (hcurrent : state.lifecycle.current = some observer) :
    applyOperation state .terminateCurrent =
      installTerminatedSubject state observer
        (ResumablePreemption.cleanupSubject state.resumable observer) := by
  have hreply := reply_terminateCurrent hstate hcurrent
  have hcurrent' : state.scheduler.lifecycle.current = some observer := by
    rw [hstate.1.2.1]
    exact hcurrent
  simp only [operationReply, OperationReply.scheduler.injEq] at hreply
  simp only [applyOperation, hreply, hcurrent']

/-- **Step consistency of the observer's own termination.** -/
theorem own_step_terminate_self {observer : Nat} {left right : CompositeState}
    (h : OwnStep observer left right) (hleft : AuthoritativeRuntimeWellFormed left)
    (hright : AuthoritativeRuntimeWellFormed right) :
    LowEquiv observer (authoritativeGate left (.ordinary (.terminateSubject observer))).state
      (authoritativeGate right (.ordinary (.terminateSubject observer))).state := by
  apply lowEquiv_gate_of_apply h.low h.mode
  unfold LowEquiv
  rw [apply_terminate_self h.leftWF h.current, apply_terminate_self h.rightWF h.rightCurrent,
    observe_installTerminatedSubject_self hleft h.current,
    observe_installTerminatedSubject_self hright h.rightCurrent, h.low.capacity,
    show left.blockingIPC.completion observer = right.blockingIPC.completion observer from
      congrArg View.completion h.low]

/-- **Step consistency of `terminateCurrent` by the scheduled observer.** -/
theorem own_step_terminateCurrent {observer : Nat} {left right : CompositeState}
    (h : OwnStep observer left right) (hleft : AuthoritativeRuntimeWellFormed left)
    (hright : AuthoritativeRuntimeWellFormed right) :
    LowEquiv observer (authoritativeGate left (.ordinary .terminateCurrent)).state
      (authoritativeGate right (.ordinary .terminateCurrent)).state := by
  apply lowEquiv_gate_of_apply h.low h.mode
  unfold LowEquiv
  rw [apply_terminateCurrent_self h.leftWF h.current,
    apply_terminateCurrent_self h.rightWF h.rightCurrent,
    observe_installTerminatedSubject_self hleft h.current,
    observe_installTerminatedSubject_self hright h.rightCurrent, h.low.capacity,
    show left.blockingIPC.completion observer = right.blockingIPC.completion observer from
      congrArg View.completion h.low]

/-! ## Interrupts and NMIs -/

/-- The raw interrupt classification reads only the entry flag and the current
subject of its context. -/
theorem interrupt_action_eq (first second : Interrupt.State) (frame : Interrupt.HardwareFrame)
    (hentry : first.context.entryActive = second.context.entryActive)
    (hsubject : first.context.currentSubject = second.context.currentSubject) :
    (Interrupt.dispatchHardware first frame).action =
      (Interrupt.dispatchHardware second frame).action := by
  unfold Interrupt.dispatchHardware
  rw [hentry, hsubject]
  repeat' split
  all_goals rfl

/-- The latch classification of a completed first entry, as a function of the
raw classification. -/
def latchAction : Interrupt.Action → EntryAction
  | .fatal reason => .fatal (mapFatal reason)
  | .contained subject => .contained subject
  | .timer => .timer
  | .syscall => .syscall
  | .rejected reason => .rejected reason

theorem finishEntry_action (state : FailStop.State) (frame : Interrupt.HardwareFrame)
    (hmode : state.mode = .running) :
    (finishEntry (beginEntry state frame).state).action =
      latchAction (Interrupt.dispatchHardware
        { (beginEntry state frame).state.core with context :=
          { (beginEntry state frame).state.core.context with entryActive := false } }
        (activeEntry frame).frame).action := by
  simp only [beginEntry, hmode, finishEntry]
  generalize Interrupt.dispatchHardware _ (activeEntry frame).frame = outcome
  rcases outcome with ⟨core, action⟩
  cases action <;> simp [latchAction, halt]

/-- An interrupt's classification reads the frame, the latch mode, and the
current subject. -/
theorem dispatchHardware_action_eq (first second : FailStop.State)
    (frame : Interrupt.HardwareFrame) (hmode : first.mode = second.mode)
    (hsubject : first.core.context.currentSubject = second.core.context.currentSubject) :
    (dispatchHardware first frame).action = (dispatchHardware second frame).action := by
  unfold dispatchHardware
  cases hfirst : first.mode with
  | running =>
      have hsecond : second.mode = .running := hmode ▸ hfirst
      simp only [hsecond]
      rw [finishEntry_action first frame hfirst, finishEntry_action second frame hsecond]
      congr 1
      apply interrupt_action_eq
      · rfl
      · simp only [beginEntry, hfirst, hsecond, hsubject]
  | handling active =>
      have hsecond : second.mode = .handling active := hmode ▸ hfirst
      simp only [hsecond, halt]
  | halted record =>
      have hsecond : second.mode = .halted record := hmode ▸ hfirst
      simp only [hsecond]

/-- The observer's view after an interrupt: a contained fault of the
scheduled subject terminates it, and every other classification leaves the
view unchanged. -/
theorem observe_apply_interrupt_own {observer : Nat} {state : CompositeState}
    (hstate : AuthoritativeRuntimeWellFormed state)
    (hcurrent : state.lifecycle.current = some observer) (frame : Interrupt.HardwareFrame) :
    observe observer (applyOperation state (.interrupt frame)) =
      match (dispatchHardware state.execution frame).action with
      | .contained subject =>
          if state.lifecycle.current = some subject then
            deadView (state.capabilities.slotCapacity observer)
              (state.blockingIPC.completion observer)
          else observe observer state
      | _ => observe observer state := by
  have hcoherent := coherent_of hstate
  simp only [applyOperation]
  generalize (dispatchHardware state.execution frame).action = action
  cases action with
  | contained subject =>
      simp only
      split
      · rename_i hsubject
        rw [hcurrent, Option.some.injEq] at hsubject
        subst hsubject
        exact observe_publishInterruptCleanup_self hstate hcurrent
      · rfl
  | fatal reason =>
      exact CompositeLocalRespect.observe_installResumable observer
        { state with execution := (dispatchHardware state.execution frame).state }
        { state.resumable with halted := true } (resumable_lifecycle (state := state) hcoherent)
        (capabilities_eq_lifecycle (state := state) hcoherent)
        (translations_eq (state := state) hcoherent) rfl rfl
  | timer => rfl
  | syscall => rfl
  | rejected reason => rfl
  | alreadyHalted record => rfl

/-- **Step consistency of an interrupt while the observer is scheduled.** -/
theorem own_step_interrupt {observer : Nat} {left right : CompositeState}
    (h : OwnStep observer left right) (hleft : AuthoritativeRuntimeWellFormed left)
    (hright : AuthoritativeRuntimeWellFormed right) (frame : Interrupt.HardwareFrame) :
    LowEquiv observer (authoritativeGate left (.ordinary (.interrupt frame))).state
      (authoritativeGate right (.ordinary (.interrupt frame))).state := by
  apply lowEquiv_gate_of_apply h.low h.mode
  unfold LowEquiv
  have haction := dispatchHardware_action_eq left.execution right.execution frame h.mode
    (h.leftActor.1.trans h.rightActor.1.symm)
  rw [observe_apply_interrupt_own hleft h.current, observe_apply_interrupt_own hright
    h.rightCurrent, haction, h.current, h.rightCurrent, h.low.capacity,
    show left.blockingIPC.completion observer = right.blockingIPC.completion observer from
      congrArg View.completion h.low, h.low]

/-- **Output consistency of an interrupt while the observer is scheduled.** -/
theorem own_output_interrupt {observer : Nat} {left right : CompositeState}
    (h : OwnStep observer left right) (frame : Interrupt.HardwareFrame) :
    (authoritativeGate left (.ordinary (.interrupt frame))).result =
      (authoritativeGate right (.ordinary (.interrupt frame))).result := by
  apply authoritativeGate_result_of_reply left right _ (not_nmi_of rfl) h.mode
  have haction := dispatchHardware_action_eq left.execution right.execution frame h.mode
    (h.leftActor.1.trans h.rightActor.1.symm)
  simp only [operationReply, haction, h.current, h.rightCurrent]

/-- An NMI's latch action reads the mode, the hardware snapshot, and the
scheduled subject and address space. -/
theorem dispatchNmi_action_eq (first second : FailStop.State)
    (raw : InterruptEntry.RawNmiEntry) (context : InterruptEntry.NmiContext)
    (hmode : first.mode = second.mode)
    (hsubject : first.core.context.currentSubject = second.core.context.currentSubject)
    (hspace : first.core.context.activeAddressSpace =
      second.core.context.activeAddressSpace) :
    (dispatchNmi first raw context).action = (dispatchNmi second raw context).action := by
  unfold dispatchNmi
  rw [← hmode, hsubject, hspace]
  cases first.mode with
  | halted record => rfl
  | running =>
      simp only
      split
      · rfl
      · split <;> rfl
  | handling active =>
      simp only
      split
      · rfl
      · split <;> rfl

/-- **Output consistency of an NMI while the observer is scheduled.** -/
theorem own_output_nmi {observer : Nat} {left right : CompositeState}
    (h : OwnStep observer left right) (raw : InterruptEntry.RawNmiEntry)
    (context : InterruptEntry.NmiContext) :
    (authoritativeGate left (.ordinary (.nmi raw context))).result =
      (authoritativeGate right (.ordinary (.nmi raw context))).result := by
  have haction := dispatchNmi_action_eq left.execution right.execution raw context h.mode
    (h.leftActor.1.trans h.rightActor.1.symm) (h.leftActor.2.trans h.rightActor.2.symm)
  unfold authoritativeGate
  simp only [operationReply, haction, ← h.mode]
  cases left.execution.mode <;> rfl

end LeanOS.CompositeOwnTermination
