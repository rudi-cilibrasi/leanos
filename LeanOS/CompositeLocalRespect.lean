import LeanOS.CompositeOwnSteps

/-!
# Composite unwinding: local respect for more of other subjects' operations

`CompositeUnwinding.isSilentCoherent` classifies another subject's operation
as silent for the observer only for protection, creation, delegation, direct
revocation, memory, data IPC, frame-rule families, and non-blocking blocking
IPC away from the observer.  This module extends local respect, under the same
trace invariant `AuthoritativeRuntimeWellFormed`, to:

* the scheduler operations `scheduleNext`, `scheduleYield`, `scheduleTick`
  (the composite never applies them), `scheduleAdd` (it writes only scheduler
  queues), and `scheduleRemove` of a subject that is not the scheduled one;
* transfer offer and receipt on an endpoint the observer does not name;
* an interrupt that contains no scheduled subject (timer, syscall, rejected,
  or fatal entries, and contained faults of an unscheduled identity);
* a resumable switch that fails (it either rejects or latches the halt);
* a deferred-cancellation drain of another subject.

Local respect is `authoritativeGate_silentExtended_observe`; the trace theorem
is `finite_trace_lowEquiv_extended`.  A drain of another subject also leaves
the observer's view unchanged when the observer itself is scheduled, so drains
are step consistent for the observer (`own_step_drain`), and a drain of the
observer itself is output consistent (`own_output_drain_self`).
-/
namespace LeanOS.CompositeLocalRespect

open LeanOS
open LeanOS.FailStop
open LeanOS.CompositeObservation
open LeanOS.CompositeUnwinding
open LeanOS.CompositeOwnSteps
set_option linter.unusedSimpArgs false

/-! ## Transfer publication without a change to the observer's view -/

/-- Publishing the current transfer store changes nothing the observer sees. -/
theorem observe_installTransfers_self (observer : Nat) (state : CompositeState)
    (hcoherent : state.Coherent) :
    observe observer (installTransfers state state.transfers) = observe observer state := by
  obtain ⟨hcaps, hmailbox⟩ := transfers_published hcoherent
  rw [observe_installTransfers_eq, hcaps, hmailbox]
  rfl

/-- A transfer store that agrees with the published one on the observer's row
and on every object it names leaves the observer's view unchanged. -/
theorem observe_installTransfers_of (observer : Nat) (state : CompositeState)
    (hcoherent : state.Coherent) (transfers : CapabilityTransfer.State)
    (hlive : transfers.capabilities.subjects observer =
      state.transfers.capabilities.subjects observer)
    (hcapacity : transfers.capabilities.slotCapacity observer =
      state.transfers.capabilities.slotCapacity observer)
    (hrow : Capability.capabilitySpace transfers.capabilities observer =
      Capability.capabilitySpace state.transfers.capabilities observer)
    (hnamed : ∀ object, Names state observer object = true →
      transfers.capabilities.objects object = state.transfers.capabilities.objects object ∧
        transfers.capabilities.kinds object = state.transfers.capabilities.kinds object ∧
        transfers.mailbox object = state.transfers.mailbox object ∧
        transfers.pending object = state.transfers.pending object) :
    observe observer (installTransfers state transfers) = observe observer state := by
  have hlow : LowEquiv observer (installTransfers state transfers)
      (installTransfers state state.transfers) := by
    apply lowEquiv_installTransfers (show LowEquiv observer state state from rfl) _ _ hlive
      hcapacity hrow
    intro cap hmem
    have hnames : Names state observer cap.object = true := by
      rw [hrow, (transfers_published hcoherent).1] at hmem
      simp only [Names, List.any_eq_true]
      exact ⟨some cap, hmem, by simp⟩
    exact ⟨rfl, hnamed cap.object hnames⟩
  exact hlow.trans (observe_installTransfers_self observer state hcoherent)

/-- The endpoint a transfer offer or receipt resolves for the acting subject. -/
def transferTarget (state : CompositeState) (endpointWord : UInt64) : Option Nat :=
  match CapabilityHandle.resolveCurrent state.transfers.capabilities
      { caller := actor state } endpointWord .endpoint with
  | .ok resolution => some resolution.capability.object
  | .error _ => none

theorem offerWordsCheck_endpoint (a : CapabilityTransfer.State) caller endpointWord sourceWord
    sourceKind (rights : Capability.Rights) endpointCap source
    (hcheck : offerWordsCheck a caller endpointWord sourceWord sourceKind rights =
      .ok (endpointCap, source)) :
    ∃ resolution, CapabilityHandle.resolveCurrent a.capabilities { caller } endpointWord
        .endpoint = .ok resolution ∧ resolution.capability.object = endpointCap.object := by
  unfold offerWordsCheck at hcheck
  split at hcheck
  · cases hcheck
  · cases hcheck
  · cases hcheck
  · rename_i resolution hresolve
    refine ⟨resolution, hresolve, ?_⟩
    have hlookup := resolveCurrent_ok_lookup _ _ _ _ _ hresolve
    split at hcheck
    · cases hcheck
    · cases hcheck
    · split at hcheck
      · cases hcheck
      · unfold offerCheck at hcheck
        rw [hlookup] at hcheck
        simp only at hcheck
        repeat' split at hcheck
        all_goals first
          | (cases hcheck; done)
          | skip
        all_goals
          simp only [Except.ok.injEq, Prod.mk.injEq] at hcheck
          rw [← hcheck.1]

/-- A transfer offer on an endpoint the observer does not name is invisible. -/
theorem observe_apply_offer_other (observer : Nat) (state : CompositeState)
    (hcoherent : state.Coherent) endpointWord sourceWord sourceKind payload
    (rights : Capability.Rights)
    (htarget : ∀ object, transferTarget state endpointWord = some object →
      Names state observer object = false) :
    observe observer (applyOperation state
      (.transferOffer endpointWord sourceWord sourceKind payload rights)) =
      observe observer state := by
  rw [applyOperation_transferOffer]
  cases hcheck : offerWordsCheck state.transfers state.execution.core.context.currentSubject
      endpointWord sourceWord sourceKind rights with
  | error reason => rfl
  | ok caps =>
      obtain ⟨endpointCap, source⟩ := caps
      obtain ⟨resolution, hresolve, hobject⟩ :=
        offerWordsCheck_endpoint _ _ _ _ _ _ _ _ hcheck
      have hnotNamed : Names state observer endpointCap.object = false := by
        apply htarget
        simp only [transferTarget, actor, hresolve, hobject]
      apply observe_installTransfers_of observer state hcoherent
        (offerAccepted state.transfers state.execution.core.context.currentSubject endpointCap
          source payload rights) rfl rfl rfl
      intro object hnames
      have hne : object ≠ endpointCap.object := by
        intro heq
        rw [heq, hnotNamed] at hnames
        cases hnames
      refine ⟨rfl, rfl, ?_, ?_⟩
      · simp [offerAccepted, CapabilityTransfer.record, EndpointIPC.setOption, hne]
      · simp [offerAccepted, CapabilityTransfer.record, CapabilityTransfer.setPending, hne]

theorem acceptWordCheck_endpoint (a : CapabilityTransfer.State) caller endpointWord
    destinationSlot endpointCap envelope sealed
    (hcheck : acceptWordCheck a caller endpointWord destinationSlot =
      .ok (endpointCap, envelope, sealed)) :
    ∃ resolution, CapabilityHandle.resolveCurrent a.capabilities { caller } endpointWord
        .endpoint = .ok resolution ∧ resolution.capability.object = endpointCap.object := by
  unfold acceptWordCheck at hcheck
  split at hcheck
  · cases hcheck
  · cases hcheck
  · cases hcheck
  · rename_i resolution hresolve
    refine ⟨resolution, hresolve, ?_⟩
    have hlookup := resolveCurrent_ok_lookup _ _ _ _ _ hresolve
    have hfound : ∀ slot, slot = resolution.handle.slot →
        acceptCheck a caller slot destinationSlot = .ok (endpointCap, envelope, sealed) →
        resolution.capability.object = endpointCap.object := by
      intro slot hslot hcheck'
      subst hslot
      have := (acceptCheck_ok a caller _ destinationSlot _ _ _ hcheck').1
      rw [hlookup] at this
      cases this
      rfl
    split at hcheck
    · split at hcheck
      · cases hcheck
      · split at hcheck
        · cases hcheck
        · exact hfound _ rfl hcheck
    · exact hfound _ rfl hcheck

/-- A transfer receipt on an endpoint the observer does not name, by another
subject, is invisible: it installs into the actor's row and consumes that
endpoint's mailbox. -/
theorem observe_apply_accept_other (observer : Nat) (state : CompositeState)
    (hcoherent : state.Coherent) (hactor : actor state ≠ observer) endpointWord destinationSlot
    (htarget : ∀ object, transferTarget state endpointWord = some object →
      Names state observer object = false) :
    observe observer (applyOperation state (.transferAccept endpointWord destinationSlot)) =
      observe observer state := by
  rw [applyOperation_transferAccept]
  cases hcheck : acceptWordCheck state.transfers state.execution.core.context.currentSubject
      endpointWord destinationSlot with
  | error reason => rfl
  | ok result =>
      obtain ⟨endpointCap, envelope, sealed⟩ := result
      obtain ⟨resolution, hresolve, hobject⟩ :=
        acceptWordCheck_endpoint _ _ _ _ _ _ _ hcheck
      have hnotNamed : Names state observer endpointCap.object = false := by
        apply htarget
        simp only [transferTarget, actor, hresolve, hobject]
      have hactor' : observer ≠ state.execution.core.context.currentSubject :=
        fun heq => hactor heq.symm
      have hne : ∀ object, Names state observer object = true → object ≠ endpointCap.object := by
        intro object hnames heq
        rw [heq, hnotNamed] at hnames
        cases hnames
      cases sealed with
      | none =>
          dsimp only [acceptOutcome]
          apply observe_installTransfers_of observer state hcoherent
            (CapabilityTransfer.deliverData state.transfers
              state.execution.core.context.currentSubject endpointCap envelope).state rfl rfl rfl
          intro object hnames
          refine ⟨rfl, rfl, ?_, rfl⟩
          simp [acceptOutcome, CapabilityTransfer.deliverData, CapabilityTransfer.record,
            EndpointIPC.setOption, hne object hnames]
      | some transfer =>
          dsimp only [acceptOutcome]
          apply observe_installTransfers_of observer state hcoherent
            (CapabilityTransfer.deliver state.transfers state.execution.core.context.currentSubject
              destinationSlot endpointCap envelope transfer).state
          · rfl
          · rfl
          · simp only [acceptOutcome, CapabilityTransfer.deliver, CapabilityTransfer.record,
              Capability.capabilitySpace]
            rw [Capability.install_other_subject _ _ _ _ _ hactor']
            rfl
          · intro object hnames
            refine ⟨rfl, rfl, ?_, ?_⟩
            · simp [acceptOutcome, CapabilityTransfer.deliver, CapabilityTransfer.record,
                EndpointIPC.setOption, hne object hnames]
            · simp [acceptOutcome, CapabilityTransfer.deliver, CapabilityTransfer.record,
                CapabilityTransfer.setPending, hne object hnames]

/-! ## Halting and failed resumable switches -/

/-- Republishing a resumable bank with the same scheduler and the same
virtual-memory translation leaves the observer's view unchanged. -/
theorem observe_installResumable (observer : Nat) (state : CompositeState)
    (resumable : ResumablePreemption.State)
    (hlifecycle : state.resumable.scheduler.lifecycle = state.lifecycle)
    (hcapabilities : state.capabilities = state.lifecycle.capabilities)
    (hvirtual : state.resumable.translations.virtual = state.virtualMemory)
    (hscheduler : resumable.scheduler = state.resumable.scheduler)
    (htranslations : resumable.translations.virtual = state.resumable.translations.virtual) :
    observe observer (installResumable state resumable) = observe observer state := by
  have hlife : resumable.scheduler.lifecycle = state.lifecycle := by
    rw [hscheduler, hlifecycle]
  have hvm : resumable.translations.virtual = state.virtualMemory := by
    rw [htranslations, hvirtual]
  apply observe_eq_of <;>
    simp only [installResumable, hlife, hvm, ← hcapabilities]
  all_goals first
    | (intro _ _; rfl)
    | (intro _ _; trivial)
    | trivial

/-- Whether an interrupt leaves every subject's authority in place: it does
unless it contains the scheduled subject. -/
def interruptSilent (state : CompositeState) (frame : Interrupt.HardwareFrame) : Bool :=
  match (dispatchHardware state.execution frame).action with
  | .contained subject => state.lifecycle.current != some subject
  | _ => true

theorem observe_apply_interrupt (observer : Nat) (state : CompositeState)
    (hcoherent : state.Coherent) (frame : Interrupt.HardwareFrame)
    (hsilent : interruptSilent state frame = true) :
    observe observer (applyOperation state (.interrupt frame)) = observe observer state := by
  unfold interruptSilent at hsilent
  simp only [applyOperation]
  split
  · rename_i subject haction
    simp only [haction, bne_iff_ne, ne_eq] at hsilent
    simp only [hsilent, ↓reduceIte]
  · exact observe_installResumable observer _ _ (resumable_lifecycle (state := state) hcoherent)
      (capabilities_eq_lifecycle (state := state) hcoherent)
      (translations_eq (state := state) hcoherent) rfl rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem switch_error_frame (resumable : ResumablePreemption.State)
    (interruptState : Interrupt.State) (frame : Interrupt.HardwareFrame)
    (registers : ResumablePreemption.Registers)
    (herror : (ResumablePreemption.switch resumable interruptState frame
      registers).error.isSome = true) :
    (ResumablePreemption.switch resumable interruptState frame registers).state.scheduler =
        resumable.scheduler ∧
      (ResumablePreemption.switch resumable interruptState frame
        registers).state.translations = resumable.translations := by
  revert herror
  unfold ResumablePreemption.switch
  generalize Scheduler.tick resumable.scheduler = scheduled
  rcases scheduled with ⟨next, (_ | selected) | reason⟩
  all_goals
    simp only
    repeat' split
  all_goals simp [ResumablePreemption.reject, ResumablePreemption.halt]

theorem observe_apply_resumePreempt (observer : Nat) (state : CompositeState)
    (hcoherent : state.Coherent) (frame : Interrupt.HardwareFrame)
    (registers : ResumablePreemption.Registers)
    (herror : (ResumablePreemption.switch state.resumable state.execution.core frame
      registers).error.isSome = true) :
    observe observer (applyOperation state (.resumePreempt frame registers)) =
      observe observer state := by
  obtain ⟨hscheduler, htranslations⟩ := switch_error_frame _ _ _ _ herror
  simp only [applyOperation]
  split
  · split
    · exact observe_installResumable observer _ _
        (resumable_lifecycle (state := state) hcoherent)
        (capabilities_eq_lifecycle (state := state) hcoherent)
        (translations_eq (state := state) hcoherent) hscheduler (by rw [htranslations])
    · rfl
  · rfl
  · rename_i hnone
    rw [hnone] at herror
    cases herror

/-! ## Queue removal of an unscheduled subject -/

theorem observe_apply_scheduleRemove_unscheduled (observer : Nat) {subject : Nat}
    {state : CompositeState} (hcoherent : state.Coherent)
    (hcurrent : state.lifecycle.current ≠ some subject) :
    observe observer (applyOperation state (.scheduleRemove subject)) =
      observe observer state := by
  simp only [applyOperation]
  split
  · rfl
  · rename_i context haccepted
    rw [observe_installSchedulerRemoval,
      remove_accepted_current _ _ context haccepted, resumable_lifecycle hcoherent]
    simp only [hcurrent, ↓reduceIte]
    rfl

/-! ## Deferred-cancellation drains -/

theorem drainDeferred_frame (state : BlockingIPCContext.State)
    (deferred : BlockingIPCContext.DeferredCancelState)
    (resumable : List ResumableContext.Context) (capacity : Nat) (subject : Nat) :
    let next := (BlockingIPCContext.drainDeferred state deferred resumable capacity
      subject).state
    next.ipc.scheduler.lifecycle.current = state.ipc.scheduler.lifecycle.current ∧
      next.ipc.mailbox = state.ipc.mailbox ∧
      next.ipc.waiters = state.ipc.waiters ∧
      next.ipc.waiterEndpoint = state.ipc.waiterEndpoint ∧
      ∀ candidate, candidate ≠ subject →
        next.ipc.completion candidate = state.ipc.completion candidate := by
  simp only [BlockingIPCContext.drainDeferred]
  repeat' split
  all_goals simp_all [BlockingIPC.setCompletion]

/-- A drain of a subject other than the observer leaves the observer's view
unchanged, whoever performs it. -/
theorem observe_drain_other (observer : Nat) (state : CompositeState)
    (hcoherent : state.BlockingIPCCoherent) (subject : Nat) (hne : subject ≠ observer) :
    observe observer (drainDeferredCancellation state subject).state =
      observe observer state := by
  obtain ⟨hcurrent, hmailbox, hwaiters, hwaiting, hcompletion⟩ :=
    drainDeferred_frame state.blockingIPCContext state.deferredCancels
      state.resumable.contexts state.resumable.capacity subject
  simp only [drainDeferredCancellation]
  generalize houtcome : BlockingIPCContext.drainDeferred state.blockingIPCContext
    state.deferredCancels state.resumable.contexts state.resumable.capacity subject = outcome
    at hcurrent hmailbox hwaiters hwaiting hcompletion
  rcases outcome with ⟨next, nextDeferred, nextResumable, result⟩
  cases result with
  | rejected reason => rfl
  | drained saved =>
      show observe observer (publishBlockingIPCContext state next) = observe observer state
      apply observe_publishBlockingIPCContext
      · rw [hcurrent]
        exact blockingCurrent_eq hcoherent
      · intro object _
        exact ⟨by rw [hmailbox]; rfl, by rw [hwaiters]; rfl⟩
      · rw [hwaiting]
        rfl
      · exact hcompletion observer (Ne.symm hne)

/-- The scheduled subject has no retained cancellation, so draining it is
rejected and changes nothing. -/
theorem drain_self_rejected {observer : Nat} {state : CompositeState}
    (hstate : AuthoritativeRuntimeWellFormed state)
    (hcurrent : state.lifecycle.current = some observer) :
    drainDeferredCancellation state observer = ⟨state, .rejected .notDeferred⟩ := by
  have hretained : state.deferredCancels.retained observer = none := by
    cases hsaved : state.deferredCancels.retained observer with
    | none => rfl
    | some saved =>
        exfalso
        have hnot := (hstate.right.1.2.2 observer saved hsaved).2.2.2.2.1
        apply hnot
        rw [show state.blockingIPCContext.ipc.scheduler.lifecycle.current =
          state.blockingIPC.scheduler.lifecycle.current from rfl,
          blockingCurrent_eq (blockingCoherent_of hstate), hcurrent]
  simp [drainDeferredCancellation, BlockingIPCContext.drainDeferred, hretained]

theorem authoritativeGate_drain_pair (left right : CompositeState) (subject : Nat)
    (hmode : left.execution.mode = right.execution.mode) :
    ((authoritativeGate left (.drainDeferred subject)).state = left ∧
        (authoritativeGate right (.drainDeferred subject)).state = right) ∨
      ((authoritativeGate left (.drainDeferred subject)).state =
          (drainDeferredCancellation left subject).state ∧
        (authoritativeGate right (.drainDeferred subject)).state =
          (drainDeferredCancellation right subject).state) := by
  rw [authoritativeGate_drainDeferred_state, authoritativeGate_drainDeferred_state, ← hmode]
  cases left.execution.mode <;> simp

/-- **Step consistency of deferred drains** for the scheduled observer, for any
drained subject. -/
theorem own_step_drain {observer : Nat} {left right : CompositeState}
    (h : OwnStep observer left right) (hleft : AuthoritativeRuntimeWellFormed left)
    (hright : AuthoritativeRuntimeWellFormed right) (subject : Nat) :
    LowEquiv observer (authoritativeGate left (.drainDeferred subject)).state
      (authoritativeGate right (.drainDeferred subject)).state := by
  rcases authoritativeGate_drain_pair left right subject h.mode with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · rw [hl, hr]
    exact h.low
  rw [hl, hr]
  by_cases hsubject : subject = observer
  · subst hsubject
    rw [drain_self_rejected hleft h.current, drain_self_rejected hright h.rightCurrent]
    exact h.low
  · exact lowEquiv_of_unchanged h.low
      (observe_drain_other observer left (blockingCoherent_of hleft) subject hsubject)
      (observe_drain_other observer right (blockingCoherent_of hright) subject hsubject)

/-- **Output consistency of the observer's own drain**: it is always rejected
as not deferred. -/
theorem own_output_drain_self {observer : Nat} {left right : CompositeState}
    (h : OwnStep observer left right) (hleft : AuthoritativeRuntimeWellFormed left)
    (hright : AuthoritativeRuntimeWellFormed right) :
    (authoritativeGate left (.drainDeferred observer)).result =
      (authoritativeGate right (.drainDeferred observer)).result := by
  have hL := drain_self_rejected hleft h.current
  have hR := drain_self_rejected hright h.rightCurrent
  unfold authoritativeGate
  simp only [applyAuthoritativeOperation, authoritativeOperationReply, hL, hR, ← h.mode]
  cases left.execution.mode <;> rfl

/-! ## The extended silence classification -/

/-- Silence for the ordinary operations added here; every other ordinary
operation is classified by `isSilentCoherentOrdinary`. -/
def isSilentExtendedOrdinary (observer : Nat) (state : CompositeState) :
    Operation → Bool
  | .scheduleNext | .scheduleYield | .scheduleTick | .scheduleAdd _ => actor state != observer
  | .scheduleRemove subject =>
      actor state != observer && state.lifecycle.current != some subject
  | .transferOffer endpointWord _ _ _ _ | .transferAccept endpointWord _ =>
      actor state != observer &&
        match transferTarget state endpointWord with
        | none => true
        | some object => !Names state observer object
  | .interrupt frame => actor state != observer && interruptSilent state frame
  | .resumePreempt frame registers =>
      actor state != observer &&
        (ResumablePreemption.switch state.resumable state.execution.core frame
          registers).error.isSome
  | operation => isSilentCoherentOrdinary observer state operation

/-- The extended, decidable silence classification. -/
def isSilentExtended (observer : Nat) (state : CompositeState) :
    AuthoritativeOperation → Bool
  | .ordinary operation => isSilentExtendedOrdinary observer state operation
  | .blocking operation => isSilentBlocking observer state operation
  | .drainDeferred subject => actor state != observer && subject != observer

theorem isSilentExtended_of_isSilentCoherent {observer state operation}
    (hsilent : isSilentCoherent observer state operation = true) :
    isSilentExtended observer state operation = true := by
  cases operation with
  | ordinary operation =>
      cases operation <;>
        simp_all [isSilentCoherent, isSilentExtended, isSilentExtendedOrdinary,
          isSilentCoherentOrdinary, isSilentOrdinary]
  | blocking operation => exact hsilent
  | drainDeferred subject => simp [isSilentCoherent] at hsilent

theorem transferTarget_not_named {observer : Nat} {state : CompositeState}
    {endpointWord : UInt64}
    (hsilent : (match transferTarget state endpointWord with
      | none => true
      | some object => !Names state observer object) = true) :
    ∀ object, transferTarget state endpointWord = some object →
      Names state observer object = false := by
  intro object htarget
  rw [htarget] at hsilent
  simpa using hsilent

/-- **Local respect** for ordinary operations under the extended
classification. -/
theorem applyOperation_silentExtended_observe (observer : Nat) (state : CompositeState)
    (operation : Operation) (hcoherent : state.Coherent)
    (hsilent : isSilentExtendedOrdinary observer state operation = true) :
    observe observer (applyOperation state operation) = observe observer state := by
  cases operation with
  | scheduleNext => rw [apply_scheduleNext]
  | scheduleYield => rw [apply_scheduleYield]
  | scheduleTick => rw [apply_scheduleTick]
  | scheduleAdd subject => exact observe_apply_scheduleAdd observer state subject
  | scheduleRemove subject =>
      simp only [isSilentExtendedOrdinary, Bool.and_eq_true, bne_iff_ne, ne_eq] at hsilent
      exact observe_apply_scheduleRemove_unscheduled observer hcoherent hsilent.2
  | transferOffer endpointWord sourceWord sourceKind payload rights =>
      simp only [isSilentExtendedOrdinary, Bool.and_eq_true] at hsilent
      exact observe_apply_offer_other observer state hcoherent endpointWord sourceWord
        sourceKind payload rights (transferTarget_not_named hsilent.2)
  | transferAccept endpointWord destinationSlot =>
      simp only [isSilentExtendedOrdinary, Bool.and_eq_true, bne_iff_ne, ne_eq] at hsilent
      exact observe_apply_accept_other observer state hcoherent hsilent.1 endpointWord
        destinationSlot (transferTarget_not_named hsilent.2)
  | interrupt frame =>
      simp only [isSilentExtendedOrdinary, Bool.and_eq_true] at hsilent
      exact observe_apply_interrupt observer state hcoherent frame hsilent.2
  | resumePreempt frame registers =>
      simp only [isSilentExtendedOrdinary, Bool.and_eq_true] at hsilent
      exact observe_apply_resumePreempt observer state hcoherent frame registers hsilent.2
  | nmi raw context =>
      exact applyOperation_silentCoherent_observe observer state _ hcoherent hsilent
  | selectUserReturn purpose =>
      exact applyOperation_silentCoherent_observe observer state _ hcoherent hsilent
  | userReturn request =>
      exact applyOperation_silentCoherent_observe observer state _ hcoherent hsilent
  | syscall call =>
      exact applyOperation_silentCoherent_observe observer state _ hcoherent hsilent
  | ipc call => exact applyOperation_silentCoherent_observe observer state _ hcoherent hsilent
  | capabilityCopy source destination destinationSlot rights =>
      exact applyOperation_silentCoherent_observe observer state _ hcoherent hsilent
  | capabilityRevoke authoritySlot victim victimSlot =>
      exact applyOperation_silentCoherent_observe observer state _ hcoherent hsilent
  | capabilityRevokeSubtree authoritySlot victim victimSlot =>
      exact applyOperation_silentCoherent_observe observer state _ hcoherent hsilent
  | map slot page permissions =>
      exact applyOperation_silentCoherent_observe observer state _ hcoherent hsilent
  | unmap page => exact applyOperation_silentCoherent_observe observer state _ hcoherent hsilent
  | protect page permissions =>
      exact applyOperation_silentCoherent_observe observer state _ hcoherent hsilent
  | createSubject subject =>
      exact applyOperation_silentCoherent_observe observer state _ hcoherent hsilent
  | terminateSubject subject =>
      exact applyOperation_silentCoherent_observe observer state _ hcoherent hsilent
  | terminateCurrent =>
      exact applyOperation_silentCoherent_observe observer state _ hcoherent hsilent
  | restart => exact applyOperation_silentCoherent_observe observer state _ hcoherent hsilent

/-- **Local respect** on the authoritative gate for the extended
classification, given the trace invariant. -/
theorem authoritativeGate_silentExtended_observe (observer : Nat) (state : CompositeState)
    (operation : AuthoritativeOperation) (hstate : AuthoritativeRuntimeWellFormed state)
    (hsilent : isSilentExtended observer state operation = true) :
    observe observer (authoritativeGate state operation).state = observe observer state := by
  cases operation with
  | ordinary operation =>
      rw [authoritativeGate_ordinary_state]
      rcases gate_state_cases state operation with hsame | happly
      · rw [hsame]
      · rw [happly]
        exact applyOperation_silentExtended_observe observer state operation
          (coherent_of hstate) hsilent
  | blocking operation =>
      exact authoritativeGate_silentCoherent_observe observer state (.blocking operation) hstate
        hsilent
  | drainDeferred subject =>
      simp only [isSilentExtended, Bool.and_eq_true, bne_iff_ne, ne_eq] at hsilent
      rw [authoritativeGate_drainDeferred_state]
      cases state.execution.mode with
      | running =>
          exact observe_drain_other observer state (blockingCoherent_of hstate) subject
            hsilent.2
      | handling active => rfl
      | halted record => rfl

/-! ## Finite traces with the extended families silent -/

def executeExtended (observer : Nat) (state : CompositeState)
    (operation : AuthoritativeOperation) : CompositeState × Option Event :=
  let outcome := authoritativeGate state operation
  (outcome.state,
    if isSilentExtended observer state operation then none
    else some
      { view := observe observer outcome.state
        reply := if actor state = observer then some outcome.result else none })

def systemExtended (observer : Nat) :
    ReplayUnwinding.System CompositeState AuthoritativeOperation Event View where
  observe := observe observer
  execute := executeExtended observer
  applyEvent _ event := event.view

def runExtended (observer : Nat) (state : CompositeState)
    (operations : List AuthoritativeOperation) : CompositeState × List Event :=
  ReplayUnwinding.run (systemExtended observer) state operations

def projectionExtended (observer : Nat) (state : CompositeState)
    (operations : List AuthoritativeOperation) : List Event :=
  ReplayUnwinding.projection (systemExtended observer) state operations

/-- The run's state component is exactly the authoritative gate trace. -/
theorem runExtended_state (observer : Nat) (state : CompositeState)
    (operations : List AuthoritativeOperation) :
    (runExtended observer state operations).1 =
      operations.foldl (fun current operation => (authoritativeGate current operation).state)
        state := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation rest ih =>
      simp only [runExtended, ReplayUnwinding.run, List.foldl] at ih ⊢
      exact ih _

theorem systemExtended_replaysOn (observer : Nat) :
    ReplayUnwinding.ReplaysOn (systemExtended observer) AuthoritativeRuntimeWellFormed := by
  apply ReplayUnwinding.replaysOn_of_unwinding
  · intro state operation hstate hnone
    simp only [systemExtended, executeExtended] at hnone ⊢
    split at hnone
    · rename_i hsilent
      exact authoritativeGate_silentExtended_observe observer state operation hstate hsilent
    · simp at hnone
  · intro state operation event _ hsome
    simp only [systemExtended, executeExtended] at hsome ⊢
    split at hsome
    · simp at hsome
    · simp only [Option.some.injEq] at hsome
      rw [← hsome]

/-- **Composite finite-trace noninterference with the extended families
silent.**  Scheduler operations that leave the scheduled subject in place,
transfers on endpoints the observer does not name, interrupts that contain no
scheduled subject, failed resumable switches, and drains of other subjects, all
by other subjects, emit no event in addition to the coherent families. -/
theorem finite_trace_lowEquiv_extended (observer : Nat) (left right : CompositeState)
    (leftOperations rightOperations : List AuthoritativeOperation)
    (hleft : AuthoritativeRuntimeWellFormed left)
    (hright : AuthoritativeRuntimeWellFormed right)
    (hlow : LowEquiv observer left right)
    (hevents : projectionExtended observer left leftOperations =
      projectionExtended observer right rightOperations) :
    LowEquiv observer (runExtended observer left leftOperations).1
      (runExtended observer right rightOperations).1 :=
  ReplayUnwinding.finite_trace_lowEquiv_on (systemExtended observer)
    (systemExtended_replaysOn observer)
    (fun state operation hstate =>
      authoritativeGate_preserves_authoritativeRuntimeWellFormed state operation hstate)
    left right leftOperations rightOperations hleft hright hlow hevents

end LeanOS.CompositeLocalRespect
