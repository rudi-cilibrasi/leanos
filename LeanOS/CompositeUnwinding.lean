import LeanOS.CompositeObservation

/-!
# Composite unwinding: coherent silent families, step and output consistency

`LeanOS.CompositeObservation` proves local respect for silent operation
families that need no invariant, and finite-trace noninterference by replay.
This module completes the three classical unwinding conditions over the same
observer view and the same `FailStop.authoritativeGate`, and states the
channels where they genuinely fail as theorems.

**Trace invariant.**  `FailStop.AuthoritativeRuntimeWellFormed` is preserved
by every authoritative operation
(`authoritativeGate_preserves_authoritativeRuntimeWellFormed`).  It carries
`CompositeState.Coherent` and the blocking-store coherence that the families
below need, so it is threaded through traces by
`ReplayUnwinding.finite_trace_lowEquiv_on`.

**More silent families** (`isSilentCoherent`, local respect
`authoritativeGate_silentCoherent_observe`): in addition to `isSilent`,
`protect` by another subject, `createSubject` of a subject other than the
observer, and blocking send, receive, and cancel that stay away from the
observer's named endpoints, waiter queue entries, waiter index, and
completion (a receive must also not block, since blocking changes the public
scheduler choice).

**Step consistency for the observer's own operations**
(`own_step_consistent`): when the observer is the scheduled subject of two
runtime-well-formed low-equivalent states in the same fail-stop mode
(`OwnStep`), `ipc`, `map`,
`unmap`, `protect`, `syscall`, `capabilityRevoke`, `capabilityCopy` to another
subject, `createSubject` of another subject, and the frame-rule families give
low-equivalent results.

**Output consistency** (`own_output_consistent`): under the same premises the
gate returns equal results for `ipc`, `map`, `unmap`, `protect`, `syscall`,
`capabilityCopy` into the observer's own row, `capabilityRevoke` of the
observer's own slot, and `restart`.

**Classical noninterference for the observer's own runs**
(`own_run_noninterference`): step and output consistency compose, so the same
run of the observer's operations that are in both families returns the same
gate results at every step and ends low-equivalent; equal observations are
concluded rather than assumed.

**Channels stated as theorems.**  The global capability-identity counter
(`identity_counter_step_inconsistent`) and the liveness and slot occupancy of
a delegation's destination (`copy_destination_output_inconsistent`) are real
channels of the model.  They are proved to break step consistency and output
consistency respectively, so they are exclusions of the claim rather than
gaps hidden by it.
-/
namespace LeanOS.CompositeUnwinding

open LeanOS
open LeanOS.FailStop
open LeanOS.CompositeObservation
set_option linter.unusedSimpArgs false

abbrev SubjectId := Capability.SubjectId
abbrev ObjectId := Capability.ObjectId

/-! ## The trace invariant -/

theorem coherent_of {state : CompositeState}
    (hstate : AuthoritativeRuntimeWellFormed state) : state.Coherent :=
  hstate.left.1

theorem blockingCoherent_of {state : CompositeState}
    (hstate : AuthoritativeRuntimeWellFormed state) : state.BlockingIPCCoherent := by
  rcases hstate.left with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hblocking, _⟩
  exact hblocking

theorem capabilities_eq_lifecycle {state : CompositeState} (hcoherent : state.Coherent) :
    state.capabilities = state.lifecycle.capabilities :=
  hcoherent.2.2.2.1

theorem memoryCapabilities_eq {state : CompositeState} (hcoherent : state.Coherent) :
    state.virtualMemory.memory.capabilities = state.capabilities :=
  hcoherent.2.2.2.2.1.trans hcoherent.2.2.2.1.symm

theorem translations_eq {state : CompositeState} (hcoherent : state.Coherent) :
    state.resumable.translations.virtual = state.virtualMemory :=
  hcoherent.2.2.2.2.2.2.2.2.1

theorem blockingCurrent_eq {state : CompositeState} (hcoherent : state.BlockingIPCCoherent) :
    state.blockingIPC.scheduler.lifecycle.current = state.lifecycle.current := by
  rw [hcoherent.2]

/-- In a coherent state the scheduled subject is the actor and its own address
space is active. -/
theorem actor_of_current {state : CompositeState} {observer : SubjectId}
    (hcoherent : state.Coherent) (hcurrent : state.lifecycle.current = some observer) :
    actor state = observer ∧ state.execution.core.context.activeAddressSpace = observer :=
  hcoherent.2.2.2.2.2.2.2.2.2.2.1 observer hcurrent

/-! ## Additional silent families -/

/-- The endpoint a blocking send or receive resolves, exactly as
`dispatchBlockingSend` and `dispatchBlockingReceive` resolve it. -/
def blockingTarget (state : CompositeState) (handleWord : UInt64) : Option ObjectId :=
  match CapabilityHandle.resolveCurrent state.blockingIPC.scheduler.lifecycle.capabilities
      { caller := actor state } handleWord .endpoint with
  | .ok resolution => some resolution.capability.object
  | .error _ => none

/-- Whether any endpoint the observer names has `subject` in its waiter queue. -/
def NamedWaiter (state : CompositeState) (observer subject : SubjectId) : Bool :=
  (row state observer).any fun slot =>
    slot.any fun cap => (state.blockingIPC.waiters cap.object).contains subject

/-- Silence for blocking operations.  A send must resolve to an endpoint the
observer does not name, on which the observer is not waiting.  A receive must
resolve to an endpoint the observer does not name and must not block (the
caller has a reserved completion or the mailbox holds a message), since
blocking changes the public scheduler choice.  A cancellation must target a
subject other than the observer that waits on no endpoint the observer names. -/
def isSilentBlocking (observer : SubjectId) (state : CompositeState) :
    CompositeBlockingOperation → Bool
  | .send handleWord _ _ =>
      actor state != observer &&
        match blockingTarget state handleWord with
        | none => true
        | some endpoint =>
            !Names state observer endpoint &&
              !(state.blockingIPC.waiters endpoint).contains observer
  | .receive handleWord _ _ =>
      actor state != observer &&
        match blockingTarget state handleWord with
        | none => true
        | some endpoint =>
            !Names state observer endpoint &&
              ((state.blockingIPC.completion (actor state)).isSome ||
                (state.blockingIPC.mailbox endpoint).isSome)
  | .cancel subject =>
      actor state != observer && subject != observer &&
        !NamedWaiter state observer subject

/-- Ordinary families that are silent given composite coherence. -/
def isSilentCoherentOrdinary (observer : SubjectId) (state : CompositeState) :
    Operation → Bool
  | .protect _ _ => actor state != observer
  | .createSubject subject => actor state != observer && subject != observer
  | operation => isSilentOrdinary observer state operation

/-- The extended, still decidable, silence classification.  It agrees with
`isSilent` except that it also classifies the coherent families as silent. -/
def isSilentCoherent (observer : SubjectId) (state : CompositeState) :
    AuthoritativeOperation → Bool
  | .ordinary operation => isSilentCoherentOrdinary observer state operation
  | .blocking operation => isSilentBlocking observer state operation
  | .drainDeferred _ => false

theorem isSilentCoherent_of_isSilent {observer state operation}
    (hsilent : isSilent observer state operation = true) :
    isSilentCoherent observer state operation = true := by
  cases operation with
  | ordinary operation =>
      cases operation <;> simp_all [isSilent, isSilentCoherent, isSilentCoherentOrdinary,
        isSilentOrdinary]
  | blocking _ => simp [isSilent] at hsilent
  | drainDeferred _ => simp [isSilent] at hsilent

theorem isSilentCoherent_actor {observer state operation}
    (hsilent : isSilentCoherent observer state operation = true) : actor state ≠ observer := by
  cases operation with
  | ordinary operation =>
      cases operation <;>
        simp_all [isSilentCoherent, isSilentCoherentOrdinary, isSilentOrdinary] <;>
        (try split at hsilent) <;> simp_all
  | blocking operation =>
      cases operation <;> simp_all [isSilentCoherent, isSilentBlocking]
  | drainDeferred _ => simp [isSilentCoherent] at hsilent

/-! ### Protection -/

theorem protect_frame (translations : TLB.State) actor space page permissions
    (observer : SubjectId) (hne : actor ≠ observer) :
    let next := (TLB.protect translations actor space page permissions).state.virtual
    next.owner = translations.virtual.owner ∧ next.memory = translations.virtual.memory ∧
      ∀ candidate, translations.virtual.owner candidate = some observer →
        next.mappings candidate = translations.virtual.mappings candidate := by
  simp only [TLB.protect]
  repeat' split
  all_goals simp_all [TLB.invalidatePage, VirtualMapping.setMapping]
  all_goals
    intro candidate hown
    funext candidatePage
    have hspace : candidate ≠ space := by
      intro hsame
      subst hsame
      simp_all
    simp [hspace]

/-! ### Subject creation -/

theorem create_frame (lifecycle : SubjectLifecycle.State) (subject observer : SubjectId)
    (hne : subject ≠ observer) :
    let next := (SubjectLifecycle.create lifecycle subject).state.capabilities
    next.subjects observer = lifecycle.capabilities.subjects observer ∧
      next.slotCapacity = lifecycle.capabilities.slotCapacity ∧
      next.slots = lifecycle.capabilities.slots ∧
      next.objects = lifecycle.capabilities.objects ∧
      next.kinds = lifecycle.capabilities.kinds := by
  simp only [SubjectLifecycle.create]
  repeat' split
  all_goals simp [SubjectLifecycle.reject, SubjectLifecycle.setBool, Ne.symm hne]

theorem observe_installCreatedSubject (observer : SubjectId) (state : CompositeState)
    (subject : SubjectId) (hne : subject ≠ observer) (hcoherent : state.Coherent) :
    observe observer (installCreatedSubject state subject) = observe observer state := by
  obtain ⟨hsubjects, hcapacity, hslots, hobjects, hkinds⟩ :=
    create_frame state.lifecycle subject observer hne
  have hcaps := capabilities_eq_lifecycle hcoherent
  apply observe_eq_of <;>
    simp [installCreatedSubject, objectView, hsubjects, hcapacity, hslots, hobjects, hkinds,
      hcaps]
  intro _ _
  rfl

/-! ### Blocking IPC frames -/

/-- A blocking send changes only its endpoint's mailbox and queue and, on a
wake, the woken receiver's waiter index and completion.  The scheduled subject
is unchanged. -/
theorem blockingSend_frame (blocking : BlockingIPC.State) caller slot payload
    (cap : Capability.Capability)
    (hlookup : Capability.lookup blocking.scheduler.lifecycle.capabilities caller slot =
      .found cap)
    (observer : SubjectId) (hwaiter : (blocking.waiters cap.object).contains observer = false) :
    let next := (BlockingIPC.send blocking caller slot payload).state
    next.scheduler.lifecycle.current = blocking.scheduler.lifecycle.current ∧
      (∀ object, object ≠ cap.object →
        next.mailbox object = blocking.mailbox object ∧
          next.waiters object = blocking.waiters object) ∧
      next.waiterEndpoint observer = blocking.waiterEndpoint observer ∧
      next.completion observer = blocking.completion observer := by
  simp only [BlockingIPC.send, hlookup]
  repeat' split
  all_goals simp_all [BlockingIPC.reject, BlockingIPC.setMailbox, BlockingIPC.wakeState,
    BlockingIPC.setWaiters, BlockingIPC.setWaiterEndpoint, BlockingIPC.setCompletion]
  all_goals
    first
      | (intro object hne; simp [hne])
      | skip
  all_goals
    rename_i receiver rest hqueue _
    have : receiver ≠ observer := by
      intro heq
      subst heq
      simp [hqueue] at hwaiter
    simp [Ne.symm this]

/-- A receive with a reserved completion or a queued message never blocks; it
changes only the caller's completion or its endpoint's mailbox. -/
theorem blockingReceive_frame (blocking : BlockingIPC.State) caller slot
    (cap : Capability.Capability)
    (hlookup : Capability.lookup blocking.scheduler.lifecycle.capabilities caller slot =
      .found cap)
    (hready : (blocking.completion caller).isSome = true ∨
      (blocking.mailbox cap.object).isSome = true)
    (observer : SubjectId) (hne : caller ≠ observer) :
    let outcome := BlockingIPC.receiveOrBlock blocking caller slot
    outcome.result ≠ .blocked ∧
      outcome.state.scheduler = blocking.scheduler ∧
      (∀ object, object ≠ cap.object →
        outcome.state.mailbox object = blocking.mailbox object) ∧
      outcome.state.waiters = blocking.waiters ∧
      outcome.state.waiterEndpoint = blocking.waiterEndpoint ∧
      outcome.state.completion observer = blocking.completion observer := by
  simp only [BlockingIPC.receiveOrBlock, hlookup]
  repeat' split
  all_goals simp_all [BlockingIPC.rejectReceive, BlockingIPC.setMailbox,
    BlockingIPC.setCompletion, Ne.symm hne]
  all_goals (intro object hobject; simp [hobject])

/-- Cancelling another subject leaves the scheduled subject, every mailbox,
the observer's waiter index and completion, and every queue not containing the
cancelled subject unchanged. -/
theorem blockingCancel_frame (blocking : BlockingIPC.State) (subject observer : SubjectId)
    (hne : subject ≠ observer) :
    let next := BlockingIPC.cancelSubject blocking subject
    next.scheduler.lifecycle.current = blocking.scheduler.lifecycle.current ∧
      next.mailbox = blocking.mailbox ∧
      (∀ object, (blocking.waiters object).contains subject = false →
        next.waiters object = blocking.waiters object) ∧
      next.waiterEndpoint observer = blocking.waiterEndpoint observer ∧
      next.completion observer = blocking.completion observer := by
  simp only [BlockingIPC.cancelSubject]
  repeat' split
  all_goals simp_all [BlockingIPC.removeWaiter, BlockingIPC.setWaiterEndpoint,
    BlockingIPC.setCompletion, Ne.symm hne]
  all_goals
    intro object hnot waiter hmem heq
    subst heq
    exact hnot hmem

/-! ### Blocking publication -/

theorem observe_publishBlockingIPCContext (observer : SubjectId) (state : CompositeState)
    (blocking : BlockingIPCContext.State)
    (hcurrent : blocking.ipc.scheduler.lifecycle.current = state.lifecycle.current)
    (hnamed : ∀ object, Names state observer object = true →
      blocking.ipc.mailbox object = state.blockingIPC.mailbox object ∧
        blocking.ipc.waiters object = state.blockingIPC.waiters object)
    (hwaiting : blocking.ipc.waiterEndpoint observer =
      state.blockingIPC.waiterEndpoint observer)
    (hcompletion : blocking.ipc.completion observer = state.blockingIPC.completion observer) :
    observe observer (publishBlockingIPCContext state blocking) = observe observer state := by
  apply observe_eq_of <;> simp [publishBlockingIPCContext, objectView, hcurrent, hwaiting,
    hcompletion]
  intro object hnames
  obtain ⟨hmailbox, hwaiters⟩ := hnamed object hnames
  exact ⟨hmailbox, hwaiters, rfl⟩

theorem publishReleasedBlockingContext_observe (observer : SubjectId) (state : CompositeState)
    (blocking : BlockingIPCContext.State) (saved : ResumableContext.Context)
    (next : CompositeState)
    (hpublished : publishReleasedBlockingContext state blocking saved = .ok next) :
    observe observer next = observe observer (publishBlockingIPCContext state blocking) := by
  unfold publishReleasedBlockingContext at hpublished
  split at hpublished <;> try contradiction
  split at hpublished <;> try contradiction
  split at hpublished <;> try contradiction
  split at hpublished <;> try contradiction
  simp only [Except.ok.injEq] at hpublished
  subst next
  rfl

theorem blockingTarget_of_resolve (state : CompositeState) (handleWord : UInt64)
    (resolution : CapabilityHandle.Resolution)
    (hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities
      { caller := state.execution.core.context.currentSubject } handleWord .endpoint =
        .ok resolution) :
    blockingTarget state handleWord = some resolution.capability.object := by
  simp only [blockingTarget, actor, hresolve]

/-- Local respect for a silent blocking send. -/
theorem observe_dispatchBlockingSend (observer : SubjectId) (state : CompositeState)
    (handleWord word0 word1 : UInt64) (hcoherent : state.BlockingIPCCoherent)
    (hsilent : isSilentBlocking observer state (.send handleWord word0 word1) = true) :
    observe observer (dispatchBlockingSend state handleWord word0 word1).state =
      observe observer state := by
  simp only [isSilentBlocking, Bool.and_eq_true] at hsilent
  obtain ⟨_, htarget⟩ := hsilent
  cases hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities
      { caller := state.execution.core.context.currentSubject } handleWord .endpoint with
  | error reason => simp [dispatchBlockingSend, hresolve]
  | ok resolution =>
    rw [blockingTarget_of_resolve state handleWord resolution hresolve] at htarget
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at htarget
    obtain ⟨hnotNamed, hnotWaiting⟩ := htarget
    have hlookup := resolveCurrent_ok_lookup _ _ _ _ _ hresolve
    obtain ⟨hcurrent, hother, hwaiting, hcompletion⟩ := blockingSend_frame state.blockingIPC
      _ _ { word0, word1 } _ hlookup observer hnotWaiting
    have hraw : ∀ (outcome : BlockingIPCContext.SendOutcome),
        BlockingIPCContext.send state.blockingIPCContext
          state.execution.core.context.currentSubject resolution.handle.slot
          { word0, word1 } = outcome →
        outcome.result = .accepted →
        observe observer (publishBlockingIPCContext state outcome.state) =
          observe observer state := by
      intro outcome houtcome haccepted
      have hexact := (BlockingIPCContext.send_accepted_ipc_exact state.blockingIPCContext
        state.execution.core.context.currentSubject resolution.handle.slot { word0, word1 }
        (by rw [houtcome]; exact haccepted)).1
      rw [houtcome] at hexact
      apply observe_publishBlockingIPCContext
      · rw [hexact, ← blockingCurrent_eq hcoherent]
        exact hcurrent
      · intro object hnames
        have hne : object ≠ resolution.capability.object := by
          intro hsame
          subst hsame
          simp [hnames] at hnotNamed
        rw [hexact]
        exact hother object hne
      · rw [hexact]
        exact hwaiting
      · rw [hexact]
        exact hcompletion
    simp only [dispatchBlockingSend, hresolve]
    generalize houtcome : BlockingIPCContext.send state.blockingIPCContext
      state.execution.core.context.currentSubject resolution.handle.slot
      { word0, word1 } = outcome
    rcases outcome with ⟨next, result, released⟩
    cases result with
    | ipcRejected reason => rfl
    | contextRejected reason => rfl
    | accepted =>
        have hpublish := hraw _ houtcome rfl
        cases released with
        | none => exact hpublish
        | some saved =>
            simp only
            split
            · rfl
            · rename_i published hpublished
              rw [publishReleasedBlockingContext_observe observer state _ saved published
                hpublished]
              exact hpublish

/-- Local respect for a silent (non-blocking) blocking receive. -/
theorem observe_dispatchBlockingReceive (observer : SubjectId) (state : CompositeState)
    (handleWord : UInt64) (frame : Interrupt.HardwareFrame)
    (registers : ResumableContext.Registers) (hcoherent : state.BlockingIPCCoherent)
    (hsilent : isSilentBlocking observer state (.receive handleWord frame registers) = true) :
    observe observer (dispatchBlockingReceive state handleWord frame registers).state =
      observe observer state := by
  simp only [isSilentBlocking, Bool.and_eq_true, bne_iff_ne, ne_eq] at hsilent
  obtain ⟨hactor, htarget⟩ := hsilent
  cases hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities
      { caller := state.execution.core.context.currentSubject } handleWord .endpoint with
  | error reason => simp [dispatchBlockingReceive, hresolve]
  | ok resolution =>
    rw [blockingTarget_of_resolve state handleWord resolution hresolve] at htarget
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true] at htarget
    obtain ⟨hnotNamed, hready⟩ := htarget
    have hlookup := resolveCurrent_ok_lookup _ _ _ _ _ hresolve
    obtain ⟨hnotBlocked, hscheduler, hmailbox, hwaiters, hwaiting, hcompletion⟩ :=
      blockingReceive_frame state.blockingIPC _ _ _ hlookup hready observer hactor
    simp only [dispatchBlockingReceive, hresolve]
    generalize houtcome : BlockingIPCContext.receiveOrBlock state.blockingIPCContext
      state.execution.core.context.currentSubject resolution.handle.slot
      (state.blockingSavedContext frame registers) = outcome
    rcases outcome with ⟨next, result⟩
    cases result with
    | contextRejected reason => rfl
    | completed result =>
        cases result with
        | rejected reason => rfl
        | blocked =>
            have hexact := (BlockingIPCContext.receive_blocked_ipc_exact
              state.blockingIPCContext _ _ _ (by rw [houtcome])).2
            exact absurd hexact hnotBlocked
        | delivered envelope =>
            have hexact := (BlockingIPCContext.receive_delivered_ipc_exact
              state.blockingIPCContext _ _ _ envelope (by rw [houtcome])).1
            rw [houtcome] at hexact
            dsimp only [CompositeState.blockingIPCContext] at hexact
            apply observe_publishBlockingIPCContext
            · simp only [hexact, hscheduler]
              exact blockingCurrent_eq hcoherent
            · intro object hnames
              have hne : object ≠ resolution.capability.object := by
                intro hsame
                subst hsame
                simp [hnames] at hnotNamed
              simp only [hexact]
              exact ⟨hmailbox object hne, by rw [hwaiters]⟩
            · simp only [hexact, hwaiting]
            · simp only [hexact]
              exact hcompletion

theorem cancelSubjectTyped_cancelled_state (blocking : BlockingIPC.State) (subject : SubjectId)
    (hcancelled : (BlockingIPC.cancelSubjectTyped blocking subject).result = .cancelled) :
    (BlockingIPC.cancelSubjectTyped blocking subject).state =
      BlockingIPC.cancelSubject blocking subject := by
  unfold BlockingIPC.cancelSubjectTyped at hcancelled ⊢
  split at hcancelled
  · simp at hcancelled
  · split at hcancelled
    · simp at hcancelled
    · rename_i hif
      simp [hif]

/-- Local respect for a silent blocking cancellation. -/
theorem observe_dispatchBlockingCancel (observer : SubjectId) (state : CompositeState)
    (subject : SubjectId) (hcoherent : state.BlockingIPCCoherent)
    (hsilent : isSilentBlocking observer state (.cancel subject) = true) :
    observe observer (dispatchBlockingCancel state subject).state = observe observer state := by
  simp only [isSilentBlocking, Bool.and_eq_true, bne_iff_ne, ne_eq,
    Bool.not_eq_true'] at hsilent
  obtain ⟨⟨_, hsubject⟩, hnotNamed⟩ := hsilent
  obtain ⟨hcurrent, hmailbox, hwaiters, hwaiting, hcompletion⟩ :=
    blockingCancel_frame state.blockingIPC subject observer hsubject
  have hraw : ∀ (outcome : BlockingIPCContext.CancelOutcome),
      BlockingIPCContext.cancel state.blockingIPCContext subject = outcome →
      outcome.result = .cancelled →
      observe observer (publishBlockingIPCContext state outcome.state) =
        observe observer state := by
    intro outcome houtcome hcancelled
    have hexact := BlockingIPCContext.cancel_cancelled_ipc_exact state.blockingIPCContext
      subject (by rw [houtcome]; exact hcancelled)
    rw [houtcome] at hexact
    have hstate : outcome.state.ipc = BlockingIPC.cancelSubject state.blockingIPC subject :=
      hexact.1.trans (cancelSubjectTyped_cancelled_state _ _ hexact.2)
    apply observe_publishBlockingIPCContext
    · rw [hstate, hcurrent]
      exact blockingCurrent_eq hcoherent
    · intro object hnames
      rw [hstate, hmailbox]
      refine ⟨rfl, hwaiters object ?_⟩
      cases hcontains : (state.blockingIPC.waiters object).contains subject with
      | false => rfl
      | true =>
          exfalso
          have hnamedWaiter : NamedWaiter state observer subject = true := by
            simp only [Names, List.any_eq_true] at hnames
            obtain ⟨slot, hmem, hslot⟩ := hnames
            simp only [NamedWaiter, List.any_eq_true]
            refine ⟨slot, hmem, ?_⟩
            cases slot with
            | none => simp at hslot
            | some cap =>
                simp only [Option.any_some, beq_iff_eq] at hslot ⊢
                rw [hslot]
                exact hcontains
          rw [hnamedWaiter] at hnotNamed
          exact Bool.false_ne_true hnotNamed.symm
    · rw [hstate]
      exact hwaiting
    · rw [hstate]
      exact hcompletion
  unfold dispatchBlockingCancel
  generalize houtcome : BlockingIPCContext.cancel state.blockingIPCContext subject = outcome
  rcases outcome with ⟨next, result, released⟩
  cases result with
  | notWaiting => rfl
  | ipcRejected reason => rfl
  | contextRejected reason => rfl
  | cancelled =>
      have hpublish := hraw _ houtcome rfl
      cases released with
      | none => rfl
      | some saved =>
          simp only
          split
          · rfl
          · rename_i published hpublished
            rw [publishReleasedBlockingContext_observe observer state _ saved published
              hpublished]
            exact hpublish

/-! ### Local respect for the coherent families -/

/-- **Local respect** for ordinary operations under composite coherence. -/
theorem applyOperation_silentCoherent_observe (observer : SubjectId) (state : CompositeState)
    (operation : Operation) (hcoherent : state.Coherent)
    (hsilent : isSilentCoherentOrdinary observer state operation = true) :
    observe observer (applyOperation state operation) = observe observer state := by
  cases operation with
  | protect page permissions =>
      simp only [isSilentCoherentOrdinary, bne_iff_ne, ne_eq, actor] at hsilent
      obtain ⟨howner, hmemory, hmappings⟩ := protect_frame state.resumable.translations
        state.execution.core.context.currentSubject
        state.execution.core.context.activeAddressSpace page permissions observer hsilent
      rw [translations_eq hcoherent] at howner hmemory hmappings
      simp only [applyOperation]
      split
      · rfl
      · exact observe_installVirtualMemory observer state _ _ howner hmemory hmappings
  | createSubject subject =>
      simp only [isSilentCoherentOrdinary, Bool.and_eq_true, bne_iff_ne, ne_eq] at hsilent
      simp only [applyOperation]
      split
      · rfl
      · exact observe_installCreatedSubject observer state subject hsilent.2 hcoherent
  | interrupt frame => exact applyOperation_silent_observe observer state _ hsilent
  | nmi raw context => exact applyOperation_silent_observe observer state _ hsilent
  | selectUserReturn purpose => exact applyOperation_silent_observe observer state _ hsilent
  | userReturn request => exact applyOperation_silent_observe observer state _ hsilent
  | syscall call => exact applyOperation_silent_observe observer state _ hsilent
  | ipc call => exact applyOperation_silent_observe observer state _ hsilent
  | resumePreempt frame registers =>
      exact applyOperation_silent_observe observer state _ hsilent
  | transferOffer endpointWord sourceWord sourceKind payload rights =>
      exact applyOperation_silent_observe observer state _ hsilent
  | transferAccept endpointWord destinationSlot =>
      exact applyOperation_silent_observe observer state _ hsilent
  | capabilityCopy source destination destinationSlot rights =>
      exact applyOperation_silent_observe observer state _ hsilent
  | capabilityRevoke authoritySlot victim victimSlot =>
      exact applyOperation_silent_observe observer state _ hsilent
  | capabilityRevokeSubtree authoritySlot victim victimSlot =>
      exact applyOperation_silent_observe observer state _ hsilent
  | map slot page permissions => exact applyOperation_silent_observe observer state _ hsilent
  | unmap page => exact applyOperation_silent_observe observer state _ hsilent
  | terminateSubject subject => exact applyOperation_silent_observe observer state _ hsilent
  | scheduleAdd subject => exact applyOperation_silent_observe observer state _ hsilent
  | scheduleRemove subject => exact applyOperation_silent_observe observer state _ hsilent
  | scheduleNext => exact applyOperation_silent_observe observer state _ hsilent
  | scheduleYield => exact applyOperation_silent_observe observer state _ hsilent
  | scheduleTick => exact applyOperation_silent_observe observer state _ hsilent
  | terminateCurrent => exact applyOperation_silent_observe observer state _ hsilent
  | restart => exact applyOperation_silent_observe observer state _ hsilent

/-- **Local respect** on the authoritative gate for the extended
classification, including busy and halted stutters, given the trace
invariant. -/
theorem authoritativeGate_silentCoherent_observe (observer : SubjectId)
    (state : CompositeState) (operation : AuthoritativeOperation)
    (hstate : AuthoritativeRuntimeWellFormed state)
    (hsilent : isSilentCoherent observer state operation = true) :
    observe observer (authoritativeGate state operation).state = observe observer state := by
  cases operation with
  | ordinary operation =>
      rw [authoritativeGate_ordinary_state]
      rcases gate_state_cases state operation with hsame | happly
      · rw [hsame]
      · rw [happly]
        exact applyOperation_silentCoherent_observe observer state operation
          (coherent_of hstate) hsilent
  | blocking operation =>
      rw [authoritativeGate_blocking_state]
      have hblocking := blockingCoherent_of hstate
      cases hmode : state.execution.mode with
      | handling active => simp [blockingGate, hmode]
      | halted record => simp [blockingGate, hmode]
      | running =>
          rw [blockingGate_running_exact state operation hmode]
          cases operation with
          | send handleWord word0 word1 =>
              exact observe_dispatchBlockingSend observer state handleWord word0 word1
                hblocking hsilent
          | receive handleWord frame registers =>
              exact observe_dispatchBlockingReceive observer state handleWord frame registers
                hblocking hsilent
          | cancel subject =>
              exact observe_dispatchBlockingCancel observer state subject hblocking hsilent
  | drainDeferred _ => simp [isSilentCoherent] at hsilent

/-! ## Finite traces with the coherent families silent -/

/-- Execute one authoritative operation; operations silent under the extended
classification emit nothing. -/
def executeCoherent (observer : SubjectId) (state : CompositeState)
    (operation : AuthoritativeOperation) : CompositeState × Option Event :=
  let outcome := authoritativeGate state operation
  (outcome.state,
    if isSilentCoherent observer state operation then none
    else some
      { view := observe observer outcome.state
        reply := if actor state = observer then some outcome.result else none })

def systemCoherent (observer : SubjectId) :
    ReplayUnwinding.System CompositeState AuthoritativeOperation Event View where
  observe := observe observer
  execute := executeCoherent observer
  applyEvent _ event := event.view

def runCoherent (observer : SubjectId) (state : CompositeState)
    (operations : List AuthoritativeOperation) : CompositeState × List Event :=
  ReplayUnwinding.run (systemCoherent observer) state operations

def projectionCoherent (observer : SubjectId) (state : CompositeState)
    (operations : List AuthoritativeOperation) : List Event :=
  ReplayUnwinding.projection (systemCoherent observer) state operations

/-- The run's state component is exactly the authoritative gate trace. -/
theorem runCoherent_state (observer : SubjectId) (state : CompositeState)
    (operations : List AuthoritativeOperation) :
    (runCoherent observer state operations).1 =
      operations.foldl (fun current operation => (authoritativeGate current operation).state)
        state := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation rest ih =>
      simp only [runCoherent, ReplayUnwinding.run, List.foldl] at ih ⊢
      exact ih _

/-- The trace invariant is preserved by every step. -/
theorem systemCoherent_preserves (observer : SubjectId) :
    ReplayUnwinding.Preserves (systemCoherent observer) AuthoritativeRuntimeWellFormed :=
  fun state operation hstate =>
    authoritativeGate_preserves_authoritativeRuntimeWellFormed state operation hstate

theorem systemCoherent_replaysOn (observer : SubjectId) :
    ReplayUnwinding.ReplaysOn (systemCoherent observer) AuthoritativeRuntimeWellFormed := by
  apply ReplayUnwinding.replaysOn_of_unwinding
  · intro state operation hstate hnone
    simp only [systemCoherent, executeCoherent] at hnone ⊢
    split at hnone
    · rename_i hsilent
      exact authoritativeGate_silentCoherent_observe observer state operation hstate hsilent
    · simp at hnone
  · intro state operation event _ hsome
    simp only [systemCoherent, executeCoherent] at hsome ⊢
    split at hsome
    · simp at hsome
    · simp only [Option.some.injEq] at hsome
      rw [← hsome]

/-- **Composite finite-trace noninterference with the coherent families
silent.**  From two well-formed, observer-low-equivalent composite states,
finite `authoritativeGate` runs with equal observer event projections end
low-equivalent.  `protect`, `createSubject`, and blocking send, receive, and
cancel by other subjects that stay away from the observer emit no event, so
the runs may contain different numbers and choices of them. -/
theorem finite_trace_lowEquiv_coherent (observer : SubjectId) (left right : CompositeState)
    (leftOperations rightOperations : List AuthoritativeOperation)
    (hleft : AuthoritativeRuntimeWellFormed left)
    (hright : AuthoritativeRuntimeWellFormed right)
    (hlow : LowEquiv observer left right)
    (hevents : projectionCoherent observer left leftOperations =
      projectionCoherent observer right rightOperations) :
    LowEquiv observer (runCoherent observer left leftOperations).1
      (runCoherent observer right rightOperations).1 :=
  ReplayUnwinding.finite_trace_lowEquiv_on (systemCoherent observer)
    (systemCoherent_replaysOn observer) (systemCoherent_preserves observer)
    left right leftOperations rightOperations hleft hright hlow hevents

/-! ## Step consistency for the observer's own operations -/

/-- The scheduled subject owns its own address space. -/
theorem owner_current {state : CompositeState} {observer : SubjectId}
    (hstate : RuntimeWellFormed state) (hcurrent : state.lifecycle.current = some observer) :
    state.virtualMemory.owner observer = some observer := by
  rcases hstate with ⟨hcoherent, _, _, _, _, _, hscheduler, _, hresumable, _⟩
  have hagree := hresumable.2.2.2.2.2.2.1.1
  rw [hcoherent.2.2.2.2.2.2.2.1, hcoherent.2.1, translations_eq hcoherent] at hagree
  have hsched := hscheduler.2.2.2.2 observer (by rw [hcoherent.2.1]; exact hcurrent)
  obtain ⟨_, _, howns, _⟩ := hsched
  unfold Scheduler.ownsAddressSpace at howns
  split at howns
  · rename_i hown
    rw [hagree, ← hcoherent.2.1]
    exact hown
  · contradiction

/-- Premises of step and output consistency for the observer's own
operations: two runtime-well-formed, low-equivalent states in which the
observer is the scheduled subject and the shared fail-stop latch is in the
same mode. -/
structure OwnStep (observer : SubjectId) (left right : CompositeState) : Prop where
  low : LowEquiv observer left right
  leftWF : RuntimeWellFormed left
  rightWF : RuntimeWellFormed right
  current : left.lifecycle.current = some observer
  mode : left.execution.mode = right.execution.mode

theorem OwnStep.rightCurrent {observer left right} (h : OwnStep observer left right) :
    right.lifecycle.current = some observer :=
  h.low.scheduled ▸ h.current

theorem OwnStep.leftActor {observer left right} (h : OwnStep observer left right) :
    left.execution.core.context.currentSubject = observer ∧
      left.execution.core.context.activeAddressSpace = observer :=
  actor_of_current h.leftWF.1 h.current

theorem OwnStep.rightActor {observer left right} (h : OwnStep observer left right) :
    right.execution.core.context.currentSubject = observer ∧
      right.execution.core.context.activeAddressSpace = observer :=
  actor_of_current h.rightWF.1 h.rightCurrent

/-- With equal modes, the gate either stutters on both sides or applies the
operation on both sides. -/
theorem gate_state_pair (left right : CompositeState) (operation : Operation)
    (hmode : left.execution.mode = right.execution.mode) :
    ((gate left operation).state = left ∧ (gate right operation).state = right) ∨
      ((gate left operation).state = applyOperation left operation ∧
        (gate right operation).state = applyOperation right operation) := by
  cases operation <;> cases hleft : left.execution.mode <;>
    simp_all [gate] <;> simp [← hmode]

/-- Gate-level step consistency from step consistency of `applyOperation`. -/
theorem lowEquiv_gate_of_apply {observer : SubjectId} {left right : CompositeState}
    {operation : Operation} (hlow : LowEquiv observer left right)
    (hmode : left.execution.mode = right.execution.mode)
    (happly : LowEquiv observer (applyOperation left operation)
      (applyOperation right operation)) :
    LowEquiv observer (authoritativeGate left (.ordinary operation)).state
      (authoritativeGate right (.ordinary operation)).state := by
  rw [authoritativeGate_ordinary_state, authoritativeGate_ordinary_state]
  rcases gate_state_pair left right operation hmode with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · rw [hl, hr]
    exact hlow
  · rw [hl, hr]
    exact happly

/-- Step consistency when the operation leaves each side's view unchanged. -/
theorem lowEquiv_of_unchanged {observer : SubjectId} {left right left' right' : CompositeState}
    (hlow : LowEquiv observer left right)
    (hleft : observe observer left' = observe observer left)
    (hright : observe observer right' = observe observer right) :
    LowEquiv observer left' right' := by
  unfold LowEquiv at *
  rw [hleft, hright, hlow]

/-! ### Families whose effect stays outside the observer's view -/

theorem observe_apply_copy_other (observer : SubjectId) (state : CompositeState)
    (source destination destinationSlot : Nat) (rights : Capability.Rights)
    (hne : destination ≠ observer) :
    observe observer
        (applyOperation state (.capabilityCopy source destination destinationSlot rights)) =
      observe observer state := by
  obtain ⟨hsubjects, hcapacity, hslots, hobjects, hkinds⟩ :=
    copy_frame state.capabilities state.execution.core.context.currentSubject source
      destination destinationSlot rights observer hne
  simp only [applyOperation]
  split
  · rfl
  · exact observe_installCopiedCapabilities observer state _ hsubjects hcapacity hslots
      hobjects hkinds

theorem observe_apply_revoke_other (observer : SubjectId) (state : CompositeState)
    (authoritySlot victim victimSlot : Nat) (hne : victim ≠ observer) :
    observe observer
        (applyOperation state (.capabilityRevoke authoritySlot victim victimSlot)) =
      observe observer state := by
  obtain ⟨hsubjects, hcapacity, hslots, hobjects, hkinds⟩ :=
    revokeRuntimeSafe_frame state.capabilities state.execution.core.context.currentSubject
      authoritySlot victim victimSlot observer hne
  simp only [applyOperation]
  split
  · rfl
  · exact observe_installCopiedCapabilities observer state _ hsubjects hcapacity hslots
      hobjects hkinds

theorem observe_apply_create_other (observer : SubjectId) (state : CompositeState)
    (subject : SubjectId) (hne : subject ≠ observer) (hcoherent : state.Coherent) :
    observe observer (applyOperation state (.createSubject subject)) =
      observe observer state := by
  simp only [applyOperation]
  split
  · rfl
  · exact observe_installCreatedSubject observer state subject hne hcoherent

/-! ### Virtual-memory congruence -/

/-- What `VirtualMapping.map` reads about one memory object beyond its
capability: `backing` restated over a bare virtual-memory state. -/
def vmBacking (virtualMemory : VirtualMapping.State) (object : ObjectId) : Option Bool :=
  (virtualMemory.memory.binding object).map fun frame =>
    decide (virtualMemory.memory.allocator.status frame = .owned object)

theorem map_congr (a b : VirtualMapping.State) (actor slot space page permissions)
    (howner : a.owner space = b.owner space)
    (hlookup : Capability.lookup a.memory.capabilities actor slot =
      Capability.lookup b.memory.capabilities actor slot)
    (hpage : a.mappings space page = b.mappings space page)
    (hbacking : ∀ cap, Capability.lookup b.memory.capabilities actor slot = .found cap →
      vmBacking a cap.object = vmBacking b cap.object) :
    (VirtualMapping.map a actor slot space page permissions).result =
        (VirtualMapping.map b actor slot space page permissions).result ∧
      (VirtualMapping.map a actor slot space page permissions).state.mappings space page =
        (VirtualMapping.map b actor slot space page permissions).state.mappings space page := by
  simp only [VirtualMapping.map, howner, hlookup, hpage]
  cases hown : b.owner space with
  | none => simp [VirtualMapping.reject, hpage]
  | some owner =>
      simp only
      split
      · simp [VirtualMapping.reject, hpage]
      · cases hfound : Capability.lookup b.memory.capabilities actor slot with
        | invalidSubject => simp [VirtualMapping.reject, hpage]
        | staleSlot => simp [VirtualMapping.reject, hpage]
        | found cap =>
            have hback := hbacking cap hfound
            simp only [vmBacking] at hback
            simp only
            by_cases hkind : cap.kind = .memory <;>
              by_cases hocc : (b.mappings space page).isSome = true <;>
              by_cases hperm : permissions.nonempty = true <;>
              by_cases hsub : VirtualMapping.permissionsSubset permissions cap.rights = true <;>
              simp [hkind, hocc, hperm, hsub, VirtualMapping.reject, hpage]
            cases ha : a.memory.binding cap.object <;>
              cases hb : b.memory.binding cap.object <;>
              simp_all [VirtualMapping.reject, VirtualMapping.setMapping]
            all_goals (split <;> simp_all [VirtualMapping.reject, VirtualMapping.setMapping])

theorem map_other (a : VirtualMapping.State) (actor slot space page permissions) :
    let next := (VirtualMapping.map a actor slot space page permissions).state
    next.owner = a.owner ∧ next.memory = a.memory ∧
      ∀ candidate candidatePage, ¬ (candidate = space ∧ candidatePage = page) →
        next.mappings candidate candidatePage = a.mappings candidate candidatePage := by
  simp only [VirtualMapping.map]
  repeat' split
  all_goals simp_all [VirtualMapping.reject, VirtualMapping.setMapping]

theorem unmap_other (a : VirtualMapping.State) (actor space page) :
    let next := (VirtualMapping.unmap a actor space page).state
    next.owner = a.owner ∧ next.memory = a.memory ∧
      ∀ candidate candidatePage, ¬ (candidate = space ∧ candidatePage = page) →
        next.mappings candidate candidatePage = a.mappings candidate candidatePage := by
  simp only [VirtualMapping.unmap]
  repeat' split
  all_goals simp_all [VirtualMapping.reject, VirtualMapping.setMapping]

theorem protect_other (a : TLB.State) (actor space page permissions) :
    let next := (TLB.protect a actor space page permissions).state.virtual
    next.owner = a.virtual.owner ∧ next.memory = a.virtual.memory ∧
      ∀ candidate candidatePage, ¬ (candidate = space ∧ candidatePage = page) →
        next.mappings candidate candidatePage = a.virtual.mappings candidate candidatePage := by
  simp only [TLB.protect]
  repeat' split
  all_goals simp_all [TLB.invalidatePage, VirtualMapping.setMapping]

theorem unmap_congr (a b : VirtualMapping.State) (actor space page)
    (howner : a.owner space = b.owner space)
    (hpage : a.mappings space page = b.mappings space page) :
    (VirtualMapping.unmap a actor space page).result =
        (VirtualMapping.unmap b actor space page).result ∧
      (VirtualMapping.unmap a actor space page).state.mappings space page =
        (VirtualMapping.unmap b actor space page).state.mappings space page := by
  simp only [VirtualMapping.unmap, howner, hpage]
  repeat' split
  all_goals simp_all [VirtualMapping.reject, VirtualMapping.setMapping]

theorem protect_congr (a b : TLB.State) (actor space page permissions)
    (howner : a.virtual.owner space = b.virtual.owner space)
    (hpage : a.virtual.mappings space page = b.virtual.mappings space page) :
    (TLB.protect a actor space page permissions).result =
        (TLB.protect b actor space page permissions).result ∧
      (TLB.protect a actor space page permissions).state.virtual.mappings space page =
        (TLB.protect b actor space page permissions).state.virtual.mappings space page := by
  simp only [TLB.protect, howner, hpage]
  repeat' split
  all_goals simp_all [TLB.invalidatePage, VirtualMapping.setMapping]

theorem backing_installVirtualMemory (state : CompositeState)
    (virtualMemory : VirtualMapping.State) (translations : TLB.State)
    (hmemory : virtualMemory.memory = state.virtualMemory.memory) :
    backing (installVirtualMemory state virtualMemory translations) = backing state := by
  funext object
  simp only [backing, installVirtualMemory, hmemory]

theorem observe_installVirtualMemory_eq (observer : SubjectId) (state : CompositeState)
    (virtualMemory : VirtualMapping.State) (translations : TLB.State)
    (howner : virtualMemory.owner = state.virtualMemory.owner)
    (hmemory : virtualMemory.memory = state.virtualMemory.memory) :
    observe observer (installVirtualMemory state virtualMemory translations) =
      { observe observer state with
        mappings := fun space page =>
          if state.virtualMemory.owner space = some observer then
            virtualMemory.mappings space page
          else none } := by
  have hview : ∀ object, objectView (installVirtualMemory state virtualMemory translations)
      object = objectView state object := by
    intro object
    simp only [objectView, backing_installVirtualMemory state virtualMemory translations hmemory]
    rfl
  simp only [observe, hview]
  simp only [installVirtualMemory, howner]
  rfl

/-- Two low-equivalent states that install virtual-memory states preserving
ownership and frame bindings, and agreeing on every space the observer owns,
stay low-equivalent. -/
theorem lowEquiv_installVirtualMemory {observer : SubjectId} {left right : CompositeState}
    (hlow : LowEquiv observer left right)
    (leftVirtual rightVirtual : VirtualMapping.State) (leftTLB rightTLB : TLB.State)
    (hleftOwner : leftVirtual.owner = left.virtualMemory.owner)
    (hrightOwner : rightVirtual.owner = right.virtualMemory.owner)
    (hleftMemory : leftVirtual.memory = left.virtualMemory.memory)
    (hrightMemory : rightVirtual.memory = right.virtualMemory.memory)
    (hmappings : ∀ space, left.virtualMemory.owner space = some observer →
      leftVirtual.mappings space = rightVirtual.mappings space) :
    LowEquiv observer (installVirtualMemory left leftVirtual leftTLB)
      (installVirtualMemory right rightVirtual rightTLB) := by
  unfold LowEquiv
  rw [observe_installVirtualMemory_eq observer left leftVirtual leftTLB hleftOwner hleftMemory,
    observe_installVirtualMemory_eq observer right rightVirtual rightTLB hrightOwner
      hrightMemory]
  have hmap : (fun space page =>
        if left.virtualMemory.owner space = some observer then
          leftVirtual.mappings space page else none) =
      (fun space page =>
        if right.virtualMemory.owner space = some observer then
          rightVirtual.mappings space page else none) := by
    funext space page
    by_cases hown : left.virtualMemory.owner space = some observer
    · simp [hown, (hlow.ownsIff space).1 hown, hmappings space hown]
    · have hown' : ¬ right.virtualMemory.owner space = some observer :=
        fun h => hown ((hlow.ownsIff space).2 h)
      simp [hown, hown']
  rw [hmap, hlow]

/-- A capability the observer can look up names an object in its row. -/
theorem names_of_lookup (state : CompositeState) (observer : SubjectId) (slot : Nat)
    (cap : Capability.Capability)
    (hfound : Capability.lookup state.capabilities observer slot = .found cap) :
    Names state observer cap.object = true := by
  obtain ⟨hin, hslot⟩ := lookup_found_inRange _ _ _ _ hfound
  have hmem : some cap ∈ row state observer := by
    rw [List.mem_iff_getElem?]
    exact ⟨slot, by rw [row_getElem? state observer slot hin, hslot]⟩
  simp only [Names, List.any_eq_true]
  exact ⟨some cap, hmem, by simp⟩

theorem OwnStep.lookup {observer left right} (h : OwnStep observer left right) (slot : Nat) :
    Capability.lookup left.capabilities observer slot =
      Capability.lookup right.capabilities observer slot :=
  h.low.lookup slot

/-- Objects the observer can look up in the right state have the same view on
both sides. -/
theorem OwnStep.lookupView {observer left right} (h : OwnStep observer left right)
    (slot : Nat) (cap : Capability.Capability)
    (hfound : Capability.lookup right.capabilities observer slot = .found cap) :
    CompositeObservation.objectView left cap.object =
      CompositeObservation.objectView right cap.object := by
  have hnames := names_of_lookup right observer slot cap hfound
  rw [← h.low.namesEq] at hnames
  exact h.low.namedView cap.object hnames

/-- Mapping-family step consistency from agreement on the observer's own
space: the page touched and every other page. -/
theorem lowEquiv_mapping_step {observer : SubjectId} {left right : CompositeState}
    (hlow : LowEquiv observer left right) (page : Nat)
    (leftVirtual rightVirtual : VirtualMapping.State) (leftTLB rightTLB : TLB.State)
    (hleftOwner : leftVirtual.owner = left.virtualMemory.owner)
    (hrightOwner : rightVirtual.owner = right.virtualMemory.owner)
    (hleftMemory : leftVirtual.memory = left.virtualMemory.memory)
    (hrightMemory : rightVirtual.memory = right.virtualMemory.memory)
    (hleftOther : ∀ candidate candidatePage, ¬ (candidate = observer ∧ candidatePage = page) →
      leftVirtual.mappings candidate candidatePage =
        left.virtualMemory.mappings candidate candidatePage)
    (hrightOther : ∀ candidate candidatePage, ¬ (candidate = observer ∧ candidatePage = page) →
      rightVirtual.mappings candidate candidatePage =
        right.virtualMemory.mappings candidate candidatePage)
    (hpage : leftVirtual.mappings observer page = rightVirtual.mappings observer page) :
    LowEquiv observer (installVirtualMemory left leftVirtual leftTLB)
      (installVirtualMemory right rightVirtual rightTLB) := by
  apply lowEquiv_installVirtualMemory hlow _ _ _ _ hleftOwner hrightOwner hleftMemory
    hrightMemory
  intro space hown
  funext candidatePage
  by_cases htouched : space = observer ∧ candidatePage = page
  · obtain ⟨rfl, rfl⟩ := htouched
    exact hpage
  · rw [hleftOther _ _ htouched, hrightOther _ _ htouched, hlow.ownedMappings space hown]

theorem own_step_map {observer : SubjectId} {left right : CompositeState}
    (h : OwnStep observer left right) (slot page : Nat)
    (permissions : VirtualMapping.Permissions) :
    LowEquiv observer (applyOperation left (.map slot page permissions))
      (applyOperation right (.map slot page permissions)) := by
  obtain ⟨hLs, hLa⟩ := h.leftActor
  obtain ⟨hRs, hRa⟩ := h.rightActor
  have hLown := owner_current h.leftWF h.current
  have hRown := owner_current h.rightWF h.rightCurrent
  have hcongr := map_congr left.virtualMemory right.virtualMemory observer slot observer page
    permissions (by rw [hLown, hRown])
    (by rw [memoryCapabilities_eq h.leftWF.1, memoryCapabilities_eq h.rightWF.1]
        exact h.lookup slot)
    (by rw [h.low.ownedMappings observer hLown])
    (fun cap hfound => by
      rw [memoryCapabilities_eq h.rightWF.1] at hfound
      exact congrArg ObjectView.backing (h.lookupView slot cap hfound))
  obtain ⟨hLowner, hLmemory, hLother⟩ := map_other left.virtualMemory observer slot observer
    page permissions
  obtain ⟨hRowner, hRmemory, hRother⟩ := map_other right.virtualMemory observer slot observer
    page permissions
  simp only [applyOperation, hLs, hLa, hRs, hRa]
  rw [hcongr.1]
  cases (VirtualMapping.map right.virtualMemory observer slot observer page permissions).result with
  | rejected reason => exact h.low
  | accepted =>
      exact lowEquiv_mapping_step h.low page _ _ _ _ hLowner hRowner hLmemory hRmemory
        hLother hRother hcongr.2

theorem own_step_unmap {observer : SubjectId} {left right : CompositeState}
    (h : OwnStep observer left right) (page : Nat) :
    LowEquiv observer (applyOperation left (.unmap page))
      (applyOperation right (.unmap page)) := by
  obtain ⟨hLs, hLa⟩ := h.leftActor
  obtain ⟨hRs, hRa⟩ := h.rightActor
  have hLown := owner_current h.leftWF h.current
  have hRown := owner_current h.rightWF h.rightCurrent
  have hcongr := unmap_congr left.virtualMemory right.virtualMemory observer observer page
    (by rw [hLown, hRown]) (by rw [h.low.ownedMappings observer hLown])
  obtain ⟨hLowner, hLmemory, hLother⟩ := unmap_other left.virtualMemory observer observer page
  obtain ⟨hRowner, hRmemory, hRother⟩ := unmap_other right.virtualMemory observer observer page
  simp only [applyOperation, hLs, hLa, hRs, hRa]
  rw [hcongr.1]
  cases (VirtualMapping.unmap right.virtualMemory observer observer page).result with
  | rejected reason => exact h.low
  | accepted =>
      exact lowEquiv_mapping_step h.low page _ _ _ _ hLowner hRowner hLmemory hRmemory
        hLother hRother hcongr.2

theorem own_step_protect {observer : SubjectId} {left right : CompositeState}
    (h : OwnStep observer left right) (page : Nat)
    (permissions : VirtualMapping.Permissions) :
    LowEquiv observer (applyOperation left (.protect page permissions))
      (applyOperation right (.protect page permissions)) := by
  obtain ⟨hLs, hLa⟩ := h.leftActor
  obtain ⟨hRs, hRa⟩ := h.rightActor
  have hLown := owner_current h.leftWF h.current
  have hRown := owner_current h.rightWF h.rightCurrent
  have hLtr := translations_eq h.leftWF.1
  have hRtr := translations_eq h.rightWF.1
  have hcongr := protect_congr left.resumable.translations right.resumable.translations
    observer observer page permissions (by rw [hLtr, hRtr, hLown, hRown])
    (by rw [hLtr, hRtr, h.low.ownedMappings observer hLown])
  obtain ⟨hLowner, hLmemory, hLother⟩ := protect_other left.resumable.translations observer
    observer page permissions
  obtain ⟨hRowner, hRmemory, hRother⟩ := protect_other right.resumable.translations observer
    observer page permissions
  rw [hLtr] at hLowner hLmemory hLother
  rw [hRtr] at hRowner hRmemory hRother
  simp only [applyOperation, hLs, hLa, hRs, hRa]
  rw [hcongr.1]
  cases (TLB.protect right.resumable.translations observer observer page permissions).result with
  | rejected reason => exact h.low
  | accepted =>
      exact lowEquiv_mapping_step h.low page _ _ _ _ hLowner hRowner hLmemory hRmemory
        hLother hRother hcongr.2

theorem lowEquiv_selectLiveReturnAuthority {observer : SubjectId} {left right : CompositeState}
    (hlow : LowEquiv observer left right) (leftPurpose rightPurpose : Interrupt.ReturnPurpose) :
    LowEquiv observer (selectLiveReturnAuthority left leftPurpose)
      (selectLiveReturnAuthority right rightPurpose) :=
  lowEquiv_of_unchanged hlow (observe_selectLiveReturnAuthority observer left leftPurpose)
    (observe_selectLiveReturnAuthority observer right rightPurpose)

theorem own_step_syscall {observer : SubjectId} {left right : CompositeState}
    (h : OwnStep observer left right) (call : Syscall.UntrustedCall) :
    LowEquiv observer (applyOperation left (.syscall call))
      (applyOperation right (.syscall call)) := by
  obtain ⟨hLs, hLa⟩ := h.leftActor
  obtain ⟨hRs, hRa⟩ := h.rightActor
  have hLown := owner_current h.leftWF h.current
  have hRown := owner_current h.rightWF h.rightCurrent
  cases hdecode : Syscall.decode call with
  | error reason =>
      simp only [applyOperation, Syscall.dispatch, hdecode]
      exact h.low
  | ok decoded =>
      cases decoded with
      | access page access =>
          -- An access check never changes the view, whatever its reply.
          have hL : observe observer (applyOperation left (.syscall call)) =
              observe observer left := by
            simp only [applyOperation, hdecode]
            split
            · rfl
            · exact observe_selectLiveReturnAuthority observer left _
          have hR : observe observer (applyOperation right (.syscall call)) =
              observe observer right := by
            simp only [applyOperation, hdecode]
            split
            · rfl
            · exact observe_selectLiveReturnAuthority observer right _
          exact lowEquiv_of_unchanged h.low hL hR
      | unmap page =>
          have hcongr := unmap_congr left.virtualMemory right.virtualMemory observer observer
            page (by rw [hLown, hRown]) (by rw [h.low.ownedMappings observer hLown])
          obtain ⟨hLowner, hLmemory, hLother⟩ :=
            unmap_other left.virtualMemory observer observer page
          obtain ⟨hRowner, hRmemory, hRother⟩ :=
            unmap_other right.virtualMemory observer observer page
          simp only [applyOperation, Syscall.dispatch, Syscall.dispatchDecoded, hdecode,
            CompositeState.syscallContext, hLs, hLa, hRs, hRa]
          rw [hcongr.1]
          cases (VirtualMapping.unmap right.virtualMemory observer observer page).result with
          | rejected reason => exact h.low
          | accepted =>
              exact lowEquiv_selectLiveReturnAuthority
                (lowEquiv_mapping_step h.low page _ _ _ _ hLowner hRowner hLmemory hRmemory
                  hLother hRother hcongr.2) _ _
      | map handleWord page permissions =>
          have hresolve : CapabilityHandle.resolveCurrent left.virtualMemory.memory.capabilities
                { caller := observer } handleWord .memory =
              CapabilityHandle.resolveCurrent right.virtualMemory.memory.capabilities
                { caller := observer } handleWord .memory := by
            rw [memoryCapabilities_eq h.leftWF.1, memoryCapabilities_eq h.rightWF.1]
            exact h.low.resolveCurrent handleWord .memory
          simp only [applyOperation, Syscall.dispatch, Syscall.dispatchDecoded, hdecode,
            CompositeState.syscallContext, hLs, hLa, hRs, hRa, hresolve]
          cases hres : CapabilityHandle.resolveCurrent right.virtualMemory.memory.capabilities
              { caller := observer } handleWord .memory with
          | error reason => exact h.low
          | ok resolution =>
              have hcongr := map_congr left.virtualMemory right.virtualMemory observer
                resolution.handle.slot observer page permissions (by rw [hLown, hRown])
                (by rw [memoryCapabilities_eq h.leftWF.1, memoryCapabilities_eq h.rightWF.1]
                    exact h.lookup _)
                (by rw [h.low.ownedMappings observer hLown])
                (fun cap hfound => by
                  rw [memoryCapabilities_eq h.rightWF.1] at hfound
                  exact congrArg ObjectView.backing (h.lookupView _ cap hfound))
              obtain ⟨hLowner, hLmemory, hLother⟩ := map_other left.virtualMemory observer
                resolution.handle.slot observer page permissions
              obtain ⟨hRowner, hRmemory, hRother⟩ := map_other right.virtualMemory observer
                resolution.handle.slot observer page permissions
              simp only
              rw [hcongr.1]
              cases (VirtualMapping.map right.virtualMemory observer resolution.handle.slot
                  observer page permissions).result with
              | rejected reason => exact h.low
              | accepted =>
                  exact lowEquiv_selectLiveReturnAuthority
                    (lowEquiv_mapping_step h.low page _ _ _ _ hLowner hRowner hLmemory
                      hRmemory hLother hRother hcongr.2) _ _

/-! ### The observer's own data-only IPC -/

theorem observe_installIPC_eq (observer : SubjectId) (state : CompositeState)
    (ipc : IPCSyscall.State) :
    observe observer (installIPC state ipc) =
      { observe observer state with
        named := (row state observer).map (Option.map fun cap =>
          { CompositeObservation.objectView state cap.object with
            mailbox := ipc.endpoints.mailbox cap.object }) } :=
  rfl

theorem lowEquiv_installIPC {observer : SubjectId} {left right : CompositeState}
    (hlow : LowEquiv observer left right) (leftIPC rightIPC : IPCSyscall.State)
    (hmailbox : ∀ object, Names left observer object = true →
      leftIPC.endpoints.mailbox object = rightIPC.endpoints.mailbox object) :
    LowEquiv observer (installIPC left leftIPC) (installIPC right rightIPC) := by
  unfold LowEquiv
  rw [observe_installIPC_eq, observe_installIPC_eq]
  have hnamed :
      (row left observer).map (Option.map fun cap =>
          { CompositeObservation.objectView left cap.object with
            mailbox := leftIPC.endpoints.mailbox cap.object }) =
        (row right observer).map (Option.map fun cap =>
          { CompositeObservation.objectView right cap.object with
            mailbox := rightIPC.endpoints.mailbox cap.object }) := by
    rw [← hlow.rowEq]
    apply List.map_congr_left
    intro slot hmem
    cases slot with
    | none => rfl
    | some cap =>
        have hnames : Names left observer cap.object = true := by
          simp only [Names, List.any_eq_true]
          exact ⟨some cap, hmem, by simp⟩
        simp only [Option.map_some, hlow.namedView cap.object hnames,
          hmailbox cap.object hnames]
  rw [hnamed, hlow]

theorem endpointSend_mailbox_congr (a b : EndpointIPC.State) caller slot payload
    (hlookup : Capability.lookup a.capabilities caller slot =
      Capability.lookup b.capabilities caller slot)
    (hobject : ∀ cap, Capability.lookup b.capabilities caller slot = .found cap →
      a.capabilities.objects cap.object = b.capabilities.objects cap.object ∧
        a.capabilities.kinds cap.object = b.capabilities.kinds cap.object ∧
        a.mailbox cap.object = b.mailbox cap.object)
    (object : ObjectId) (hmailbox : a.mailbox object = b.mailbox object) :
    (EndpointIPC.send a caller slot payload).state.mailbox object =
      (EndpointIPC.send b caller slot payload).state.mailbox object := by
  simp only [EndpointIPC.send, hlookup]
  cases hfound : Capability.lookup b.capabilities caller slot with
  | invalidSubject => simp [EndpointIPC.reject, hmailbox]
  | staleSlot => simp [EndpointIPC.reject, hmailbox]
  | found cap =>
      obtain ⟨hobjects, hkinds, hcapMailbox⟩ := hobject cap hfound
      simp only [hobjects, hkinds, hcapMailbox]
      repeat' split
      all_goals simp [EndpointIPC.reject, EndpointIPC.setOption, hmailbox]

theorem endpointReceive_mailbox_congr (a b : EndpointIPC.State) caller slot
    (hlookup : Capability.lookup a.capabilities caller slot =
      Capability.lookup b.capabilities caller slot)
    (hobject : ∀ cap, Capability.lookup b.capabilities caller slot = .found cap →
      a.capabilities.objects cap.object = b.capabilities.objects cap.object ∧
        a.capabilities.kinds cap.object = b.capabilities.kinds cap.object ∧
        a.mailbox cap.object = b.mailbox cap.object)
    (object : ObjectId) (hmailbox : a.mailbox object = b.mailbox object) :
    (EndpointIPC.receive a caller slot).state.mailbox object =
      (EndpointIPC.receive b caller slot).state.mailbox object := by
  simp only [EndpointIPC.receive, hlookup]
  cases hfound : Capability.lookup b.capabilities caller slot with
  | invalidSubject => simp [EndpointIPC.rejectReceive, hmailbox]
  | staleSlot => simp [EndpointIPC.rejectReceive, hmailbox]
  | found cap =>
      obtain ⟨hobjects, hkinds, hcapMailbox⟩ := hobject cap hfound
      simp only [hobjects, hkinds, hcapMailbox]
      repeat' split
      all_goals simp [EndpointIPC.rejectReceive, EndpointIPC.setOption, hmailbox]

/-- The endpoint fields the data-only IPC transitions read, for an object the
observer can look up. -/
theorem OwnStep.endpointObject {observer left right} (h : OwnStep observer left right)
    (slot : Nat) (cap : Capability.Capability)
    (hfound : Capability.lookup right.ipc.endpoints.capabilities observer slot = .found cap) :
    left.ipc.endpoints.capabilities.objects cap.object =
        right.ipc.endpoints.capabilities.objects cap.object ∧
      left.ipc.endpoints.capabilities.kinds cap.object =
        right.ipc.endpoints.capabilities.kinds cap.object ∧
      left.ipc.endpoints.mailbox cap.object = right.ipc.endpoints.mailbox cap.object := by
  have hL := (ipcCapabilitiesPublished_of_coherent h.leftWF.1).1
  have hR := (ipcCapabilitiesPublished_of_coherent h.rightWF.1).1
  rw [hR] at hfound
  have hview := h.lookupView slot cap hfound
  have hlive := congrArg ObjectView.live hview
  have hkind := congrArg ObjectView.kind hview
  have hmailbox := congrArg ObjectView.mailbox hview
  simp only [CompositeObservation.objectView] at hlive hkind hmailbox
  rw [hL, hR]
  exact ⟨hlive, hkind, hmailbox⟩

theorem OwnStep.endpointLookup {observer left right} (h : OwnStep observer left right)
    (slot : Nat) :
    Capability.lookup left.ipc.endpoints.capabilities observer slot =
      Capability.lookup right.ipc.endpoints.capabilities observer slot := by
  rw [(ipcCapabilitiesPublished_of_coherent h.leftWF.1).1,
    (ipcCapabilitiesPublished_of_coherent h.rightWF.1).1]
  exact h.lookup slot

theorem OwnStep.endpointResolve {observer left right} (h : OwnStep observer left right)
    (word : UInt64) :
    CapabilityHandle.resolveCurrent left.ipc.endpoints.capabilities { caller := observer } word
        .endpoint =
      CapabilityHandle.resolveCurrent right.ipc.endpoints.capabilities { caller := observer }
        word .endpoint := by
  rw [(ipcCapabilitiesPublished_of_coherent h.leftWF.1).1,
    (ipcCapabilitiesPublished_of_coherent h.rightWF.1).1]
  exact h.low.resolveCurrent word .endpoint

theorem OwnStep.namedMailbox {observer left right} (h : OwnStep observer left right)
    (object : ObjectId) (hnames : Names left observer object = true) :
    left.ipc.endpoints.mailbox object = right.ipc.endpoints.mailbox object :=
  congrArg ObjectView.mailbox (h.low.namedView object hnames)

/-- **Step consistency of the observer's data-only IPC transition.** -/
theorem own_step_dispatchIPC {observer : SubjectId} {left right : CompositeState}
    (h : OwnStep observer left right) (call : IPCSyscall.Call) :
    LowEquiv observer (dispatchIPC left call).state (dispatchIPC right call).state := by
  obtain ⟨hLs, _⟩ := h.leftActor
  obtain ⟨hRs, _⟩ := h.rightActor
  have hsendMailbox : ∀ handleWord word0 word1 object, Names left observer object = true →
      (IPCSyscall.dispatch left.ipc left.ipcContext (.send handleWord word0 word1)).state.endpoints.mailbox object =
        (IPCSyscall.dispatch right.ipc right.ipcContext (.send handleWord word0 word1)).state.endpoints.mailbox object := by
    intro handleWord word0 word1 object hnames
    simp only [IPCSyscall.dispatch, CompositeState.ipcContext, hLs, hRs,
      h.endpointResolve handleWord]
    split
    · exact h.namedMailbox object hnames
    · exact endpointSend_mailbox_congr _ _ _ _ _ (h.endpointLookup _)
        (fun cap hfound => h.endpointObject _ cap hfound) object
        (h.namedMailbox object hnames)
  have hreceiveMailbox : ∀ handleWord object, Names left observer object = true →
      (IPCSyscall.dispatch left.ipc left.ipcContext (.receive handleWord)).state.endpoints.mailbox object =
        (IPCSyscall.dispatch right.ipc right.ipcContext (.receive handleWord)).state.endpoints.mailbox object := by
    intro handleWord object hnames
    simp only [IPCSyscall.dispatch, CompositeState.ipcContext, hLs, hRs,
      h.endpointResolve handleWord]
    split
    · exact h.namedMailbox object hnames
    · exact endpointReceive_mailbox_congr _ _ _ _ (h.endpointLookup _)
        (fun cap hfound => h.endpointObject _ cap hfound) object
        (h.namedMailbox object hnames)
  cases call with
  | send handleWord word0 word1 =>
      exact lowEquiv_installIPC h.low _ _ (hsendMailbox handleWord word0 word1)
  | receive handleWord =>
      have hL := (ipcCapabilitiesPublished_of_coherent h.leftWF.1).2
      have hR := (ipcCapabilitiesPublished_of_coherent h.rightWF.1).2
      have hinstall := lowEquiv_installIPC h.low _ _ (hreceiveMailbox handleWord)
      simp only [dispatchIPC, hLs, hRs, hL, hR, h.low.resolveCurrent handleWord .endpoint]
      split
      · rename_i endpoint hresolve
        have hsealed := congrArg ObjectView.sealed
          (h.lookupView _ _ (resolveCurrent_ok_lookup _ _ _ _ _ hresolve))
        simp only [CompositeObservation.objectView] at hsealed
        rw [hsealed]
        split
        · exact h.low
        · exact hinstall
      · exact hinstall

theorem own_step_ipc {observer : SubjectId} {left right : CompositeState}
    (h : OwnStep observer left right) (call : IPCSyscall.Call) :
    LowEquiv observer (applyOperation left (.ipc call)) (applyOperation right (.ipc call)) := by
  have hreply : (dispatchIPC left call).reply = (dispatchIPC right call).reply := by
    have hout := ipc_output_consistent observer left right call h.low h.leftActor.1
      h.rightActor.1 (ipcCapabilitiesPublished_of_coherent h.leftWF.1)
      (ipcCapabilitiesPublished_of_coherent h.rightWF.1)
    simp only [operationReply, OperationReply.ipc.injEq] at hout
    exact hout
  have hstate := own_step_dispatchIPC h call
  simp only [applyOperation]
  rw [hreply]
  split <;> first | exact h.low | exact hstate

/-! ### The observer's own direct revocation -/

theorem revokeRuntimeSafe_self_congr (a b : Capability.State) (observer : SubjectId)
    (authoritySlot victimSlot : Nat)
    (hlookup : ∀ slot, Capability.lookup a observer slot = Capability.lookup b observer slot) :
    (Capability.revokeRuntimeSafe a observer authoritySlot observer victimSlot).result =
      (Capability.revokeRuntimeSafe b observer authoritySlot observer victimSlot).result := by
  simp only [Capability.revokeRuntimeSafe, Capability.revoke,
    Capability.directRevocationRuntimeSafe, hlookup authoritySlot, hlookup victimSlot]
  repeat' split
  all_goals simp_all [Capability.reject]

theorem revokeRuntimeSafe_accepted_state (a : Capability.State) (actor : SubjectId)
    (authoritySlot victim victimSlot : Nat)
    (haccepted : (Capability.revokeRuntimeSafe a actor authoritySlot victim victimSlot).result =
      .accepted) :
    (Capability.revokeRuntimeSafe a actor authoritySlot victim victimSlot).state =
      Capability.clear a victim victimSlot := by
  simp only [Capability.revokeRuntimeSafe, Capability.revoke] at haccepted ⊢
  repeat' split at haccepted
  all_goals simp_all [Capability.reject]
  all_goals (repeat' split) <;> simp_all [Capability.reject]

theorem observe_installCopiedCapabilities_eq (observer : SubjectId) (state : CompositeState)
    (capabilities : Capability.State)
    (hobjects : capabilities.objects = state.capabilities.objects)
    (hkinds : capabilities.kinds = state.capabilities.kinds) :
    observe observer (installCopiedCapabilities state capabilities) =
      { observe observer state with
        live := capabilities.subjects observer
        capacity := capabilities.slotCapacity observer
        row := Capability.capabilitySpace capabilities observer
        named := (Capability.capabilitySpace capabilities observer).map
          (Option.map fun cap => CompositeObservation.objectView state cap.object) } := by
  have hview : ∀ object,
      CompositeObservation.objectView (installCopiedCapabilities state capabilities) object =
        CompositeObservation.objectView state object := by
    intro object
    simp only [CompositeObservation.objectView, installCopiedCapabilities, hobjects, hkinds]
    rfl
  simp only [observe, hview]
  rfl

theorem lowEquiv_installCopiedCapabilities {observer : SubjectId} {left right : CompositeState}
    (hlow : LowEquiv observer left right) (leftCaps rightCaps : Capability.State)
    (hleftObjects : leftCaps.objects = left.capabilities.objects)
    (hleftKinds : leftCaps.kinds = left.capabilities.kinds)
    (hrightObjects : rightCaps.objects = right.capabilities.objects)
    (hrightKinds : rightCaps.kinds = right.capabilities.kinds)
    (hlive : leftCaps.subjects observer = rightCaps.subjects observer)
    (hcapacity : leftCaps.slotCapacity observer = rightCaps.slotCapacity observer)
    (hrow : Capability.capabilitySpace leftCaps observer =
      Capability.capabilitySpace rightCaps observer)
    (hnamed : ∀ cap, some cap ∈ Capability.capabilitySpace leftCaps observer →
      Names left observer cap.object = true) :
    LowEquiv observer (installCopiedCapabilities left leftCaps)
      (installCopiedCapabilities right rightCaps) := by
  unfold LowEquiv
  rw [observe_installCopiedCapabilities_eq observer left leftCaps hleftObjects hleftKinds,
    observe_installCopiedCapabilities_eq observer right rightCaps hrightObjects hrightKinds]
  have hnamedList :
      (Capability.capabilitySpace leftCaps observer).map
          (Option.map fun cap => CompositeObservation.objectView left cap.object) =
        (Capability.capabilitySpace rightCaps observer).map
          (Option.map fun cap => CompositeObservation.objectView right cap.object) := by
    rw [← hrow]
    apply List.map_congr_left
    intro slot hmem
    cases slot with
    | none => rfl
    | some cap =>
        simp only [Option.map_some, hlow.namedView cap.object (hnamed cap hmem)]
  rw [hnamedList, hlive, hcapacity, hrow, hlow]

theorem capabilitySpace_clear_self (capabilities : Capability.State) (subject : SubjectId)
    (slot : Nat) :
    Capability.capabilitySpace (Capability.clear capabilities subject slot) subject =
      (List.range (capabilities.slotCapacity subject)).map fun candidate =>
        if candidate = slot then none else capabilities.slots subject candidate := by
  simp [Capability.capabilitySpace, Capability.clear]

theorem own_step_revoke {observer : SubjectId} {left right : CompositeState}
    (h : OwnStep observer left right) (authoritySlot victim victimSlot : Nat) :
    LowEquiv observer (applyOperation left (.capabilityRevoke authoritySlot victim victimSlot))
      (applyOperation right (.capabilityRevoke authoritySlot victim victimSlot)) := by
  by_cases hvictim : victim = observer
  · subst hvictim
    obtain ⟨hLs, _⟩ := h.leftActor
    obtain ⟨hRs, _⟩ := h.rightActor
    have hresult := revokeRuntimeSafe_self_congr left.capabilities right.capabilities victim
      authoritySlot victimSlot h.lookup
    simp only [applyOperation, hLs, hRs]
    rw [hresult]
    cases hres : (Capability.revokeRuntimeSafe right.capabilities victim authoritySlot victim
        victimSlot).result with
    | rejected reason => exact h.low
    | accepted =>
        simp only
        rw [revokeRuntimeSafe_accepted_state _ _ _ _ _ (hresult.trans hres),
          revokeRuntimeSafe_accepted_state _ _ _ _ _ hres]
        have hcapacity := h.low.capacity
        apply lowEquiv_installCopiedCapabilities h.low <;> try rfl
        · exact h.low.live
        · exact hcapacity
        · rw [capabilitySpace_clear_self, capabilitySpace_clear_self, hcapacity]
          apply List.map_congr_left
          intro candidate hmem
          rw [List.mem_range] at hmem
          split
          · rfl
          · exact (h.low.slot candidate (hcapacity ▸ hmem)).1
        · intro cap hmem
          rw [capabilitySpace_clear_self, List.mem_map] at hmem
          obtain ⟨candidate, hrange, hslot⟩ := hmem
          rw [List.mem_range] at hrange
          split at hslot
          · simp at hslot
          · have hrow : some cap ∈ row left victim := by
              rw [List.mem_iff_getElem?]
              exact ⟨candidate, by rw [row_getElem? left victim candidate hrange, hslot]⟩
            simp only [Names, List.any_eq_true]
            exact ⟨some cap, hrow, by simp⟩
  · exact lowEquiv_of_unchanged h.low
      (observe_apply_revoke_other observer left authoritySlot victim victimSlot hvictim)
      (observe_apply_revoke_other observer right authoritySlot victim victimSlot hvictim)

/-! ### Step consistency: the family theorem -/

/-- The observer's own operations for which step consistency holds.  Copying
into the observer's own row is excluded: it allocates the identity of the new
capability from the global counter (`identity_counter_step_inconsistent`). -/
def ownStepConsistent (observer : SubjectId) : Operation → Bool
  | .nmi _ _ | .selectUserReturn _ | .userReturn _ | .restart => true
  | .ipc _ | .map _ _ _ | .unmap _ | .protect _ _ | .syscall _ => true
  | .capabilityRevoke _ _ _ => true
  | .capabilityCopy _ destination _ _ => destination != observer
  | .createSubject subject => subject != observer
  | _ => false

/-- **Step consistency for the observer's own operations.**  When the
observer is the scheduled subject of two runtime-well-formed, low-equivalent
composite states with the same fail-stop mode, each operation in
`ownStepConsistent` leaves the two states low-equivalent after
`authoritativeGate`. -/
theorem own_step_consistent {observer : SubjectId} {left right : CompositeState}
    (h : OwnStep observer left right) (operation : Operation)
    (hfamily : ownStepConsistent observer operation = true) :
    LowEquiv observer (authoritativeGate left (.ordinary operation)).state
      (authoritativeGate right (.ordinary operation)).state := by
  cases operation with
  | nmi raw context =>
      exact step_consistent_of_untouched observer left right _
        (by simp only [CompositeFootprint.Untouched, Operation.footprint]; decide) h.low
  | selectUserReturn purpose =>
      exact step_consistent_of_untouched observer left right _
        (by simp only [CompositeFootprint.Untouched, Operation.footprint]; decide) h.low
  | userReturn request =>
      exact step_consistent_of_untouched observer left right _
        (by simp only [CompositeFootprint.Untouched, Operation.footprint]; decide) h.low
  | restart =>
      exact step_consistent_of_untouched observer left right _
        (by simp only [CompositeFootprint.Untouched, Operation.footprint]; decide) h.low
  | ipc call => exact lowEquiv_gate_of_apply h.low h.mode (own_step_ipc h call)
  | map slot page permissions =>
      exact lowEquiv_gate_of_apply h.low h.mode (own_step_map h slot page permissions)
  | unmap page => exact lowEquiv_gate_of_apply h.low h.mode (own_step_unmap h page)
  | protect page permissions =>
      exact lowEquiv_gate_of_apply h.low h.mode (own_step_protect h page permissions)
  | syscall call => exact lowEquiv_gate_of_apply h.low h.mode (own_step_syscall h call)
  | capabilityRevoke authoritySlot victim victimSlot =>
      exact lowEquiv_gate_of_apply h.low h.mode
        (own_step_revoke h authoritySlot victim victimSlot)
  | capabilityCopy source destination destinationSlot rights =>
      simp only [ownStepConsistent, bne_iff_ne, ne_eq] at hfamily
      exact lowEquiv_gate_of_apply h.low h.mode (lowEquiv_of_unchanged h.low
        (observe_apply_copy_other observer left source destination destinationSlot rights
          hfamily)
        (observe_apply_copy_other observer right source destination destinationSlot rights
          hfamily))
  | createSubject subject =>
      simp only [ownStepConsistent, bne_iff_ne, ne_eq] at hfamily
      exact lowEquiv_gate_of_apply h.low h.mode (lowEquiv_of_unchanged h.low
        (observe_apply_create_other observer left subject hfamily h.leftWF.1)
        (observe_apply_create_other observer right subject hfamily h.rightWF.1))
  | _ => simp [ownStepConsistent] at hfamily

/-! ### Access checks -/

/-- In a runtime-well-formed state, any page of the observer's own space that
permits an access names an object the observer holds a capability for. -/
theorem names_of_mapping {state : CompositeState} {observer : SubjectId}
    (hstate : RuntimeWellFormed state) (space : VirtualMapping.AddressSpaceId)
    (page : Nat) (mapping : VirtualMapping.Mapping) (access : VirtualMapping.Access)
    (howner : state.virtualMemory.owner space = some observer)
    (hmapping : state.virtualMemory.mappings space page = some mapping)
    (hpermits : mapping.permissions.permits access = true) :
    Names state observer mapping.object = true := by
  rcases hstate with ⟨hcoherent, _, _, hcapabilities, hvirtual, _⟩
  obtain ⟨subject, _, hsubject, _, _, _, hread, hwrite⟩ :=
    hvirtual.1.2 space page mapping hmapping
  rw [howner] at hsubject
  cases hsubject
  have hauthority : Capability.HasAuthority state.capabilities observer mapping.object
      access.right := by
    rw [← memoryCapabilities_eq hcoherent]
    cases access with
    | read => exact hread hpermits
    | write => exact hwrite hpermits
  obtain ⟨slot, cap, hslot, hobject, _⟩ := hauthority
  have hin : slot < state.capabilities.slotCapacity observer := by
    apply Nat.lt_of_not_le
    intro hout
    have := hcapabilities.2.2.2 observer slot hout
    rw [hslot] at this
    contradiction
  have hrow : some cap ∈ row state observer := by
    rw [List.mem_iff_getElem?]
    exact ⟨slot, by rw [row_getElem? state observer slot hin, hslot]⟩
  simp only [Names, List.any_eq_true]
  exact ⟨some cap, hrow, by simp [hobject]⟩

/-- The error an access check reports, or `none` when it succeeds. -/
def translateError (virtualMemory : VirtualMapping.State) (actor : SubjectId)
    (space : VirtualMapping.AddressSpaceId) (page : Nat) (access : VirtualMapping.Access) :
    Option VirtualMapping.TranslationError :=
  match VirtualMapping.translate virtualMemory actor space page access with
  | .ok _ => none
  | .error reason => some reason

theorem translateError_congr (a b : VirtualMapping.State) (actor space page access)
    (howner : a.owner space = b.owner space)
    (hpage : a.mappings space page = b.mappings space page)
    (hobject : ∀ mapping, b.mappings space page = some mapping →
      mapping.permissions.permits access = true →
      a.memory.capabilities.kinds mapping.object = b.memory.capabilities.kinds mapping.object ∧
        vmBacking a mapping.object = vmBacking b mapping.object) :
    translateError a actor space page access = translateError b actor space page access := by
  simp only [translateError, VirtualMapping.translate, howner, hpage]
  cases hown : b.owner space with
  | none => rfl
  | some owner =>
      by_cases hactor : owner = actor
      · subst hactor
        simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        cases hmapping : b.mappings space page with
        | none => rfl
        | some mapping =>
            by_cases hpermits : mapping.permissions.permits access = true
            · obtain ⟨hkind, hback⟩ := hobject mapping hmapping hpermits
              simp only [vmBacking] at hback
              simp only [hpermits, hkind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              by_cases hk : b.memory.capabilities.kinds mapping.object = some .memory
              · simp only [hk, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
                cases ha : a.memory.binding mapping.object with
                | none =>
                    cases hb : b.memory.binding mapping.object with
                    | none => rfl
                    | some frameB => simp [ha, hb] at hback
                | some frameA =>
                    cases hb : b.memory.binding mapping.object with
                    | none => simp [ha, hb] at hback
                    | some frameB =>
                        simp only [ha, hb, Option.map_some, Option.some.injEq,
                          decide_eq_decide] at hback
                        by_cases hs : b.memory.allocator.status frameB = .owned mapping.object
                        · simp [hs, hback.2 hs]
                        · have hs' : ¬ a.memory.allocator.status frameA =
                              .owned mapping.object := fun h => hs (hback.1 h)
                          simp [hs, hs']
              · simp [hk]
            · simp [hpermits]
      · simp [hactor]

theorem own_output_syscall_access {observer : SubjectId} {left right : CompositeState}
    (h : OwnStep observer left right) (page : Nat) (access : VirtualMapping.Access) :
    translateError left.virtualMemory observer observer page access =
      translateError right.virtualMemory observer observer page access := by
  have hLown := owner_current h.leftWF h.current
  have hRown := owner_current h.rightWF h.rightCurrent
  have hpage : left.virtualMemory.mappings observer page =
      right.virtualMemory.mappings observer page := by
    rw [h.low.ownedMappings observer hLown]
  apply translateError_congr _ _ _ _ _ _ (by rw [hLown, hRown]) hpage
  intro mapping hmapping hpermits
  have hnames := names_of_mapping h.leftWF observer page mapping access hLown
    (hpage.trans hmapping) hpermits
  have hview := h.low.namedView mapping.object hnames
  have hkind := congrArg ObjectView.kind hview
  simp only [CompositeObservation.objectView] at hkind
  rw [memoryCapabilities_eq h.leftWF.1, memoryCapabilities_eq h.rightWF.1]
  exact ⟨hkind, congrArg ObjectView.backing hview⟩

/-! ## Output consistency for the observer's own operations -/

/-- With equal modes, equal operation replies give equal gate results. -/
theorem authoritativeGate_result_of_reply (left right : CompositeState) (operation : Operation)
    (hnmi : ∀ raw context, operation ≠ .nmi raw context)
    (hmode : left.execution.mode = right.execution.mode)
    (hreply : operationReply left operation = operationReply right operation) :
    (authoritativeGate left (.ordinary operation)).result =
      (authoritativeGate right (.ordinary operation)).result := by
  cases operation
  case nmi raw context => exact absurd rfl (hnmi raw context)
  all_goals
    cases hleft : left.execution.mode <;> cases hright : right.execution.mode <;>
      simp_all [authoritativeGate, authoritativeOperationReply]

theorem copy_self_congr (a b : Capability.State) (observer : SubjectId)
    (source destinationSlot : Nat) (rights : Capability.Rights)
    (hlookup : ∀ slot, Capability.lookup a observer slot = Capability.lookup b observer slot)
    (hlive : a.subjects observer = b.subjects observer)
    (hcapacity : a.slotCapacity observer = b.slotCapacity observer)
    (hslots : ∀ slot, slot < b.slotCapacity observer →
      a.slots observer slot = b.slots observer slot) :
    (Capability.copy a observer source observer destinationSlot rights).result =
      (Capability.copy b observer source observer destinationSlot rights).result := by
  simp only [Capability.copy, hlookup source, Capability.slotInRange, hlive, hcapacity]
  by_cases hin : destinationSlot < b.slotCapacity observer
  · rw [hslots destinationSlot hin]
    repeat' split
    all_goals simp_all [Capability.reject]
  · repeat' split
    all_goals simp_all [Capability.reject]

/-- The observer's own operations for which output consistency holds.  A
delegation to another subject is excluded: its reply reveals that subject's
liveness and slot occupancy (`copy_destination_output_inconsistent`). -/
def ownOutputConsistent (observer : SubjectId) : Operation → Bool
  | .ipc _ | .map _ _ _ | .unmap _ | .protect _ _ | .syscall _ | .restart => true
  | .capabilityCopy _ destination _ _ => destination == observer
  | .capabilityRevoke _ victim _ => victim == observer
  | _ => false

/-- **Output consistency for the observer's own operations.**  Under the
premises of `own_step_consistent`, each operation in `ownOutputConsistent`
returns the same gate result in both states. -/
theorem own_output_consistent {observer : SubjectId} {left right : CompositeState}
    (h : OwnStep observer left right) (operation : Operation)
    (hfamily : ownOutputConsistent observer operation = true) :
    (authoritativeGate left (.ordinary operation)).result =
      (authoritativeGate right (.ordinary operation)).result := by
  obtain ⟨hLs, hLa⟩ := h.leftActor
  obtain ⟨hRs, hRa⟩ := h.rightActor
  have hLown := owner_current h.leftWF h.current
  have hRown := owner_current h.rightWF h.rightCurrent
  apply authoritativeGate_result_of_reply left right operation _ h.mode
  · cases operation with
    | ipc call =>
        exact ipc_output_consistent observer left right call h.low hLs hRs
          (ipcCapabilitiesPublished_of_coherent h.leftWF.1)
          (ipcCapabilitiesPublished_of_coherent h.rightWF.1)
    | map slot page permissions =>
        simp only [operationReply, hLs, hLa, hRs, hRa]
        rw [(map_congr left.virtualMemory right.virtualMemory observer slot observer page
          permissions (by rw [hLown, hRown])
          (by rw [memoryCapabilities_eq h.leftWF.1, memoryCapabilities_eq h.rightWF.1]
              exact h.lookup slot)
          (by rw [h.low.ownedMappings observer hLown])
          (fun cap hfound => by
            rw [memoryCapabilities_eq h.rightWF.1] at hfound
            exact congrArg ObjectView.backing (h.lookupView slot cap hfound))).1]
    | unmap page =>
        simp only [operationReply, hLs, hLa, hRs, hRa]
        rw [(unmap_congr left.virtualMemory right.virtualMemory observer observer page
          (by rw [hLown, hRown]) (by rw [h.low.ownedMappings observer hLown])).1]
    | protect page permissions =>
        have hLtr := translations_eq h.leftWF.1
        have hRtr := translations_eq h.rightWF.1
        simp only [operationReply, hLs, hLa, hRs, hRa]
        rw [(protect_congr left.resumable.translations right.resumable.translations observer
          observer page permissions (by rw [hLtr, hRtr, hLown, hRown])
          (by rw [hLtr, hRtr, h.low.ownedMappings observer hLown])).1]
    | restart => rfl
    | syscall call =>
        simp only [operationReply, Syscall.dispatch, CompositeState.syscallContext,
          hLs, hLa, hRs, hRa]
        cases hdecode : Syscall.decode call with
        | error reason => rfl
        | ok decoded =>
            cases decoded with
            | access page access =>
                have haccess := own_output_syscall_access h page access
                simp only [translateError] at haccess
                simp only [Syscall.dispatchDecoded]
                cases hleft : VirtualMapping.translate left.virtualMemory observer observer page
                    access <;>
                  cases hright : VirtualMapping.translate right.virtualMemory observer observer
                    page access <;>
                  simp_all
            | unmap page =>
                simp only [Syscall.dispatchDecoded]
                rw [(unmap_congr left.virtualMemory right.virtualMemory observer observer page
                  (by rw [hLown, hRown]) (by rw [h.low.ownedMappings observer hLown])).1]
            | map handleWord page permissions =>
                have hresolve : CapabilityHandle.resolveCurrent
                      left.virtualMemory.memory.capabilities { caller := observer } handleWord
                      .memory =
                    CapabilityHandle.resolveCurrent right.virtualMemory.memory.capabilities
                      { caller := observer } handleWord .memory := by
                  rw [memoryCapabilities_eq h.leftWF.1, memoryCapabilities_eq h.rightWF.1]
                  exact h.low.resolveCurrent handleWord .memory
                simp only [Syscall.dispatchDecoded, hresolve]
                split
                · rfl
                · rename_i resolution _
                  rw [(map_congr left.virtualMemory right.virtualMemory observer
                    resolution.handle.slot observer page permissions (by rw [hLown, hRown])
                    (by rw [memoryCapabilities_eq h.leftWF.1,
                          memoryCapabilities_eq h.rightWF.1]
                        exact h.lookup _)
                    (by rw [h.low.ownedMappings observer hLown])
                    (fun cap hfound => by
                      rw [memoryCapabilities_eq h.rightWF.1] at hfound
                      exact congrArg ObjectView.backing (h.lookupView _ cap hfound))).1]
    | capabilityCopy source destination destinationSlot rights =>
        simp only [ownOutputConsistent, beq_iff_eq] at hfamily
        subst hfamily
        simp only [operationReply, hLs, hRs]
        rw [copy_self_congr left.capabilities right.capabilities destination source
          destinationSlot rights h.lookup h.low.live h.low.capacity
          (fun slot hslot => (h.low.slot slot (h.low.capacity ▸ hslot)).1)]
    | capabilityRevoke authoritySlot victim victimSlot =>
        simp only [ownOutputConsistent, beq_iff_eq] at hfamily
        subst hfamily
        simp only [operationReply, hLs, hRs]
        rw [revokeRuntimeSafe_self_congr left.capabilities right.capabilities victim
          authoritySlot victimSlot h.lookup]
    | _ => simp [ownOutputConsistent] at hfamily
  · intro raw context hnmi
    subst hnmi
    simp [ownOutputConsistent] at hfamily

/-! ## Channels that break the unwinding conditions

The excluded families are not gaps hidden by the theorem: the model has real
channels there, proved below on the canonical, runtime-well-formed dispatcher
seed `FailStop.compositeDispatcherInitial`.  Subject 2 is scheduled and
observes; its slot 0 holds a grantable endpoint capability, subject 1's slot 2
and subject 2's slot 3 are empty, and the global identity counter is 6.

`shifted` is the seed after subject 2 delegates its endpoint into subject 1's
slot 2.  That delegation leaves subject 2's view unchanged, so `seed` and
`shifted` satisfy every premise of `own_step_consistent` and
`own_output_consistent`; it only advances the counter and fills a slot that
subject 2 cannot see. -/
namespace Channels

def seed (plan : BootPageTablePlan.Plan) : CompositeState :=
  compositeDispatcherInitial plan

/-- Subject 2 delegates a send-only endpoint capability into subject 1's
empty slot 2. -/
def delegateToOther : Operation := .capabilityCopy 0 1 2 { send := true }

/-- Subject 2 delegates a send-only endpoint capability into its own empty
slot 3. -/
def delegateToSelf : Operation := .capabilityCopy 0 2 3 { send := true }

def shifted (plan : BootPageTablePlan.Plan) : CompositeState :=
  (authoritativeGate (seed plan) (.ordinary delegateToOther)).state

theorem seed_wellFormed (plan : BootPageTablePlan.Plan) :
    AuthoritativeRuntimeWellFormed (seed plan) :=
  compositeDispatcherInitial_authoritativeRuntimeWellFormed plan

theorem seed_ownStep_shifted (plan : BootPageTablePlan.Plan) :
    OwnStep 2 (seed plan) (shifted plan) where
  low := by
    unfold LowEquiv shifted
    rw [authoritativeGate_ordinary_state]
    rcases gate_state_cases (seed plan) delegateToOther with hsame | happly
    · rw [hsame]
    · rw [happly]
      exact (observe_apply_copy_other 2 (seed plan) 0 1 2 { send := true } (by decide)).symm
  leftWF := (seed_wellFormed plan).left
  rightWF := (authoritativeGate_preserves_authoritativeRuntimeWellFormed _ _
    (seed_wellFormed plan)).left
  current := rfl
  mode := rfl

/-- Identities of the capabilities in subject 2's row, slot by slot. -/
def rowIdentities (state : CompositeState) : List (Option Nat) :=
  (row state 2).map (Option.map (·.identity))

theorem seed_delegateToSelf_identities (plan : BootPageTablePlan.Plan) :
    rowIdentities (authoritativeGate (seed plan) (.ordinary delegateToSelf)).state =
      [some 3, some 4, some 5, some 6] := rfl

theorem shifted_delegateToSelf_identities (plan : BootPageTablePlan.Plan) :
    rowIdentities (authoritativeGate (shifted plan) (.ordinary delegateToSelf)).state =
      [some 3, some 4, some 5, some 7] := rfl

/-- **The capability-identity counter breaks step consistency.**  Two
runtime-well-formed states that are low-equivalent for the scheduled
observer, in the same mode, end distinguishable after the observer's own
delegation into its own row: the new capability's identity (the generation of
its handle) is drawn from the global `nextIdentity`, which the observer's
earlier, view-invisible delegation to another subject advanced.  No view
abstraction can hide it, because the observer must present that generation in
every later handle word. -/
theorem identity_counter_step_inconsistent (plan : BootPageTablePlan.Plan) :
    OwnStep 2 (seed plan) (shifted plan) ∧
      ¬ LowEquiv 2 (authoritativeGate (seed plan) (.ordinary delegateToSelf)).state
        (authoritativeGate (shifted plan) (.ordinary delegateToSelf)).state := by
  refine ⟨seed_ownStep_shifted plan, fun hlow => ?_⟩
  have hrow := congrArg (fun view : View => view.row.map (Option.map (·.identity))) hlow
  change rowIdentities _ = rowIdentities _ at hrow
  rw [seed_delegateToSelf_identities, shifted_delegateToSelf_identities] at hrow
  simp at hrow

theorem seed_delegateToOther_result (plan : BootPageTablePlan.Plan) :
    (authoritativeGate (seed plan) (.ordinary delegateToOther)).result =
      .completed (.ordinary (.capability .accepted)) := rfl

theorem shifted_delegateToOther_result (plan : BootPageTablePlan.Plan) :
    (authoritativeGate (shifted plan) (.ordinary delegateToOther)).result =
      .completed (.ordinary (.capability (.rejected .occupiedSlot))) := rfl

/-- **Delegation to another subject breaks output consistency.**  The reply
to the observer's delegation reveals whether the destination slot is occupied
(and, by the same check, whether the destination subject is live), which the
observer's view does not contain. -/
theorem copy_destination_output_inconsistent (plan : BootPageTablePlan.Plan) :
    OwnStep 2 (seed plan) (shifted plan) ∧
      (authoritativeGate (seed plan) (.ordinary delegateToOther)).result ≠
        (authoritativeGate (shifted plan) (.ordinary delegateToOther)).result := by
  refine ⟨seed_ownStep_shifted plan, ?_⟩
  rw [seed_delegateToOther_result, shifted_delegateToOther_result]
  simp

end Channels

/-! ## Classical noninterference for the observer's own runs

While the observer stays scheduled, only it acts.  Its operations that are
both step and output consistent keep the `OwnStep` premises, so step and
output consistency compose: from two `OwnStep` states, the same run of such
operations returns the same gate results at every step and ends
low-equivalent.  Unlike the replay theorem, equal observations are concluded
here, not assumed. -/

/-- Operations that are both step and output consistent for the observer. -/
def ownTraceFamily (observer : SubjectId) (operation : Operation) : Bool :=
  ownStepConsistent observer operation && ownOutputConsistent observer operation

theorem dispatchIPC_lifecycle_execution (state : CompositeState) (call : IPCSyscall.Call) :
    (dispatchIPC state call).state.lifecycle = state.lifecycle ∧
      (dispatchIPC state call).state.execution = state.execution := by
  cases call with
  | send handleWord word0 word1 => exact ⟨rfl, rfl⟩
  | receive handleWord =>
      simp only [dispatchIPC]
      repeat' split
      all_goals exact ⟨rfl, rfl⟩

theorem selectLiveReturnAuthority_lifecycle (state : CompositeState)
    (purpose : Interrupt.ReturnPurpose) :
    (selectLiveReturnAuthority state purpose).lifecycle = state.lifecycle := by
  unfold selectLiveReturnAuthority
  split <;> rfl

/-- The operations of `ownTraceFamily` keep the scheduled subject and the
fail-stop mode. -/
theorem ownTraceFamily_preserves (observer : SubjectId) (state : CompositeState)
    (operation : Operation) (hfamily : ownTraceFamily observer operation = true) :
    (authoritativeGate state (.ordinary operation)).state.lifecycle.current =
        state.lifecycle.current ∧
      (authoritativeGate state (.ordinary operation)).state.execution.mode =
        state.execution.mode := by
  rw [authoritativeGate_ordinary_state]
  rcases gate_state_cases state operation with hsame | happly
  · rw [hsame]
    exact ⟨rfl, rfl⟩
  · rw [happly]
    cases operation with
    | ipc call =>
        have h := dispatchIPC_lifecycle_execution state call
        simp only [applyOperation]
        split <;> first | exact ⟨rfl, rfl⟩ | exact ⟨by rw [h.1], by rw [h.2]⟩
    | map slot page permissions =>
        simp only [applyOperation]
        split <;> simp [installVirtualMemory]
    | unmap page =>
        simp only [applyOperation]
        split <;> simp [installVirtualMemory]
    | protect page permissions =>
        simp only [applyOperation]
        split <;> simp [installVirtualMemory]
    | syscall call =>
        simp only [applyOperation]
        split
        · exact ⟨rfl, rfl⟩
        · split <;> simp [installVirtualMemory, selectLiveReturnAuthority_mode,
            selectLiveReturnAuthority_lifecycle]
    | capabilityRevoke authoritySlot victim victimSlot =>
        simp only [applyOperation]
        split <;> simp [installCopiedCapabilities]
    | restart => exact ⟨rfl, rfl⟩
    | _ => simp [ownTraceFamily, ownStepConsistent, ownOutputConsistent] at hfamily

/-- One gate step of `ownTraceFamily` keeps the `OwnStep` premises. -/
theorem OwnStep.next {observer : SubjectId} {left right : CompositeState}
    (h : OwnStep observer left right) (operation : Operation)
    (hfamily : ownTraceFamily observer operation = true) :
    OwnStep observer (authoritativeGate left (.ordinary operation)).state
      (authoritativeGate right (.ordinary operation)).state := by
  simp only [ownTraceFamily, Bool.and_eq_true] at hfamily
  have hleft := ownTraceFamily_preserves observer left operation
    (by simp [ownTraceFamily, hfamily.1, hfamily.2])
  have hright := ownTraceFamily_preserves observer right operation
    (by simp [ownTraceFamily, hfamily.1, hfamily.2])
  exact
    { low := own_step_consistent h operation hfamily.1
      leftWF := authoritativeGate_preserves_runtimeWellFormed left _ h.leftWF trivial
      rightWF := authoritativeGate_preserves_runtimeWellFormed right _ h.rightWF trivial
      current := hleft.1.trans h.current
      mode := hleft.2.trans (h.mode.trans hright.2.symm) }

/-- Run ordinary operations through `authoritativeGate`, collecting every gate
result. -/
def ownRun : CompositeState → List Operation → CompositeState × List AuthoritativeGateResult
  | state, [] => (state, [])
  | state, operation :: rest =>
      let outcome := authoritativeGate state (.ordinary operation)
      let tail := ownRun outcome.state rest
      (tail.1, outcome.result :: tail.2)

/-- **Noninterference for the observer's own runs, from the unwinding
conditions.**  From two runtime-well-formed states that are low-equivalent for
the scheduled observer and share the fail-stop mode, the same finite run of
the observer's step- and output-consistent operations returns the same gate
result at every step and ends in low-equivalent states. -/
theorem own_run_noninterference {observer : SubjectId} {left right : CompositeState}
    (h : OwnStep observer left right) (operations : List Operation)
    (hfamily : ∀ operation, operation ∈ operations → ownTraceFamily observer operation = true) :
    (ownRun left operations).2 = (ownRun right operations).2 ∧
      LowEquiv observer (ownRun left operations).1 (ownRun right operations).1 := by
  induction operations generalizing left right with
  | nil => exact ⟨rfl, h.low⟩
  | cons operation rest ih =>
      have hhead := hfamily operation (by simp)
      have htail := ih (h.next operation hhead) fun candidate hmem =>
        hfamily candidate (by simp [hmem])
      simp only [ownTraceFamily, Bool.and_eq_true] at hhead
      refine ⟨?_, htail.2⟩
      simp only [ownRun, List.cons.injEq]
      exact ⟨own_output_consistent h operation hhead.2, htail.1⟩

end LeanOS.CompositeUnwinding
