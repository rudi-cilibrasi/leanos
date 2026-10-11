import LeanOS.CompositeOwnSwitch

/-!
# Composite unwinding: the observer's blocking operations

With the scheduler's bookkeeping public (`CompositeOwnSwitch.KernelPublic`),
the observer's blocking send, its blocking receive, and its cancellation of
itself are step and output consistent.

* **Send** (`own_blockingSend`).  The decision reads the observer's handle,
  the endpoint's liveness, mailbox and waiter queue (all in the view), the
  ready queue and its capacity, and, when a waiter is woken, the resumable
  bank's length and capacity (`dispatchBlockingSend_shape`).  The woken
  receiver's saved context moves to the bank; it is never in the reply, which
  names the receiver only, the head of a queue the observer sees.
* **Receive** (`own_blockingReceive`).  The decision reads the frame's
  validity, the observer's completion, the endpoint's mailbox and queue, the
  waiter-queue capacity, and, when the observer blocks, the head of the ready
  queue and whether the bank holds its context (`dispatchBlockingReceive_shape`).
* **Cancellation of itself** (`own_blockingCancel_self`): the scheduled
  observer waits on nothing, so the reply is `notWaiting` and nothing changes.
  Its cancellation of another subject's wait is refused by the subject gate
  (ADR 0025).

The reply of the observer's admission of itself to the ready queue is a
duplicate (`reply_scheduleAdd_self`).
-/
namespace LeanOS.CompositeOwnBlocking

open LeanOS
open LeanOS.FailStop
open LeanOS.CompositeObservation
open LeanOS.CompositeUnwinding
open LeanOS.CompositeOwnSteps
open LeanOS.CompositeOwnSwitch
set_option linter.unusedSimpArgs false


theorem observe_publishBlocking_eq (observer : Nat) (state : CompositeState)
    (blocking : BlockingIPCContext.State) :
    observe observer (publishBlockingIPCContext state blocking) =
      { observe observer state with
        scheduled := blocking.ipc.scheduler.lifecycle.current
        named := (row state observer).map (Option.map fun cap =>
          { objectView state cap.object with
            blockingMailbox := blocking.ipc.mailbox cap.object
            waiters := blocking.ipc.waiters cap.object })
        waitingOn := blocking.ipc.waiterEndpoint observer
        completion := blocking.ipc.completion observer } := rfl

/-- Two-state publication of blocking stores. -/
theorem lowEquiv_publishBlocking {observer : Nat} {left right : CompositeState}
    (hlow : LowEquiv observer left right) (bl br : BlockingIPCContext.State)
    (hcurrent : bl.ipc.scheduler.lifecycle.current = br.ipc.scheduler.lifecycle.current)
    (hnamed : ∀ object, Names left observer object = true →
      bl.ipc.mailbox object = br.ipc.mailbox object ∧ bl.ipc.waiters object = br.ipc.waiters object)
    (hwaiting : bl.ipc.waiterEndpoint observer = br.ipc.waiterEndpoint observer)
    (hcompletion : bl.ipc.completion observer = br.ipc.completion observer) :
    LowEquiv observer (publishBlockingIPCContext left bl) (publishBlockingIPCContext right br) := by
  unfold LowEquiv
  rw [observe_publishBlocking_eq, observe_publishBlocking_eq]
  have hlist :
      (row left observer).map (Option.map fun cap =>
          { objectView left cap.object with
            blockingMailbox := bl.ipc.mailbox cap.object
            waiters := bl.ipc.waiters cap.object }) =
        (row right observer).map (Option.map fun cap =>
          { objectView right cap.object with
            blockingMailbox := br.ipc.mailbox cap.object
            waiters := br.ipc.waiters cap.object }) := by
    rw [← hlow.rowEq]
    apply List.map_congr_left
    intro slot hmem
    cases slot with
    | none => rfl
    | some cap =>
        have hnames : Names left observer cap.object = true := by
          simp only [Names, List.any_eq_true]
          exact ⟨some cap, hmem, by simp⟩
        obtain ⟨hmailbox, hwaiters⟩ := hnamed cap.object hnames
        simp only [Option.map_some, hlow.namedView cap.object hnames, hmailbox, hwaiters]
  rw [hlist, hcurrent, hwaiting, hcompletion, hlow]


/-- Two-state congruence of a raw blocking send. -/
theorem send_congr (a b : BlockingIPC.State) (caller slot : Nat) (payload : BlockingIPC.Payload)
    (hcurrent : a.scheduler.lifecycle.current = b.scheduler.lifecycle.current)
    (hlookup : Capability.lookup a.scheduler.lifecycle.capabilities caller slot =
      Capability.lookup b.scheduler.lifecycle.capabilities caller slot)
    (hfields : ∀ cap, Capability.lookup b.scheduler.lifecycle.capabilities caller slot =
        .found cap →
      a.scheduler.lifecycle.capabilities.objects cap.object =
          b.scheduler.lifecycle.capabilities.objects cap.object ∧
        a.waiters cap.object = b.waiters cap.object ∧ a.mailbox cap.object = b.mailbox cap.object)
    (hready : a.scheduler.ready.length = b.scheduler.ready.length)
    (hcapacity : a.scheduler.capacity = b.scheduler.capacity) :
    (BlockingIPC.send a caller slot payload).result =
        (BlockingIPC.send b caller slot payload).result ∧
      (∀ object, a.mailbox object = b.mailbox object → a.waiters object = b.waiters object →
        (BlockingIPC.send a caller slot payload).state.mailbox object =
            (BlockingIPC.send b caller slot payload).state.mailbox object ∧
          (BlockingIPC.send a caller slot payload).state.waiters object =
            (BlockingIPC.send b caller slot payload).state.waiters object) := by
  simp only [BlockingIPC.send, hcurrent, hlookup]
  cases hfound : Capability.lookup b.scheduler.lifecycle.capabilities caller slot with
  | invalidSubject =>
      simp only [BlockingIPC.reject]
      split <;> exact ⟨rfl, fun _ h1 h2 => ⟨h1, h2⟩⟩
  | staleSlot =>
      simp only [BlockingIPC.reject]
      split <;> exact ⟨rfl, fun _ h1 h2 => ⟨h1, h2⟩⟩
  | found cap =>
      obtain ⟨hobj, hwait, hmail⟩ := hfields cap hfound
      simp only [hobj, hwait, hmail, hready, hcapacity]
      repeat' split
      all_goals first
        | exact ⟨rfl, fun _ h1 h2 => ⟨h1, h2⟩⟩
        | (refine ⟨rfl, fun object h1 h2 => ?_⟩
           simp only [BlockingIPC.setMailbox, BlockingIPC.wakeState, BlockingIPC.setWaiters]
           split
           · subst object
             simp_all
           · exact ⟨h1, h2⟩)


/-- An accepted raw send names an endpoint capability. -/
theorem send_accepted_kind (blocking : BlockingIPC.State) (caller slot : Nat)
    (payload : BlockingIPC.Payload) (cap : Capability.Capability)
    (hlookup : Capability.lookup blocking.scheduler.lifecycle.capabilities caller slot =
      .found cap)
    (haccepted : (BlockingIPC.send blocking caller slot payload).result = .accepted) :
    cap.kind = .endpoint := by
  revert haccepted
  simp only [BlockingIPC.send, hlookup]
  repeat' split
  all_goals simp_all [BlockingIPC.reject]

/-- An accepted raw send to an endpoint with a waiter wakes that waiter. -/
theorem send_accepted_wake (blocking : BlockingIPC.State) (caller slot : Nat)
    (payload : BlockingIPC.Payload) (cap : Capability.Capability)
    (hlookup : Capability.lookup blocking.scheduler.lifecycle.capabilities caller slot =
      .found cap)
    (haccepted : (BlockingIPC.send blocking caller slot payload).result = .accepted)
    (receiver : Nat) (rest : List Nat) (hwaiters : blocking.waiters cap.object = receiver :: rest) :
    (BlockingIPC.send blocking caller slot payload).state =
      BlockingIPC.wakeState blocking cap.object receiver
        { endpoint := cap.object, sender := caller, payload := payload } := by
  revert haccepted
  simp only [BlockingIPC.send, hlookup, hwaiters]
  repeat' split
  all_goals simp_all [BlockingIPC.reject]

theorem endpointOf_of_lookup (blocking : BlockingIPC.State) (caller slot : Nat)
    (cap : Capability.Capability)
    (hlookup : Capability.lookup blocking.scheduler.lifecycle.capabilities caller slot =
      .found cap)
    (hkind : cap.kind = .endpoint) :
    BlockingIPC.endpointOf blocking caller slot = some cap.object := by
  simp [BlockingIPC.endpointOf, hlookup, hkind]

/-- Publication of a woken receiver's context succeeds unless the resumable
bank is full, given the facts the blocking invariant supplies. -/
theorem publishReleased_eq (state : CompositeState) (next : BlockingIPCContext.State)
    (saved : ResumableContext.Context) (receiver : Nat)
    (hvalid : BlockingIPCContext.validSaved receiver saved = true)
    (hlive : next.ipc.scheduler.lifecycle.capabilities.subjects receiver = true)
    (hrunnable : next.ipc.scheduler.lifecycle.runnable receiver = true)
    (hown : next.ipc.scheduler.lifecycle.addressOwner receiver = some receiver)
    (hready : receiver ∈ next.ipc.scheduler.ready)
    (hbank : ResumablePreemption.contextFor state.resumable.contexts receiver = none) :
    publishReleasedBlockingContext state next saved =
      if state.resumable.capacity ≤ state.resumable.contexts.length then .error .bankFull
      else .ok { publishBlockingIPCContext state next with
        resumable := { (publishBlockingIPCContext state next).resumable with
          contexts := saved :: state.resumable.contexts } } := by
  have howner := BlockingIPCContext.validSaved_owner receiver saved hvalid
  have hkind := BlockingIPCContext.validSaved_kind receiver saved hvalid
  simp only [BlockingIPCContext.validSaved, Bool.and_eq_true, beq_iff_eq] at hvalid
  obtain ⟨⟨⟨_, hspace⟩, _⟩, hframe⟩ := hvalid
  subst howner
  unfold publishReleasedBlockingContext
  have hne : (ResumableContext.ContextKind.suspended != ResumableContext.ContextKind.suspended) =
      false := by decide
  simp [hframe, hspace, hkind, hlive, hrunnable, hown, hready, hbank, hne]


def sendShape (observer : Nat) (state : CompositeState) (slot endpoint : Nat)
    (payload : BlockingIPC.Payload) : CompositeBlockingSendReply × View :=
  match (BlockingIPC.send state.blockingIPC observer slot payload).result with
  | .rejected reason => (.rejected reason, observe observer state)
  | .accepted =>
      match state.blockingIPC.waiters endpoint with
      | [] => (.sent, observe observer (publishBlockingIPCContext state
          ⟨(BlockingIPC.send state.blockingIPC observer slot payload).state,
            state.blockingContexts⟩))
      | receiver :: _ =>
          if state.resumable.capacity ≤ state.resumable.contexts.length then
            (.restoreRejected .bankFull, observe observer state)
          else (.woke receiver, observe observer (publishBlockingIPCContext state
            ⟨(BlockingIPC.send state.blockingIPC observer slot payload).state,
              state.blockingContexts⟩))

theorem dispatchBlockingSend_shape {observer : Nat} {state : CompositeState}
    (hstate : AuthoritativeRuntimeWellFormed state)
    (hcurrent : state.lifecycle.current = some observer)
    (handleWord word0 word1 : UInt64) (resolution : CapabilityHandle.Resolution)
    (hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities { caller := observer } handleWord
      .endpoint = .ok resolution) :
    ((dispatchBlockingSend state handleWord word0 word1).reply,
        observe observer (dispatchBlockingSend state handleWord word0 word1).state) =
      sendShape observer state resolution.handle.slot resolution.capability.object
        { word0, word1 } := by
  have hcoherent := coherent_of hstate
  have hS : state.execution.core.context.currentSubject = observer :=
    (actor_of_current hcoherent hcurrent).1
  have hlookup := resolveCurrent_ok_lookup _ _ _ _ _ hresolve
  have hcontext : BlockingIPCContext.WellFormed state.blockingIPCContext := hstate.blocking.2
  simp only [dispatchBlockingSend, hS, hresolve]
  unfold BlockingIPCContext.send sendShape
  simp only [CompositeState.blockingIPCContext]
  generalize hraw : BlockingIPC.send state.blockingIPC observer resolution.handle.slot
    { word0, word1 } = raw
  rcases raw with ⟨next, result⟩
  cases result with
  | rejected reason => rfl
  | accepted =>
      have hkind := send_accepted_kind state.blockingIPC observer resolution.handle.slot
        { word0, word1 } resolution.capability hlookup (by rw [hraw])
      simp only [endpointOf_of_lookup state.blockingIPC observer resolution.handle.slot
        resolution.capability hlookup hkind]
      cases hwaiters : state.blockingIPC.waiters resolution.capability.object with
      | nil => rfl
      | cons receiver rest =>
          have hmember : receiver ∈ state.blockingIPC.waiters resolution.capability.object := by
            rw [hwaiters]; exact List.mem_cons_self
          obtain ⟨hipcWF, hagreement⟩ := hcontext
          have hindex := (hipcWF.2.2.2.2.1 resolution.capability.object receiver).1 hmember
          have hwaiterFacts := hipcWF.2.2.1 resolution.capability.object receiver hmember
          obtain ⟨saved, hsaved⟩ : ∃ saved, state.blockingContexts receiver = some saved := by
            have := hagreement.1 receiver
            have hindex' : state.blockingIPC.waiterEndpoint receiver =
                some resolution.capability.object := hindex
            simp only [CompositeState.blockingIPCContext, hindex', Option.isSome_some] at this
            exact Option.isSome_iff_exists.1 this
          simp only [hsaved]
          have hvalid := hagreement.2 receiver saved hsaved
          have hbank := hstate.2.2.1 receiver saved hsaved
          have hwake := send_accepted_wake state.blockingIPC observer resolution.handle.slot
            { word0, word1 } resolution.capability hlookup (by rw [hraw]) receiver rest hwaiters
          rw [hraw] at hwake
          simp only at hwake
          subst hwake
          have hown : state.blockingIPC.scheduler.lifecycle.addressOwner receiver =
              some receiver := by
            have hsome := hwaiterFacts.2.2.2.2.1
            unfold Scheduler.ownsAddressSpace at hsome
            split at hsome
            · assumption
            · contradiction
          rw [publishReleased_eq state _ saved receiver hvalid
            (by simpa [BlockingIPC.wakeState, CompositeState.blockingIPCContext] using
              hwaiterFacts.2.2.1)
            (by simp [BlockingIPC.wakeState, SubjectLifecycle.setBool])
            (by simpa [BlockingIPC.wakeState, CompositeState.blockingIPCContext] using hown)
            (by simp [BlockingIPC.wakeState]) hbank]
          by_cases hfull : state.resumable.capacity ≤ state.resumable.contexts.length
          · simp [hfull]
          · simp only [hfull, ↓reduceIte, CompositeBlockingSendReply.woke.injEq, Prod.mk.injEq]
            exact ⟨BlockingIPCContext.validSaved_owner receiver saved hvalid, rfl⟩


theorem current_not_waiter {state : CompositeState} {observer : Nat}
    (hstate : AuthoritativeRuntimeWellFormed state)
    (hcurrent : state.lifecycle.current = some observer) (endpoint : Nat) :
    observer ∉ state.blockingIPC.waiters endpoint := by
  intro hmem
  have hfacts := hstate.blocking.2.1.2.2.1 endpoint observer hmem
  apply hfacts.2.2.2.2.2.1
  change state.blockingIPC.scheduler.lifecycle.current = some observer
  rw [blockingCurrent_eq (blockingCoherent_of hstate)]
  exact hcurrent

/-- **The observer's blocking send gives equal replies and low-equivalent
states.** -/
theorem sendShape_eq {observer : Nat} {left right : CompositeState}
    (h : OwnStep observer left right) (hleft : AuthoritativeRuntimeWellFormed left)
    (hright : AuthoritativeRuntimeWellFormed right) (hpublic : KernelPublic left right)
    (resolution : CapabilityHandle.Resolution)
    (hlookupL : Capability.lookup left.blockingIPC.scheduler.lifecycle.capabilities observer
      resolution.handle.slot = .found resolution.capability)
    (payload : BlockingIPC.Payload) :
    sendShape observer left resolution.handle.slot resolution.capability.object payload =
      sendShape observer right resolution.handle.slot resolution.capability.object payload := by
  have hcohL := coherent_of hleft
  have hcohR := coherent_of hright
  have hcapsL : left.blockingIPC.scheduler.lifecycle.capabilities = left.capabilities := by
    rw [hleft.1.blockingLifecycle, ← capabilities_eq_lifecycle hcohL]
  have hcapsR : right.blockingIPC.scheduler.lifecycle.capabilities = right.capabilities := by
    rw [hright.1.blockingLifecycle, ← capabilities_eq_lifecycle hcohR]
  have hlookup : Capability.lookup left.blockingIPC.scheduler.lifecycle.capabilities observer
      resolution.handle.slot = Capability.lookup right.blockingIPC.scheduler.lifecycle.capabilities
        observer resolution.handle.slot := by
    rw [hcapsL, hcapsR]; exact h.lookup _
  have hnamed : Names left observer resolution.capability.object = true := by
    rw [hcapsL] at hlookupL
    exact names_of_lookup left observer _ _ hlookupL
  have hview := h.low.namedView resolution.capability.object hnamed
  have hlive := congrArg ObjectView.live hview
  have hmailbox := congrArg ObjectView.blockingMailbox hview
  have hwaiters := congrArg ObjectView.waiters hview
  simp only [objectView] at hlive hmailbox hwaiters
  have hcurL : left.blockingIPC.scheduler.lifecycle.current = some observer := by
    rw [blockingCurrent_eq (blockingCoherent_of hleft)]; exact h.current
  have hcurR : right.blockingIPC.scheduler.lifecycle.current = some observer := by
    rw [blockingCurrent_eq (blockingCoherent_of hright)]; exact h.rightCurrent
  have hschedL : left.blockingIPC.scheduler = left.scheduler := hleft.1.blockingScheduler
  have hschedR : right.blockingIPC.scheduler = right.scheduler := hright.1.blockingScheduler
  obtain ⟨hresult, hstates⟩ := send_congr left.blockingIPC right.blockingIPC observer
    resolution.handle.slot payload (hcurL.trans hcurR.symm) hlookup
    (by
      intro cap hcap
      rw [← hlookup, hlookupL] at hcap
      cases hcap
      refine ⟨?_, hwaiters, hmailbox⟩
      rw [hcapsL, hcapsR]; exact hlive)
    (by rw [hschedL, hschedR, hpublic.ready])
    (by rw [hschedL, hschedR, hpublic.capacity])
  have hbankLength : left.resumable.contexts.length = right.resumable.contexts.length := by
    have := congrArg List.length hpublic.bank
    simpa using this
  have hlookupR : Capability.lookup right.blockingIPC.scheduler.lifecycle.capabilities observer
      resolution.handle.slot = .found resolution.capability := by rw [← hlookup]; exact hlookupL
  obtain ⟨hcurNextL, _, hwaitL, hcompL⟩ := CompositeUnwinding.blockingSend_frame
    left.blockingIPC observer resolution.handle.slot payload resolution.capability hlookupL observer
    (Bool.eq_false_iff.2 fun hc =>
      current_not_waiter hleft h.current resolution.capability.object (by simpa using hc))
  obtain ⟨hcurNextR, _, hwaitR, hcompR⟩ := CompositeUnwinding.blockingSend_frame
    right.blockingIPC observer resolution.handle.slot payload resolution.capability hlookupR
    observer
    (Bool.eq_false_iff.2 fun hc =>
      current_not_waiter hright h.rightCurrent resolution.capability.object (by simpa using hc))
  have hpublish : observe observer (publishBlockingIPCContext left
        ⟨(BlockingIPC.send left.blockingIPC observer resolution.handle.slot payload).state,
          left.blockingContexts⟩) =
      observe observer (publishBlockingIPCContext right
        ⟨(BlockingIPC.send right.blockingIPC observer resolution.handle.slot payload).state,
          right.blockingContexts⟩) := by
    apply lowEquiv_publishBlocking h.low
    · simp only
      rw [hcurNextL, hcurNextR, hcurL, hcurR]
    · intro object hnames
      have hv := h.low.namedView object hnames
      exact hstates object (congrArg ObjectView.blockingMailbox hv)
        (congrArg ObjectView.waiters hv)
    · simp only
      rw [hwaitL, hwaitR]
      exact congrArg View.waitingOn h.low
    · simp only
      rw [hcompL, hcompR]
      exact congrArg View.completion h.low
  unfold sendShape
  rw [hresult, hwaiters, hbankLength, hpublic.bankCapacity, hpublish, h.low]


theorem blockingCaps_eq {state : CompositeState} (hstate : AuthoritativeRuntimeWellFormed state) :
    state.blockingIPC.scheduler.lifecycle.capabilities = state.capabilities := by
  rw [hstate.1.blockingLifecycle, ← capabilities_eq_lifecycle (coherent_of hstate)]

/-- The observer's blocking send: equal replies and views. -/
theorem dispatchBlockingSend_pair_eq {observer : Nat} {left right : CompositeState}
    (h : OwnStep observer left right) (hleft : AuthoritativeRuntimeWellFormed left)
    (hright : AuthoritativeRuntimeWellFormed right) (hpublic : KernelPublic left right)
    (handleWord word0 word1 : UInt64) :
    ((dispatchBlockingSend left handleWord word0 word1).reply,
        observe observer (dispatchBlockingSend left handleWord word0 word1).state) =
      ((dispatchBlockingSend right handleWord word0 word1).reply,
        observe observer (dispatchBlockingSend right handleWord word0 word1).state) := by
  have hresolve : CapabilityHandle.resolveCurrent
      left.blockingIPC.scheduler.lifecycle.capabilities { caller := observer } handleWord
      .endpoint = CapabilityHandle.resolveCurrent
        right.blockingIPC.scheduler.lifecycle.capabilities { caller := observer } handleWord
        .endpoint := by
    rw [blockingCaps_eq hleft, blockingCaps_eq hright]
    exact h.low.resolveCurrent handleWord .endpoint
  cases hres : CapabilityHandle.resolveCurrent left.blockingIPC.scheduler.lifecycle.capabilities
      { caller := observer } handleWord .endpoint with
  | error reason =>
      have hresR := hresolve.symm.trans hres
      have hSL : left.execution.core.context.currentSubject = observer := h.leftActor.1
      have hSR : right.execution.core.context.currentSubject = observer := h.rightActor.1
      simp only [dispatchBlockingSend, hSL, hSR, hres, hresR]
      rw [h.low]
  | ok resolution =>
      rw [dispatchBlockingSend_shape hleft h.current handleWord word0 word1 resolution hres,
        dispatchBlockingSend_shape hright h.rightCurrent handleWord word0 word1 resolution
          (hresolve.symm.trans hres)]
      exact sendShape_eq h hleft hright hpublic resolution
        (resolveCurrent_ok_lookup _ _ _ _ _ hres) _

/-- **Step and output consistency of the observer's blocking send**, with the
scheduler's bookkeeping public. -/
theorem own_blockingSend {observer : Nat} {left right : CompositeState}
    (h : OwnStep observer left right) (hleft : AuthoritativeRuntimeWellFormed left)
    (hright : AuthoritativeRuntimeWellFormed right) (hpublic : KernelPublic left right)
    (handleWord word0 word1 : UInt64) :
    LowEquiv observer (authoritativeGate left (.blocking (.send handleWord word0 word1))).state
        (authoritativeGate right (.blocking (.send handleWord word0 word1))).state ∧
      (authoritativeGate left (.blocking (.send handleWord word0 word1))).result =
        (authoritativeGate right (.blocking (.send handleWord word0 word1))).result := by
  cases hmode : left.execution.mode with
  | handling entry =>
      have hrm : right.execution.mode = .handling entry := h.mode ▸ hmode
      simp only [authoritativeGate, hmode, hrm]
      exact ⟨h.low, trivial⟩
  | halted record =>
      have hrm : right.execution.mode = .halted record := h.mode ▸ hmode
      simp only [authoritativeGate, hmode, hrm]
      exact ⟨h.low, trivial⟩
  | running =>
      have hrm : right.execution.mode = .running := h.mode ▸ hmode
      have hpair := dispatchBlockingSend_pair_eq h hleft hright hpublic handleWord word0 word1
      simp only [Prod.mk.injEq] at hpair
      simp only [authoritativeGate, hmode, hrm, applyAuthoritativeOperation,
        applyBlockingOperation, authoritativeOperationReply, blockingOperationReply]
      exact ⟨hpair.2, by rw [hpair.1]⟩


/-- Two-state congruence of a raw receive-or-block. -/
theorem receive_congr (a b : BlockingIPC.State) (caller slot : Nat)
    (hcurrent : a.scheduler.lifecycle.current = b.scheduler.lifecycle.current)
    (hlookup : Capability.lookup a.scheduler.lifecycle.capabilities caller slot =
      Capability.lookup b.scheduler.lifecycle.capabilities caller slot)
    (hfields : ∀ cap, Capability.lookup b.scheduler.lifecycle.capabilities caller slot =
        .found cap →
      a.scheduler.lifecycle.capabilities.objects cap.object =
          b.scheduler.lifecycle.capabilities.objects cap.object ∧
        a.waiters cap.object = b.waiters cap.object ∧ a.mailbox cap.object = b.mailbox cap.object)
    (hcompletion : a.completion caller = b.completion caller)
    (hwaiting : a.waiterEndpoint caller = b.waiterEndpoint caller)
    (hcapacity : a.waiterCapacity = b.waiterCapacity)
    (hready : a.scheduler.ready = b.scheduler.ready)
    (hownA : ∀ subject, subject ∈ a.scheduler.ready →
      a.scheduler.lifecycle.addressOwner subject = some subject)
    (hownB : ∀ subject, subject ∈ b.scheduler.ready →
      b.scheduler.lifecycle.addressOwner subject = some subject) :
    (BlockingIPC.receiveOrBlock a caller slot).result =
        (BlockingIPC.receiveOrBlock b caller slot).result ∧
      (BlockingIPC.receiveOrBlock a caller slot).state.scheduler.lifecycle.current =
        (BlockingIPC.receiveOrBlock b caller slot).state.scheduler.lifecycle.current ∧
      (∀ object, a.mailbox object = b.mailbox object → a.waiters object = b.waiters object →
        (BlockingIPC.receiveOrBlock a caller slot).state.mailbox object =
            (BlockingIPC.receiveOrBlock b caller slot).state.mailbox object ∧
          (BlockingIPC.receiveOrBlock a caller slot).state.waiters object =
            (BlockingIPC.receiveOrBlock b caller slot).state.waiters object) ∧
      (BlockingIPC.receiveOrBlock a caller slot).state.waiterEndpoint caller =
        (BlockingIPC.receiveOrBlock b caller slot).state.waiterEndpoint caller ∧
      (BlockingIPC.receiveOrBlock a caller slot).state.completion caller =
        (BlockingIPC.receiveOrBlock b caller slot).state.completion caller := by
  have hselect : ∀ (x : BlockingIPC.State), (∀ subject, subject ∈ x.scheduler.ready →
      x.scheduler.lifecycle.addressOwner subject = some subject) → ∀ endpoint,
      Scheduler.selectNext (BlockingIPC.blockState x endpoint caller).scheduler =
        match x.scheduler.ready with
        | [] => { state := (BlockingIPC.blockState x endpoint caller).scheduler
                  result := .accepted none }
        | head :: rest =>
            { state := { (BlockingIPC.blockState x endpoint caller).scheduler with
                ready := rest
                lifecycle := { (BlockingIPC.blockState x endpoint caller).scheduler.lifecycle with
                  current := some head } }
              result := .accepted (some ⟨head, head⟩) } := by
    intro x hown endpoint
    simp only [BlockingIPC.blockState, Scheduler.selectNext]
    cases hq : x.scheduler.ready with
    | nil => rfl
    | cons head rest =>
        have := hown head (by rw [hq]; exact List.mem_cons_self)
        simp [Scheduler.ownsAddressSpace, this]
  simp only [BlockingIPC.receiveOrBlock, hcurrent, hlookup]
  cases hfound : Capability.lookup b.scheduler.lifecycle.capabilities caller slot with
  | invalidSubject =>
      simp only [BlockingIPC.rejectReceive]
      split <;> exact ⟨rfl, hcurrent, fun _ h1 h2 => ⟨h1, h2⟩, hwaiting, hcompletion⟩
  | staleSlot =>
      simp only [BlockingIPC.rejectReceive]
      split <;> exact ⟨rfl, hcurrent, fun _ h1 h2 => ⟨h1, h2⟩, hwaiting, hcompletion⟩
  | found cap =>
      obtain ⟨hobj, hwait, hmail⟩ := hfields cap hfound
      simp only [hobj, hwait, hmail, hcompletion, hcapacity, BlockingIPC.allWaiters, hwaiting]
      simp only [hselect a hownA cap.object, hselect b hownB cap.object, hready]
      by_cases hc1 : (b.scheduler.lifecycle.current != some caller) = true
      · simp [hc1, BlockingIPC.rejectReceive, hcurrent, hwaiting, hcompletion] <;>
          exact fun _ h1 h2 => ⟨h1, h2⟩
      by_cases hc2 : (cap.kind != .endpoint) = true
      · simp [hc1, hc2, BlockingIPC.rejectReceive, hcurrent, hwaiting, hcompletion] <;>
          exact fun _ h1 h2 => ⟨h1, h2⟩
      by_cases hc3 : (!cap.rights.receive) = true
      · simp [hc1, hc2, hc3, BlockingIPC.rejectReceive, hcurrent, hwaiting, hcompletion] <;>
          exact fun _ h1 h2 => ⟨h1, h2⟩
      by_cases hc4 : (!b.scheduler.lifecycle.capabilities.objects cap.object) = true
      · simp [hc1, hc2, hc3, hc4, BlockingIPC.rejectReceive, hcurrent, hwaiting, hcompletion] <;>
          exact fun _ h1 h2 => ⟨h1, h2⟩
      simp only [hc1, hc2, hc3, hc4, Bool.false_eq_true, ↓reduceIte]
      cases hcomp : b.completion caller with
      | some completion =>
          cases completion <;>
            simp [BlockingIPC.setCompletion, hcurrent, hwaiting, hcomp] <;>
            exact fun _ h1 h2 => ⟨h1, h2⟩
      | none =>
          simp only
          cases hmbox : b.mailbox cap.object with
          | some envelope =>
              simp only [BlockingIPC.setMailbox]
              refine ⟨?_, ?_, fun object h1 h2 => ?_, ?_, ?_⟩
              all_goals
                first | rfl | trivial | exact hcurrent | exact hwaiting | exact hcompletion | skip
              split
              · exact ⟨rfl, h2⟩
              · exact ⟨h1, h2⟩
          | none =>
              simp only
              by_cases hw : (b.waiterEndpoint caller).isSome = true
              · simp [hw, BlockingIPC.rejectReceive, hcurrent, hwaiting, hcompletion] <;>
                  exact fun _ h1 h2 => ⟨h1, h2⟩
              by_cases hfull : b.waiterCapacity ≤ (b.waiters cap.object).length
              · simp [hw, hfull, BlockingIPC.rejectReceive, hcurrent, hwaiting, hcompletion] <;>
                  exact fun _ h1 h2 => ⟨h1, h2⟩
              simp only [hw, hfull, Bool.false_eq_true, ↓reduceIte]
              cases hq : b.scheduler.ready with
              | nil =>
                  simp only [BlockingIPC.blockState]
                  refine ⟨?_, ?_, fun object h1 h2 => ?_, ?_, ?_⟩
                  all_goals
                    first | rfl | trivial | exact hcompletion | simp [BlockingIPC.setWaiterEndpoint] | skip
                  simp only [BlockingIPC.setWaiters]
                  split
                  · subst object; simp [hwait, h1]
                  · exact ⟨h1, h2⟩
              | cons head rest =>
                  simp only [BlockingIPC.blockState]
                  refine ⟨?_, ?_, fun object h1 h2 => ?_, ?_, ?_⟩
                  all_goals
                    first | rfl | trivial | exact hcompletion | simp [BlockingIPC.setWaiterEndpoint] | skip
                  simp only [BlockingIPC.setWaiters]
                  split
                  · subst object; simp [hwait, h1]
                  · exact ⟨h1, h2⟩


def receiveShape (observer : Nat) (state : CompositeState) (slot : Nat)
    (frame : Interrupt.HardwareFrame) : CompositeBlockingReceiveReply × View :=
  if Interrupt.validSavedUserFrame frame = false then
    (.contextRejected .invalidSaved, observe observer state)
  else
    match (BlockingIPC.receiveOrBlock state.blockingIPC observer slot).result with
    | .rejected reason => (.rejected reason, observe observer state)
    | .delivered envelope => (.delivered envelope, observe observer (publishBlockingIPCContext
        state ⟨(BlockingIPC.receiveOrBlock state.blockingIPC observer slot).state,
          state.blockingContexts⟩))
    | .blocked =>
        match (BlockingIPC.receiveOrBlock state.blockingIPC observer
            slot).state.scheduler.lifecycle.current with
        | none => (.blocked, observe observer (publishBlockingIPCContext state
            ⟨(BlockingIPC.receiveOrBlock state.blockingIPC observer slot).state,
              state.blockingContexts⟩))
        | some head =>
            if head ∈ state.resumable.contexts.map (·.owner) then
              (.blocked, observe observer (publishBlockingIPCContext state
                ⟨(BlockingIPC.receiveOrBlock state.blockingIPC observer slot).state,
                  state.blockingContexts⟩))
            else (.switchRequired, observe observer state)

/-- A blocking handoff restores the head of the ready queue exactly when the
bank holds its context. -/
theorem restoreBlockingPeer_shape (state : CompositeState) (blocking : BlockingIPCContext.State)
    (head : Nat) (hcurrent : blocking.ipc.scheduler.lifecycle.current = some head)
    (hvalid : ∀ destination, destination ∈ state.resumable.contexts →
      destination.owner = head →
      destination.addressSpace = head ∧ Interrupt.validSavedUserFrame destination.frame = true ∧
        blocking.ipc.scheduler.lifecycle.capabilities.subjects head = true ∧
        blocking.ipc.scheduler.lifecycle.runnable head = true ∧
        blocking.ipc.scheduler.lifecycle.addressOwner head = some head ∧
        state.resumable.translations.virtual.owner head = some head) :
    (match restoreBlockingPeer state blocking with
      | .error _ => none
      | .ok next => some (observe observer next)) =
      if head ∈ state.resumable.contexts.map (·.owner) then
        some (observe observer (publishBlockingIPCContext state blocking))
      else none := by
  unfold restoreBlockingPeer
  simp only [hcurrent]
  cases hfind : ResumablePreemption.contextFor state.resumable.contexts head with
  | none =>
      have hnot : head ∉ state.resumable.contexts.map (·.owner) := by
        intro hmem
        have := (contextFor_some_iff state.resumable.contexts head).2 hmem
        rw [hfind] at this
        cases this
      simp [hnot]
  | some destination =>
      have hmem : head ∈ state.resumable.contexts.map (·.owner) :=
        (contextFor_some_iff state.resumable.contexts head).1 (by rw [hfind]; rfl)
      have hdmem : destination ∈ state.resumable.contexts := List.mem_of_find?_eq_some hfind
      have hdowner : destination.owner = head := by
        have := List.find?_some hfind
        simpa using this
      obtain ⟨hspace, hframe, hlive, hrunnable, hown, hvirtual⟩ := hvalid destination hdmem hdowner
      simp [hmem, hdowner, hspace, hframe, hlive, hrunnable, hown, hvirtual]
      rfl


/-- A blocked raw receive keeps the lifecycle except that the caller is no
longer runnable and the head of the ready queue, if any, is scheduled. -/
theorem receive_blocked_lifecycle (blocking : BlockingIPC.State) (caller slot : Nat)
    (hblocked : (BlockingIPC.receiveOrBlock blocking caller slot).result = .blocked) :
    (BlockingIPC.receiveOrBlock blocking caller slot).state.scheduler.lifecycle.capabilities =
        blocking.scheduler.lifecycle.capabilities ∧
      (BlockingIPC.receiveOrBlock blocking caller slot).state.scheduler.lifecycle.runnable =
        SubjectLifecycle.setBool blocking.scheduler.lifecycle.runnable caller false ∧
      (BlockingIPC.receiveOrBlock blocking caller slot).state.scheduler.lifecycle.addressOwner =
        blocking.scheduler.lifecycle.addressOwner ∧
      (∀ head, (BlockingIPC.receiveOrBlock blocking caller
          slot).state.scheduler.lifecycle.current = some head →
        head ∈ blocking.scheduler.ready) := by
  revert hblocked
  unfold BlockingIPC.receiveOrBlock
  repeat' split
  all_goals simp_all [BlockingIPC.rejectReceive]
  all_goals
    rename_i hselect
    simp only [BlockingIPC.blockState, Scheduler.selectNext] at hselect ⊢
    revert hselect
    repeat' split
  all_goals simp_all [Scheduler.reject]


theorem dispatchBlockingReceive_shape {observer : Nat} {state : CompositeState}
    (hstate : AuthoritativeRuntimeWellFormed state)
    (hcurrent : state.lifecycle.current = some observer)
    (handleWord : UInt64) (frame : Interrupt.HardwareFrame)
    (registers : ResumableContext.Registers) (resolution : CapabilityHandle.Resolution)
    (hresolve : CapabilityHandle.resolveCurrent
      state.blockingIPC.scheduler.lifecycle.capabilities { caller := observer } handleWord
      .endpoint = .ok resolution) :
    ((dispatchBlockingReceive state handleWord frame registers).reply,
        observe observer (dispatchBlockingReceive state handleWord frame registers).state) =
      receiveShape observer state resolution.handle.slot frame := by
  have hcoherent := coherent_of hstate
  obtain ⟨hS, hspace⟩ := actor_of_current hcoherent hcurrent
  have hS' : state.execution.core.context.currentSubject = observer := hS
  have hcontext : BlockingIPCContext.WellFormed state.blockingIPCContext := hstate.blocking.2
  have hnotWaiting : state.blockingIPC.waiterEndpoint observer = none := by
    cases h : state.blockingIPC.waiterEndpoint observer with
    | none => rfl
    | some endpoint =>
        exact absurd ((hcontext.1.2.2.2.2.1 endpoint observer).2 h)
          (current_not_waiter hstate hcurrent endpoint)
  have hnotBlocked : state.blockingContexts observer = none := by
    have := hcontext.2.1 observer
    simp only [CompositeState.blockingIPCContext, hnotWaiting, Option.isSome_none] at this
    exact Option.not_isSome_iff_eq_none.1 (by simp [this])
  simp only [dispatchBlockingReceive, hS', hresolve]
  unfold BlockingIPCContext.receiveOrBlock receiveShape
  have hvalid : BlockingIPCContext.validSaved observer
      (state.blockingSavedContext frame registers) = Interrupt.validSavedUserFrame frame := by
    have hkind : (ResumableContext.ContextKind.suspended ==
        ResumableContext.ContextKind.suspended) = true := by decide
    simp [BlockingIPCContext.validSaved, CompositeState.blockingSavedContext, hS', hspace, hkind]
  simp only [hvalid, CompositeState.blockingIPCContext, hnotBlocked, Option.isSome_none]
  by_cases hframe : Interrupt.validSavedUserFrame frame = false
  · simp [hframe]
  have hframeTrue : Interrupt.validSavedUserFrame frame = true := by simpa using hframe
  simp only [hframeTrue, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  generalize hraw : BlockingIPC.receiveOrBlock state.blockingIPC observer
    resolution.handle.slot = raw
  rcases raw with ⟨next, result⟩
  cases result with
  | rejected reason => rfl
  | delivered envelope => rfl
  | blocked =>
      obtain ⟨hcaps, hrunnable, howner, hready⟩ := receive_blocked_lifecycle state.blockingIPC
        observer resolution.handle.slot (by rw [hraw])
      rw [hraw] at hcaps hrunnable howner hready
      simp only at hcaps hrunnable howner hready ⊢
      cases hnext : next.scheduler.lifecycle.current with
      | none => rfl
      | some head =>
          simp only [Option.isSome_some, ↓reduceIte]
          have hheadReady := hready head hnext
          have hschedWF := hstate.1.2.2.2.2.2.2.1
          have hblockScheduler : state.blockingIPC.scheduler = state.scheduler :=
            hstate.1.blockingScheduler
          rw [hblockScheduler] at hheadReady
          obtain ⟨hlive, hrun, hownsSpace⟩ := hschedWF.2.2.2.1 head hheadReady
          have hne : head ≠ observer := by
            intro heq
            subst heq
            exact (hschedWF.2.2.2.2 head (by rw [hcoherent.2.1]; exact hcurrent)).2.2.2 hheadReady
          have hownHead : state.scheduler.lifecycle.addressOwner head = some head := by
            unfold Scheduler.ownsAddressSpace at hownsSpace
            split at hownsSpace
            · assumption
            · contradiction
          have hres := restoreBlockingPeer_shape (observer := observer) state
            ⟨next, BlockingIPCContext.setBlocked state.blockingContexts observer
              (some (state.blockingSavedContext frame registers))⟩ head hnext (by
            intro destination hdmem hdowner
            obtain ⟨hdframe, hdspace, _, _, _⟩ := hstate.1.2.2.2.2.2.2.2.2.1.2.2.2.1
              destination hdmem
            have htranslation := hstate.1.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.1
            refine ⟨by rw [hdspace, hdowner], hdframe, ?_, ?_, ?_, ?_⟩
            · simp only [hcaps, hblockScheduler]; exact hlive
            · simp only [hrunnable, SubjectLifecycle.setBool, hne, ↓reduceIte, hblockScheduler]
              exact hrun
            · simp only [howner, hblockScheduler]; exact hownHead
            · rw [htranslation.1, resumable_lifecycle hcoherent, ← hcoherent.2.1]
              exact hownHead)
          revert hres
          cases restoreBlockingPeer state _ with
          | error reason =>
              intro hres
              simp only at hres
              split at hres
              · simp at hres
              · rename_i hnot
                simp [hnot]
          | ok published =>
              intro hres
              simp only at hres
              split at hres
              · rename_i hmem
                simp only [Option.some.injEq] at hres
                simp only [hmem, ↓reduceIte, hres, Prod.mk.injEq, true_and]
                rfl
              · simp at hres


theorem receiveShape_eq {observer : Nat} {left right : CompositeState}
    (h : OwnStep observer left right) (hleft : AuthoritativeRuntimeWellFormed left)
    (hright : AuthoritativeRuntimeWellFormed right) (hpublic : KernelPublic left right)
    (resolution : CapabilityHandle.Resolution)
    (hlookupL : Capability.lookup left.blockingIPC.scheduler.lifecycle.capabilities observer
      resolution.handle.slot = .found resolution.capability)
    (frame : Interrupt.HardwareFrame) :
    receiveShape observer left resolution.handle.slot frame =
      receiveShape observer right resolution.handle.slot frame := by
  have hlookup : Capability.lookup left.blockingIPC.scheduler.lifecycle.capabilities observer
      resolution.handle.slot = Capability.lookup right.blockingIPC.scheduler.lifecycle.capabilities
        observer resolution.handle.slot := by
    rw [blockingCaps_eq hleft, blockingCaps_eq hright]; exact h.lookup _
  have hcurL : left.blockingIPC.scheduler.lifecycle.current = some observer := by
    rw [blockingCurrent_eq (blockingCoherent_of hleft)]; exact h.current
  have hcurR : right.blockingIPC.scheduler.lifecycle.current = some observer := by
    rw [blockingCurrent_eq (blockingCoherent_of hright)]; exact h.rightCurrent
  have hschedL : left.blockingIPC.scheduler = left.scheduler := hleft.1.blockingScheduler
  have hschedR : right.blockingIPC.scheduler = right.scheduler := hright.1.blockingScheduler
  have howns : ∀ (state : CompositeState), AuthoritativeRuntimeWellFormed state →
      ∀ subject, subject ∈ state.blockingIPC.scheduler.ready →
        state.blockingIPC.scheduler.lifecycle.addressOwner subject = some subject := by
    intro state hstate subject hmem
    rw [hstate.1.blockingScheduler] at hmem ⊢
    have hsome := (hstate.1.2.2.2.2.2.2.1.2.2.2.1 subject hmem).2.2
    unfold Scheduler.ownsAddressSpace at hsome
    split at hsome
    · assumption
    · contradiction
  obtain ⟨hresult, hcurrent, hstates, hwaiting, hcompletion⟩ := receive_congr
    left.blockingIPC right.blockingIPC observer resolution.handle.slot
    (hcurL.trans hcurR.symm) hlookup
    (by
      intro cap hcap
      rw [← hlookup, hlookupL] at hcap
      cases hcap
      have hnamed : Names left observer resolution.capability.object = true := by
        rw [blockingCaps_eq hleft] at hlookupL
        exact names_of_lookup left observer _ _ hlookupL
      have hview := h.low.namedView resolution.capability.object hnamed
      refine ⟨?_, congrArg ObjectView.waiters hview, congrArg ObjectView.blockingMailbox hview⟩
      rw [blockingCaps_eq hleft, blockingCaps_eq hright]
      exact congrArg ObjectView.live hview)
    (congrArg View.completion h.low) (congrArg View.waitingOn h.low) hpublic.waiterCapacity
    (by rw [hschedL, hschedR, hpublic.ready]) (howns left hleft) (howns right hright)
  have hpublish : observe observer (publishBlockingIPCContext left
        ⟨(BlockingIPC.receiveOrBlock left.blockingIPC observer resolution.handle.slot).state,
          left.blockingContexts⟩) =
      observe observer (publishBlockingIPCContext right
        ⟨(BlockingIPC.receiveOrBlock right.blockingIPC observer resolution.handle.slot).state,
          right.blockingContexts⟩) := by
    apply lowEquiv_publishBlocking h.low
    · exact hcurrent
    · intro object hnames
      have hv := h.low.namedView object hnames
      exact hstates object (congrArg ObjectView.blockingMailbox hv)
        (congrArg ObjectView.waiters hv)
    · exact hwaiting
    · exact hcompletion
  unfold receiveShape
  rw [hresult, hcurrent, hpublic.bank, hpublish, h.low]

theorem dispatchBlockingReceive_pair_eq {observer : Nat} {left right : CompositeState}
    (h : OwnStep observer left right) (hleft : AuthoritativeRuntimeWellFormed left)
    (hright : AuthoritativeRuntimeWellFormed right) (hpublic : KernelPublic left right)
    (handleWord : UInt64) (frame : Interrupt.HardwareFrame)
    (registers : ResumableContext.Registers) :
    ((dispatchBlockingReceive left handleWord frame registers).reply,
        observe observer (dispatchBlockingReceive left handleWord frame registers).state) =
      ((dispatchBlockingReceive right handleWord frame registers).reply,
        observe observer (dispatchBlockingReceive right handleWord frame registers).state) := by
  have hresolve : CapabilityHandle.resolveCurrent
      left.blockingIPC.scheduler.lifecycle.capabilities { caller := observer } handleWord
      .endpoint = CapabilityHandle.resolveCurrent
        right.blockingIPC.scheduler.lifecycle.capabilities { caller := observer } handleWord
        .endpoint := by
    rw [blockingCaps_eq hleft, blockingCaps_eq hright]
    exact h.low.resolveCurrent handleWord .endpoint
  cases hres : CapabilityHandle.resolveCurrent left.blockingIPC.scheduler.lifecycle.capabilities
      { caller := observer } handleWord .endpoint with
  | error reason =>
      have hresR := hresolve.symm.trans hres
      have hSL : left.execution.core.context.currentSubject = observer := h.leftActor.1
      have hSR : right.execution.core.context.currentSubject = observer := h.rightActor.1
      simp only [dispatchBlockingReceive, hSL, hSR, hres, hresR]
      rw [h.low]
  | ok resolution =>
      rw [dispatchBlockingReceive_shape hleft h.current handleWord frame registers resolution hres,
        dispatchBlockingReceive_shape hright h.rightCurrent handleWord frame registers resolution
          (hresolve.symm.trans hres)]
      exact receiveShape_eq h hleft hright hpublic resolution
        (resolveCurrent_ok_lookup _ _ _ _ _ hres) frame

theorem own_blockingReceive {observer : Nat} {left right : CompositeState}
    (h : OwnStep observer left right) (hleft : AuthoritativeRuntimeWellFormed left)
    (hright : AuthoritativeRuntimeWellFormed right) (hpublic : KernelPublic left right)
    (handleWord : UInt64) (frame : Interrupt.HardwareFrame)
    (registers : ResumableContext.Registers) :
    LowEquiv observer
        (authoritativeGate left (.blocking (.receive handleWord frame registers))).state
        (authoritativeGate right (.blocking (.receive handleWord frame registers))).state ∧
      (authoritativeGate left (.blocking (.receive handleWord frame registers))).result =
        (authoritativeGate right (.blocking (.receive handleWord frame registers))).result := by
  cases hmode : left.execution.mode with
  | handling entry =>
      have hrm : right.execution.mode = .handling entry := h.mode ▸ hmode
      simp only [authoritativeGate, hmode, hrm]
      exact ⟨h.low, trivial⟩
  | halted record =>
      have hrm : right.execution.mode = .halted record := h.mode ▸ hmode
      simp only [authoritativeGate, hmode, hrm]
      exact ⟨h.low, trivial⟩
  | running =>
      have hrm : right.execution.mode = .running := h.mode ▸ hmode
      have hpair := dispatchBlockingReceive_pair_eq h hleft hright hpublic handleWord frame
        registers
      simp only [Prod.mk.injEq] at hpair
      simp only [authoritativeGate, hmode, hrm, applyAuthoritativeOperation,
        applyBlockingOperation, authoritativeOperationReply, blockingOperationReply]
      exact ⟨hpair.2, by rw [hpair.1]⟩


/-- The scheduled observer waits on nothing, so its cancellation of itself is
`notWaiting` and changes nothing. -/
theorem dispatchBlockingCancel_self {observer : Nat} {state : CompositeState}
    (hstate : AuthoritativeRuntimeWellFormed state)
    (hcurrent : state.lifecycle.current = some observer) :
    dispatchBlockingCancel state observer = { state, reply := .notWaiting } := by
  have hcontext : BlockingIPCContext.WellFormed state.blockingIPCContext := hstate.blocking.2
  have hnotWaiting : state.blockingIPC.waiterEndpoint observer = none := by
    cases h : state.blockingIPC.waiterEndpoint observer with
    | none => rfl
    | some endpoint =>
        exact absurd ((hcontext.1.2.2.2.2.1 endpoint observer).2 h)
          (current_not_waiter hstate hcurrent endpoint)
  simp [dispatchBlockingCancel, BlockingIPCContext.cancel, CompositeState.blockingIPCContext,
    hnotWaiting]

theorem own_blockingCancel_self {observer : Nat} {left right : CompositeState}
    (h : OwnStep observer left right) (hleft : AuthoritativeRuntimeWellFormed left)
    (hright : AuthoritativeRuntimeWellFormed right) :
    LowEquiv observer (authoritativeGate left (.blocking (.cancel observer))).state
        (authoritativeGate right (.blocking (.cancel observer))).state ∧
      (authoritativeGate left (.blocking (.cancel observer))).result =
        (authoritativeGate right (.blocking (.cancel observer))).result := by
  cases hmode : left.execution.mode with
  | handling entry =>
      have hrm : right.execution.mode = .handling entry := h.mode ▸ hmode
      simp only [authoritativeGate, hmode, hrm]
      exact ⟨h.low, trivial⟩
  | halted record =>
      have hrm : right.execution.mode = .halted record := h.mode ▸ hmode
      simp only [authoritativeGate, hmode, hrm]
      exact ⟨h.low, trivial⟩
  | running =>
      have hrm : right.execution.mode = .running := h.mode ▸ hmode
      simp only [authoritativeGate, hmode, hrm, applyAuthoritativeOperation,
        applyBlockingOperation, authoritativeOperationReply, blockingOperationReply,
        dispatchBlockingCancel_self hleft h.current, dispatchBlockingCancel_self hright h.rightCurrent]
      exact ⟨h.low, trivial⟩

/-- The scheduled observer's admission of itself is a duplicate. -/
theorem reply_scheduleAdd_self {observer : Nat} {state : CompositeState}
    (hstate : AuthoritativeRuntimeWellFormed state)
    (hcurrent : state.lifecycle.current = some observer) :
    operationReply state (.scheduleAdd observer) = .scheduler (.rejected .duplicate) := by
  have hretained : state.deferredCancels.retained observer = none := by
    cases h : state.deferredCancels.retained observer with
    | none => rfl
    | some saved =>
        have := (hstate.2.1.2.2 observer saved h).2.2.2.2.1
        exact absurd (show state.blockingIPC.scheduler.lifecycle.current = some observer by
          rw [blockingCurrent_eq (blockingCoherent_of hstate)]; exact hcurrent) this
  have hcurrentScheduler : state.scheduler.lifecycle.current = some observer := by
    rw [hstate.1.1.2.1]; exact hcurrent
  obtain ⟨hlive, hrunnable, howns, _⟩ := hstate.1.2.2.2.2.2.2.1.2.2.2.2 observer
    hcurrentScheduler
  have hown : state.scheduler.lifecycle.addressOwner observer = some observer := by
    unfold Scheduler.ownsAddressSpace at howns
    split at howns
    · assumption
    · contradiction
  simp [operationReply, schedulerAdmission, hretained, Scheduler.add, hlive, hrunnable,
    Scheduler.ownsAddressSpace, hown, hcurrentScheduler, Scheduler.reject]

end LeanOS.CompositeOwnBlocking
