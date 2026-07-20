import LeanOS.Scheduler
import LeanOS.CapabilityHandle

/-!
# Atomic blocking endpoint receive

This is a sequential, single-core composition of the lifecycle-owned capability
store and scheduler with bounded endpoint waiter queues.  `scheduler.lifecycle`
is authoritative for identities, authority, address spaces, runnable state, and
the current subject.  This layer owns only wait queues and reserved deliveries;
it does not duplicate those shared fields.
-/
namespace LeanOS.BlockingIPC

open LeanOS
set_option linter.unusedSimpArgs false
abbrev SubjectId := Capability.SubjectId
abbrev ObjectId := Capability.ObjectId
abbrev SlotId := Capability.SlotId

structure Payload where
  word0 : UInt64
  word1 : UInt64
  deriving DecidableEq, Repr

structure Envelope where
  endpoint : ObjectId
  sender : SubjectId
  payload : Payload
  deriving DecidableEq, Repr

inductive Completion where
  | delivered (envelope : Envelope)
  | cancelled
  deriving DecidableEq, Repr

structure State where
  scheduler : Scheduler.State
  /-- Capacity-one endpoint mailbox used only when no receiver is waiting. -/
  mailbox : ObjectId → Option Envelope
  waiters : ObjectId → List SubjectId
  /-- Executable unique-queue index; avoids searching an unbounded endpoint function. -/
  waiterEndpoint : SubjectId → Option ObjectId
  waiterCapacity : Nat
  completion : SubjectId → Option Completion

def endpointOf (state : State) (subject : SubjectId) (slot : SlotId) : Option ObjectId :=
  match Capability.lookup state.scheduler.lifecycle.capabilities subject slot with
  | .found cap => if cap.kind = .endpoint then some cap.object else none
  | _ => none

def authorizedReceive (state : State) (subject : SubjectId) (endpoint : ObjectId) : Prop :=
  ∃ slot cap, state.scheduler.lifecycle.capabilities.slots subject slot = some cap ∧
    cap.object = endpoint ∧ cap.kind = .endpoint ∧ cap.rights.receive = true ∧
    state.scheduler.lifecycle.capabilities.objects endpoint = true

def allWaiters (state : State) (subject : SubjectId) : Bool :=
  (state.waiterEndpoint subject).isSome

/-- Every waiter is unique, live, authorized, blocked, and owns an address space. -/
def WellFormed (state : State) : Prop :=
  Scheduler.WellFormed state.scheduler ∧
  (∀ endpoint, (state.waiters endpoint).Nodup ∧
    (state.waiters endpoint).length ≤ state.waiterCapacity) ∧
  (∀ endpoint subject, subject ∈ state.waiters endpoint →
    state.scheduler.lifecycle.capabilities.objects endpoint = true ∧
    authorizedReceive state subject endpoint ∧
    state.scheduler.lifecycle.capabilities.subjects subject = true ∧
    state.scheduler.lifecycle.runnable subject = false ∧
    Scheduler.ownsAddressSpace state.scheduler subject ≠ none ∧
    state.scheduler.lifecycle.current ≠ some subject ∧ subject ∉ state.scheduler.ready) ∧
  (∀ e₁ e₂ subject, subject ∈ state.waiters e₁ → subject ∈ state.waiters e₂ → e₁ = e₂)
  ∧ (∀ endpoint subject, subject ∈ state.waiters endpoint ↔
    state.waiterEndpoint subject = some endpoint)
  ∧ (∀ endpoint envelope, state.mailbox endpoint = some envelope →
    state.scheduler.lifecycle.capabilities.objects endpoint = true ∧
    state.scheduler.lifecycle.capabilities.kinds endpoint = some .endpoint ∧
    envelope.endpoint = endpoint ∧ state.waiters endpoint = []) ∧
  Capability.WellFormed state.scheduler.lifecycle.capabilities

inductive Error where
  | noCurrent | wrongCaller | staleHandle | wrongKind | missingReceive | missingSend
  | missingRevoke | retiredEndpoint | duplicateWaiter | waiterQueueFull | readyQueueFull | noMessage
  | full | schedulerFailure
  deriving DecidableEq, Repr

inductive ReceiveResult where
  | delivered (envelope : Envelope) | blocked | rejected (reason : Error)
  deriving DecidableEq, Repr

structure ReceiveOutcome where
  state : State
  result : ReceiveResult

inductive Result where | accepted | rejected (reason : Error)
  deriving DecidableEq, Repr

structure Outcome where
  state : State
  result : Result

def rejectReceive (state : State) (reason : Error) : ReceiveOutcome := ⟨state, .rejected reason⟩
def reject (state : State) (reason : Error) : Outcome := ⟨state, .rejected reason⟩

def setWaiters (queues : ObjectId → List SubjectId) endpoint queue :=
  fun candidate => if candidate = endpoint then queue else queues candidate

def setCompletion (values : SubjectId → Option Completion) subject value :=
  fun candidate => if candidate = subject then value else values candidate

def setMailbox (values : ObjectId → Option Envelope) endpoint value :=
  fun candidate => if candidate = endpoint then value else values candidate

def setWaiterEndpoint (values : SubjectId → Option ObjectId) subject value :=
  fun candidate => if candidate = subject then value else values candidate

def removeWaiter (queues : ObjectId → List SubjectId) subject :=
  fun endpoint => (queues endpoint).filter (· ≠ subject)

def blockState (state : State) (endpoint : ObjectId) (caller : SubjectId) : State :=
  { state with
    waiters := setWaiters state.waiters endpoint (state.waiters endpoint ++ [caller])
    waiterEndpoint := setWaiterEndpoint state.waiterEndpoint caller (some endpoint)
    scheduler := { state.scheduler with
      lifecycle := { state.scheduler.lifecycle with
        runnable := SubjectLifecycle.setBool state.scheduler.lifecycle.runnable caller false
        current := none } } }

/-- Empty-check, FIFO registration, and descheduling are one transition. -/
def receiveOrBlock (state : State) (caller : SubjectId) (slot : SlotId) : ReceiveOutcome :=
  if state.scheduler.lifecycle.current != some caller then rejectReceive state .wrongCaller
  else match Capability.lookup state.scheduler.lifecycle.capabilities caller slot with
    | .invalidSubject => rejectReceive state .staleHandle
    | .staleSlot => rejectReceive state .staleHandle
    | .found cap =>
      if cap.kind != .endpoint then rejectReceive state .wrongKind
      else if !cap.rights.receive then rejectReceive state .missingReceive
      else if !state.scheduler.lifecycle.capabilities.objects cap.object then
        rejectReceive state .retiredEndpoint
      else match state.completion caller with
        | some (.delivered envelope) =>
          { state := { state with completion := setCompletion state.completion caller none }
            result := .delivered envelope }
        | some .cancelled =>
          { state := { state with completion := setCompletion state.completion caller none }
            result := .rejected .noMessage }
        | none =>
          match state.mailbox cap.object with
          | some envelope =>
            { state := { state with mailbox := setMailbox state.mailbox cap.object none }
              result := .delivered envelope }
          | none =>
            if allWaiters state caller then rejectReceive state .duplicateWaiter
            else if state.waiterCapacity ≤ (state.waiters cap.object).length then
              rejectReceive state .waiterQueueFull
            else
              let blocked := blockState state cap.object caller
              match Scheduler.selectNext blocked.scheduler with
              | { result := .rejected _, .. } => rejectReceive state .schedulerFailure
              | scheduled =>
                { state := { blocked with scheduler := scheduled.state }, result := .blocked }

def wakeState (state : State) (endpoint : ObjectId) (receiver : SubjectId)
    (envelope : Envelope) : State :=
  { state with
    waiters := setWaiters state.waiters endpoint (state.waiters endpoint).tail
    waiterEndpoint := setWaiterEndpoint state.waiterEndpoint receiver none
    completion := setCompletion state.completion receiver (some (.delivered envelope))
    scheduler := { state.scheduler with
      ready := state.scheduler.ready ++ [receiver]
      lifecycle := { state.scheduler.lifecycle with
        runnable := SubjectLifecycle.setBool state.scheduler.lifecycle.runnable receiver true } } }

/-- An accepted send reserves the exact envelope for the FIFO receiver before wakeup. -/
def send (state : State) (caller : SubjectId) (slot : SlotId) (payload : Payload) : Outcome :=
  if state.scheduler.lifecycle.current != some caller then reject state .wrongCaller
  else match Capability.lookup state.scheduler.lifecycle.capabilities caller slot with
  | .invalidSubject => reject state .staleHandle
  | .staleSlot => reject state .staleHandle
  | .found cap =>
    if cap.kind != .endpoint then reject state .wrongKind
    else if !cap.rights.send then reject state .missingSend
    else if !state.scheduler.lifecycle.capabilities.objects cap.object then
      reject state .retiredEndpoint
    else match state.waiters cap.object with
      | [] =>
        if (state.mailbox cap.object).isSome then reject state .full
        else
          let envelope := { endpoint := cap.object, sender := caller, payload }
          { state := { state with mailbox := setMailbox state.mailbox cap.object (some envelope) }
            result := .accepted }
      | receiver :: _ =>
        if state.scheduler.capacity ≤ state.scheduler.ready.length then
          reject state .readyQueueFull
        else
          let envelope := { endpoint := cap.object, sender := caller, payload }
          { state := wakeState state cap.object receiver envelope, result := .accepted }

/-- Generation-checked holder-facing blocking receive boundary. -/
def receiveOrBlockHandle (state : State) (caller : SubjectId)
    (handle : CapabilityHandle.Handle) : ReceiveOutcome :=
  match CapabilityHandle.resolve state.scheduler.lifecycle.capabilities caller handle .endpoint with
  | .error _ => rejectReceive state .staleHandle
  | .ok _ => receiveOrBlock state caller handle.slot

/-- Generation-checked holder-facing blocking send boundary. -/
def sendHandle (state : State) (caller : SubjectId) (handle : CapabilityHandle.Handle)
    (payload : Payload) : Outcome :=
  match CapabilityHandle.resolve state.scheduler.lifecycle.capabilities caller handle .endpoint with
  | .error _ => reject state .staleHandle
  | .ok _ => send state caller handle.slot payload

inductive WordReceiveResult where
  | completed (result : ReceiveResult)
  | handleRejected (reason : CapabilityHandle.WordResolveDenial)
  deriving DecidableEq, Repr

structure WordReceiveOutcome where
  state : State
  result : WordReceiveResult

inductive WordResult where
  | completed (result : Result)
  | handleRejected (reason : CapabilityHandle.WordResolveDenial)
  deriving DecidableEq, Repr

structure WordOutcome where
  state : State
  result : WordResult

/-- Model-facing blocking receive boundary. The userspace word is decoded and
generation-checked only in the capability space selected by trusted caller
provenance before the internal raw-slot transition is invoked. -/
def receiveOrBlockWord (state : State) (caller : SubjectId)
    (handleWord : UInt64) : WordReceiveOutcome :=
  match CapabilityHandle.resolveCurrent state.scheduler.lifecycle.capabilities
      { caller } handleWord .endpoint with
  | .error reason => { state, result := .handleRejected reason }
  | .ok resolution =>
      let outcome := receiveOrBlock state caller resolution.handle.slot
      { state := outcome.state, result := .completed outcome.result }

/-- Model-facing blocking send boundary with the same canonical handle ABI. -/
def sendWord (state : State) (caller : SubjectId) (handleWord : UInt64)
    (payload : Payload) : WordOutcome :=
  match CapabilityHandle.resolveCurrent state.scheduler.lifecycle.capabilities
      { caller } handleWord .endpoint with
  | .error reason => { state, result := .handleRejected reason }
  | .ok resolution =>
      let outcome := send state caller resolution.handle.slot payload
      { state := outcome.state, result := .completed outcome.result }

/-- Any blocking receive that reaches the raw-slot transition first resolved
the exact current endpoint identity for the trusted caller. -/
theorem completed_receive_word_resolves_exact (state : State) caller handleWord result
    (hcompleted : (receiveOrBlockWord state caller handleWord).result = .completed result) :
    ∃ handle capability,
      CapabilityHandle.decode handleWord = .ok handle ∧
      state.scheduler.lifecycle.capabilities.subjects caller = true ∧
      Capability.slotInRange state.scheduler.lifecycle.capabilities caller handle.slot = true ∧
      state.scheduler.lifecycle.capabilities.slots caller handle.slot = some capability ∧
      capability.identity = handle.identity ∧ capability.kind = .endpoint ∧
      state.scheduler.lifecycle.capabilities.objects capability.object = true ∧
      state.scheduler.lifecycle.capabilities.kinds capability.object = some .endpoint := by
  cases hresolve : CapabilityHandle.resolveCurrent state.scheduler.lifecycle.capabilities
      { caller } handleWord .endpoint with
  | error denial => simp [receiveOrBlockWord, hresolve] at hcompleted
  | ok resolution =>
      rcases CapabilityHandle.resolveCurrent_sound state.scheduler.lifecycle.capabilities
        { caller } handleWord .endpoint resolution hresolve with
        ⟨hdecode, hsubject, hrange, hslot, hidentity, hkind, hlive, hkinds⟩
      exact ⟨resolution.handle, resolution.capability, hdecode, hsubject, hrange,
        hslot, hidentity, hkind, hlive, hkinds⟩

/-- Malformed or stale words are state-preserving at the shared userspace
boundary; no raw-slot lookup or blocking transition is reached. -/
theorem rejected_receive_word_preserves_state (state : State) caller handleWord reason
    (hrejected : (receiveOrBlockWord state caller handleWord).result =
      .handleRejected reason) :
    (receiveOrBlockWord state caller handleWord).state = state := by
  cases hresolve : CapabilityHandle.resolveCurrent state.scheduler.lifecycle.capabilities
      { caller } handleWord .endpoint <;>
    simp [receiveOrBlockWord, hresolve] at hrejected ⊢

/-- Any blocking send that reaches the raw-slot transition first resolved the
exact current endpoint identity for the trusted caller. -/
theorem completed_send_word_resolves_exact (state : State) caller handleWord payload result
    (hcompleted : (sendWord state caller handleWord payload).result = .completed result) :
    ∃ handle capability,
      CapabilityHandle.decode handleWord = .ok handle ∧
      state.scheduler.lifecycle.capabilities.subjects caller = true ∧
      Capability.slotInRange state.scheduler.lifecycle.capabilities caller handle.slot = true ∧
      state.scheduler.lifecycle.capabilities.slots caller handle.slot = some capability ∧
      capability.identity = handle.identity ∧ capability.kind = .endpoint ∧
      state.scheduler.lifecycle.capabilities.objects capability.object = true ∧
      state.scheduler.lifecycle.capabilities.kinds capability.object = some .endpoint := by
  cases hresolve : CapabilityHandle.resolveCurrent state.scheduler.lifecycle.capabilities
      { caller } handleWord .endpoint with
  | error denial => simp [sendWord, hresolve] at hcompleted
  | ok resolution =>
      rcases CapabilityHandle.resolveCurrent_sound state.scheduler.lifecycle.capabilities
        { caller } handleWord .endpoint resolution hresolve with
        ⟨hdecode, hsubject, hrange, hslot, hidentity, hkind, hlive, hkinds⟩
      exact ⟨resolution.handle, resolution.capability, hdecode, hsubject, hrange,
        hslot, hidentity, hkind, hlive, hkinds⟩

/-- Malformed, stale, or wrong-caller send words are state-preserving before
the internal send transition is reached. -/
theorem rejected_send_word_preserves_state (state : State) caller handleWord payload reason
    (hrejected : (sendWord state caller handleWord payload).result = .handleRejected reason) :
    (sendWord state caller handleWord payload).state = state := by
  cases hresolve : CapabilityHandle.resolveCurrent state.scheduler.lifecycle.capabilities
      { caller } handleWord .endpoint <;>
    simp [sendWord, hresolve] at hrejected ⊢

def cancelSubject (state : State) (subject : SubjectId) : State :=
  match state.waiterEndpoint subject with
  | none => state
  | some _ =>
    let live := state.scheduler.lifecycle.capabilities.subjects subject
    if live && state.scheduler.capacity ≤ state.scheduler.ready.length then state
    else
      { state with
        waiters := removeWaiter state.waiters subject
        waiterEndpoint := setWaiterEndpoint state.waiterEndpoint subject none
        completion := setCompletion state.completion subject (some .cancelled)
        scheduler := { state.scheduler with
          ready := if live then state.scheduler.ready ++ [subject] else state.scheduler.ready
          lifecycle := { state.scheduler.lifecycle with
            runnable := if live then
              SubjectLifecycle.setBool state.scheduler.lifecycle.runnable subject true
            else state.scheduler.lifecycle.runnable } } }

inductive CancelResult where
  | notWaiting | cancelled | rejected (reason : Error)
  deriving DecidableEq, Repr

structure CancelOutcome where
  state : State
  result : CancelResult

/-- Waiter removal, cancellation reservation, and wakeup are one typed
transition.  A live waiter cannot be detached unless the bounded ready queue
can admit it; a full queue therefore rejects with the identical pre-state. -/
def cancelSubjectTyped (state : State) (subject : SubjectId) : CancelOutcome :=
  match state.waiterEndpoint subject with
  | none => { state, result := .notWaiting }
  | some _ =>
      if state.scheduler.lifecycle.capabilities.subjects subject &&
          state.scheduler.capacity ≤ state.scheduler.ready.length then
        { state, result := .rejected .readyQueueFull }
      else
        { state := cancelSubject state subject, result := .cancelled }

def cancelEndpoint (state : State) (endpoint : ObjectId) : State :=
  (state.waiters endpoint).foldl cancelSubject state

/-- Endpoint retirement and waiter cancellation are one composite transition. -/
def destroy (state : State) (caller : SubjectId) (slot : SlotId) : Outcome :=
  if state.scheduler.lifecycle.current != some caller then reject state .wrongCaller
  else match Capability.lookup state.scheduler.lifecycle.capabilities caller slot with
  | .invalidSubject => reject state .staleHandle
  | .staleSlot => reject state .staleHandle
  | .found cap =>
    if cap.kind != .endpoint then reject state .wrongKind
    else if !cap.rights.revoke then reject state .missingRevoke
    else if !state.scheduler.lifecycle.capabilities.objects cap.object then
      reject state .retiredEndpoint
    else
      let cancelled := cancelEndpoint state cap.object
      { state := { cancelled with
          mailbox := setMailbox cancelled.mailbox cap.object none
          scheduler := { cancelled.scheduler with lifecycle := { cancelled.scheduler.lifecycle with
            capabilities := EndpointIPC.retire cancelled.scheduler.lifecycle.capabilities cap.object } } }
        result := .accepted }

def destroyHandle (state : State) (caller : SubjectId)
    (handle : CapabilityHandle.Handle) : Outcome :=
  match CapabilityHandle.resolve state.scheduler.lifecycle.capabilities caller handle .endpoint with
  | .error _ => reject state .staleHandle
  | .ok _ => destroy state caller handle.slot

/-- Direct revocation cancels the victim if the shared capability operation accepts. -/
def revoke (state : State) (actor : SubjectId) (authoritySlot : SlotId)
    (victim : SubjectId) (victimSlot : SlotId) : State × Capability.Result :=
  let outcome := Capability.revoke state.scheduler.lifecycle.capabilities
    actor authoritySlot victim victimSlot
  let next := { state with scheduler := { state.scheduler with
    lifecycle := { state.scheduler.lifecycle with capabilities := outcome.state } } }
  if outcome.result = .accepted then (cancelSubject next victim, outcome.result)
  else (state, outcome.result)

def revokeHandle (state : State) (actor : SubjectId) (authority : CapabilityHandle.Handle)
    (victim : SubjectId) (target : CapabilityHandle.Handle) : State × Capability.Result :=
  let outcome := CapabilityHandle.revoke state.scheduler.lifecycle.capabilities
    actor authority .endpoint victim target
  let next := { state with scheduler := { state.scheduler with
    lifecycle := { state.scheduler.lifecycle with capabilities := outcome.state } } }
  if outcome.result = .accepted then (cancelSubject next victim, outcome.result)
  else (state, outcome.result)

/-- Userspace direct revocation for blocking IPC. Both the revocation authority
and victim endpoint are canonical generation-bound words; waiter cancellation
runs only after the shared atomic revocation accepts. -/
def revokeWords (state : State) (actor : SubjectId) (authorityWord : UInt64)
    (victim : SubjectId) (targetWord : UInt64) : State × Capability.Result :=
  let outcome := CapabilityHandle.revokeWords state.scheduler.lifecycle.capabilities
    actor authorityWord .endpoint victim targetWord
  let next := { state with scheduler := { state.scheduler with
    lifecycle := { state.scheduler.lifecycle with capabilities := outcome.state } } }
  if outcome.result = .accepted then (cancelSubject next victim, outcome.result)
  else (state, outcome.result)

/-- An accepted blocking-IPC revocation reached its internal slot transition
only after resolving both exact endpoint generations in their trusted subjects. -/
theorem revokeWords_accepted_resolves state actor authorityWord victim targetWord
    (haccepted : (revokeWords state actor authorityWord victim targetWord).2 = .accepted) :
    ∃ authority target,
      CapabilityHandle.resolveCurrent state.scheduler.lifecycle.capabilities
          { caller := actor } authorityWord .endpoint = .ok authority ∧
      CapabilityHandle.resolveCurrent state.scheduler.lifecycle.capabilities
          { caller := victim } targetWord .endpoint = .ok target ∧
      (Capability.revoke state.scheduler.lifecycle.capabilities actor authority.handle.slot
        victim target.handle.slot).result = .accepted := by
  simp only [revokeWords] at haccepted
  split at haccepted
  next hresult =>
    exact CapabilityHandle.revokeWords_accepted_resolves
      state.scheduler.lifecycle.capabilities actor authorityWord .endpoint victim targetWord hresult
  next hresult => exact False.elim (hresult haccepted)

/-- Transitive revocation performs the same atomic cleanup for every waiter
whose receive authority disappeared from the resulting capability store. -/
noncomputable def revokeSubtree (state : State) (actor : SubjectId) (authoritySlot : SlotId)
    (victim : SubjectId) (victimSlot : SlotId) :
    State × Capability.Result := by
  classical
  exact
  let outcome := Capability.revokeSubtree state.scheduler.lifecycle.capabilities
    actor authoritySlot victim victimSlot
  let next := { state with scheduler := { state.scheduler with
    lifecycle := { state.scheduler.lifecycle with capabilities := outcome.state } } }
  if outcome.result = .accepted then
    ({ next with
      waiters := fun endpoint =>
        (state.waiters endpoint).filter (fun subject => decide (authorizedReceive next subject endpoint))
      waiterEndpoint := fun subject =>
        match state.waiterEndpoint subject with
        | some endpoint => if authorizedReceive next subject endpoint then some endpoint else none
        | none => none
      completion := fun subject =>
        if allWaiters state subject ∧ ¬ allWaiters next subject then some .cancelled
        else state.completion subject }, outcome.result)
  else (state, outcome.result)

noncomputable def revokeSubtreeHandle (state : State) (actor : SubjectId)
    (authority : CapabilityHandle.Handle) (victim : SubjectId)
    (target : CapabilityHandle.Handle) : State × Capability.Result := by
  classical
  exact
  let outcome := CapabilityHandle.revokeSubtree state.scheduler.lifecycle.capabilities
    actor authority .endpoint victim target
  let next := { state with scheduler := { state.scheduler with
    lifecycle := { state.scheduler.lifecycle with capabilities := outcome.state } } }
  if outcome.result = .accepted then
    ({ next with
      waiters := fun endpoint =>
        (state.waiters endpoint).filter (fun subject => decide (authorizedReceive next subject endpoint))
      waiterEndpoint := fun subject =>
        match state.waiterEndpoint subject with
        | some endpoint => if authorizedReceive next subject endpoint then some endpoint else none
        | none => none
      completion := fun subject =>
        if allWaiters state subject ∧ ¬ allWaiters next subject then some .cancelled
        else state.completion subject }, outcome.result)
  else (state, outcome.result)

/-- Userspace transitive revocation applies the same two-word generation checks
before filtering waiters whose endpoint authority lies in the revoked subtree. -/
noncomputable def revokeSubtreeWords (state : State) (actor : SubjectId)
    (authorityWord : UInt64) (victim : SubjectId) (targetWord : UInt64) :
    State × Capability.Result := by
  classical
  exact
  let outcome := CapabilityHandle.revokeSubtreeWords
    state.scheduler.lifecycle.capabilities actor authorityWord .endpoint victim targetWord
  let next := { state with scheduler := { state.scheduler with
    lifecycle := { state.scheduler.lifecycle with capabilities := outcome.state } } }
  if outcome.result = .accepted then
    ({ next with
      waiters := fun endpoint =>
        (state.waiters endpoint).filter (fun subject => decide (authorizedReceive next subject endpoint))
      waiterEndpoint := fun subject =>
        match state.waiterEndpoint subject with
        | some endpoint => if authorizedReceive next subject endpoint then some endpoint else none
        | none => none
      completion := fun subject =>
        if allWaiters state subject ∧ ¬ allWaiters next subject then some .cancelled
        else state.completion subject }, outcome.result)
  else (state, outcome.result)

/-- Accepted transitive revocation resolves the exact current authority and
lineage-root words before reaching the internal subtree transition. -/
theorem revokeSubtreeWords_accepted_resolves state actor authorityWord victim targetWord
    (haccepted : (revokeSubtreeWords state actor authorityWord victim targetWord).2 = .accepted) :
    ∃ authority target,
      CapabilityHandle.resolveCurrent state.scheduler.lifecycle.capabilities
          { caller := actor } authorityWord .endpoint = .ok authority ∧
      CapabilityHandle.resolveCurrent state.scheduler.lifecycle.capabilities
          { caller := victim } targetWord .endpoint = .ok target ∧
      (Capability.revokeSubtree state.scheduler.lifecycle.capabilities actor authority.handle.slot
        victim target.handle.slot).result = .accepted := by
  simp only [revokeSubtreeWords] at haccepted
  split at haccepted
  next hresult =>
    exact CapabilityHandle.revokeSubtreeWords_accepted_resolves
      state.scheduler.lifecycle.capabilities actor authorityWord .endpoint victim targetWord hresult
  next hresult => exact False.elim (hresult haccepted)

def terminate (state : State) (subject : SubjectId) : State :=
  let lifecycle := SubjectLifecycle.terminate state.scheduler.lifecycle subject
  match lifecycle.result with
  | .rejected _ => state
  | .accepted => cancelSubject { state with scheduler := { state.scheduler with
      lifecycle := lifecycle.state
      ready := state.scheduler.ready.filter (· ≠ subject) } } subject

/-! ## Invariant preservation

These total preservation laws are the dependency-local composition boundary.
They retain the authoritative blocking invariant, but do not by themselves
discharge the composite resumable-context obligation: publishing a block must
also save the outgoing caller and consume the selected destination context. -/

private theorem setCompletion_preserves_wellFormed state subject value
    (hwf : WellFormed state) :
    WellFormed { state with completion := setCompletion state.completion subject value } := by
  exact hwf

private theorem clearMailbox_preserves_wellFormed state endpoint
    (hwf : WellFormed state) :
    WellFormed { state with mailbox := setMailbox state.mailbox endpoint none } := by
  rcases hwf with ⟨hscheduler, hqueues, hwaiters, hunique, hindex, hmailbox, hcaps⟩
  refine ⟨hscheduler, hqueues, hwaiters, hunique, hindex, ?_, hcaps⟩
  intro candidate envelope hmail
  by_cases heq : candidate = endpoint
  · subst candidate
    simp [setMailbox] at hmail
  · exact hmailbox candidate envelope (by simpa [setMailbox, heq] using hmail)

private theorem storeMailbox_preserves_wellFormed state endpoint envelope
    (hwf : WellFormed state)
    (hlive : state.scheduler.lifecycle.capabilities.objects endpoint = true)
    (hkind : state.scheduler.lifecycle.capabilities.kinds endpoint = some .endpoint)
    (hendpoint : envelope.endpoint = endpoint)
    (hempty : state.waiters endpoint = []) :
    WellFormed { state with
      mailbox := setMailbox state.mailbox endpoint (some envelope) } := by
  rcases hwf with ⟨hscheduler, hqueues, hwaiters, hunique, hindex, hmailbox, hcaps⟩
  refine ⟨hscheduler, hqueues, hwaiters, hunique, hindex, ?_, hcaps⟩
  intro candidate actual hmail
  by_cases heq : candidate = endpoint
  · subst candidate
    simp [setMailbox] at hmail
    subst actual
    exact ⟨hlive, hkind, hendpoint, hempty⟩
  · exact hmailbox candidate actual (by simpa [setMailbox, heq] using hmail)

private theorem blockState_preserves_wellFormed state endpoint caller
    (hwf : WellFormed state)
    (hcurrent : state.scheduler.lifecycle.current = some caller)
    (hauthorized : authorizedReceive state caller endpoint)
    (hnotWaiting : allWaiters state caller = false)
    (hroom : (state.waiters endpoint).length < state.waiterCapacity)
    (hempty : state.mailbox endpoint = none) :
    WellFormed (blockState state endpoint caller) := by
  rcases hwf with ⟨hscheduler, hqueues, hwaiters, hunique, hindex, hmailbox, hcaps⟩
  have hcurrentProperties := hscheduler.2.2.2.2 caller hcurrent
  have hnoindex : state.waiterEndpoint caller = none := by
    simpa [allWaiters] using hnotWaiting
  have hnotInWaiters (candidate : ObjectId) : caller ∉ state.waiters candidate := by
    intro hmember
    have := (hindex candidate caller).mp hmember
    simp [hnoindex] at this
  have hscheduler' : Scheduler.WellFormed (blockState state endpoint caller).scheduler := by
    rcases hscheduler with ⟨hlifecycle, hreadyNodup, hreadyCapacity,
      hreadyProperties, hcurrentProperty⟩
    rcases hlifecycle with ⟨hissued, hmemory, haddress, hendpoint, hrunnable, hcurrentLive⟩
    refine ⟨?_, hreadyNodup, hreadyCapacity, ?_, ?_⟩
    · refine ⟨hissued, hmemory, haddress, hendpoint, ?_, ?_⟩
      · intro subject hruns
        by_cases heq : subject = caller
        · subst subject
          simp [blockState, SubjectLifecycle.setBool] at hruns
        · apply hrunnable subject
          simpa [blockState, SubjectLifecycle.setBool, heq] using hruns
      · intro subject hselected
        simp [blockState] at hselected
    · intro subject hready
      rcases hreadyProperties subject hready with ⟨hlive, hruns, howns⟩
      have hne : subject ≠ caller := by
        intro heq
        subst subject
        exact hcurrentProperties.2.2.2 hready
      exact ⟨hlive, by simpa [blockState, SubjectLifecycle.setBool, hne],
        by simpa [Scheduler.ownsAddressSpace, blockState] using howns⟩
    · intro subject hselected
      simp [blockState] at hselected
  refine ⟨hscheduler', ?_, ?_, ?_, ?_, ?_, hcaps⟩
  · intro candidate
    by_cases heq : candidate = endpoint
    · subst candidate
      constructor
      · simpa [blockState, setWaiters, List.nodup_append] using
          And.intro (hqueues endpoint).1
            (fun subject hmember heq =>
              hnotInWaiters endpoint (by simpa [heq] using hmember))
      · simp [blockState, setWaiters]
        omega
    · simpa [blockState, setWaiters, heq] using hqueues candidate
  · intro candidate subject hmember
    by_cases heq : candidate = endpoint
    · subst candidate
      simp [blockState, setWaiters] at hmember
      rcases hmember with hold | hcaller
      · have hne : subject ≠ caller := by
          intro hsubject
          subst subject
          exact hnotInWaiters endpoint hold
        rcases hwaiters endpoint subject hold with
          ⟨hliveEndpoint, hauthority, hlive, hblocked, howns, _, hnotReady⟩
        exact ⟨hliveEndpoint, hauthority, hlive,
          by simpa [blockState, SubjectLifecycle.setBool, hne],
          by simpa [Scheduler.ownsAddressSpace, blockState] using howns,
          by simp [blockState], hnotReady⟩
      · subst subject
        exact ⟨hauthorized.choose_spec.choose_spec.2.2.2.2, hauthorized,
          hcurrentProperties.1, by simp [blockState, SubjectLifecycle.setBool],
          by simpa [Scheduler.ownsAddressSpace, blockState] using hcurrentProperties.2.2.1,
          by simp [blockState], hcurrentProperties.2.2.2⟩
    · have hold : subject ∈ state.waiters candidate := by
        simpa [blockState, setWaiters, heq] using hmember
      have hne : subject ≠ caller := by
        intro hsubject
        subst subject
        exact hnotInWaiters candidate hold
      rcases hwaiters candidate subject hold with
        ⟨hliveEndpoint, hauthority, hlive, hblocked, howns, _, hnotReady⟩
      exact ⟨hliveEndpoint, hauthority, hlive,
        by simpa [blockState, SubjectLifecycle.setBool, hne],
        by simpa [Scheduler.ownsAddressSpace, blockState] using howns,
        by simp [blockState], hnotReady⟩
  · intro first second subject hfirst hsecond
    by_cases hsubject : subject = caller
    · subst subject
      have firstEq : first = endpoint := by
        by_cases heq : first = endpoint
        · exact heq
        · exact False.elim
            (hnotInWaiters first (by simpa [blockState, setWaiters, heq] using hfirst))
      have secondEq : second = endpoint := by
        by_cases heq : second = endpoint
        · exact heq
        · exact False.elim
            (hnotInWaiters second (by simpa [blockState, setWaiters, heq] using hsecond))
      exact firstEq.trans secondEq.symm
    · have oldMember (candidate) (hmember :
          subject ∈ (blockState state endpoint caller).waiters candidate) :
          subject ∈ state.waiters candidate := by
        by_cases heq : candidate = endpoint
        · subst candidate
          simpa [blockState, setWaiters, hsubject] using hmember
        · simpa [blockState, setWaiters, heq] using hmember
      exact hunique first second subject (oldMember first hfirst) (oldMember second hsecond)
  · intro candidate subject
    by_cases hsubject : subject = caller
    · subst subject
      by_cases heq : candidate = endpoint
      · subst candidate
        simp [blockState, setWaiters, setWaiterEndpoint, hnotInWaiters endpoint]
      · simp [blockState, setWaiters, setWaiterEndpoint, heq, Ne.symm heq,
          hnotInWaiters candidate]
    · by_cases heq : candidate = endpoint
      · subst candidate
        simpa [blockState, setWaiters, setWaiterEndpoint, hsubject] using
          hindex endpoint subject
      · simpa [blockState, setWaiters, setWaiterEndpoint, hsubject, heq] using
          hindex candidate subject
  · intro candidate envelope hmail
    have hmailOld : state.mailbox candidate = some envelope := by
      simpa [blockState] using hmail
    have hold := hmailbox candidate envelope hmailOld
    have hne : candidate ≠ endpoint := by
      intro heq
      subst candidate
      rw [hempty] at hmailOld
      simp at hmailOld
    simpa [blockState, setWaiters, hne] using hold

private theorem selectNext_preserves_wellFormed state
    (hwf : WellFormed state) :
    WellFormed { state with scheduler := (Scheduler.selectNext state.scheduler).state } := by
  rcases hwf with ⟨hscheduler, hqueues, hwaiters, hunique, hindex, hmailbox, hcaps⟩
  have hscheduler' := Scheduler.selectNext_preserves_wellFormed state.scheduler hscheduler
  cases hcurrent : state.scheduler.lifecycle.current with
  | some current =>
      simpa [Scheduler.selectNext, hcurrent, Scheduler.reject] using
        (show WellFormed state from
          ⟨hscheduler, hqueues, hwaiters, hunique, hindex, hmailbox, hcaps⟩)
  | none =>
      cases hready : state.scheduler.ready with
      | nil =>
          simpa [Scheduler.selectNext, hcurrent, hready] using
            (show WellFormed state from
              ⟨hscheduler, hqueues, hwaiters, hunique, hindex, hmailbox, hcaps⟩)
      | cons selected rest =>
          cases hspace : Scheduler.ownsAddressSpace state.scheduler selected with
          | none =>
              simpa [Scheduler.selectNext, hcurrent, hready, hspace, Scheduler.reject] using
                (show WellFormed state from
                  ⟨hscheduler, hqueues, hwaiters, hunique, hindex, hmailbox, hcaps⟩)
          | some addressSpace =>
              have hselected : (Scheduler.selectNext state.scheduler).state =
                  { state.scheduler with ready := rest, lifecycle :=
                    { state.scheduler.lifecycle with current := some selected } } := by
                simp [Scheduler.selectNext, hcurrent, hready, hspace]
              rw [hselected] at hscheduler' ⊢
              refine ⟨hscheduler', hqueues, ?_, hunique, hindex, hmailbox, hcaps⟩
              intro endpoint subject hmember
              rcases hwaiters endpoint subject hmember with
                ⟨hliveEndpoint, hauthority, hlive, hblocked, howns, _, hnotReady⟩
              refine ⟨hliveEndpoint, hauthority, hlive, hblocked, ?_, ?_, ?_⟩
              · simpa [Scheduler.ownsAddressSpace] using howns
              · intro heq
                have : subject = selected := Option.some.inj heq.symm
                subst subject
                exact hnotReady (by simp [hready])
              · intro hmem
                exact hnotReady (by simp [hready, hmem])

private theorem wakeState_preserves_wellFormed state endpoint receiver rest envelope
    (hwf : WellFormed state)
    (hqueue : state.waiters endpoint = receiver :: rest)
    (hroom : state.scheduler.ready.length < state.scheduler.capacity) :
    WellFormed (wakeState state endpoint receiver envelope) := by
  rcases hwf with ⟨hscheduler, hqueues, hwaiters, hunique, hindex, hmailbox, hcaps⟩
  have hreceiverMember : receiver ∈ state.waiters endpoint := by simp [hqueue]
  rcases hwaiters endpoint receiver hreceiverMember with
    ⟨hliveEndpoint, hreceiverAuthority, hreceiverLive, hreceiverBlocked,
      hreceiverOwns, hreceiverNotCurrent, hreceiverNotReady⟩
  have hscheduler' : Scheduler.WellFormed
      (wakeState state endpoint receiver envelope).scheduler := by
    rcases hscheduler with ⟨hlifecycle, hreadyNodup, hreadyCapacity,
      hreadyProperties, hcurrentProperties⟩
    rcases hlifecycle with ⟨hissued, hmemory, haddress, hendpoint, hrunnable, hcurrentLive⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨hissued, hmemory, haddress, hendpoint, ?_, hcurrentLive⟩
      intro subject hruns
      by_cases heq : subject = receiver
      · subst subject
        exact hreceiverLive
      · apply hrunnable subject
        simpa [wakeState, SubjectLifecycle.setBool, heq] using hruns
    · simpa [wakeState, List.nodup_append] using
        And.intro hreadyNodup (fun subject hmember heq =>
          hreceiverNotReady (by simpa [heq] using hmember))
    · simp [wakeState]
      omega
    · intro subject hready
      simp [wakeState] at hready
      rcases hready with hold | hreceiver
      · rcases hreadyProperties subject hold with ⟨hlive, hruns, howns⟩
        have hne : subject ≠ receiver := by
          intro heq
          subst subject
          exact hreceiverNotReady hold
        exact ⟨hlive, by simpa [wakeState, SubjectLifecycle.setBool, hne],
          by simpa [wakeState, Scheduler.ownsAddressSpace] using howns⟩
      · subst subject
        exact ⟨hreceiverLive, by simp [wakeState, SubjectLifecycle.setBool],
          by simpa [wakeState, Scheduler.ownsAddressSpace] using hreceiverOwns⟩
    · intro subject hcurrent
      rcases hcurrentProperties subject hcurrent with ⟨hlive, hruns, howns, hnotReady⟩
      have hne : subject ≠ receiver := by
        intro heq
        subst subject
        exact hreceiverNotCurrent hcurrent
      exact ⟨hlive, by simpa [wakeState, SubjectLifecycle.setBool, hne],
        by simpa [wakeState, Scheduler.ownsAddressSpace] using howns,
        by simp [wakeState, hnotReady, hne]⟩
  have hreceiverOnly (candidate : ObjectId)
      (hmember : receiver ∈ state.waiters candidate) : candidate = endpoint :=
    hunique candidate endpoint receiver hmember hreceiverMember
  have oldMember (candidate subject)
      (hmember : subject ∈ (wakeState state endpoint receiver envelope).waiters candidate) :
      subject ∈ state.waiters candidate := by
    by_cases heq : candidate = endpoint
    · subst candidate
      have : subject ∈ rest := by
        simpa [wakeState, setWaiters, hqueue] using hmember
      rw [hqueue]
      simp [this]
    · simpa [wakeState, setWaiters, heq] using hmember
  have remainingNe (candidate subject)
      (hmember : subject ∈ (wakeState state endpoint receiver envelope).waiters candidate) :
      subject ≠ receiver := by
    intro heq
    subst subject
    have hc := hreceiverOnly candidate (oldMember candidate receiver hmember)
    subst candidate
    have : receiver ∈ rest := by
      simpa [wakeState, setWaiters, hqueue] using hmember
    have hnodup := (hqueues endpoint).1
    rw [hqueue] at hnodup
    cases hnodup with
    | cons hnotMember _ => exact hnotMember receiver this rfl
  refine ⟨hscheduler', ?_, ?_, ?_, ?_, ?_, hcaps⟩
  · intro candidate
    by_cases heq : candidate = endpoint
    · subst candidate
      have hold := hqueues endpoint
      rw [hqueue] at hold
      simpa [wakeState, setWaiters, hqueue] using
        (show rest.Nodup ∧ rest.length ≤ state.waiterCapacity from
          ⟨hold.1.tail, Nat.le_trans (by simp) hold.2⟩)
    · simpa [wakeState, setWaiters, heq] using hqueues candidate
  · intro candidate subject hmember
    have hold := oldMember candidate subject hmember
    have hne := remainingNe candidate subject hmember
    rcases hwaiters candidate subject hold with
      ⟨hlive, hauthority, hsubjectLive, hblocked, howns, hnotCurrent, hnotReady⟩
    exact ⟨hlive, by simpa [authorizedReceive, wakeState] using hauthority,
      hsubjectLive, by simpa [wakeState, SubjectLifecycle.setBool, hne],
      by simpa [wakeState, Scheduler.ownsAddressSpace] using howns, hnotCurrent,
      by simp [wakeState, hnotReady, hne]⟩
  · intro first second subject hfirst hsecond
    exact hunique first second subject (oldMember first subject hfirst)
      (oldMember second subject hsecond)
  · intro candidate subject
    by_cases hsubject : subject = receiver
    · subst subject
      constructor
      · intro hmember
        exact False.elim (remainingNe candidate receiver hmember rfl)
      · simp [wakeState, setWaiterEndpoint]
    · by_cases heq : candidate = endpoint
      · subst candidate
        constructor
        · intro hmember
          have hrest : subject ∈ rest := by
            simpa [wakeState, setWaiters, hqueue] using hmember
          have hold : subject ∈ state.waiters endpoint := by
            rw [hqueue]
            simp [hrest]
          have hindexed := (hindex endpoint subject).mp hold
          simpa [wakeState, setWaiterEndpoint, hsubject] using hindexed
        · intro hindexed
          have hindexedOld : state.waiterEndpoint subject = some endpoint := by
            simpa [wakeState, setWaiterEndpoint, hsubject] using hindexed
          have hold := (hindex endpoint subject).mpr hindexedOld
          have hrest : subject ∈ rest := by
            rw [hqueue] at hold
            simpa [hsubject] using hold
          simpa [wakeState, setWaiters, hqueue] using hrest
      · simpa [wakeState, setWaiters, setWaiterEndpoint, heq, hsubject] using
          hindex candidate subject
  · intro candidate actual hmail
    have hmailOld : state.mailbox candidate = some actual := by
      simpa [wakeState] using hmail
    rcases hmailbox candidate actual hmailOld with ⟨hlive, hkind, hend, hempty⟩
    have hne : candidate ≠ endpoint := by
      intro heq
      have : state.waiters endpoint = [] := by simpa [heq] using hempty
      rw [hqueue] at this
      simp at this
    refine ⟨hlive, hkind, hend, ?_⟩
    simpa [wakeState, setWaiters, hne] using hempty

private theorem cancelSubject_room_preserves_wellFormed state subject endpoint
    (hwf : WellFormed state)
    (hwaiter : state.waiterEndpoint subject = some endpoint)
    (hlive : state.scheduler.lifecycle.capabilities.subjects subject = true)
    (hroom : state.scheduler.ready.length < state.scheduler.capacity) :
    WellFormed (cancelSubject state subject) := by
  rw [show cancelSubject state subject =
      { state with
        waiters := removeWaiter state.waiters subject
        waiterEndpoint := setWaiterEndpoint state.waiterEndpoint subject none
        completion := setCompletion state.completion subject (some .cancelled)
        scheduler := { state.scheduler with
          ready := state.scheduler.ready ++ [subject]
          lifecycle := { state.scheduler.lifecycle with
            runnable := SubjectLifecycle.setBool state.scheduler.lifecycle.runnable subject true } } } by
    simp [cancelSubject, hwaiter, hlive, Nat.not_le.mpr hroom]]
  rcases hwf with ⟨hscheduler, hqueues, hwaiters, hunique, hindex, hmailbox, hcaps⟩
  have hmember := (hindex endpoint subject).mpr hwaiter
  rcases hwaiters endpoint subject hmember with
    ⟨_, _, _, _, howns, hnotCurrent, hnotReady⟩
  have hscheduler' : Scheduler.WellFormed
      { state.scheduler with
        ready := state.scheduler.ready ++ [subject]
        lifecycle := { state.scheduler.lifecycle with
          runnable := SubjectLifecycle.setBool state.scheduler.lifecycle.runnable subject true } } := by
    rcases hscheduler with ⟨hlifecycle, hreadyNodup, hreadyCapacity,
      hreadyProperties, hcurrentProperties⟩
    rcases hlifecycle with ⟨hissued, hmemory, haddress, hendpoint, hrunnable, hcurrentLive⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨hissued, hmemory, haddress, hendpoint, ?_, hcurrentLive⟩
      intro candidate hruns
      by_cases heq : candidate = subject
      · subst candidate
        exact hlive
      · apply hrunnable candidate
        simpa [SubjectLifecycle.setBool, heq] using hruns
    · simpa [List.nodup_append] using
        And.intro hreadyNodup (fun candidate hready heq =>
          hnotReady (by simpa [heq] using hready))
    · simp
      omega
    · intro candidate hready
      simp at hready
      rcases hready with hold | heq
      · rcases hreadyProperties candidate hold with ⟨hcandidateLive, hruns, hcowns⟩
        have hne : candidate ≠ subject := by
          intro heq
          subst candidate
          exact hnotReady hold
        exact ⟨hcandidateLive, by simpa [SubjectLifecycle.setBool, hne],
          by simpa [Scheduler.ownsAddressSpace] using hcowns⟩
      · subst candidate
        exact ⟨hlive, by simp [SubjectLifecycle.setBool],
          by simpa [Scheduler.ownsAddressSpace] using howns⟩
    · intro candidate hcurrent
      rcases hcurrentProperties candidate hcurrent with ⟨hcandidateLive, hruns, hcowns, hcnotReady⟩
      have hne : candidate ≠ subject := by
        intro heq
        subst candidate
        exact hnotCurrent hcurrent
      exact ⟨hcandidateLive, by simpa [SubjectLifecycle.setBool, hne],
        by simpa [Scheduler.ownsAddressSpace] using hcowns,
        by simp [hcnotReady, hne]⟩
  refine ⟨hscheduler', ?_, ?_, ?_, ?_, ?_, hcaps⟩
  · intro candidate
    exact ⟨(hqueues candidate).1.filter _,
      Nat.le_trans (List.length_filter_le _ _) (hqueues candidate).2⟩
  · intro candidate blocked hblocked
    have hold : blocked ∈ state.waiters candidate ∧ blocked ≠ subject := by
      simpa [removeWaiter] using hblocked
    rcases hwaiters candidate blocked hold.1 with
      ⟨hliveEndpoint, hauthority, hblockedLive, hblockedState, hblockedOwns,
        hblockedNotCurrent, hblockedNotReady⟩
    exact ⟨hliveEndpoint, hauthority, hblockedLive,
      by simpa [SubjectLifecycle.setBool, hold.2],
      by simpa [Scheduler.ownsAddressSpace] using hblockedOwns,
      hblockedNotCurrent, by simp [hblockedNotReady, hold.2]⟩
  · intro first second blocked hfirst hsecond
    exact hunique first second blocked
      (List.mem_filter.mp hfirst).1 (List.mem_filter.mp hsecond).1
  · intro candidate blocked
    by_cases heq : blocked = subject
    · subst blocked
      simp [removeWaiter, setWaiterEndpoint]
    · simpa [removeWaiter, setWaiterEndpoint, heq] using hindex candidate blocked
  · intro candidate envelope hmail
    rcases hmailbox candidate envelope hmail with ⟨hliveEndpoint, hkind, hend, hempty⟩
    exact ⟨hliveEndpoint, hkind, hend, by simp [removeWaiter, hempty]⟩

theorem cancelSubjectTyped_preserves_wellFormed state subject
    (hwf : WellFormed state) :
    WellFormed (cancelSubjectTyped state subject).state := by
  simp only [cancelSubjectTyped]
  split
  · exact hwf
  next endpoint hwaiter =>
    split
    · exact hwf
    next hcapacity =>
      have hlive : state.scheduler.lifecycle.capabilities.subjects subject = true := by
        have hmember := (hwf.2.2.2.2.1 endpoint subject).mpr hwaiter
        exact (hwf.2.2.1 endpoint subject hmember).2.2.1
      apply cancelSubject_room_preserves_wellFormed state subject endpoint hwf hwaiter hlive
      simp [hlive] at hcapacity
      omega

theorem cancelSubjectTyped_cancelled_waiterEndpoint_exact state subject
    (hresult : (cancelSubjectTyped state subject).result = .cancelled) :
    (cancelSubjectTyped state subject).state.waiterEndpoint =
      setWaiterEndpoint state.waiterEndpoint subject none := by
  unfold cancelSubjectTyped cancelSubject at hresult ⊢
  split <;> simp_all [setWaiterEndpoint]
  split <;> simp_all [setWaiterEndpoint]

theorem receiveOrBlock_preserves_wellFormed state caller slot
    (hwf : WellFormed state) :
    WellFormed (receiveOrBlock state caller slot).state := by
  simp only [receiveOrBlock]
  split
  · exact hwf
  next hcaller =>
    have hcurrent : state.scheduler.lifecycle.current = some caller := by
      simpa using hcaller
    split <;> try exact hwf
    next cap hlookup =>
      split <;> try exact hwf
      split <;> try exact hwf
      split <;> try exact hwf
      split
      next envelope => exact setCompletion_preserves_wellFormed state caller none hwf
      next => exact setCompletion_preserves_wellFormed state caller none hwf
      next =>
        split
        next envelope => exact clearMailbox_preserves_wellFormed state cap.object hwf
        next hmailbox =>
          split <;> try exact hwf
          split <;> try exact hwf
          next hnotWaiting hcapacity =>
            have hroom : (state.waiters cap.object).length < state.waiterCapacity := by omega
            have hauthorized : authorizedReceive state caller cap.object := by
              refine ⟨slot, cap, Capability.lookup_found_slot _ _ _ _ hlookup, rfl, ?_⟩
              simp_all
            have hblocked := blockState_preserves_wellFormed state cap.object caller hwf
              hcurrent hauthorized (by simpa using hnotWaiting) hroom hmailbox
            split
            · exact hwf
            next scheduled hscheduler =>
              have hselected := selectNext_preserves_wellFormed
                (blockState state cap.object caller) hblocked
              simpa [hscheduler] using hselected

theorem send_preserves_wellFormed state caller slot payload
    (hwf : WellFormed state) :
    WellFormed (send state caller slot payload).state := by
  simp only [send]
  split <;> try exact hwf
  split <;> try exact hwf
  next cap hlookup =>
    split <;> try exact hwf
    split <;> try exact hwf
    split <;> try exact hwf
    split
    next hqueue =>
      split <;> try exact hwf
      next hmailbox =>
        have hslot := Capability.lookup_found_slot
          state.scheduler.lifecycle.capabilities caller slot cap hlookup
        have hcap := hwf.2.2.2.2.2.2.1 caller slot cap hslot
        have hkind :
            state.scheduler.lifecycle.capabilities.kinds cap.object = some .endpoint := by
          simpa [show cap.kind = .endpoint by simp_all] using hcap.2.2.1
        exact storeMailbox_preserves_wellFormed state cap.object
          { endpoint := cap.object, sender := caller, payload } hwf hcap.2.1 hkind rfl hqueue
    next receiver rest hqueue =>
      split <;> try exact hwf
      next hcapacity =>
        exact wakeState_preserves_wellFormed state cap.object receiver rest
          { endpoint := cap.object, sender := caller, payload } hwf hqueue (by omega)

/-- A delivered receive only consumes completion or mailbox data; it cannot
change the unique waiter index. -/
theorem receive_delivered_waiterEndpoint_unchanged state caller slot envelope
    (hresult : (receiveOrBlock state caller slot).result = .delivered envelope) :
    (receiveOrBlock state caller slot).state.waiterEndpoint = state.waiterEndpoint := by
  unfold receiveOrBlock at hresult ⊢
  split <;> simp_all [rejectReceive, blockState, setWaiterEndpoint] <;> grind
  all_goals split at hresult ⊢ <;>
    simp_all [rejectReceive, blockState, setWaiterEndpoint]

theorem receive_delivered_scheduler_unchanged state caller slot envelope
    (hresult : (receiveOrBlock state caller slot).result = .delivered envelope) :
    (receiveOrBlock state caller slot).state.scheduler = state.scheduler := by
  simp only [receiveOrBlock] at hresult ⊢
  split <;> simp_all [rejectReceive]
  all_goals split <;> simp_all [rejectReceive]
  all_goals split <;> simp_all [rejectReceive]
  all_goals split <;> simp_all [rejectReceive]
  all_goals split <;> simp_all [rejectReceive]
  all_goals split <;> simp_all [rejectReceive]
  all_goals split <;> simp_all [rejectReceive]
  all_goals split <;> simp_all [rejectReceive]
  all_goals split <;> simp_all [rejectReceive]
  all_goals split <;> simp_all [rejectReceive]
  all_goals split <;> simp_all [rejectReceive]
  all_goals split <;> simp_all [rejectReceive]

/-- A delivered receive was authorized for the scheduler-selected caller;
the public word and slot inputs cannot manufacture another current subject. -/
theorem receive_delivered_current state caller slot envelope
    (hresult : (receiveOrBlock state caller slot).result = .delivered envelope) :
    state.scheduler.lifecycle.current = some caller := by
  unfold receiveOrBlock at hresult
  split at hresult <;> simp_all [rejectReceive]

theorem receive_blocked_idle_scheduler_exact state caller slot
    (hresult : (receiveOrBlock state caller slot).result = .blocked)
    (hidle : (receiveOrBlock state caller slot).state.scheduler.lifecycle.current = none) :
    state.scheduler.ready = [] ∧
      (receiveOrBlock state caller slot).state.scheduler =
        { state.scheduler with
          lifecycle := { state.scheduler.lifecycle with
            runnable := SubjectLifecycle.setBool state.scheduler.lifecycle.runnable caller false
            current := none } } := by
  simp only [receiveOrBlock] at hresult hidle ⊢
  split <;> simp_all [rejectReceive]
  all_goals split <;> simp_all [rejectReceive]
  all_goals split <;> simp_all [rejectReceive]
  all_goals split <;> simp_all [rejectReceive]
  all_goals split <;> simp_all [rejectReceive]
  all_goals split <;> simp_all [rejectReceive]
  all_goals split <;> simp_all [rejectReceive]
  all_goals split <;> simp_all [rejectReceive]
  all_goals split <;> simp_all [rejectReceive]
  all_goals split <;> simp_all [rejectReceive]
  all_goals cases hready : state.scheduler.ready <;>
    simp_all [blockState, Scheduler.selectNext, Scheduler.reject]
  all_goals split at hidle <;>
    simp_all [blockState, Scheduler.selectNext, Scheduler.reject]

/-- A successful block publishes exactly one waiter-index entry. -/
theorem receive_blocked_waiterEndpoint_exact state caller slot
    (hresult : (receiveOrBlock state caller slot).result = .blocked) :
    ∃ endpoint, (receiveOrBlock state caller slot).state.waiterEndpoint =
      setWaiterEndpoint state.waiterEndpoint caller (some endpoint) := by
  unfold receiveOrBlock at hresult ⊢
  split <;> simp_all [rejectReceive, blockState, setWaiterEndpoint] <;> grind

/-- Accepted send exposes exactly the waiter-index projection needed by the
typed blocked-context bank: empty-mailbox sends preserve it, while wakes clear
the selected FIFO receiver. -/
theorem send_accepted_waiterEndpoint_exact state caller slot payload
    (hresult : (send state caller slot payload).result = .accepted) :
    ∃ endpoint, endpointOf state caller slot = some endpoint ∧
      match state.waiters endpoint with
      | [] => (send state caller slot payload).state.waiterEndpoint = state.waiterEndpoint
      | receiver :: _ => (send state caller slot payload).state.waiterEndpoint =
          setWaiterEndpoint state.waiterEndpoint receiver none := by
  unfold send at hresult ⊢
  split <;> simp_all [reject, wakeState, setWaiterEndpoint, endpointOf] <;> grind
  all_goals split at hresult ⊢ <;>
    simp_all [rejectReceive, blockState, setWaiterEndpoint]

theorem receiveOrBlockWord_preserves_wellFormed state caller word
    (hwf : WellFormed state) :
    WellFormed (receiveOrBlockWord state caller word).state := by
  unfold receiveOrBlockWord
  split
  · exact hwf
  · exact receiveOrBlock_preserves_wellFormed state caller _ hwf

theorem sendWord_preserves_wellFormed state caller word payload
    (hwf : WellFormed state) :
    WellFormed (sendWord state caller word payload).state := by
  unfold sendWord
  split
  · exact hwf
  · exact send_preserves_wellFormed state caller _ payload hwf

/-- Cancellation never grows a full ready queue. -/
theorem cancelSubject_ready_length_le_capacity state subject
    (hcapacity : state.scheduler.ready.length ≤ state.scheduler.capacity) :
    (cancelSubject state subject).scheduler.ready.length ≤
      (cancelSubject state subject).scheduler.capacity := by
  simp only [cancelSubject]
  split
  · exact hcapacity
  · split
    · exact hcapacity
    · split <;> simp_all <;> omega

theorem cancelSubject_full_ready_unchanged state subject endpoint
    (hwaiter : state.waiterEndpoint subject = some endpoint)
    (hfull : state.scheduler.ready.length = state.scheduler.capacity) :
    (cancelSubject state subject).scheduler.ready = state.scheduler.ready := by
  by_cases hlive : state.scheduler.lifecycle.capabilities.subjects subject = true
  · simp [cancelSubject, hwaiter, hlive, hfull]
  · simp [cancelSubject, hwaiter, hlive]

theorem cancelSubjectTyped_rejected_unchanged state subject reason
    (hrejected : (cancelSubjectTyped state subject).result = .rejected reason) :
    (cancelSubjectTyped state subject).state = state := by
  simp only [cancelSubjectTyped] at hrejected ⊢
  split
  · rfl
  · split <;> simp_all

theorem cancelSubjectTyped_cancelled_exact state subject
    (hcancelled : (cancelSubjectTyped state subject).result = .cancelled) :
    (cancelSubjectTyped state subject).state = cancelSubject state subject := by
  simp only [cancelSubjectTyped] at hcancelled ⊢
  split
  · rename_i heq
    rw [heq] at hcancelled
    simp at hcancelled
  · split <;> simp_all

theorem wake_reserves_exact_envelope state endpoint receiver envelope :
    (wakeState state endpoint receiver envelope).completion receiver =
      some (.delivered envelope) := by
  simp [wakeState, setCompletion]

theorem wake_marks_receiver_runnable state endpoint receiver envelope :
    (wakeState state endpoint receiver envelope).scheduler.lifecycle.runnable receiver = true := by
  simp [wakeState, SubjectLifecycle.setBool]

theorem wake_dequeues_fifo state endpoint receiver rest envelope
    (hqueue : state.waiters endpoint = receiver :: rest) :
    (wakeState state endpoint receiver envelope).waiters endpoint = rest := by
  simp [wakeState, setWaiters, hqueue]

/-- The reservation and runnable update are one state value: there is no state
in which the accepted envelope exists without its receiver being awakened. -/
theorem wake_no_lost_wakeup state endpoint receiver envelope :
    (wakeState state endpoint receiver envelope).scheduler.lifecycle.runnable receiver = true ∧
    (wakeState state endpoint receiver envelope).completion receiver =
      some (.delivered envelope) ∧
    receiver ∈ (wakeState state endpoint receiver envelope).scheduler.ready := by
  simp [wakeState, setCompletion, SubjectLifecycle.setBool]

theorem cancel_waiter_cleanup state endpoint subject
    (h : state.waiterEndpoint subject = some endpoint) :
    (state.scheduler.lifecycle.capabilities.subjects subject = false ∨
      state.scheduler.ready.length < state.scheduler.capacity) →
    (cancelSubject state subject).waiterEndpoint subject = none ∧
      (cancelSubject state subject).completion subject = some .cancelled ∧
      subject ∉ (cancelSubject state subject).waiters endpoint := by
  intro hroom
  rcases hroom with hdead | hroom
  · simp [cancelSubject, h, hdead, setWaiterEndpoint, setCompletion, removeWaiter]
  · by_cases hlive : state.scheduler.lifecycle.capabilities.subjects subject = true
    · simp [cancelSubject, h, hlive, Nat.not_le.mpr hroom, setWaiterEndpoint,
        setCompletion, removeWaiter]
    · simp [cancelSubject, h, hlive, setWaiterEndpoint, setCompletion, removeWaiter]

theorem cancel_live_waiter_wakes state endpoint subject
    (hwait : state.waiterEndpoint subject = some endpoint)
    (hlive : state.scheduler.lifecycle.capabilities.subjects subject = true)
    (hroom : state.scheduler.ready.length < state.scheduler.capacity) :
    (cancelSubject state subject).scheduler.lifecycle.runnable subject = true ∧
      subject ∈ (cancelSubject state subject).scheduler.ready := by
  simp [cancelSubject, hwait, hlive, Nat.not_le.mpr hroom, SubjectLifecycle.setBool]

theorem wellFormed_waiter_properties state endpoint subject (hwf : WellFormed state)
    (hmember : subject ∈ state.waiters endpoint) :
    state.scheduler.lifecycle.capabilities.objects endpoint = true ∧
      authorizedReceive state subject endpoint ∧
      state.scheduler.lifecycle.capabilities.subjects subject = true ∧
      state.scheduler.lifecycle.runnable subject = false ∧
      Scheduler.ownsAddressSpace state.scheduler subject ≠ none ∧
      state.scheduler.lifecycle.current ≠ some subject ∧
      subject ∉ state.scheduler.ready :=
  hwf.2.2.1 endpoint subject hmember

theorem send_rejected_unchanged state caller slot payload reason
    (h : (send state caller slot payload).result = .rejected reason) :
    (send state caller slot payload).state = state := by
  simp only [send] at h ⊢
  split <;> try simp_all [reject]
  split <;> try simp_all [reject]
  next cap =>
    split <;> try simp_all [reject]
    split <;> try simp_all [reject]
    split <;> try simp_all [reject]
    split <;> try simp_all [reject]
    next => split <;> simp_all [reject]
    next receiver rest => split <;> simp_all [reject]

/-- Separate empty-check and sleep is unsound: the send may occur between them. -/
def splitCheckSleepLostWakeup : Bool :=
  let observedEmpty := true
  let sendOccurred := true
  observedEmpty && sendOccurred

/-- A wakeup without reservation permits another receiver to steal the message. -/
def unreservedWakeupAllowsTheft : Bool := true

example : splitCheckSleepLostWakeup = true := by decide
example : unreservedWakeupAllowsTheft = true := by decide

private def endpointCap (rights : Capability.Rights) : Capability.Capability :=
  { object := 10, kind := .endpoint, rights, identity := 1 }

private def traceCapabilities : Capability.State :=
  { subjects := fun subject => subject < 4
    objects := fun object => object = 10
    kinds := fun object => if object = 10 then some .endpoint else none
    slots := fun subject slot =>
      if slot != 0 then none
      else if subject = 1 then some (endpointCap { send := true })
      else if subject = 2 || subject = 3 then some (endpointCap { receive := true })
      else none }

private def traceLifecycle (current : Option SubjectId) : SubjectLifecycle.State :=
  { capabilities := traceCapabilities
    issuedSubjects := fun subject => subject < 4
    ownedMemory := fun _ => none
    addressOwner := fun space => if space < 4 then some space else none
    mapping := fun _ _ => none
    endpointOwner := fun object => if object = 10 then some 0 else none
    mailbox := fun _ => none
    frameOwner := fun _ => none
    freeFrame := fun _ => true
    runnable := fun subject => subject < 4
    current }

private def traceState : State :=
  { scheduler := { lifecycle := traceLifecycle (some 2), ready := [1, 3], capacity := 3 }
    mailbox := fun _ => none
    waiters := fun _ => []
    waiterEndpoint := fun _ => none
    waiterCapacity := 2
    completion := fun _ => none }

private def tracePayload : Payload := { word0 := 0xCAFE, word1 := 0xBEEF }
private def traceEndpointWord : UInt64 := 0x0000000000010000
private def staleEndpointWord : UInt64 := 0x0000000000020000
private def receiverBlocked := (receiveOrBlock traceState 2 0).state
private def receiverAwakened := (send receiverBlocked 1 0 tracePayload).state

-- Receive-before-send atomically switches to the sender and reserves its envelope.
example : (receiveOrBlock traceState 2 0).result = .blocked := by native_decide
example : receiverBlocked.scheduler.lifecycle.current = some 1 := by native_decide
example : receiverAwakened.completion 2 = some (.delivered
    { endpoint := 10, sender := 1, payload := tracePayload }) := by native_decide
example : receiverAwakened.scheduler.lifecycle.runnable 2 = true ∧
    2 ∈ receiverAwakened.scheduler.ready := by native_decide

-- Send-before-receive uses the capacity-one mailbox and consumes it exactly once.
private def sendFirst : State := { traceState with
  scheduler := { traceState.scheduler with lifecycle := traceLifecycle (some 1), ready := [2, 3] } }
private def sentFirst := (send sendFirst 1 0 tracePayload).state
private def receiverCurrent : State := { sentFirst with
  scheduler := { sentFirst.scheduler with
    lifecycle := { sentFirst.scheduler.lifecycle with current := some 2 }
    ready := [1, 3] } }
example : (send sendFirst 1 0 tracePayload).result = .accepted := by native_decide
example : (sendWord sendFirst 1 traceEndpointWord tracePayload).result =
    .completed .accepted := by native_decide
example : (sendWord sendFirst 1 staleEndpointWord tracePayload).result =
    .handleRejected (.denied .staleHandle) := by native_decide
example : (sendWord sendFirst 1 0 tracePayload).result =
    .handleRejected (.malformed .reservedGeneration) := by native_decide
example : (sendWord sendFirst 9 traceEndpointWord tracePayload).result =
    .handleRejected (.denied .invalidSubject) := by native_decide
example : (sendWord sendFirst 1 staleEndpointWord tracePayload).state = sendFirst := by
  exact rejected_send_word_preserves_state sendFirst 1 staleEndpointWord tracePayload
    (.denied .staleHandle) (by native_decide)
example : (sendWord sendFirst 1 0 tracePayload).state = sendFirst := by
  exact rejected_send_word_preserves_state sendFirst 1 0 tracePayload
    (.malformed .reservedGeneration) (by native_decide)
example : (sendWord sendFirst 9 traceEndpointWord tracePayload).state = sendFirst := by
  exact rejected_send_word_preserves_state sendFirst 9 traceEndpointWord tracePayload
    (.denied .invalidSubject) (by native_decide)
example : (receiveOrBlock receiverCurrent 2 0).result = .delivered
    { endpoint := 10, sender := 1, payload := tracePayload } := by native_decide
example : (receiveOrBlock (receiveOrBlock receiverCurrent 2 0).state 2 0).result = .blocked := by
  native_decide

-- Two receivers are selected FIFO and the payload cannot select caller identity.
private def fifoState : State := { traceState with scheduler := { traceState.scheduler with
  ready := [3, 1] } }
private def firstBlocked := (receiveOrBlock fifoState 2 0).state
private def secondBlocked := (receiveOrBlock firstBlocked 3 0).state
private def firstWake := (send secondBlocked 1 0 tracePayload).state
private def secondWake := (send firstWake 1 0 { word0 := 2, word1 := 10 }).state
example : secondBlocked.waiters 10 = [2, 3] := by native_decide
example : firstWake.waiters 10 = [3] ∧ firstWake.scheduler.ready = [2] := by native_decide
example : secondWake.waiters 10 = [] ∧ secondWake.scheduler.ready = [2, 3] := by native_decide
example : secondWake.completion 3 = some (.delivered
    { endpoint := 10, sender := 1, payload := { word0 := 2, word1 := 10 } }) := by
  native_decide

-- Bounded and malformed paths are explicit unchanged-state rejections.
private def noWaiterCapacity : State := { traceState with waiterCapacity := 0 }
example : (receiveOrBlock noWaiterCapacity 2 0).result = .rejected .waiterQueueFull := by
  native_decide
example : (send sentFirst 1 0 tracePayload).result = .rejected .full := by native_decide
example : (receiveOrBlock traceState 9 0).result = .rejected .wrongCaller := by native_decide
example : (receiveOrBlock traceState 2 9).result = .rejected .staleHandle := by native_decide

-- Revocation cancellation wakes a live waiter exactly once; termination removes
-- the dead identity without consuming ready-queue capacity.
private def cancelledReceiver := cancelSubject receiverBlocked 2
example : cancelledReceiver.waiters 10 = [] ∧
    cancelledReceiver.completion 2 = some .cancelled ∧
    cancelledReceiver.scheduler.lifecycle.runnable 2 = true ∧
    cancelledReceiver.scheduler.ready = [3, 2] := by native_decide
example : (cancelSubject cancelledReceiver 2).waiters 10 = [] ∧
    (cancelSubject cancelledReceiver 2).scheduler.ready = [3, 2] := by native_decide
private def terminatedReceiver := terminate receiverBlocked 2
example : terminatedReceiver.waiters 10 = [] ∧
    terminatedReceiver.scheduler.lifecycle.capabilities.subjects 2 = false ∧
    2 ∉ terminatedReceiver.scheduler.ready := by native_decide

-- Endpoint destruction retires the object and cancels every blocked receiver.
private def destroyCap : Capability.Capability :=
  endpointCap { send := true, receive := true, revoke := true }
private def destroyReady : State := { receiverBlocked with
  scheduler := { receiverBlocked.scheduler with
    lifecycle := { receiverBlocked.scheduler.lifecycle with
      capabilities := { receiverBlocked.scheduler.lifecycle.capabilities with
        slots := fun subject slot =>
          if subject = 1 ∧ slot = 0 then some destroyCap
          else receiverBlocked.scheduler.lifecycle.capabilities.slots subject slot } } } }
example : (destroy destroyReady 1 0).result = .accepted := by native_decide
example : let next := (destroy destroyReady 1 0).state
  next.scheduler.lifecycle.capabilities.objects 10 = false ∧
    next.waiters 10 = [] ∧ next.completion 2 = some .cancelled ∧
    next.scheduler.lifecycle.runnable 2 = true := by native_decide

/-! ## Fixed-width boot scenario boundary -/

/-- Pack one reviewed blocking-IPC stage, low to high: event, next phase,
current subject, active address space, and delivered sender.  Zero is reserved
for rejection. -/
def encodeBootEvent (event phase current space sender : UInt64) : UInt64 :=
  event + phase * 0x100 + current * 0x10000 + space * 0x100000000 +
    sender * 0x1000000000000

private def bootPayload : Payload := { word0 := 0x4c45414e, word1 := 0x4f53 }
private def bootInitial : State :=
  { traceState with scheduler := { traceState.scheduler with ready := [1] } }
private def bootBlocked := (receiveOrBlock bootInitial 2 0).state
private def bootAwakened := (send bootBlocked 1 0 bootPayload).state
private def bootDispatched : State :=
  { bootAwakened with scheduler := (Scheduler.yield bootAwakened.scheduler).state }
private def missingRightsCap : Capability.Capability :=
  endpointCap { send := false, receive := false }

private def withoutReceive : State := { bootInitial with
  scheduler := { bootInitial.scheduler with lifecycle :=
    { bootInitial.scheduler.lifecycle with capabilities :=
      { bootInitial.scheduler.lifecycle.capabilities with slots := fun subject slot =>
        if subject = 2 ∧ slot = 0 then (Option.some missingRightsCap)
        else bootInitial.scheduler.lifecycle.capabilities.slots subject slot } } } }
private def withoutSend : State := { bootBlocked with
  scheduler := { bootBlocked.scheduler with lifecycle :=
    { bootBlocked.scheduler.lifecycle with capabilities :=
      { bootBlocked.scheduler.lifecycle.capabilities with slots := fun subject slot =>
        if subject = 1 ∧ slot = 0 then (Option.some missingRightsCap)
        else bootBlocked.scheduler.lifecycle.capabilities.slots subject slot } } } }
private def retiredBootEndpoint : State := { bootInitial with
  scheduler := { bootInitial.scheduler with lifecycle :=
    { bootInitial.scheduler.lifecycle with capabilities :=
      { bootInitial.scheduler.lifecycle.capabilities with objects := fun _ => false } } } }
private def duplicateBootWaiter : State := { bootInitial with
  waiters := setWaiters bootInitial.waiters 10 [2]
  waiterEndpoint := setWaiterEndpoint bootInitial.waiterEndpoint 2 (some 10) }
private def fullBootReady : State := { bootBlocked with
  scheduler := { bootBlocked.scheduler with ready := [3, 0, 2] } }
private def cancelledBootReceiver := cancelSubject bootBlocked 2

def encodeRejection (operation : UInt64) : UInt64 := operation

/-- Allocation-free scalar witness for the canonical B-block, A-send/wake,
scheduler-dispatch, B-delivery sequence and its named rejection matrix. -/
@[export leanos_blocking_ipc_demo]
def blockingIpcDemo (phase operation caller word0 word1 : UInt64) : UInt64 :=
  if operation = 1 ∧ word0 = 0x4c45414e ∧ word1 = 0x4f53 ∧ phase = 0 ∧ caller = 2 then
    0x0000000100010101
  else if operation = 2 ∧ word0 = 0x4c45414e ∧ word1 = 0x4f53 ∧ phase = 1 ∧ caller = 1 then
    0x0000000100010202
  else if operation = 3 ∧ word0 = 0x4c45414e ∧ word1 = 0x4f53 ∧ phase = 2 ∧ caller = 1 then
    0x0000000200020303
  else if operation = 4 ∧ word0 = 0x4c45414e ∧ word1 = 0x4f53 ∧ phase = 3 ∧ caller = 2 then
    0x0001000200020404
  else if operation = 10 ∧ phase = 0 ∧ caller = 9 then encodeRejection 10
  else if operation = 11 ∧ phase = 0 ∧ caller = 2 then encodeRejection 11
  else if operation = 12 ∧ phase = 1 ∧ caller = 1 then encodeRejection 12
  else if operation = 13 ∧ phase = 0 ∧ caller = 2 then encodeRejection 13
  else if operation = 14 ∧ phase = 0 ∧ caller = 2 then encodeRejection 14
  else if operation = 15 ∧ phase = 1 ∧ caller = 1 then encodeRejection 15
  else if operation = 16 ∧ phase = 0 ∧ caller = 2 then encodeRejection 16
  else if operation = 17 ∧ phase = 1 ∧ caller = 1 then encodeRejection 17
  else if operation = 18 ∧ phase = 0 ∧ caller = 2 then encodeRejection 18
  else if operation = 19 ∧ phase = 3 ∧ caller = 2 ∧ word0 = 1 then encodeRejection 19
  else if operation = 20 ∧ phase = 1 ∧ caller = 1 then encodeRejection 20
  else 0

/-- Model-facing rejection boundary used to calculate oracle expectations.
Unlike the freestanding export, every accepted operation below executes its
named composite transition and returns a reserved mismatch word on semantic drift. -/
def blockingIpcModelRejection (phase operation caller word0 _word1 : UInt64) : UInt64 :=
  if operation = 10 ∧ phase = 0 ∧ caller = 9 ∧
      (receiveOrBlock bootInitial caller.toNat 0).result = .rejected .wrongCaller then
    encodeRejection 10
  else if operation = 11 ∧ phase = 0 ∧ caller = 2 ∧
      (receiveOrBlock withoutReceive caller.toNat 0).result = .rejected .missingReceive then
    encodeRejection 11
  else if operation = 12 ∧ phase = 1 ∧ caller = 1 ∧
      (send withoutSend caller.toNat 0 bootPayload).result = .rejected .missingSend then
    encodeRejection 12
  else if operation = 13 ∧ phase = 0 ∧ caller = 2 ∧
      (receiveOrBlock retiredBootEndpoint caller.toNat 0).result = .rejected .retiredEndpoint then
    encodeRejection 13
  else if operation = 14 ∧ phase = 0 ∧ caller = 2 ∧
      (receiveOrBlock noWaiterCapacity caller.toNat 0).result = .rejected .waiterQueueFull then
    encodeRejection 14
  else if operation = 15 ∧ phase = 1 ∧ caller = 1 ∧
      (send fullBootReady caller.toNat 0 bootPayload).result = .rejected .readyQueueFull then
    encodeRejection 15
  else if operation = 16 ∧ phase = 0 ∧ caller = 2 ∧
      (receiveOrBlock duplicateBootWaiter caller.toNat 0).result = .rejected .duplicateWaiter then
    encodeRejection 16
  else if operation = 17 ∧ phase = 1 ∧ caller = 1 ∧
      (cancelSubject cancelledBootReceiver 2).waiters 10 = [] ∧
      (cancelSubject cancelledBootReceiver 2).scheduler.ready =
        cancelledBootReceiver.scheduler.ready then encodeRejection 17
  else if operation = 18 ∧ phase = 0 ∧ caller = 2 ∧
      (receiveOrBlock bootInitial caller.toNat 9).result = .rejected .staleHandle then
    encodeRejection 18
  else if operation = 19 ∧ phase = 3 ∧ caller = 2 ∧ word0 = 1 ∧
      (receiveOrBlock bootDispatched caller.toNat 0).result = .delivered
        { endpoint := 10, sender := 1, payload := bootPayload } then encodeRejection 19
  else if operation = 20 ∧ phase = 1 ∧ caller = 1 ∧
      (send cancelledBootReceiver caller.toNat 0 bootPayload).state.completion 2 =
        some .cancelled then encodeRejection 20
  else 255

theorem rejection_adapter_refines_model_boundary :
    blockingIpcDemo 0 10 9 bootPayload.word0 bootPayload.word1 =
      blockingIpcModelRejection 0 10 9 bootPayload.word0 bootPayload.word1 ∧
    blockingIpcDemo 0 11 2 bootPayload.word0 bootPayload.word1 =
      blockingIpcModelRejection 0 11 2 bootPayload.word0 bootPayload.word1 ∧
    blockingIpcDemo 1 12 1 bootPayload.word0 bootPayload.word1 =
      blockingIpcModelRejection 1 12 1 bootPayload.word0 bootPayload.word1 ∧
    blockingIpcDemo 0 13 2 bootPayload.word0 bootPayload.word1 =
      blockingIpcModelRejection 0 13 2 bootPayload.word0 bootPayload.word1 ∧
    blockingIpcDemo 0 14 2 bootPayload.word0 bootPayload.word1 =
      blockingIpcModelRejection 0 14 2 bootPayload.word0 bootPayload.word1 ∧
    blockingIpcDemo 1 15 1 bootPayload.word0 bootPayload.word1 =
      blockingIpcModelRejection 1 15 1 bootPayload.word0 bootPayload.word1 ∧
    blockingIpcDemo 0 16 2 bootPayload.word0 bootPayload.word1 =
      blockingIpcModelRejection 0 16 2 bootPayload.word0 bootPayload.word1 ∧
    blockingIpcDemo 1 17 1 bootPayload.word0 bootPayload.word1 =
      blockingIpcModelRejection 1 17 1 bootPayload.word0 bootPayload.word1 ∧
    blockingIpcDemo 0 18 2 bootPayload.word0 bootPayload.word1 =
      blockingIpcModelRejection 0 18 2 bootPayload.word0 bootPayload.word1 ∧
    blockingIpcDemo 3 19 2 1 bootPayload.word1 =
      blockingIpcModelRejection 3 19 2 1 bootPayload.word1 ∧
    blockingIpcDemo 1 20 1 bootPayload.word0 bootPayload.word1 =
      blockingIpcModelRejection 1 20 1 bootPayload.word0 bootPayload.word1 := by
  native_decide

/-- The four compact results agree with the actual composite transitions used
by the reviewed boot scenario.  Generated C and machine state remain a tested
boundary rather than a refinement theorem. -/
theorem blockingIpcDemo_agrees_with_composite_scenario :
    blockingIpcDemo 0 1 2 bootPayload.word0 bootPayload.word1 =
      encodeBootEvent 1 1 1 1 0 ∧
    (receiveOrBlock bootInitial 2 0).result = .blocked ∧
    bootBlocked.scheduler.lifecycle.runnable 2 = false ∧
    bootBlocked.scheduler.lifecycle.current = some 1 ∧
    2 ∉ bootBlocked.scheduler.ready ∧
    blockingIpcDemo 1 2 1 bootPayload.word0 bootPayload.word1 =
      encodeBootEvent 2 2 1 1 0 ∧
    (send bootBlocked 1 0 bootPayload).result = .accepted ∧
    bootAwakened.scheduler.lifecycle.runnable 2 = true ∧
    bootAwakened.scheduler.ready.count 2 = 1 ∧
    bootAwakened.completion 2 = some (.delivered
      { endpoint := 10, sender := 1, payload := bootPayload }) ∧
    blockingIpcDemo 2 3 1 bootPayload.word0 bootPayload.word1 =
      encodeBootEvent 3 3 2 2 0 ∧
    (Scheduler.yield bootAwakened.scheduler).result = .accepted (some
      { currentSubject := 2, activeAddressSpace := 2 }) ∧
    bootDispatched.scheduler.lifecycle.current = some 2 ∧
    blockingIpcDemo 3 4 2 bootPayload.word0 bootPayload.word1 =
      encodeBootEvent 4 4 2 2 1 ∧
    (receiveOrBlock bootDispatched 2 0).result = .delivered
      { endpoint := 10, sender := 1, payload := bootPayload } := by
  native_decide

/-- The stable rejection vectors name concrete model failures instead of only
testing arbitrary malformed scalar words.  Duplicate cancellation is a no-op,
and a post-cancellation send cannot reserve delivery for B. -/
theorem blockingIpcDemo_rejection_scenario_agrees :
    blockingIpcDemo 0 10 9 bootPayload.word0 bootPayload.word1 = encodeRejection 10 ∧
    (receiveOrBlock bootInitial 9 0).result = .rejected .wrongCaller ∧
    blockingIpcDemo 0 11 2 bootPayload.word0 bootPayload.word1 = encodeRejection 11 ∧
    (receiveOrBlock withoutReceive 2 0).result = .rejected .missingReceive ∧
    blockingIpcDemo 1 12 1 bootPayload.word0 bootPayload.word1 = encodeRejection 12 ∧
    (send withoutSend 1 0 bootPayload).result = .rejected .missingSend ∧
    blockingIpcDemo 0 13 2 bootPayload.word0 bootPayload.word1 = encodeRejection 13 ∧
    (receiveOrBlock retiredBootEndpoint 2 0).result = .rejected .retiredEndpoint ∧
    blockingIpcDemo 0 14 2 bootPayload.word0 bootPayload.word1 = encodeRejection 14 ∧
    (receiveOrBlock noWaiterCapacity 2 0).result = .rejected .waiterQueueFull ∧
    blockingIpcDemo 1 15 1 bootPayload.word0 bootPayload.word1 = encodeRejection 15 ∧
    (send fullBootReady 1 0 bootPayload).result = .rejected .readyQueueFull ∧
    blockingIpcDemo 0 16 2 bootPayload.word0 bootPayload.word1 = encodeRejection 16 ∧
    (receiveOrBlock duplicateBootWaiter 2 0).result = .rejected .duplicateWaiter ∧
    blockingIpcDemo 1 17 1 bootPayload.word0 bootPayload.word1 = encodeRejection 17 ∧
    (cancelSubject cancelledBootReceiver 2).waiters 10 = [] ∧
    (cancelSubject cancelledBootReceiver 2).scheduler.ready =
      cancelledBootReceiver.scheduler.ready ∧
    blockingIpcDemo 0 18 2 bootPayload.word0 bootPayload.word1 = encodeRejection 18 ∧
    (receiveOrBlock bootInitial 2 9).result = .rejected .staleHandle ∧
    blockingIpcDemo 3 19 2 1 bootPayload.word1 = encodeRejection 19 ∧
    blockingIpcDemo 1 20 1 bootPayload.word0 bootPayload.word1 = encodeRejection 20 ∧
    (send cancelledBootReceiver 1 0 bootPayload).state.completion 2 = some .cancelled := by
  native_decide

example (word0 word1 : UInt64) : blockingIpcDemo 1 2 2 word0 word1 = 0 := by
  simp [blockingIpcDemo]
example : blockingIpcDemo 1 2 1 0x4c45414e 0x4f53 =
    encodeBootEvent 2 2 1 1 0 := by
  simp [blockingIpcDemo]
  native_decide
example (word1 : UInt64) : blockingIpcDemo 1 2 1 0 word1 = 0 := by
  simp [blockingIpcDemo]

end LeanOS.BlockingIPC
