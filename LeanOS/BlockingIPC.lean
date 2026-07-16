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
    state.scheduler.lifecycle.current ≠ some subject ∧ subject ∉ state.scheduler.ready) ∧
  (∀ e₁ e₂ subject, subject ∈ state.waiters e₁ → subject ∈ state.waiters e₂ → e₁ = e₂)
  ∧ (∀ endpoint subject, subject ∈ state.waiters endpoint ↔
    state.waiterEndpoint subject = some endpoint)
  ∧ (∀ endpoint envelope, state.mailbox endpoint = some envelope →
    state.scheduler.lifecycle.capabilities.objects endpoint = true ∧
    state.scheduler.lifecycle.capabilities.kinds endpoint = some .endpoint ∧
    envelope.endpoint = endpoint ∧ state.waiters endpoint = [])

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

def cancelSubject (state : State) (subject : SubjectId) : State :=
  match state.waiterEndpoint subject with
  | none => state
  | some _ =>
    let live := state.scheduler.lifecycle.capabilities.subjects subject
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

def terminate (state : State) (subject : SubjectId) : State :=
  let lifecycle := SubjectLifecycle.terminate state.scheduler.lifecycle subject
  match lifecycle.result with
  | .rejected _ => state
  | .accepted => cancelSubject { state with scheduler := { state.scheduler with
      lifecycle := lifecycle.state
      ready := state.scheduler.ready.filter (· ≠ subject) } } subject

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
    (cancelSubject state subject).waiterEndpoint subject = none ∧
      (cancelSubject state subject).completion subject = some .cancelled ∧
      subject ∉ (cancelSubject state subject).waiters endpoint := by
  simp [cancelSubject, h, setWaiterEndpoint, setCompletion, removeWaiter]

theorem cancel_live_waiter_wakes state endpoint subject
    (hwait : state.waiterEndpoint subject = some endpoint)
    (hlive : state.scheduler.lifecycle.capabilities.subjects subject = true) :
    (cancelSubject state subject).scheduler.lifecycle.runnable subject = true ∧
      subject ∈ (cancelSubject state subject).scheduler.ready := by
  simp [cancelSubject, hwait, hlive, SubjectLifecycle.setBool]

theorem wellFormed_waiter_properties state endpoint subject (hwf : WellFormed state)
    (hmember : subject ∈ state.waiters endpoint) :
    state.scheduler.lifecycle.capabilities.objects endpoint = true ∧
      authorizedReceive state subject endpoint ∧
      state.scheduler.lifecycle.capabilities.subjects subject = true ∧
      state.scheduler.lifecycle.runnable subject = false ∧
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
  { object := 10, kind := .endpoint, rights }

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

end LeanOS.BlockingIPC
