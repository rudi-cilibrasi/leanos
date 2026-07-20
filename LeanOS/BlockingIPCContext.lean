import LeanOS.BlockingIPC
import LeanOS.ResumableContext

/-!
# Typed blocked-context transfers

This is the context-aware successor to `BlockingIPC.State`.  It keeps the
proved endpoint/scheduler state intact and adds one separate bank containing
the exact `ResumableContext.Context` of each sleeping receiver.  The checked
transitions publish endpoint and bank changes together.
-/
namespace LeanOS.BlockingIPCContext

open LeanOS

abbrev SubjectId := BlockingIPC.SubjectId
abbrev SlotId := BlockingIPC.SlotId

structure State where
  ipc : BlockingIPC.State
  blocked : SubjectId → Option ResumableContext.Context

/-- Saved contexts detached from wait queues by authority-destroying cleanup.
They are not runnable contexts: a separate checked drain must reserve scheduler
capacity before returning one to the caller. -/
structure DeferredCancelState where
  retained : SubjectId → Option ResumableContext.Context

def emptyDeferred : DeferredCancelState :=
  ⟨fun _ => none⟩

def setBlocked (values : SubjectId → Option ResumableContext.Context)
    (subject : SubjectId) (value : Option ResumableContext.Context) :=
  fun candidate => if candidate = subject then value else values candidate

def validSaved (caller : SubjectId) (saved : ResumableContext.Context) : Bool :=
  saved.owner == caller && saved.addressSpace == caller &&
    saved.kind == .suspended && Interrupt.validSavedUserFrame saved.frame

/-- Small projection used by composite restoration proofs without unfolding
the complete saved-context validator. -/
theorem validSaved_owner caller saved
    (hvalid : validSaved caller saved = true) : saved.owner = caller := by
  simp only [validSaved, Bool.and_eq_true, beq_iff_eq] at hvalid
  exact hvalid.1.1.1

/-- The separate bank is an exact typed projection of the waiter index.  It
contains no runnable-only entry: every waiter has one valid suspended context,
and no non-waiter has a blocked context. -/
def ContextAgreement (state : State) : Prop :=
  (forall subject, (state.blocked subject).isSome =
    (state.ipc.waiterEndpoint subject).isSome) /\
  (forall subject saved, state.blocked subject = some saved ->
    validSaved subject saved = true)

def WellFormed (state : State) : Prop :=
  BlockingIPC.WellFormed state.ipc /\ ContextAgreement state

/-- Exact classification of sleeping contexts after contained-fault cleanup.
Ordinary blocked contexts agree exactly with the waiter index.  Detached
contexts are disjoint, remain valid for their owner, and retain only enough
lifecycle authority to be resumed by a later capacity-checked drain. -/
def DeferredWellFormed (state : State) (deferred : DeferredCancelState) : Prop :=
  WellFormed state /\
  (∀ subject, (state.blocked subject).isSome = true →
    deferred.retained subject = none) /\
  (∀ subject saved, deferred.retained subject = some saved →
    validSaved subject saved = true ∧
    state.ipc.waiterEndpoint subject = none ∧
    state.ipc.scheduler.lifecycle.capabilities.subjects subject = true ∧
    state.ipc.scheduler.lifecycle.runnable subject = false ∧
    state.ipc.scheduler.lifecycle.current ≠ some subject ∧
    subject ∉ state.ipc.scheduler.ready ∧
    Scheduler.ownsAddressSpace state.ipc.scheduler subject = some subject)

def setRetained (deferred : DeferredCancelState) (subject : SubjectId)
    (value : Option ResumableContext.Context) : DeferredCancelState :=
  ⟨fun candidate => if candidate = subject then value else deferred.retained candidate⟩

/-- Pointwise authority test used by contained cleanup. -/
def remainsWaitingAuthorized (state : State) (subject : SubjectId) : Prop :=
  ∃ endpoint, state.ipc.waiterEndpoint subject = some endpoint ∧
    BlockingIPC.authorizedReceive state.ipc subject endpoint

/-- Detach every waiter invalidated by a replacement authoritative scheduler.
The old, validated context is moved to the typed deferred bank; already
deferred entries are retained. -/
def detachInvalidated (state : State) (deferred : DeferredCancelState)
    (scheduler : Scheduler.State) : State × DeferredCancelState :=
  let next : BlockingIPC.State := { state.ipc with scheduler }
  let retainedWaiter (subject : SubjectId) : Bool :=
    match state.ipc.waiterEndpoint subject with
    | some endpoint => scheduler.lifecycle.capabilities.objects endpoint
    | none => false
    ({ ipc := { next with
        waiters := fun endpoint =>
          (state.ipc.waiters endpoint).filter
            (fun _ => scheduler.lifecycle.capabilities.objects endpoint)
        waiterEndpoint := fun subject =>
          match state.ipc.waiterEndpoint subject with
          | some endpoint =>
              if scheduler.lifecycle.capabilities.objects endpoint then some endpoint else none
          | none => none }
       blocked := fun subject => if retainedWaiter subject then state.blocked subject else none },
     ⟨fun subject =>
       if retainedWaiter subject then deferred.retained subject
       else match state.ipc.waiterEndpoint subject with
         | some _ => state.blocked subject
         | none => deferred.retained subject⟩)

theorem detachInvalidated_preserves_contextAgreement state deferred scheduler
    (hstate : ContextAgreement state) :
    ContextAgreement (detachInvalidated state deferred scheduler).1 := by
  rcases hstate with ⟨hprojection, hvalid⟩
  constructor
  · intro subject
    cases hendpoint : state.ipc.waiterEndpoint subject with
    | none =>
        have hblocked := hprojection subject
        simp [detachInvalidated, hendpoint] at hblocked ⊢
    | some endpoint =>
        cases hlive : scheduler.lifecycle.capabilities.objects endpoint
        · simp [detachInvalidated, hendpoint, hlive]
        · simpa [detachInvalidated, hendpoint, hlive] using hprojection subject
  · intro subject saved hsaved
    change (if (match state.ipc.waiterEndpoint subject with
      | some endpoint => scheduler.lifecycle.capabilities.objects endpoint
      | none => false) then state.blocked subject else none) = some saved at hsaved
    generalize hkeep : (match state.ipc.waiterEndpoint subject with
      | some endpoint => scheduler.lifecycle.capabilities.objects endpoint
      | none => false) = keep at hsaved
    cases keep <;> simp_all

theorem detachInvalidated_invalidated_exact state deferred scheduler subject endpoint saved
    (hendpoint : state.ipc.waiterEndpoint subject = some endpoint)
    (hsaved : state.blocked subject = some saved)
    (hretired : scheduler.lifecycle.capabilities.objects endpoint = false) :
    (detachInvalidated state deferred scheduler).1.ipc.waiterEndpoint subject = none ∧
      (detachInvalidated state deferred scheduler).1.blocked subject = none ∧
      (detachInvalidated state deferred scheduler).2.retained subject = some saved := by
  simp [detachInvalidated, hendpoint, hsaved, hretired]

theorem detachInvalidated_retained_exact state deferred scheduler subject endpoint
    (hendpoint : state.ipc.waiterEndpoint subject = some endpoint)
    (hlive : scheduler.lifecycle.capabilities.objects endpoint = true) :
    (detachInvalidated state deferred scheduler).1.ipc.waiterEndpoint subject = some endpoint ∧
      (detachInvalidated state deferred scheduler).1.blocked subject = state.blocked subject ∧
      (detachInvalidated state deferred scheduler).2.retained subject =
        deferred.retained subject := by
  simp [detachInvalidated, hendpoint, hlive]

inductive DrainError where
  | notDeferred | invalidRetained | staleSubject | missingAddressSpace | readyQueueFull
  deriving DecidableEq, Repr

inductive DrainResult where
  | drained (saved : ResumableContext.Context)
  | rejected (reason : DrainError)
  deriving DecidableEq, Repr

structure DrainOutcome where
  state : State
  deferred : DeferredCancelState
  result : DrainResult

/-- Atomically return one detached peer to scheduler ownership.  Every
authority fact is checked again and ready capacity is reserved before the
deferred entry, runnable bit, completion, or queue can change. -/
def drainDeferred (state : State) (deferred : DeferredCancelState)
    (subject : SubjectId) : DrainOutcome :=
  match deferred.retained subject with
  | none => ⟨state, deferred, .rejected .notDeferred⟩
  | some saved =>
      if !validSaved subject saved then
        ⟨state, deferred, .rejected .invalidRetained⟩
      else if state.ipc.scheduler.lifecycle.capabilities.subjects subject != true then
        ⟨state, deferred, .rejected .staleSubject⟩
      else if Scheduler.ownsAddressSpace state.ipc.scheduler subject != some subject then
        ⟨state, deferred, .rejected .missingAddressSpace⟩
      else if state.ipc.scheduler.capacity ≤ state.ipc.scheduler.ready.length then
        ⟨state, deferred, .rejected .readyQueueFull⟩
      else
        let scheduler := { state.ipc.scheduler with
          ready := state.ipc.scheduler.ready ++ [subject]
          lifecycle := { state.ipc.scheduler.lifecycle with
            runnable := SubjectLifecycle.setBool
              state.ipc.scheduler.lifecycle.runnable subject true } }
        ⟨{ state with ipc := { state.ipc with
            scheduler
            completion := BlockingIPC.setCompletion state.ipc.completion subject
              (some .cancelled) } },
          setRetained deferred subject none, .drained saved⟩

theorem drainDeferred_rejected_unchanged state deferred subject reason
    (h : (drainDeferred state deferred subject).result = .rejected reason) :
    (drainDeferred state deferred subject).state = state ∧
      (drainDeferred state deferred subject).deferred = deferred := by
  simp only [drainDeferred] at h ⊢
  split at * <;> try simp_all
  all_goals split at * <;> try simp_all
  all_goals split at * <;> try simp_all
  all_goals split at * <;> try simp_all
  all_goals split at * <;> simp_all

theorem drainDeferred_drained_exact state deferred subject saved
    (h : (drainDeferred state deferred subject).result = .drained saved) :
    deferred.retained subject = some saved ∧
      (drainDeferred state deferred subject).deferred.retained subject = none ∧
      (drainDeferred state deferred subject).state.ipc.scheduler.lifecycle.runnable subject =
        true ∧
      subject ∈ (drainDeferred state deferred subject).state.ipc.scheduler.ready ∧
      (drainDeferred state deferred subject).state.ipc.completion subject =
        some .cancelled := by
  simp only [drainDeferred] at h ⊢
  split at * <;> try simp_all
  all_goals split at * <;> try simp_all
  all_goals split at * <;> try simp_all
  all_goals split at * <;> try simp_all
  all_goals split at * <;>
    simp_all [setRetained]
  all_goals split at * <;>
    simp_all [SubjectLifecycle.setBool, BlockingIPC.setCompletion]
  all_goals omega

/-- A successful drain revalidates every retained-context authority fact and
reserves capacity in the pre-state before appending the subject. -/
theorem drainDeferred_drained_reserves_capacity state deferred subject saved
    (h : (drainDeferred state deferred subject).result = .drained saved) :
    validSaved subject saved = true ∧
      state.ipc.scheduler.lifecycle.capabilities.subjects subject = true ∧
      Scheduler.ownsAddressSpace state.ipc.scheduler subject = some subject ∧
      ¬ state.ipc.scheduler.capacity ≤ state.ipc.scheduler.ready.length ∧
      (drainDeferred state deferred subject).state.ipc.scheduler.ready =
        state.ipc.scheduler.ready ++ [subject] := by
  simp only [drainDeferred] at h ⊢
  split at * <;> try simp_all
  all_goals split at * <;> try simp_all
  all_goals split at * <;> try simp_all
  all_goals split at * <;> try simp_all
  all_goals split at * <;> simp_all [Nat.not_le_of_gt]

/-- Capacity rejection is typed and atomic: it can occur only after the saved
context and its subject/address-space authority have been revalidated. -/
theorem drainDeferred_readyQueueFull_exact state deferred subject
    (h : (drainDeferred state deferred subject).result =
      .rejected .readyQueueFull) :
    (∃ saved, deferred.retained subject = some saved ∧
      validSaved subject saved = true) ∧
      state.ipc.scheduler.lifecycle.capabilities.subjects subject = true ∧
      Scheduler.ownsAddressSpace state.ipc.scheduler subject = some subject ∧
      state.ipc.scheduler.capacity ≤ state.ipc.scheduler.ready.length ∧
      (drainDeferred state deferred subject).state = state ∧
      (drainDeferred state deferred subject).deferred = deferred := by
  simp only [drainDeferred] at h ⊢
  split at * <;> try simp_all
  all_goals split at * <;> try simp_all
  all_goals split at * <;> try simp_all
  all_goals split at * <;> try simp_all
  all_goals split at * <;> simp_all

inductive ContextError where
  | invalidSaved | duplicateSaved | missingSaved
  deriving DecidableEq, Repr

inductive ReceiveResult where
  | completed (result : BlockingIPC.ReceiveResult)
  | contextRejected (reason : ContextError)
  deriving DecidableEq, Repr

structure ReceiveOutcome where
  state : State
  result : ReceiveResult

/-- Invalid contexts and duplicate bank entries reject before the endpoint
transition.  A raw block and reservation of the exact context are one state. -/
def receiveOrBlock (state : State) (caller : SubjectId) (slot : SlotId)
    (saved : ResumableContext.Context) : ReceiveOutcome :=
  if !validSaved caller saved then
    { state, result := .contextRejected .invalidSaved }
  else if (state.blocked caller).isSome then
    { state, result := .contextRejected .duplicateSaved }
  else
    let outcome := BlockingIPC.receiveOrBlock state.ipc caller slot
    match outcome.result with
    | .rejected reason => { state, result := .completed (.rejected reason) }
    | .delivered envelope =>
        { state := ⟨outcome.state, state.blocked⟩,
          result := .completed (.delivered envelope) }
    | .blocked =>
        { state := ⟨outcome.state, setBlocked state.blocked caller (some saved)⟩,
          result := .completed .blocked }

inductive SendResult where
  | accepted
  | ipcRejected (reason : BlockingIPC.Error)
  | contextRejected (reason : ContextError)
  deriving DecidableEq, Repr

structure SendOutcome where
  state : State
  result : SendResult
  released : Option ResumableContext.Context

/-- An accepted wake consumes and returns the exact saved receiver context.
If the waiter projection has no matching bank entry, the entire send rejects
with the identical composite pre-state. -/
def send (state : State) (caller : SubjectId) (slot : SlotId)
    (payload : BlockingIPC.Payload) : SendOutcome :=
  let outcome := BlockingIPC.send state.ipc caller slot payload
  match outcome.result with
  | .rejected reason => { state, result := .ipcRejected reason, released := none }
  | .accepted =>
      match BlockingIPC.endpointOf state.ipc caller slot with
      | none => { state, result := .contextRejected .missingSaved, released := none }
      | some endpoint =>
          match state.ipc.waiters endpoint with
          | [] =>
              { state := { ipc := outcome.state, blocked := state.blocked }
                result := .accepted
                released := none }
          | receiver :: _ =>
              match state.blocked receiver with
              | none => { state, result := .contextRejected .missingSaved, released := none }
              | some saved =>
                  { state :=
                      { ipc := outcome.state
                        blocked := setBlocked state.blocked receiver none }
                    result := .accepted
                    released := some saved }

inductive CancelResult where
  | notWaiting | cancelled
  | ipcRejected (reason : BlockingIPC.Error)
  | contextRejected (reason : ContextError)
  deriving DecidableEq, Repr

structure CancelOutcome where
  state : State
  result : CancelResult
  released : Option ResumableContext.Context

/-- Cancellation and context release are one transition.  Missing context and
ready-capacity failures reject atomically. -/
def cancel (state : State) (subject : SubjectId) : CancelOutcome :=
  match state.ipc.waiterEndpoint subject with
  | none => { state, result := .notWaiting, released := none }
  | some _ =>
      match state.blocked subject with
      | none => { state, result := .contextRejected .missingSaved, released := none }
      | some saved =>
          let outcome := BlockingIPC.cancelSubjectTyped state.ipc subject
          match outcome.result with
          | .rejected reason => { state, result := .ipcRejected reason, released := none }
          | .notWaiting => { state, result := .notWaiting, released := none }
          | .cancelled =>
              { state := ⟨outcome.state, setBlocked state.blocked subject none⟩,
                result := .cancelled, released := some saved }

/-- Terminate one subject across the shared lifecycle/scheduler, waiter index,
and exact blocked-context bank in one state transition. -/
def terminate (state : State) (subject : SubjectId) : State :=
  match (SubjectLifecycle.terminate state.ipc.scheduler.lifecycle subject).result with
  | .rejected _ => state
  | .accepted =>
      { ipc := BlockingIPC.terminate state.ipc subject
        blocked := setBlocked state.blocked subject none }

/-! ## Focused preservation and atomicity -/

theorem receive_preserves_wellFormed state caller slot saved
    (hwf : WellFormed state) :
    WellFormed (receiveOrBlock state caller slot saved).state := by
  rcases hwf with ⟨hipc, hagreement, hvalid⟩
  unfold receiveOrBlock
  split
  · exact ⟨hipc, hagreement, hvalid⟩
  split
  · exact ⟨hipc, hagreement, hvalid⟩
  generalize hraw : BlockingIPC.receiveOrBlock state.ipc caller slot = outcome
  have hrawWf := BlockingIPC.receiveOrBlock_preserves_wellFormed state.ipc caller slot hipc
  rw [hraw] at hrawWf
  cases outcome with
  | mk next result =>
      cases result with
      | rejected reason => exact ⟨hipc, hagreement, hvalid⟩
      | delivered envelope =>
          constructor
          · exact hrawWf
          · simp only [ContextAgreement]
            constructor
            · intro subject
              have hresult :
                  (BlockingIPC.receiveOrBlock state.ipc caller slot).result =
                    .delivered envelope := by
                rw [hraw]
              have hindex := BlockingIPC.receive_delivered_waiterEndpoint_unchanged
                state.ipc caller slot envelope hresult
              have hnext : next.waiterEndpoint = state.ipc.waiterEndpoint := by
                simpa [hraw] using hindex
              simpa [hnext] using hagreement subject
            · exact hvalid
      | blocked =>
          constructor
          · exact hrawWf
          · simp only [ContextAgreement]
            constructor
            · intro subject
              have hresult :
                  (BlockingIPC.receiveOrBlock state.ipc caller slot).result = .blocked := by
                rw [hraw]
              obtain ⟨endpoint, hindex⟩ :=
                BlockingIPC.receive_blocked_waiterEndpoint_exact
                  state.ipc caller slot hresult
              have hnext : next.waiterEndpoint =
                  BlockingIPC.setWaiterEndpoint state.ipc.waiterEndpoint caller
                    (some endpoint) := by
                simpa [hraw] using hindex
              by_cases heq : subject = caller
              · subst subject
                simp [setBlocked, hnext, BlockingIPC.setWaiterEndpoint]
              · simpa [setBlocked, hnext, BlockingIPC.setWaiterEndpoint, heq] using
                  hagreement subject
            · intro subject actual hactual
              by_cases heq : subject = caller
              · subst subject
                simp [setBlocked] at hactual
                subst actual
                simp_all
              · simp [setBlocked, heq] at hactual
                exact hvalid subject actual hactual

theorem send_preserves_wellFormed state caller slot payload
    (hwf : WellFormed state) :
    WellFormed (send state caller slot payload).state := by
  rcases hwf with ⟨hipc, hagreement, hvalid⟩
  unfold send
  generalize hraw : BlockingIPC.send state.ipc caller slot payload = outcome
  have hrawWf := BlockingIPC.send_preserves_wellFormed state.ipc caller slot payload hipc
  rw [hraw] at hrawWf
  cases outcome with
  | mk next result =>
      cases result with
      | rejected reason => exact ⟨hipc, hagreement, hvalid⟩
      | accepted =>
          have hresult :
              (BlockingIPC.send state.ipc caller slot payload).result = .accepted := by
            rw [hraw]
          obtain ⟨actualEndpoint, hactualEndpoint, hprojection⟩ :=
            BlockingIPC.send_accepted_waiterEndpoint_exact
              state.ipc caller slot payload hresult
          rw [hraw] at hprojection
          split
          · exact ⟨hipc, hagreement, hvalid⟩
          next endpoint hendpoint =>
            rw [hendpoint] at hactualEndpoint
            injection hactualEndpoint with heq
            subst actualEndpoint
            split
            next hqueue =>
              rw [hqueue] at hprojection
              exact ⟨hrawWf, by
                constructor
                · intro subject
                  rw [hprojection]
                  exact hagreement subject
                · exact hvalid⟩
            next receiver rest hqueue =>
              rw [hqueue] at hprojection
              have hsome : (state.blocked receiver).isSome = true := by
                rw [hagreement receiver]
                have hindexed := (hipc.2.2.2.2.1 endpoint receiver).mp (by simp [hqueue])
                simp [hindexed]
              cases hsaved : state.blocked receiver with
              | none => simp [hsaved] at hsome
              | some saved =>
                  refine ⟨hrawWf, ?_⟩
                  constructor
                  · intro subject
                    rw [hprojection]
                    by_cases heq : subject = receiver
                    · subst subject
                      simp [setBlocked, BlockingIPC.setWaiterEndpoint]
                    · simpa [setBlocked, BlockingIPC.setWaiterEndpoint, heq] using
                        hagreement subject
                  · intro subject actual hactual
                    by_cases heq : subject = receiver
                    · subst subject
                      simp [setBlocked] at hactual
                    · apply hvalid subject actual
                      simpa [setBlocked, heq] using hactual

theorem receive_contextRejected_unchanged state caller slot saved reason
    (hrejected : (receiveOrBlock state caller slot saved).result =
      .contextRejected reason) :
    (receiveOrBlock state caller slot saved).state = state := by
  unfold receiveOrBlock at hrejected ⊢
  split <;> simp_all
  split <;> simp_all
  generalize hraw : BlockingIPC.receiveOrBlock state.ipc caller slot = outcome at hrejected ⊢
  cases outcome with
  | mk next result => cases result <;> simp_all

theorem receive_ipcRejected_unchanged state caller slot saved reason
    (hrejected : (receiveOrBlock state caller slot saved).result =
      .completed (.rejected reason)) :
    (receiveOrBlock state caller slot saved).state = state := by
  unfold receiveOrBlock at hrejected ⊢
  split <;> simp_all
  split <;> simp_all
  generalize hraw : BlockingIPC.receiveOrBlock state.ipc caller slot = outcome at hrejected ⊢
  cases outcome with
  | mk next result => cases result <;> simp_all

theorem receive_blocked_exact state caller slot saved
    (hblocked : (receiveOrBlock state caller slot saved).result = .completed .blocked) :
    validSaved caller saved = true ∧
      (receiveOrBlock state caller slot saved).state.blocked caller = some saved := by
  unfold receiveOrBlock at hblocked ⊢
  split at hblocked
  · simp at hblocked
  · have hvalid : validSaved caller saved = true := by simp_all
    split at hblocked
    · simp at hblocked
    · generalize hraw : BlockingIPC.receiveOrBlock state.ipc caller slot = outcome at hblocked ⊢
      cases outcome with
      | mk next result => cases result <;> simp_all [setBlocked]

/-- A successful typed delivery exposes the exact underlying IPC transition. -/
theorem receive_delivered_ipc_exact state caller slot saved envelope
    (hcompleted : (receiveOrBlock state caller slot saved).result =
      .completed (.delivered envelope)) :
    (receiveOrBlock state caller slot saved).state.ipc =
        (BlockingIPC.receiveOrBlock state.ipc caller slot).state ∧
      (BlockingIPC.receiveOrBlock state.ipc caller slot).result = .delivered envelope := by
  unfold receiveOrBlock at hcompleted ⊢
  split at hcompleted <;> simp_all
  split at hcompleted <;> simp_all
  generalize hraw : BlockingIPC.receiveOrBlock state.ipc caller slot = outcome at hcompleted ⊢
  cases outcome with
  | mk next result => cases result <;> simp_all

/-- A successful typed block likewise publishes the exact raw waiter and
scheduler post-state rather than reconstructing it. -/
theorem receive_blocked_ipc_exact state caller slot saved
    (hcompleted : (receiveOrBlock state caller slot saved).result = .completed .blocked) :
    (receiveOrBlock state caller slot saved).state.ipc =
        (BlockingIPC.receiveOrBlock state.ipc caller slot).state ∧
      (BlockingIPC.receiveOrBlock state.ipc caller slot).result = .blocked := by
  unfold receiveOrBlock at hcompleted ⊢
  split at hcompleted <;> simp_all
  split at hcompleted <;> simp_all
  generalize hraw : BlockingIPC.receiveOrBlock state.ipc caller slot = outcome at hcompleted ⊢
  cases outcome with
  | mk next result => cases result <;> simp_all

theorem send_rejected_unchanged state caller slot payload
    (hrejected : (send state caller slot payload).result ≠ .accepted) :
    (send state caller slot payload).state = state := by
  unfold send at hrejected ⊢
  generalize hraw : BlockingIPC.send state.ipc caller slot payload = outcome at hrejected ⊢
  cases outcome with
  | mk next result =>
      cases result with
      | rejected reason => rfl
      | accepted =>
          split <;> simp_all
          next endpoint =>
            split <;> simp_all
            next receiver rest => split <;> simp_all

/-- An accepted send that releases no blocked receiver is the mailbox-only
case.  It leaves the authoritative scheduler unchanged, which lets the
composite runtime publish the mailbox mutation without rebuilding scheduler
or resumable-context projections. -/
theorem send_accepted_unreleased_scheduler_unchanged state caller slot payload
    (haccepted : (send state caller slot payload).result = .accepted)
    (hunreleased : (send state caller slot payload).released = none) :
    (send state caller slot payload).state.ipc.scheduler = state.ipc.scheduler := by
  unfold send at haccepted hunreleased ⊢
  generalize hraw : BlockingIPC.send state.ipc caller slot payload = outcome at haccepted hunreleased ⊢
  cases outcome with
  | mk next result =>
      cases result with
      | rejected reason => simp at haccepted
      | accepted =>
          split at * <;> try simp_all
          next endpoint hendpoint =>
            split at *
            · grind [BlockingIPC.send, BlockingIPC.reject, BlockingIPC.endpointOf]
            · split at hunreleased <;> simp_all

/-- Every context-layer accepted send is the exact accepted raw IPC send. -/
theorem send_accepted_ipc_exact state caller slot payload
    (haccepted : (send state caller slot payload).result = .accepted) :
    (send state caller slot payload).state.ipc =
        (BlockingIPC.send state.ipc caller slot payload).state ∧
      (BlockingIPC.send state.ipc caller slot payload).result = .accepted := by
  unfold send at haccepted ⊢
  generalize hraw : BlockingIPC.send state.ipc caller slot payload = outcome at haccepted ⊢
  cases outcome with
  | mk next result =>
      cases result with
      | rejected reason => simp at haccepted
      | accepted =>
          split at haccepted
          · simp at haccepted
          next endpoint hendpoint =>
            split at haccepted
            next hqueue => simp
            next receiver rest hqueue =>
              split at haccepted
              · simp at haccepted
              next saved hsaved => simp

theorem send_released_exact state caller slot payload saved
    (hreleased : (send state caller slot payload).released = some saved) :
    ∃ endpoint receiver rest,
      BlockingIPC.endpointOf state.ipc caller slot = some endpoint ∧
      state.ipc.waiters endpoint = receiver :: rest ∧
      state.blocked receiver = some saved ∧
      (send state caller slot payload).result = .accepted ∧
      (send state caller slot payload).state.blocked receiver = none := by
  unfold send at hreleased ⊢
  generalize hraw : BlockingIPC.send state.ipc caller slot payload = outcome at hreleased ⊢
  cases outcome with
  | mk next result =>
      cases result with
      | rejected reason => simp at hreleased
      | accepted =>
          split at hreleased
          · simp at hreleased
          next endpoint hendpoint =>
            split at hreleased
            · simp at hreleased
            next receiver rest hwaiters =>
              split at hreleased
              · simp at hreleased
              next actual hsaved =>
                simp only at hreleased
                injection hreleased with heq
                subst actual
                exact ⟨endpoint, receiver, rest, hendpoint, hwaiters, hsaved,
                  rfl, by simp [setBlocked]⟩

theorem cancel_preserves_wellFormed state subject
    (hwf : WellFormed state) :
    WellFormed (cancel state subject).state := by
  rcases hwf with ⟨hipc, hagreement, hvalid⟩
  unfold cancel
  split
  · exact ⟨hipc, hagreement, hvalid⟩
  next endpoint hwaiter =>
    split
    · exact ⟨hipc, hagreement, hvalid⟩
    next saved hsaved =>
      generalize hraw : BlockingIPC.cancelSubjectTyped state.ipc subject = outcome
      have hrawWf := BlockingIPC.cancelSubjectTyped_preserves_wellFormed state.ipc subject hipc
      rw [hraw] at hrawWf
      cases outcome with
      | mk next result =>
          cases result with
          | rejected reason => exact ⟨hipc, hagreement, hvalid⟩
          | notWaiting => exact ⟨hipc, hagreement, hvalid⟩
          | cancelled =>
              have hresult :
                  (BlockingIPC.cancelSubjectTyped state.ipc subject).result = .cancelled := by
                rw [hraw]
              have hprojection := BlockingIPC.cancelSubjectTyped_cancelled_waiterEndpoint_exact
                state.ipc subject hresult
              rw [hraw] at hprojection
              refine ⟨hrawWf, ?_⟩
              constructor
              · intro candidate
                rw [hprojection]
                by_cases heq : candidate = subject
                · subst candidate
                  simp [setBlocked, BlockingIPC.setWaiterEndpoint]
                · simpa [setBlocked, BlockingIPC.setWaiterEndpoint, heq] using
                    hagreement candidate
              · intro candidate actual hactual
                by_cases heq : candidate = subject
                · subst candidate
                  simp [setBlocked] at hactual
                · apply hvalid candidate actual
                  simpa [setBlocked, heq] using hactual

theorem cancel_rejected_unchanged state subject
    (hrejected : (cancel state subject).result ≠ .cancelled ∧
      (cancel state subject).result ≠ .notWaiting) :
    (cancel state subject).state = state := by
  unfold cancel at hrejected ⊢
  split <;> simp_all
  split <;> simp_all
  generalize hraw : BlockingIPC.cancelSubjectTyped state.ipc subject = outcome at hrejected ⊢
  cases outcome with
  | mk next result => cases result <;> simp_all

theorem cancel_cancelled_exact state subject saved
    (hcancelled : (cancel state subject).result = .cancelled)
    (hreleased : (cancel state subject).released = some saved) :
    state.blocked subject = some saved ∧
      (cancel state subject).state.blocked subject = none := by
  unfold cancel at hcancelled hreleased ⊢
  split at hcancelled <;> simp_all
  split at hcancelled <;> simp_all
  generalize hraw : BlockingIPC.cancelSubjectTyped state.ipc subject = outcome at hcancelled hreleased ⊢
  cases outcome with
  | mk next result => cases result <;> simp_all [setBlocked]

/-- Every successful context-owning cancellation publishes the exact raw IPC
cancellation transition, including its scheduler wake. -/
theorem cancel_cancelled_ipc_exact state subject
    (hcancelled : (cancel state subject).result = .cancelled) :
    (cancel state subject).state.ipc =
        (BlockingIPC.cancelSubjectTyped state.ipc subject).state ∧
      (BlockingIPC.cancelSubjectTyped state.ipc subject).result = .cancelled := by
  unfold cancel at hcancelled ⊢
  split at hcancelled
  · simp at hcancelled
  next endpoint hwaiter =>
    split at hcancelled
    · simp at hcancelled
    next saved hsaved =>
      generalize hraw : BlockingIPC.cancelSubjectTyped state.ipc subject = outcome at hcancelled ⊢
      cases outcome with
      | mk next result => cases result <;> simp_all

@[simp] theorem terminate_blocked_self state subject :
    (SubjectLifecycle.terminate state.ipc.scheduler.lifecycle subject).result = .accepted →
      (terminate state subject).blocked subject = none := by
  intro haccepted
  simp [terminate, haccepted, setBlocked]

/-- A typed lifecycle rejection cannot detach a saved blocking context from
its still-live waiter. -/
theorem terminate_rejected_unchanged state subject reason
    (hrejected :
      (SubjectLifecycle.terminate state.ipc.scheduler.lifecycle subject).result =
        .rejected reason) :
    terminate state subject = state := by
  simp [terminate, hrejected]

/-- Once lifecycle termination accepts, waiter removal and blocked-context
removal are committed by the same typed state value.  The dead subject cannot
remain indexed in either projection. -/
theorem terminate_accepted_cleans_self state subject
    (haccepted : (SubjectLifecycle.terminate state.ipc.scheduler.lifecycle subject).result =
      .accepted) :
    (terminate state subject).ipc.waiterEndpoint subject = none ∧
      (terminate state subject).blocked subject = none := by
  have hterminated :
      (SubjectLifecycle.terminate state.ipc.scheduler.lifecycle subject).state =
        SubjectLifecycle.terminateState state.ipc.scheduler.lifecycle subject := by
    unfold SubjectLifecycle.terminate at haccepted ⊢
    split at haccepted <;> simp_all [SubjectLifecycle.reject]
    split at haccepted <;> simp_all
  have hdead :
      (SubjectLifecycle.terminate state.ipc.scheduler.lifecycle subject).state.capabilities.subjects
        subject = false := by
    rw [hterminated]
    exact SubjectLifecycle.terminated_not_live state.ipc.scheduler.lifecycle subject
  constructor
  · simp only [terminate, BlockingIPC.terminate, haccepted]
    unfold BlockingIPC.cancelSubject
    split
    · assumption
    · simp [hdead, BlockingIPC.setWaiterEndpoint]
  · exact terminate_blocked_self state subject haccepted

end LeanOS.BlockingIPCContext
