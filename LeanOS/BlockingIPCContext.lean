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

end LeanOS.BlockingIPCContext
