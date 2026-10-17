import LeanOS.FailStop.SpawnTree

/-!
# Fail-stop composite: the started child's send (#571)

The run-time loader (#492, `LeanOS.ChildLoader`) starts a loaded child, and
the child's one syscall is a send: syscall 8 sends the word in RBX through the
endpoint capability in its slot `0`, the send-only copy spawn gave it
(`spawn_child_capabilities`).  This module makes that send a step of the
composite model.

`childSend state child word` runs under the running latch, for a subject the
spawn records name as a spawned child.  It is the endpoint send of the
composite IPC model, `EndpointIPC.send`, with the child as the caller and slot
`0` as the slot (the kernel's syscall 8 names no other slot), published to
both IPC views with `installIPC` exactly as the composite gate publishes a
send.  Every check is the endpoint model's: the slot holds a live endpoint
capability with the `send` right, and the endpoint's mailbox is empty.

## Confinement

An accepted send writes exactly one mailbox: the mailbox of the object the
child's slot-`0` capability names, which receives the envelope
`(endpoint, child, word, 0)` (`childSend_sent`).  Every other mailbox and every
other projection of the composite state is unchanged (`childSend_confined`).
Every rejection, and every request outside the running latch or for a subject
that is not a spawned child, leaves the state unchanged
(`childSend_unchanged`).

## Invariants

The step keeps the combined runtime and resource invariant, the child
accounting invariant and the spawn-tree invariant (`childSend_preserves`), so
`ChildTraceStep.childSend` is a step of the whole-trace theorem
`child_resource_trace`.
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

/-- The payload of syscall 8: the word, and a zero second word. -/
def childSendPayload (word : UInt64) : EndpointIPC.Payload := { word0 := word, word1 := 0 }

inductive ChildSendResult where
  | sent
  | notRunning
  | notChild
  | rejected (reason : EndpointIPC.SendError)
  deriving DecidableEq, Repr

structure ChildSendOutcome where
  state : CompositeState
  result : ChildSendResult

/-- The endpoint model's send for the child through its slot `0`. -/
def childSendEndpoints (state : CompositeState) (child : Nat) (word : UInt64) :
    EndpointIPC.Outcome EndpointIPC.SendError :=
  EndpointIPC.send state.ipc.endpoints child childEndpointSlot (childSendPayload word)

/-- **The started child's send.**  Under the running latch, a spawned child
sends `word` through its slot-`0` endpoint capability. -/
def childSend (state : CompositeState) (child : Nat) (word : UInt64) : ChildSendOutcome :=
  match state.execution.mode with
  | .running =>
      if (state.spawn.parent child).isSome then
        match (childSendEndpoints state child word).result with
        | .accepted =>
            { state := installIPC state
                { state.ipc with endpoints := (childSendEndpoints state child word).state }
              result := .sent }
        | .rejected reason => { state, result := .rejected reason }
      else { state, result := .notChild }
  | _ => { state, result := .notRunning }

/-! ## Shape -/

theorem childSend_shape (state : CompositeState) (child : Nat) (word : UInt64) :
    ((childSend state child word).state = state ∧ (childSend state child word).result ≠ .sent) ∨
      (state.execution.mode = .running ∧ (state.spawn.parent child).isSome = true ∧
        (childSendEndpoints state child word).result = .accepted ∧
        (childSend state child word).result = .sent ∧
        (childSend state child word).state = installIPC state
          { state.ipc with endpoints := (childSendEndpoints state child word).state }) := by
  unfold childSend
  cases mode : state.execution.mode with
  | running =>
      by_cases spawned : (state.spawn.parent child).isSome = true
      · cases result : (childSendEndpoints state child word).result with
        | accepted => right; simp [spawned, result]
        | rejected reason => left; simp [spawned, result]
      · left; simp [spawned]
  | handling _ => left; simp
  | halted _ => left; simp

/-- Every outcome other than `sent` leaves the state unchanged. -/
theorem childSend_unchanged (state : CompositeState) (child : Nat) (word : UInt64)
    (notSent : (childSend state child word).result ≠ .sent) :
    (childSend state child word).state = state := by
  rcases childSend_shape state child word with ⟨same, _⟩ | ⟨_, _, _, sent, _⟩
  · exact same
  · exact absurd sent notSent

/-- An accepted endpoint send, unfolded: the slot holds a live endpoint
capability with the `send` right whose mailbox was empty, and exactly that
mailbox receives the envelope. -/
theorem endpointSend_accepted (endpoints : EndpointIPC.State) (caller slot : Nat)
    (payload : EndpointIPC.Payload)
    (accepted : (EndpointIPC.send endpoints caller slot payload).result = .accepted) :
    ∃ capability, endpoints.capabilities.slots caller slot = some capability ∧
      capability.kind = .endpoint ∧ capability.rights.send = true ∧
      endpoints.capabilities.objects capability.object = true ∧
      endpoints.mailbox capability.object = none ∧
      (EndpointIPC.send endpoints caller slot payload).state =
        { endpoints with
          mailbox := EndpointIPC.setOption endpoints.mailbox capability.object
            (some { endpoint := capability.object, sender := caller, payload })
          sendHistory := EndpointIPC.appendHistory endpoints.sendHistory capability.object
            { endpoint := capability.object, sender := caller, payload } } := by
  unfold EndpointIPC.send at accepted ⊢
  cases found : Capability.lookup endpoints.capabilities caller slot with
  | invalidSubject => simp [found, EndpointIPC.reject] at accepted
  | staleSlot => simp [found, EndpointIPC.reject] at accepted
  | found capability =>
    simp only [found] at accepted ⊢
    have held := Capability.lookup_found_slot endpoints.capabilities caller slot capability found
    by_cases kind : capability.kind = .endpoint
    · by_cases send : capability.rights.send = true
      · by_cases live : endpoints.capabilities.objects capability.object = true
        · by_cases kinds : endpoints.capabilities.kinds capability.object = some .endpoint
          · by_cases empty : endpoints.mailbox capability.object = none
            · refine ⟨capability, held, kind, send, live, empty, ?_⟩
              simp [kind, send, live, kinds, empty]
            · have full : (endpoints.mailbox capability.object).isSome = true := by
                cases h : endpoints.mailbox capability.object <;> simp_all
              simp [kind, send, live, kinds, full, EndpointIPC.reject] at accepted
          · simp [kind, send, live, kinds, EndpointIPC.reject] at accepted
        · simp [kind, send, live, EndpointIPC.reject] at accepted
      · simp [kind, send, EndpointIPC.reject] at accepted
    · simp [kind, EndpointIPC.reject] at accepted

/-- **What the child's send does.**  An accepted send is exactly the
publication of one envelope `(endpoint, child, word, 0)` into the empty
mailbox of the endpoint the child's slot-`0` capability names, which carries
the `send` right. -/
theorem childSend_sent (state : CompositeState) (child : Nat) (word : UInt64)
    (holds : RuntimeWellFormed state)
    (sent : (childSend state child word).result = .sent) :
    ∃ capability, state.capabilities.slots child childEndpointSlot = some capability ∧
      capability.kind = .endpoint ∧ capability.rights.send = true ∧
      state.ipc.endpoints.mailbox capability.object = none ∧
      (childSend state child word).state = installIPC state
        { state.ipc with endpoints := { state.ipc.endpoints with
            mailbox := EndpointIPC.setOption state.ipc.endpoints.mailbox capability.object
              (some { endpoint := capability.object, sender := child,
                      payload := childSendPayload word })
            sendHistory := EndpointIPC.appendHistory state.ipc.endpoints.sendHistory
              capability.object
              { endpoint := capability.object, sender := child,
                payload := childSendPayload word } } } := by
  rcases childSend_shape state child word with ⟨_, notSent⟩ | ⟨_, _, accepted, _, stateEq⟩
  · exact absurd sent notSent
  obtain ⟨capability, held, kind, send, _, empty, endpointsEq⟩ :=
    endpointSend_accepted _ _ _ _ accepted
  have caps : state.ipc.endpoints.capabilities = state.capabilities :=
    holds.1.2.2.2.2.2.2.1.trans holds.1.2.2.2.1.symm
  rw [caps] at held
  refine ⟨capability, held, kind, send, empty, ?_⟩
  rw [stateEq]
  simp only [childSendEndpoints] at endpointsEq ⊢
  rw [endpointsEq]

/-- **Confinement of the child's send.**  An accepted send changes only the
mailbox (and its ghost send history) of the endpoint the child's slot-`0`
capability names: every other mailbox is unchanged, and every projection of
the composite state other than the two IPC views is unchanged. -/
theorem childSend_confined (state : CompositeState) (child : Nat) (word : UInt64)
    (holds : RuntimeWellFormed state)
    (sent : (childSend state child word).result = .sent) :
    ∃ capability, state.capabilities.slots child childEndpointSlot = some capability ∧
      capability.kind = .endpoint ∧ capability.rights.send = true ∧
      (∀ object, object ≠ capability.object →
        (childSend state child word).state.ipc.endpoints.mailbox object =
          state.ipc.endpoints.mailbox object) ∧
      (childSend state child word).state.ipc.endpoints.capabilities =
        state.ipc.endpoints.capabilities ∧
      { (childSend state child word).state with ipc := state.ipc, transfers := state.transfers } =
        state := by
  obtain ⟨capability, held, kind, send, _, stateEq⟩ := childSend_sent state child word holds sent
  refine ⟨capability, held, kind, send, fun object other => ?_, ?_, ?_⟩
  · rw [stateEq]
    simp [installIPC, EndpointIPC.setOption, other]
  · rw [stateEq]; rfl
  · rw [stateEq]; rfl

/-! ## Invariants -/

private theorem send_capabilities_unchanged (endpoints : EndpointIPC.State) (caller slot : Nat)
    (payload : EndpointIPC.Payload) :
    (EndpointIPC.send endpoints caller slot payload).state.capabilities =
      endpoints.capabilities := by
  simp only [EndpointIPC.send]
  split <;> try rfl
  next cap => split <;> try rfl
              split <;> try rfl
              split <;> try rfl
              split <;> try rfl
              split <;> rfl

private theorem send_preserves_occupied_mailbox (endpoints : EndpointIPC.State)
    (caller slot : Nat) (payload : EndpointIPC.Payload) (endpoint : Nat)
    (envelope : EndpointIPC.Envelope) (hmail : endpoints.mailbox endpoint = some envelope) :
    (EndpointIPC.send endpoints caller slot payload).state.mailbox endpoint = some envelope := by
  simp only [EndpointIPC.send]
  split <;> try simpa [EndpointIPC.reject] using hmail
  next cap hlookup =>
    split <;> try simpa [EndpointIPC.reject] using hmail
    split <;> try simpa [EndpointIPC.reject] using hmail
    split <;> try simpa [EndpointIPC.reject] using hmail
    split <;> try simpa [EndpointIPC.reject] using hmail
    split <;> try simpa [EndpointIPC.reject] using hmail
    next hfree =>
      have hne : endpoint ≠ cap.object := by
        intro heq
        subst endpoint
        simp [hmail] at hfree
      simpa [EndpointIPC.setOption, hne] using hmail

private theorem send_preserves_live_senders (endpoints : EndpointIPC.State) (caller slot : Nat)
    (payload : EndpointIPC.Payload)
    (hwellFormed : Capability.WellFormed endpoints.capabilities)
    (hlive : ∀ object envelope, endpoints.mailbox object = some envelope →
      endpoints.capabilities.subjects envelope.sender = true) :
    ∀ object envelope,
      (EndpointIPC.send endpoints caller slot payload).state.mailbox object = some envelope →
        (EndpointIPC.send endpoints caller slot payload).state.capabilities.subjects
          envelope.sender = true := by
  simp only [EndpointIPC.send]
  split <;> try simpa [EndpointIPC.reject] using hlive
  next cap hlookup =>
    split <;> try simpa [EndpointIPC.reject] using hlive
    split <;> try simpa [EndpointIPC.reject] using hlive
    split <;> try simpa [EndpointIPC.reject] using hlive
    split <;> try simpa [EndpointIPC.reject] using hlive
    split <;> try simpa [EndpointIPC.reject] using hlive
    next hfree =>
      intro object envelope hmail
      by_cases heq : object = cap.object
      · subst object
        have henvelope : envelope = { endpoint := cap.object, sender := caller, payload } := by
          simpa [EndpointIPC.setOption] using hmail.symm
        subst envelope
        exact (hwellFormed.1 caller slot cap
          (Capability.lookup_found_slot endpoints.capabilities caller slot cap hlookup)).1
      · exact hlive object envelope (by simpa [EndpointIPC.setOption, heq] using hmail)

/-- Publishing the endpoint state of any endpoint send keeps the runtime
invariant, whoever the caller. -/
theorem installSend_preserves_runtimeWellFormed (state : CompositeState) (caller slot : Nat)
    (payload : EndpointIPC.Payload) (hstate : RuntimeWellFormed state) :
    RuntimeWellFormed (installIPC state
      { state.ipc with endpoints := (EndpointIPC.send state.ipc.endpoints caller slot
        payload).state }) := by
  rcases hstate with
    ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
      hscheduler, hpreemption, hresumable, htransfers, hhalted, hlive⟩
  rcases hcoherent with
    ⟨hexecLife, hschedulerLife, hpreemptionScheduler, hcapsLife,
      hmemoryCaps, hipcVirtual, hipcCaps, hresumableScheduler,
      htranslationVirtual, htransferEndpoints, hcontext, hdead, hsender⟩
  generalize hsend : EndpointIPC.send state.ipc.endpoints caller slot payload = outcome
  obtain ⟨endpoints, result⟩ := outcome
  have hcapEq : endpoints.capabilities = state.ipc.endpoints.capabilities := by
    have := send_capabilities_unchanged state.ipc.endpoints caller slot payload
    rw [hsend] at this; exact this
  have hendpoint : EndpointIPC.WellFormed endpoints := by
    have := EndpointIPC.send_preserves_wellFormed state.ipc.endpoints caller slot payload hipc.2
    rw [hsend] at this; exact this
  have htransfers' : CapabilityTransfer.WellFormed
      { state.transfers with toEndpointState := endpoints } := by
    refine ⟨hendpoint, ?_⟩
    intro endpoint transfer hpending
    have hold := htransfers.2 endpoint transfer hpending
    rcases hold with ⟨⟨envelope, hmailbox, henvelope⟩, hrest⟩
    rw [htransferEndpoints] at hmailbox
    refine ⟨⟨envelope, ?_, henvelope⟩, ?_⟩
    · have := send_preserves_occupied_mailbox state.ipc.endpoints caller slot payload endpoint
        envelope hmailbox
      rw [hsend] at this; exact this
    · simpa [htransferEndpoints, hcapEq] using hrest
  have hliveSenders : ∀ object envelope, endpoints.mailbox object = some envelope →
      endpoints.capabilities.subjects envelope.sender = true := by
    have := send_preserves_live_senders state.ipc.endpoints caller slot payload hipc.2.1
      (by
        intro priorObject priorEnvelope hprior
        simpa [hipcCaps] using hsender priorObject priorEnvelope hprior)
    rw [hsend] at this; exact this
  refine ⟨?_, hexecution, hlifecycle, hcapabilities, hvirtual, ⟨hipc.1, hendpoint⟩, hscheduler,
    hpreemption, hresumable, htransfers', hhalted, hlive⟩
  simp only [CompositeState.Coherent, installIPC]
  refine ⟨hexecLife, hschedulerLife, hpreemptionScheduler, hcapsLife, hmemoryCaps, hipcVirtual,
    by rw [hcapEq]; exact hipcCaps, hresumableScheduler, htranslationVirtual, by simp, hcontext, ?_,
    ?_⟩
  · intro object hnotLive
    exact hendpoint.2.2.2.1 object (by rw [hcapEq, hipcCaps]; exact hnotLive)
  · intro object envelope hmail
    have := hliveSenders object envelope hmail
    rw [hcapEq, hipcCaps] at this
    exact this

/-- **The child's send keeps every invariant** of the whole-trace theorem:
the combined runtime and resource invariant, the child accounting invariant,
and the spawn-tree invariant.  It writes only the two IPC views. -/
theorem childSend_preserves (state : CompositeState) (child : Nat) (word : UInt64)
    (holds : ResourceRuntimeWellFormed state) (accounting : ChildAccountingWellFormed state)
    (tree : SpawnTreeWellFormed state) :
    ResourceRuntimeWellFormed (childSend state child word).state ∧
      ChildAccountingWellFormed (childSend state child word).state ∧
      SpawnTreeWellFormed (childSend state child word).state := by
  rcases childSend_shape state child word with ⟨same, _⟩ | ⟨_, _, _, _, stateEq⟩
  · rw [same]; exact ⟨holds, accounting, tree⟩
  rw [stateEq]
  refine ⟨⟨⟨?_, holds.1.right, holds.1.publication⟩, ?_⟩, ?_, ?_⟩
  · exact installSend_preserves_runtimeWellFormed state child childEndpointSlot
      (childSendPayload word) holds.1.left
  · exact resourceWellFormed_of_historyAgrees (before := state)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ holds.2
  · exact (childAccounting_of_kept (before := state)
      (after := installIPC state
        { state.ipc with endpoints := (childSendEndpoints state child word).state })
      accounting rfl rfl rfl (fun _ issued => issued)).1
  · exact spawnTree_of_kept (before := state) tree rfl (fun _ issued => issued)

/-- The projections the whole-trace theorem tracks are unchanged by the
child's send. -/
theorem childSend_keeps (state : CompositeState) (child : Nat) (word : UInt64) :
    (childSend state child word).state.spawn = state.spawn ∧
      (childSend state child word).state.frameBudgets = state.frameBudgets ∧
      (childSend state child word).state.virtualMemory = state.virtualMemory ∧
      (childSend state child word).state.lifecycle = state.lifecycle ∧
      (childSend state child word).state.capabilities = state.capabilities := by
  rcases childSend_shape state child word with ⟨same, _⟩ | ⟨_, _, _, _, stateEq⟩
  · rw [same]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · rw [stateEq]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end LeanOS.FailStop
