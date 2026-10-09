import LeanOS.FailStop.Gate

/-!
# Fail-stop composite: IPC, sealed transfers, and scheduler soundness

Accepted-operation slices of the ordinary gate for user return, restart,
endpoint send and receive, sealed transfer offer and accept, and the exact
scheduler-reply soundness theorems.
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

/-- An accepted outgoing user return is a complete accepted-operation slice:
the runtime invariant forces its armed authority to refer to the live mapping
plan, and successful attestation leaves the entire composite state unchanged. -/
theorem gate_userReturn_accepted_preserves_runtimeWellFormed state request attested
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : (completeUserReturn state.execution request).action = .accepted attested) :
    RuntimeWellFormed (gate state (.userReturn request)).state ∧
      (gate state (.userReturn request)).state = state ∧
      (gate state (.userReturn request)).result = .completed (.userReturn .accepted) := by
  have harmed : state.execution.returnAuthorityArmed = true := by
    cases hvalue : state.execution.returnAuthorityArmed with
    | false => simp [completeUserReturn, hmode, hvalue, latchInvalidUserReturn] at haccepted
    | true => rfl
  have hplan : state.ReturnPlanLive = true := hstate.2.2.2.2.2.2.2.2.2.2.2.1 harmed
  have hunchanged := accepted_user_return_state_unchanged state.execution request attested haccepted
  have hoperation : applyOperation state (.userReturn request) = state := by
    simp [applyOperation, hplan, hunchanged, haccepted]
  refine ⟨?_, ?_, ?_⟩
  · simpa [gate, hmode, hoperation] using hstate
  · simp [gate, hmode, hoperation]
  · simp [gate, hmode, operationReply, hplan, haccepted]

/-- The complete outgoing-return operation preserves the global invariant.
Successful attestation is atomic; every malformed or unselected proposal
publishes the terminal execution latch together with the resumable latch, so
the two fail-stop projections cannot disagree after rejection. -/
theorem gate_userReturn_preserves_runtimeWellFormed state request
    (hstate : RuntimeWellFormed state) :
    RuntimeWellFormed (gate state (.userReturn request)).state := by
  by_cases hmode : state.execution.mode = .running
  · by_cases hlive : state.ReturnPlanLive = true
    · cases harmed : state.execution.returnAuthorityArmed with
      | false =>
          rcases hstate with
            ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
              hscheduler, hpreemption, hresumable, htransfers, hhalted, hauthority,
              hblockingCoherent⟩
          have hliveMailbox := hcoherent.2.2.2.2.2.2.2.2.2.2.2.2
          have hexecutionFatal := latchInvalidUserReturn_preserves_wellFormed
            state.execution request .unselectedAuthority none hexecution
          have hresumableHalted : ResumablePreemption.WellFormed
              { state.resumable with halted := true } :=
            (ResumablePreemption.wellFormed_set_halted state.resumable true).2 hresumable
          simp_all [gate, applyOperation, completeUserReturn, latchInvalidUserReturn,
            RuntimeWellFormed, CompositeState.Coherent,
            ResumablePreemption.wellFormed_set_halted]
          exact ⟨hliveMailbox,
            by simpa [CompositeState.BlockingIPCCoherent] using hblockingCoherent.1⟩
      | true =>
          cases hvalidation : Interrupt.validateUserReturn
              (authoritativeReturnRequest state.execution request) with
          | accepted attested =>
              have haccepted : (completeUserReturn state.execution request).action =
                  .accepted attested := by
                simp [completeUserReturn, hmode, harmed, hvalidation]
              exact (gate_userReturn_accepted_preserves_runtimeWellFormed state request
                attested hstate hmode haccepted).1
          | rejected reason =>
              rcases hstate with
                ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
                  hscheduler, hpreemption, hresumable, htransfers, hhalted, hauthority,
                  hblockingCoherent⟩
              have hliveMailbox := hcoherent.2.2.2.2.2.2.2.2.2.2.2.2
              have hexecutionFatal := latchInvalidUserReturn_preserves_wellFormed
                state.execution (authoritativeReturnRequest state.execution request)
                reason none hexecution
              have hresumableHalted : ResumablePreemption.WellFormed
                  { state.resumable with halted := true } :=
                (ResumablePreemption.wellFormed_set_halted state.resumable true).2 hresumable
              have hliveFatal :
                  ({ state with
                    execution := (latchInvalidUserReturn state.execution
                      (authoritativeReturnRequest state.execution request) reason none).state
                    resumable := { state.resumable with halted := true } }).ReturnPlanLive = true := by
                simpa [CompositeState.ReturnPlanLive, latchInvalidUserReturn] using hlive
              simp_all [gate, applyOperation, completeUserReturn, latchInvalidUserReturn,
                RuntimeWellFormed, CompositeState.Coherent,
                ResumablePreemption.wellFormed_set_halted]
              exact ⟨hliveMailbox,
                by simpa [CompositeState.BlockingIPCCoherent] using hblockingCoherent.1⟩
    · rcases hstate with
        ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
          hscheduler, hpreemption, hresumable, htransfers, hhalted, hauthority,
          hblockingCoherent⟩
      have hliveMailbox := hcoherent.2.2.2.2.2.2.2.2.2.2.2.2
      rcases hexecution with ⟨hcore, _hbound, hexecutionMode⟩
      have hexecutionPrepared : WellFormed
          { state.execution with returnAuthorityArmed := false } :=
        ⟨hcore, by simp, hexecutionMode⟩
      have hexecutionFatal := latchInvalidUserReturn_preserves_wellFormed
        { state.execution with returnAuthorityArmed := false }
        request .unselectedAuthority none hexecutionPrepared
      have hresumableHalted : ResumablePreemption.WellFormed
          { state.resumable with halted := true } :=
        (ResumablePreemption.wellFormed_set_halted state.resumable true).2 hresumable
      simp_all [gate, applyOperation, completeUserReturn, latchInvalidUserReturn,
        RuntimeWellFormed, CompositeState.Coherent,
        ResumablePreemption.wellFormed_set_halted]
      exact ⟨hliveMailbox,
        by simpa [CompositeState.BlockingIPCCoherent] using hblockingCoherent.1⟩
  · cases hactual : state.execution.mode with
    | running => exact False.elim (hmode hactual)
    | handling active => simpa [gate, hactual] using hstate
    | halted record => simpa [gate, hactual] using hstate

/-- Restart is the identity running operation and therefore preserves the full
runtime invariant without touching any authoritative subsystem state. -/
theorem gate_restart_preserves_runtimeWellFormed state
    (hstate : RuntimeWellFormed state) :
    RuntimeWellFormed (gate state .restart).state := by
  cases hmode : state.execution.mode with
  | running => simpa [gate, hmode, applyOperation] using hstate
  | handling active => simpa [gate, hmode] using hstate
  | halted record => simpa [gate, hmode] using hstate

/-- An accepted access-only syscall leaves virtual memory unchanged and only
reselects return authority through the live-plan boundary.  Consequently the
complete runtime invariant, not merely virtual-memory well-formedness, survives
the accepted public operation and its reply is the exact typed success. -/
theorem gate_syscall_access_accepted_preserves_runtimeWellFormed state call page access
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hdecode : Syscall.decode call = .ok (.access page access))
    (haccepted : (Syscall.dispatch state.virtualMemory state.syscallContext call).reply =
      .accepted) :
    RuntimeWellFormed (gate state (.syscall call)).state ∧
      (gate state (.syscall call)).result = .completed (.syscall .accepted) := by
  have hselected := gate_selectUserReturn_preserves_runtimeWellFormed
    state .syscallResume hstate
  have hselected' :
      RuntimeWellFormed (selectLiveReturnAuthority state .syscallResume) := by
    simpa [gate, hmode, applyOperation] using hselected
  constructor
  · simpa [gate, hmode, applyOperation, haccepted, hdecode] using hselected'
  · simp [gate, hmode, operationReply, haccepted]

/-- The guarded sealed-mailbox rejection is a genuine composite gate
preservation step: it retains the full global runtime invariant, rather than
repairing one projection after consuming the envelope. -/
theorem gate_sealed_receive_preserves_runtimeWellFormed state handleWord endpoint transfer
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hresolve : CapabilityHandle.resolveCurrent state.transfers.capabilities
      { caller := state.execution.core.context.currentSubject }
      handleWord .endpoint = .ok endpoint)
    (hpending : state.transfers.pending endpoint.capability.object = some transfer) :
    RuntimeWellFormed (gate state (.ipc (.receive handleWord))).state ∧
      (gate state (.ipc (.receive handleWord))).result =
        .completed (.ipc .sealedTransferPending) := by
  have hguard := ipc_receive_preserves_sealed_transfer state handleWord endpoint transfer
    hresolve hpending
  simp [gate, hmode, applyOperation, operationReply, hguard, hstate]

private theorem endpointSend_capabilities_unchanged state caller slot payload :
    (EndpointIPC.send state caller slot payload).state.capabilities = state.capabilities := by
  simp only [EndpointIPC.send]
  split <;> try rfl
  next cap => split <;> try rfl
              split <;> try rfl
              split <;> try rfl
              split <;> try rfl
              split <;> rfl

private theorem endpointSend_preserves_occupied_mailbox state caller slot payload
    endpoint envelope (hmail : state.mailbox endpoint = some envelope) :
    (EndpointIPC.send state caller slot payload).state.mailbox endpoint = some envelope := by
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

private theorem endpointSend_preserves_live_senders state caller slot payload
    (hwellFormed : Capability.WellFormed state.capabilities)
    (hlive : ∀ object envelope, state.mailbox object = some envelope →
      state.capabilities.subjects envelope.sender = true) :
    ∀ object envelope,
      (EndpointIPC.send state caller slot payload).state.mailbox object = some envelope →
        (EndpointIPC.send state caller slot payload).state.capabilities.subjects
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
          (Capability.lookup_found_slot state.capabilities caller slot cap hlookup)).1
      · exact hlive object envelope (by simpa [EndpointIPC.setOption, heq] using hmail)

private theorem endpointReceive_capabilities_unchanged state caller slot :
    (EndpointIPC.receive state caller slot).state.capabilities = state.capabilities := by
  simp only [EndpointIPC.receive]
  split <;> try rfl
  next cap => split <;> try rfl
              split <;> try rfl
              split <;> try rfl
              split <;> try rfl
              split <;> rfl

private theorem endpointReceive_preserves_other_mailbox state caller slot selected
    endpoint envelope
    (hlookup : Capability.lookup state.capabilities caller slot = .found selected)
    (hne : endpoint ≠ selected.object)
    (hmail : state.mailbox endpoint = some envelope) :
    (EndpointIPC.receive state caller slot).state.mailbox endpoint = some envelope := by
  simp only [EndpointIPC.receive, hlookup]
  split <;> try simpa [EndpointIPC.rejectReceive] using hmail
  split <;> try simpa [EndpointIPC.rejectReceive] using hmail
  split <;> try simpa [EndpointIPC.rejectReceive] using hmail
  split <;> try simpa [EndpointIPC.rejectReceive] using hmail
  split <;> try simpa [EndpointIPC.rejectReceive] using hmail
  next queued hqueued => simpa [EndpointIPC.setOption, hne] using hmail

private theorem endpointReceive_mailbox_provenance state caller slot endpoint envelope
    (hmail : (EndpointIPC.receive state caller slot).state.mailbox endpoint = some envelope) :
    state.mailbox endpoint = some envelope := by
  simp only [EndpointIPC.receive] at hmail
  split at hmail <;> try simpa [EndpointIPC.rejectReceive] using hmail
  next cap hlookup =>
    split at hmail <;> try simpa [EndpointIPC.rejectReceive] using hmail
    split at hmail <;> try simpa [EndpointIPC.rejectReceive] using hmail
    split at hmail <;> try simpa [EndpointIPC.rejectReceive] using hmail
    split at hmail <;> try simpa [EndpointIPC.rejectReceive] using hmail
    split at hmail <;> try simpa [EndpointIPC.rejectReceive] using hmail
    next queued hqueued =>
      by_cases heq : endpoint = cap.object
      · subst endpoint
        simp [EndpointIPC.setOption] at hmail
      · simpa [EndpointIPC.setOption, heq] using hmail

/-- A successful data send is one complete global-invariant mutation.  The
endpoint post-state is published to both the IPC and sealed-transfer views,
while the latter's pending attachment map is retained exactly. -/
theorem gate_ipc_send_accepted_preserves_runtimeWellFormed state handleWord word0 word1
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hsent : (dispatchIPC state (.send handleWord word0 word1)).reply =
      .syscall .sent) :
    RuntimeWellFormed (gate state (.ipc (.send handleWord word0 word1))).state ∧
      (gate state (.ipc (.send handleWord word0 word1))).result =
        .completed (.ipc (.syscall .sent)) := by
  rcases hstate with
    ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
      hscheduler, hpreemption, hresumable, htransfers, hhalted, hlive⟩
  rcases hcoherent with
    ⟨hexecLife, hschedulerLife, hpreemptionScheduler, hcapsLife,
      hmemoryCaps, hipcVirtual, hipcCaps, hresumableScheduler,
      htranslationVirtual, htransferEndpoints, hcontext, hdead, hsender⟩
  cases hresolve : CapabilityHandle.resolveCurrent state.ipc.endpoints.capabilities
      { caller := state.execution.core.context.currentSubject }
      handleWord .endpoint with
  | error reason => simp [dispatchIPC, IPCSyscall.dispatch, hresolve] at hsent
  | ok resolution =>
      cases hsend : EndpointIPC.send state.ipc.endpoints
          state.execution.core.context.currentSubject resolution.handle.slot
          { word0, word1 } with
      | mk endpoints result =>
          cases result with
          | rejected reason =>
              simp [dispatchIPC, IPCSyscall.dispatch, hresolve, hsend] at hsent
          | accepted =>
              have hdispatch :
                  IPCSyscall.dispatch state.ipc state.ipcContext
                    (.send handleWord word0 word1) =
                    { state := { state.ipc with endpoints }
                      reply := .sent } := by
                simp [IPCSyscall.dispatch, hresolve, hsend]
              have hcapEq : endpoints.capabilities = state.ipc.endpoints.capabilities := by
                simpa [hsend] using endpointSend_capabilities_unchanged
                  state.ipc.endpoints state.execution.core.context.currentSubject
                  resolution.handle.slot { word0, word1 }
              have hipc' : IPCSyscall.WellFormed
                  (IPCSyscall.dispatch state.ipc state.ipcContext
                    (.send handleWord word0 word1)).state :=
                IPCSyscall.dispatch_preserves_wellFormed state.ipc state.ipcContext
                  (.send handleWord word0 word1) hipc
              have hendpoint : EndpointIPC.WellFormed endpoints := by
                have preserved := EndpointIPC.send_preserves_wellFormed state.ipc.endpoints
                  state.execution.core.context.currentSubject resolution.handle.slot
                  { word0, word1 } hipc.2
                simpa [hsend] using preserved
              have htransfers' : CapabilityTransfer.WellFormed
                  { state.transfers with toEndpointState := endpoints } := by
                refine ⟨hendpoint, ?_⟩
                intro endpoint transfer hpending
                have hold := htransfers.2 endpoint transfer hpending
                rcases hold with ⟨⟨envelope, hmailbox, henvelope⟩, hrest⟩
                rw [htransferEndpoints] at hmailbox
                refine ⟨⟨envelope, ?_, henvelope⟩, ?_⟩
                · simpa [hsend] using
                    endpointSend_preserves_occupied_mailbox
                      state.ipc.endpoints
                      state.execution.core.context.currentSubject
                      resolution.handle.slot { word0, word1 } endpoint envelope hmailbox
                · simpa [htransferEndpoints, hcapEq] using hrest
              have hcoherent' :
                  (installIPC state
                    (IPCSyscall.dispatch state.ipc state.ipcContext
                      (.send handleWord word0 word1)).state).Coherent := by
                simp only [CompositeState.Coherent, installIPC]
                refine ⟨hexecLife, hschedulerLife, hpreemptionScheduler, hcapsLife,
                  hmemoryCaps, ?_, ?_, hresumableScheduler, htranslationVirtual, ?_,
                  hcontext, ?_, ?_⟩
                · simpa [IPCSyscall.dispatch, hresolve, hsend] using hipcVirtual
                · simpa [hdispatch, hcapEq] using hipcCaps
                · simp [IPCSyscall.dispatch, hresolve, hsend]
                · intro object hnotLive
                  simpa [hdispatch] using
                    hendpoint.2.2.2.1 object (by simpa [hcapEq, hipcCaps] using hnotLive)
                · intro object envelope hmail
                  have hliveSender := endpointSend_preserves_live_senders state.ipc.endpoints
                    state.execution.core.context.currentSubject resolution.handle.slot
                    { word0, word1 } hipc.2.1 (by
                      intro priorObject priorEnvelope hprior
                      simpa [hipcCaps] using hsender priorObject priorEnvelope hprior)
                    object envelope (by simpa [hdispatch, hsend] using hmail)
                  simpa [hsend, hcapEq, hipcCaps] using hliveSender
              constructor
              · rw [hdispatch] at hipc' hcoherent'
                simpa [gate, hmode, applyOperation, dispatchIPC, IPCSyscall.dispatch,
                  hresolve, hsend, installIPC, hdispatch] using
                  ⟨hcoherent', hexecution, hlifecycle, hcapabilities, hvirtual, hipc',
                    hscheduler, hpreemption, hresumable, htransfers', hhalted, hlive⟩
              · simp [gate, hmode, operationReply, dispatchIPC, IPCSyscall.dispatch,
                  hresolve, hsend]

/-- A successful data-only receive consumes exactly the selected untagged
mailbox while retaining every sealed attachment at every other endpoint.  The
updated endpoint state is published to both IPC views and preserves the full
runtime invariant together with the exact provenance-bearing delivery reply. -/
theorem gate_ipc_receive_accepted_preserves_runtimeWellFormed state handleWord sender word0 word1
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hdelivered : (dispatchIPC state (.receive handleWord)).reply =
      .syscall (.delivered sender word0 word1)) :
    RuntimeWellFormed (gate state (.ipc (.receive handleWord))).state ∧
      (gate state (.ipc (.receive handleWord))).result =
        .completed (.ipc (.syscall (.delivered sender word0 word1))) := by
  rcases hstate with
    ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
      hscheduler, hpreemption, hresumable, htransfers, hhalted, hlive⟩
  rcases hcoherent with
    ⟨hexecLife, hschedulerLife, hpreemptionScheduler, hcapsLife,
      hmemoryCaps, hipcVirtual, hipcCaps, hresumableScheduler,
      htranslationVirtual, htransferEndpoints, hcontext, hdead, hsender⟩
  have htransferCaps : state.transfers.capabilities = state.ipc.endpoints.capabilities := by
    simp [htransferEndpoints]
  cases hguard : CapabilityHandle.resolveCurrent state.transfers.capabilities
      { caller := state.execution.core.context.currentSubject }
      handleWord .endpoint with
  | error guardReason =>
      have hguard' : CapabilityHandle.resolveCurrent state.ipc.endpoints.capabilities
          { caller := state.execution.core.context.currentSubject }
          handleWord .endpoint = .error guardReason := by
        simpa [htransferCaps] using hguard
      simp [dispatchIPC, IPCSyscall.dispatch, hguard, hguard'] at hdelivered
  | ok guarded =>
      cases hpending : state.transfers.pending guarded.capability.object with
      | some transfer =>
          simp [dispatchIPC, hguard, hpending] at hdelivered
      | none =>
          have hresolve : CapabilityHandle.resolveCurrent state.ipc.endpoints.capabilities
              { caller := state.execution.core.context.currentSubject }
              handleWord .endpoint = .ok guarded := by
            simpa [htransferCaps] using hguard
          have hsound := CapabilityHandle.resolveCurrent_sound
            state.ipc.endpoints.capabilities
            { caller := state.execution.core.context.currentSubject }
            handleWord .endpoint guarded hresolve
          have hlookup : Capability.lookup state.ipc.endpoints.capabilities
              state.execution.core.context.currentSubject guarded.handle.slot =
              .found guarded.capability := by
            rcases hsound with ⟨_, hsubject, hrange, hslot, _⟩
            simp [Capability.lookup, hsubject, hrange, hslot]
          cases hreceive : EndpointIPC.receive state.ipc.endpoints
              state.execution.core.context.currentSubject guarded.handle.slot with
          | mk endpoints result =>
              cases result with
              | rejected reason =>
                  simp [dispatchIPC, IPCSyscall.dispatch, hguard, hpending,
                    hresolve, hreceive] at hdelivered
              | delivered envelope =>
                  have henvelope : envelope.sender = sender ∧
                      envelope.payload.word0 = word0 ∧ envelope.payload.word1 = word1 := by
                    simpa [dispatchIPC, IPCSyscall.dispatch, hguard, hpending,
                      hresolve, hreceive] using hdelivered
                  have hdispatch :
                      IPCSyscall.dispatch state.ipc state.ipcContext (.receive handleWord) =
                        { state := { state.ipc with endpoints }
                          reply := .delivered sender word0 word1 } := by
                    rcases henvelope with ⟨rfl, rfl, rfl⟩
                    simp [IPCSyscall.dispatch, hresolve, hreceive]
                  have hcapEq : endpoints.capabilities = state.ipc.endpoints.capabilities := by
                    simpa [hreceive] using endpointReceive_capabilities_unchanged
                      state.ipc.endpoints state.execution.core.context.currentSubject
                      guarded.handle.slot
                  have hipc' : IPCSyscall.WellFormed
                      (IPCSyscall.dispatch state.ipc state.ipcContext
                        (.receive handleWord)).state :=
                    IPCSyscall.dispatch_preserves_wellFormed state.ipc state.ipcContext
                      (.receive handleWord) hipc
                  have hendpoint : EndpointIPC.WellFormed endpoints := by
                    have preserved := EndpointIPC.receive_preserves_wellFormed
                      state.ipc.endpoints state.execution.core.context.currentSubject
                      guarded.handle.slot hipc.2
                    simpa [hreceive] using preserved
                  have htransfers' : CapabilityTransfer.WellFormed
                      { state.transfers with toEndpointState := endpoints } := by
                    refine ⟨hendpoint, ?_⟩
                    intro endpoint transfer hotherPending
                    have hold := htransfers.2 endpoint transfer hotherPending
                    rcases hold with ⟨⟨priorEnvelope, hmailbox, henvelope'⟩, hrest⟩
                    have hne : endpoint ≠ guarded.capability.object := by
                      intro heq
                      subst endpoint
                      rw [hpending] at hotherPending
                      contradiction
                    rw [htransferEndpoints] at hmailbox
                    refine ⟨⟨priorEnvelope, ?_, henvelope'⟩, ?_⟩
                    · simpa [hreceive] using endpointReceive_preserves_other_mailbox
                        state.ipc.endpoints state.execution.core.context.currentSubject
                        guarded.handle.slot guarded.capability endpoint priorEnvelope
                        hlookup hne hmailbox
                    · simpa [htransferEndpoints, hcapEq] using hrest
                  have hcoherent' :
                      (installIPC state
                        (IPCSyscall.dispatch state.ipc state.ipcContext
                          (.receive handleWord)).state).Coherent := by
                    simp only [CompositeState.Coherent, installIPC]
                    refine ⟨hexecLife, hschedulerLife, hpreemptionScheduler, hcapsLife,
                      hmemoryCaps, ?_, ?_, hresumableScheduler, htranslationVirtual, ?_,
                      hcontext, ?_, ?_⟩
                    · simpa [IPCSyscall.dispatch, hresolve, hreceive] using hipcVirtual
                    · simpa [hdispatch, hcapEq] using hipcCaps
                    · simp [IPCSyscall.dispatch, hresolve, hreceive]
                    · intro object hnotLive
                      simpa [hdispatch] using
                        hendpoint.2.2.2.1 object (by simpa [hcapEq, hipcCaps] using hnotLive)
                    · intro object found hmail
                      have hnext : endpoints.mailbox object = some found := by
                        simpa [hdispatch] using hmail
                      have hprior := endpointReceive_mailbox_provenance
                        state.ipc.endpoints state.execution.core.context.currentSubject
                        guarded.handle.slot object found (by simpa [hreceive] using hnext)
                      exact hsender object found hprior
                  constructor
                  · rw [hdispatch] at hipc' hcoherent'
                    simpa [gate, hmode, applyOperation, dispatchIPC, hguard, hpending,
                      IPCSyscall.dispatch, hresolve, hreceive, installIPC, hdispatch] using
                      ⟨hcoherent', hexecution, hlifecycle, hcapabilities, hvirtual, hipc',
                        hscheduler, hpreemption, hresumable, htransfers', hhalted, hlive⟩
                  · simpa [gate, hmode, operationReply, dispatchIPC, hguard, hpending,
                      IPCSyscall.dispatch, hresolve, hreceive, hdispatch] using henvelope

/-- An accepted public transfer offer is backed by a whole-invariant
preserving sealed-transfer mutation and is reported as that exact typed
success by the composite gate.  The remaining global lift is isolated to the
publication laws of `installTransfers`, rather than the authority transition. -/
theorem gate_transferOffer_accepted_preserves_transferWellFormed state endpointWord sourceWord
    sourceKind payload rights
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : (CapabilityTransfer.offerWords state.transfers
      state.execution.core.context.currentSubject endpointWord sourceWord sourceKind
      payload rights).result = .accepted) :
    CapabilityTransfer.WellFormed
        (CapabilityTransfer.offerWords state.transfers
          state.execution.core.context.currentSubject endpointWord sourceWord sourceKind
          payload rights).state ∧
      (gate state (.transferOffer endpointWord sourceWord sourceKind payload rights)).result =
        .completed (.transferOffer .accepted) := by
  constructor
  · exact CapabilityTransfer.offerWords_accepted_preserves_wellFormed
      state.transfers state.execution.core.context.currentSubject endpointWord sourceWord
      sourceKind payload rights hstate.2.2.2.2.2.2.2.2.2.1 haccepted
  · simp [gate, hmode, operationReply, applyOperation, haccepted]

/-- An accepted sealed-transfer offer is monotonic in the live authority
registry.  Publishing its exact capability and endpoint post-state therefore
preserves every composite consumer, while retaining the pending sealed
descendant and mailbox as one atomic transfer state. -/
theorem gate_transferOffer_accepted_preserves_runtimeWellFormed state endpointWord sourceWord
    sourceKind payload rights
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : (CapabilityTransfer.offerWords state.transfers
      state.execution.core.context.currentSubject endpointWord sourceWord sourceKind
      payload rights).result = .accepted) :
    RuntimeWellFormed
        (gate state (.transferOffer endpointWord sourceWord sourceKind payload rights)).state ∧
      (gate state (.transferOffer endpointWord sourceWord sourceKind payload rights)).result =
        .completed (.transferOffer .accepted) := by
  let next := (CapabilityTransfer.offerWords state.transfers
    state.execution.core.context.currentSubject endpointWord sourceWord sourceKind
    payload rights).state
  have htransfer : CapabilityTransfer.WellFormed next :=
    CapabilityTransfer.offerWords_accepted_preserves_wellFormed state.transfers
      state.execution.core.context.currentSubject endpointWord sourceWord sourceKind
      payload rights hstate.2.2.2.2.2.2.2.2.2.1 haccepted
  have hregistry := CapabilityTransfer.offerWords_accepted_preserves_authority_registry
    state.transfers state.execution.core.context.currentSubject endpointWord sourceWord
    sourceKind payload rights haccepted
  change next.capabilities.subjects = state.transfers.capabilities.subjects ∧
      next.capabilities.objects = state.transfers.capabilities.objects ∧
      next.capabilities.kinds = state.transfers.capabilities.kinds ∧
      next.capabilities.slots = state.transfers.capabilities.slots ∧
      next.allocator = state.transfers.allocator ∧
      next.binding = state.transfers.binding ∧
      next.issued = state.transfers.issued ∧
      next.issuedAddressSpace = state.transfers.issuedAddressSpace at hregistry
  rcases hregistry with ⟨hsubjects, hobjects, hkinds, hslots, hallocator,
    hbinding, hissued, hissuedSpace⟩
  rcases hstate with
    ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
      hscheduler, hpreemption, hresumable, _htransfers, hhalted, hlive⟩
  rcases hcoherent with
    ⟨hexecutionCoherent, hschedulerCoherent, hpreemptionCoherent,
      hcapabilitiesCoherent, hvirtualCapabilitiesCoherent, hipcVirtualCoherent,
      hipcCapabilitiesCoherent, hresumableSchedulerCoherent,
      hresumableVirtualCoherent, htransfersCoherent, hauthorityCoherent,
      hdeadMailbox, hliveSender⟩
  rw [htransfersCoherent] at hsubjects hobjects hkinds hslots hallocator hbinding
  rw [htransfersCoherent] at hissued hissuedSpace
  have hsubjectsLifecycle := hsubjects.trans
    (congrArg Capability.State.subjects hipcCapabilitiesCoherent)
  have hobjectsLifecycle := hobjects.trans
    (congrArg Capability.State.objects hipcCapabilitiesCoherent)
  have hkindsLifecycle := hkinds.trans
    (congrArg Capability.State.kinds hipcCapabilitiesCoherent)
  have hslotsLifecycle := hslots.trans
    (congrArg Capability.State.slots hipcCapabilitiesCoherent)
  have hsubjectsVirtual := hsubjectsLifecycle.trans
    (congrArg Capability.State.subjects hvirtualCapabilitiesCoherent).symm
  have hobjectsVirtual := hobjectsLifecycle.trans
    (congrArg Capability.State.objects hvirtualCapabilitiesCoherent).symm
  have hkindsVirtual := hkindsLifecycle.trans
    (congrArg Capability.State.kinds hvirtualCapabilitiesCoherent).symm
  have hslotsVirtual := hslotsLifecycle.trans
    (congrArg Capability.State.slots hvirtualCapabilitiesCoherent).symm
  have hcallerTransfer : state.transfers.capabilities.subjects
      state.execution.core.context.currentSubject = true :=
    CapabilityTransfer.offerWords_accepted_caller_live state.transfers
      state.execution.core.context.currentSubject endpointWord sourceWord sourceKind payload rights
      haccepted
  have htransferCapabilitiesCoherent :
      state.transfers.capabilities = state.lifecycle.capabilities := by
    rw [htransfersCoherent, hipcCapabilitiesCoherent]
  have hsenderTransfer : ∀ object envelope,
      state.transfers.mailbox object = some envelope →
        state.transfers.capabilities.subjects envelope.sender = true := by
    intro object envelope hmailbox
    rw [htransferCapabilitiesCoherent]
    exact hliveSender object envelope (by simpa [htransfersCoherent] using hmailbox)
  have hliveMailbox' :=
    CapabilityTransfer.offerWords_accepted_preserves_live_mailbox_senders state.transfers
      state.execution.core.context.currentSubject endpointWord sourceWord sourceKind payload rights
      hcallerTransfer hsenderTransfer haccepted
  have hcapabilities' : Capability.WellFormed next.capabilities := htransfer.1.1
  have hlifecycle' : SubjectLifecycle.WellFormed
      { state.lifecycle with capabilities := next.capabilities } := by
    simpa [SubjectLifecycle.WellFormed, hsubjectsLifecycle] using hlifecycle
  have hvirtual' : VirtualMapping.LifecycleWellFormed
      { state.virtualMemory with
        memory := { state.virtualMemory.memory with capabilities := next.capabilities } } := by
    rcases hvirtual with ⟨hwell, _hcaps, hspaces, howned⟩
    refine ⟨?_, hcapabilities', ?_, ?_⟩
    · simpa [VirtualMapping.WellFormed, Capability.HasAuthority, hsubjectsVirtual,
        hslotsVirtual]
        using hwell
    · simpa [Capability.HasAuthority, hobjectsVirtual, hkindsVirtual, hslotsVirtual]
        using hspaces
    · simpa [hobjectsVirtual, hkindsVirtual] using howned
  have hipc' : IPCSyscall.WellFormed
      { state.ipc with
        virtualMemory := { state.virtualMemory with
          memory := { state.virtualMemory.memory with capabilities := next.capabilities } }
        endpoints := next.toEndpointState } := ⟨hvirtual', htransfer.1⟩
  have hscheduler' : Scheduler.WellFormed
      { state.scheduler with lifecycle :=
        { state.lifecycle with capabilities := next.capabilities } } := by
    rcases hscheduler with ⟨_, hnodup, hcapacity, hready, hcurrent⟩
    refine ⟨hlifecycle', hnodup, hcapacity, ?_, ?_⟩
    · simpa [Scheduler.ownsAddressSpace, hschedulerCoherent, hsubjectsLifecycle]
        using hready
    · simpa [Scheduler.ownsAddressSpace, hschedulerCoherent, hsubjectsLifecycle]
        using hcurrent
  have hpreemption' : Preemption.WellFormed
      { state.preemption with scheduler :=
        { state.scheduler with lifecycle :=
          { state.lifecycle with capabilities := next.capabilities } } } :=
    ⟨hscheduler', hpreemption.2⟩
  have hresumable' : ResumablePreemption.WellFormed
      { state.resumable with
        scheduler := { state.scheduler with lifecycle :=
          { state.lifecycle with capabilities := next.capabilities } }
        translations := { state.resumable.translations with virtual :=
          { state.virtualMemory with memory :=
            { state.virtualMemory.memory with capabilities := next.capabilities } } } } := by
    rcases hresumable with
      ⟨_, hcapacity, hunique, hvalid, habsent, hready, htranslation,
        _hvirtual, hresources, htlb⟩
    refine ⟨hscheduler', hcapacity, hunique, ?_, ?_, ?_, ?_, ⟨rfl, hvirtual'⟩, ?_, ?_⟩
    · simpa [ResumablePreemption.validContext, hresumableSchedulerCoherent,
        hschedulerCoherent, hsubjectsLifecycle] using hvalid
    · simpa [hresumableSchedulerCoherent, hschedulerCoherent] using habsent
    · simpa [ResumablePreemption.ReadyContextAgreement, hresumableSchedulerCoherent,
        hschedulerCoherent] using hready
    · simpa [ResumablePreemption.TranslationAgreement, hresumableVirtualCoherent,
        hresumableSchedulerCoherent, hschedulerCoherent] using htranslation
    · simpa [ResumablePreemption.ResourceKindAgreement, hresumableSchedulerCoherent,
        hschedulerCoherent, hkindsLifecycle] using hresources
    · simpa [TLB.Coherent] using htlb
  have hexecution' : WellFormed
      { state.execution with
        core := { state.execution.core with lifecycle :=
          { state.lifecycle with capabilities := next.capabilities } }
        returnAuthorityArmed := false } := by
    rcases hexecution with ⟨_, _hbound, hmodeWellFormed⟩
    refine ⟨?_, by simp, ?_⟩
    · simpa [Interrupt.WellFormed] using hlifecycle'
    · simpa using hmodeWellFormed
  constructor
  · simp only [gate, hmode, applyOperation, haccepted]
    refine ⟨?_, hexecution', hlifecycle', hcapabilities', hvirtual', hipc',
      hscheduler', hpreemption', hresumable', htransfer, ?_, ?_⟩
    · simp [installTransfers, CompositeState.Coherent]
      refine ⟨?_, ?_, ?_⟩
      · intro subject hcurrent
        exact hauthorityCoherent subject hcurrent
      · intro object hfalse
        apply htransfer.1.2.2.2.1 object
        intro htrue
        have hfalse' : next.capabilities.objects object = false := by
          simpa [next] using hfalse
        rw [htrue] at hfalse'
        contradiction
      · intro object envelope hmailbox
        exact hliveMailbox' object envelope hmailbox
    · simpa [installTransfers] using hhalted
    · exact ⟨by simp [installTransfers], ⟨⟨rfl, rfl⟩, hlive.2.2⟩⟩
  · simp [gate, hmode, operationReply, haccepted]

/-- An accepted public transfer receipt preserves the authoritative capability
invariant and reports the exact provenance-bearing envelope and installed
generation word.  This closes the capability-store slice needed before the
stronger whole-runtime publication theorem for `installTransfers`. -/
theorem gate_transferAccept_delivered_preserves_capabilityWellFormed state endpointWord
    destinationSlot envelope
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hdelivered : (CapabilityTransfer.acceptWord state.transfers
      state.execution.core.context.currentSubject endpointWord destinationSlot).result =
        .delivered envelope) :
    Capability.WellFormed
        (CapabilityTransfer.acceptWord state.transfers
          state.execution.core.context.currentSubject endpointWord destinationSlot).state.capabilities ∧
      (gate state (.transferAccept endpointWord destinationSlot)).result =
        .completed (.transferAccept (.delivered envelope)
          (CapabilityTransfer.acceptWord state.transfers
            state.execution.core.context.currentSubject endpointWord
            destinationSlot).deliveredWord) := by
  have htransfer := hstate.2.2.2.2.2.2.2.2.2.1
  cases hendpoint : CapabilityHandle.resolveCurrent state.transfers.capabilities
      { caller := state.execution.core.context.currentSubject }
      endpointWord .endpoint with
  | error reason =>
      cases reason with
      | malformed decodeReason =>
          simp [CapabilityTransfer.acceptWord, hendpoint,
            CapabilityTransfer.rejectAccept] at hdelivered
      | denied resolveReason =>
          cases resolveReason <;>
            simp [CapabilityTransfer.acceptWord, hendpoint,
              CapabilityTransfer.rejectAccept] at hdelivered
  | ok endpoint =>
      cases hpending : state.transfers.pending endpoint.capability.object with
      | none =>
          have hpreserved := CapabilityTransfer.accept_preserves_capabilityWellFormed
            state.transfers state.execution.core.context.currentSubject endpoint.handle.slot
            destinationSlot htransfer
          constructor
          · simpa [CapabilityTransfer.acceptWord, hendpoint, hpending] using hpreserved
          · simp [gate, hmode, operationReply, applyOperation, hdelivered]
      | some transfer =>
          by_cases hslot : CapabilityHandle.slotReserved ≤ destinationSlot
          · simp [CapabilityTransfer.acceptWord, hendpoint, hpending, hslot,
              CapabilityTransfer.rejectAccept] at hdelivered
          · by_cases hexhausted : transfer.identity = 0 ∨
                CapabilityHandle.generationReserved ≤ transfer.identity
            · simp [CapabilityTransfer.acceptWord, hendpoint, hpending, hslot, hexhausted,
                CapabilityTransfer.rejectAccept] at hdelivered
            · have hpreserved := CapabilityTransfer.accept_preserves_capabilityWellFormed
                  state.transfers state.execution.core.context.currentSubject endpoint.handle.slot
                  destinationSlot htransfer
              constructor
              · simpa [CapabilityTransfer.acceptWord, hendpoint, hpending, hslot, hexhausted]
                  using hpreserved
              · simp [gate, hmode, operationReply, applyOperation, hdelivered]

/-- The complete sealed-transfer invariant, not only its embedded capability
store, survives every delivered public receipt.  The composite reply remains
paired with the exact state and generation word that produced it. -/
theorem gate_transferAccept_delivered_preserves_transferWellFormed state endpointWord
    destinationSlot envelope
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hdelivered : (CapabilityTransfer.acceptWord state.transfers
      state.execution.core.context.currentSubject endpointWord destinationSlot).result =
        .delivered envelope) :
    CapabilityTransfer.WellFormed
        (CapabilityTransfer.acceptWord state.transfers
          state.execution.core.context.currentSubject endpointWord destinationSlot).state ∧
      (gate state (.transferAccept endpointWord destinationSlot)).result =
        .completed (.transferAccept (.delivered envelope)
          (CapabilityTransfer.acceptWord state.transfers
            state.execution.core.context.currentSubject endpointWord
            destinationSlot).deliveredWord) := by
  constructor
  · exact CapabilityTransfer.acceptWord_preserves_wellFormed state.transfers
      state.execution.core.context.currentSubject endpointWord destinationSlot
      hstate.2.2.2.2.2.2.2.2.2.1
  · simp [gate, hmode, operationReply, applyOperation, hdelivered]

/-- Publishing a transfer transition is globally safe when it retains the
live registries and all pre-existing authority, and when every surviving
mailbox has a pre-state provenance witness.  This is the common composite
boundary used by receipt, whose only capability mutation fills a checked-empty
slot and whose only mailbox mutation consumes the selected message. -/
theorem installTransfers_preserves_runtimeWellFormed state next
    (hstate : RuntimeWellFormed state)
    (htransfer : CapabilityTransfer.WellFormed next)
    (hsubjects : next.capabilities.subjects = state.transfers.capabilities.subjects)
    (hobjects : next.capabilities.objects = state.transfers.capabilities.objects)
    (hkinds : next.capabilities.kinds = state.transfers.capabilities.kinds)
    (hauthority : ∀ subject object right,
      (right = .read ∨ right = .write ∨ right = .revoke) →
      Capability.HasAuthority state.transfers.capabilities subject object right →
        Capability.HasAuthority next.capabilities subject object right)
    (hmailbox : ∀ object envelope, next.mailbox object = some envelope →
      state.transfers.mailbox object = some envelope) :
    RuntimeWellFormed (installTransfers state next) := by
  rcases hstate with
    ⟨hcoherent, hexecution, hlifecycle, _hcapabilities, hvirtual, _hipc,
      hscheduler, hpreemption, hresumable, _htransfers, hhalted, _hlivePlan⟩
  rcases hcoherent with
    ⟨_hexecutionCoherent, hschedulerCoherent, _hpreemptionCoherent,
      _hcapabilitiesCoherent, hvirtualCapabilitiesCoherent, _hipcVirtualCoherent,
      hipcCapabilitiesCoherent, hresumableSchedulerCoherent,
      hresumableVirtualCoherent, htransfersCoherent, hauthorityCoherent,
      _hdeadMailbox, hliveSender⟩
  have hsubjectsLifecycle :
      next.capabilities.subjects = state.lifecycle.capabilities.subjects :=
    hsubjects.trans ((congrArg (fun endpoints : EndpointIPC.State =>
      endpoints.capabilities.subjects) htransfersCoherent).trans
      (congrArg Capability.State.subjects hipcCapabilitiesCoherent))
  have hobjectsLifecycle :
      next.capabilities.objects = state.lifecycle.capabilities.objects :=
    hobjects.trans ((congrArg (fun endpoints : EndpointIPC.State =>
      endpoints.capabilities.objects) htransfersCoherent).trans
      (congrArg Capability.State.objects hipcCapabilitiesCoherent))
  have hkindsLifecycle :
      next.capabilities.kinds = state.lifecycle.capabilities.kinds :=
    hkinds.trans ((congrArg (fun endpoints : EndpointIPC.State =>
      endpoints.capabilities.kinds) htransfersCoherent).trans
      (congrArg Capability.State.kinds hipcCapabilitiesCoherent))
  have hcapabilities' : Capability.WellFormed next.capabilities := htransfer.1.1
  have hlifecycle' : SubjectLifecycle.WellFormed
      { state.lifecycle with capabilities := next.capabilities } := by
    simpa [SubjectLifecycle.WellFormed, hsubjectsLifecycle] using hlifecycle
  have hvirtual' : VirtualMapping.LifecycleWellFormed
      { state.virtualMemory with
        memory := { state.virtualMemory.memory with capabilities := next.capabilities } } := by
    rcases hvirtual with ⟨⟨hownerLive, hmappings⟩, _hcapabilities,
      haddressSpaces, hownedAddressSpaces⟩
    refine ⟨⟨?_, ?_⟩, hcapabilities', ?_, ?_⟩
    · intro addressSpace subject howner
      have hold := hownerLive addressSpace subject howner
      rw [hvirtualCapabilitiesCoherent] at hold
      simpa [hsubjectsLifecycle] using hold
    · intro addressSpace page mapping hmapping
      obtain ⟨subject, frame, howner, hpermissions, hbinding, hframe,
        hread, hwrite⟩ := hmappings addressSpace page mapping hmapping
      refine ⟨subject, frame, howner, hpermissions, hbinding, hframe, ?_, ?_⟩
      · intro hpermission
        apply hauthority subject mapping.object .read (Or.inl rfl)
        rw [htransfersCoherent, hipcCapabilitiesCoherent,
          ← hvirtualCapabilitiesCoherent]
        exact hread hpermission
      · intro hpermission
        apply hauthority subject mapping.object .write (Or.inr (Or.inl rfl))
        rw [htransfersCoherent, hipcCapabilitiesCoherent,
          ← hvirtualCapabilitiesCoherent]
        exact hwrite hpermission
    · intro addressSpace subject howner
      obtain ⟨hlive, hkind, hissuedAddressSpace, hissuedMemory, hrevoke⟩ :=
        haddressSpaces addressSpace subject howner
      refine ⟨?_, ?_, hissuedAddressSpace, hissuedMemory, ?_⟩
      · rw [hvirtualCapabilitiesCoherent] at hlive
        simpa [hobjectsLifecycle] using hlive
      · rw [hvirtualCapabilitiesCoherent] at hkind
        simpa [hkindsLifecycle] using hkind
      · apply hauthority subject addressSpace .revoke (Or.inr (Or.inr rfl))
        rw [htransfersCoherent, hipcCapabilitiesCoherent,
          ← hvirtualCapabilitiesCoherent]
        exact hrevoke
    · intro addressSpace hlive hkind
      apply hownedAddressSpaces addressSpace
      · change next.capabilities.objects addressSpace = true at hlive
        rw [hobjectsLifecycle] at hlive
        rw [hvirtualCapabilitiesCoherent]
        exact hlive
      · change next.capabilities.kinds addressSpace = some .addressSpace at hkind
        rw [hkindsLifecycle] at hkind
        rw [hvirtualCapabilitiesCoherent]
        exact hkind
  have hipc' : IPCSyscall.WellFormed
      { state.ipc with
        virtualMemory := { state.virtualMemory with
          memory := { state.virtualMemory.memory with capabilities := next.capabilities } }
        endpoints := next.toEndpointState } := ⟨hvirtual', htransfer.1⟩
  have hscheduler' : Scheduler.WellFormed
      { state.scheduler with lifecycle :=
        { state.lifecycle with capabilities := next.capabilities } } := by
    rcases hscheduler with ⟨_, hnodup, hcapacity, hready, hcurrent⟩
    refine ⟨hlifecycle', hnodup, hcapacity, ?_, ?_⟩
    · simpa [Scheduler.ownsAddressSpace, hschedulerCoherent, hsubjectsLifecycle] using hready
    · simpa [Scheduler.ownsAddressSpace, hschedulerCoherent, hsubjectsLifecycle] using hcurrent
  have hpreemption' : Preemption.WellFormed
      { state.preemption with scheduler :=
        { state.scheduler with lifecycle :=
          { state.lifecycle with capabilities := next.capabilities } } } :=
    ⟨hscheduler', hpreemption.2⟩
  have hresumable' : ResumablePreemption.WellFormed
      { state.resumable with
        scheduler := { state.scheduler with lifecycle :=
          { state.lifecycle with capabilities := next.capabilities } }
        translations := { state.resumable.translations with virtual :=
          { state.virtualMemory with memory :=
            { state.virtualMemory.memory with capabilities := next.capabilities } } } } := by
    rcases hresumable with
      ⟨_, hcapacity, hunique, hvalid, habsent, hready, htranslation,
        _hvirtual, hresources, htlb⟩
    refine ⟨hscheduler', hcapacity, hunique, ?_, ?_, ?_, ?_, ⟨rfl, hvirtual'⟩, ?_, ?_⟩
    · simpa [ResumablePreemption.validContext, hresumableSchedulerCoherent,
        hschedulerCoherent, hsubjectsLifecycle] using hvalid
    · simpa [hresumableSchedulerCoherent, hschedulerCoherent] using habsent
    · simpa [ResumablePreemption.ReadyContextAgreement, hresumableSchedulerCoherent,
        hschedulerCoherent] using hready
    · simpa [ResumablePreemption.TranslationAgreement, hresumableVirtualCoherent,
        hresumableSchedulerCoherent, hschedulerCoherent] using htranslation
    · simpa [ResumablePreemption.ResourceKindAgreement, hresumableSchedulerCoherent,
        hschedulerCoherent, hkindsLifecycle] using hresources
    · simpa [TLB.Coherent] using htlb
  have hexecution' : WellFormed
      { state.execution with
        core := { state.execution.core with lifecycle :=
          { state.lifecycle with capabilities := next.capabilities } }
        returnAuthorityArmed := false } := by
    rcases hexecution with ⟨_, _hbound, hmodeWellFormed⟩
    refine ⟨?_, by simp, ?_⟩
    · simpa [Interrupt.WellFormed] using hlifecycle'
    · simpa using hmodeWellFormed
  refine ⟨?_, hexecution', hlifecycle', hcapabilities', hvirtual', hipc',
    hscheduler', hpreemption', hresumable', htransfer, ?_, ?_⟩
  · simp [installTransfers, CompositeState.Coherent]
    refine ⟨?_, ?_, ?_⟩
    · intro subject hcurrent
      exact hauthorityCoherent subject hcurrent
    · intro object hfalse
      apply htransfer.1.2.2.2.1 object
      intro htrue
      rw [htrue] at hfalse
      contradiction
    · intro object envelope hnextMailbox
      have hold := hliveSender object envelope (by
        simpa [htransfersCoherent] using hmailbox object envelope hnextMailbox)
      simpa [hsubjectsLifecycle] using hold
  · simpa [installTransfers] using hhalted
  · exact ⟨by simp [installTransfers], ⟨⟨rfl, rfl⟩, _hlivePlan.2.2⟩⟩

/-- A delivered public transfer receipt is a complete global mutation: it
atomically consumes the selected mailbox and pending tag, installs the sealed
descendant into the receiver's checked-empty slot, and preserves every
composite runtime invariant. -/
theorem gate_transferAccept_delivered_preserves_runtimeWellFormed state endpointWord
    destinationSlot envelope
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hdelivered : (CapabilityTransfer.acceptWord state.transfers
      state.execution.core.context.currentSubject endpointWord destinationSlot).result =
        .delivered envelope) :
    RuntimeWellFormed (gate state (.transferAccept endpointWord destinationSlot)).state ∧
      (gate state (.transferAccept endpointWord destinationSlot)).result =
        .completed (.transferAccept (.delivered envelope)
          (CapabilityTransfer.acceptWord state.transfers
            state.execution.core.context.currentSubject endpointWord
            destinationSlot).deliveredWord) := by
  let next := (CapabilityTransfer.acceptWord state.transfers
    state.execution.core.context.currentSubject endpointWord destinationSlot).state
  have htransfer : CapabilityTransfer.WellFormed next :=
    CapabilityTransfer.acceptWord_preserves_wellFormed state.transfers
      state.execution.core.context.currentSubject endpointWord destinationSlot
      hstate.2.2.2.2.2.2.2.2.2.1
  have hmetadata := CapabilityTransfer.acceptWord_delivered_preserves_registry_and_authority
    state.transfers state.execution.core.context.currentSubject endpointWord destinationSlot
      envelope hdelivered
  change next.capabilities.subjects = state.transfers.capabilities.subjects ∧
      next.capabilities.objects = state.transfers.capabilities.objects ∧
      next.capabilities.kinds = state.transfers.capabilities.kinds ∧
      next.capabilities.slotCapacity = state.transfers.capabilities.slotCapacity ∧
      (∀ subject slot capability,
        state.transfers.capabilities.slots subject slot = some capability →
          next.capabilities.slots subject slot = some capability) ∧
      (∀ subject object right,
        Capability.HasAuthority state.transfers.capabilities subject object right →
          Capability.HasAuthority next.capabilities subject object right) at hmetadata
  rcases hmetadata with ⟨hsubjects, hobjects, hkinds, _hcapacity, _hslots, hauthority⟩
  constructor
  · simp only [gate, hmode, applyOperation, hdelivered]
    exact installTransfers_preserves_runtimeWellFormed state next hstate htransfer
      hsubjects hobjects hkinds (fun subject object right _ hold =>
        hauthority subject object right hold) (by
        intro object found hmailbox
        exact CapabilityTransfer.acceptWord_mailbox_provenance state.transfers
          state.execution.core.context.currentSubject endpointWord destinationSlot
          object found (by simpa [next] using hmailbox))
  · simp [gate, hmode, operationReply, hdelivered]

/-- Busy and terminal rejection are invariant-preserving for every operation;
neither path invokes a synchronization helper or a subsystem transition. -/
theorem gate_rejected_mode_preserves_runtimeWellFormed state operation
    (hstate : RuntimeWellFormed state)
    (hnotRunning : state.execution.mode ≠ .running) :
    RuntimeWellFormed (gate state operation).state := by
  cases hmode : state.execution.mode with
  | running => exact False.elim (hnotRunning hmode)
  | handling active =>
      cases operation with
      | nmi raw context =>
          simpa [gate, hmode] using applyNmi_preserves_runtimeWellFormed
            state raw context hstate
      | _ => simpa [gate, hmode] using hstate
  | halted record => cases operation <;> simpa [gate, hmode] using hstate

/-- An accepted queue insertion is a sound composite mutation: its public
reply is the scheduler's accepted reply, its scheduler projection is the exact
subsystem post-state, and that projection remains well formed. -/
theorem gate_scheduleAdd_accepted_sound state subject context next
    (hmode : state.execution.mode = .running)
    (haccepted : schedulerAdmission state subject =
      { state := next, result := .accepted context })
    (hwellFormed : Scheduler.WellFormed state.scheduler) :
    (gate state (.scheduleAdd subject)).result =
        .completed (.scheduler (.accepted context)) ∧
      (gate state (.scheduleAdd subject)).state.scheduler = next ∧
      Scheduler.WellFormed (gate state (.scheduleAdd subject)).state.scheduler := by
  obtain ⟨_hnotRetained, hadd, _hsaved⟩ := schedulerAdmission_accepted_exact
    state subject context next haccepted
  have hpreserved := Scheduler.add_preserves_wellFormed state.scheduler subject hwellFormed
  rw [hadd] at hpreserved
  simp [gate, hmode, operationReply, applyOperation, haccepted,
    installSchedulerAdmission, hpreserved]

/-- The only accepted raw dispatch is empty selection, whose exact scheduler
post-state is the unchanged authoritative scheduler. -/
theorem gate_scheduleNext_accepted_sound state context next
    (hmode : state.execution.mode = .running)
    (haccepted : schedulerDispatch state =
      { state := next, result := .accepted context })
    (hwellFormed : Scheduler.WellFormed state.scheduler) :
    (gate state .scheduleNext).result =
        .completed (.scheduler (.accepted context)) ∧
      (gate state .scheduleNext).state.scheduler = next ∧
      Scheduler.WellFormed (gate state .scheduleNext).state.scheduler := by
  have hnone : context = none := schedulerDispatch_accepted_is_none state context (by
    simp [haccepted])
  subst context
  have hnext : next = state.scheduler := by
    have hold := schedulerDispatch_accepted_none_unchanged state (by simp [haccepted])
    simpa [haccepted] using hold
  subst next
  simp [gate, hmode, operationReply, applyOperation, haccepted, hwellFormed]

/-- Accepted queue removal publishes the exact resumable-aware cleanup result,
including saved-context consumption and active-translation invalidation. -/
theorem gate_scheduleRemove_accepted_sound state subject context next
    (hmode : state.execution.mode = .running)
    (haccepted : ResumablePreemption.remove state.resumable subject =
      { state := next, result := .accepted context })
    (hwellFormed : ResumablePreemption.WellFormed state.resumable) :
    (gate state (.scheduleRemove subject)).result =
        .completed (.scheduleRemove (.accepted context)) ∧
      (gate state (.scheduleRemove subject)).state.resumable = next ∧
      ResumablePreemption.WellFormed
        (gate state (.scheduleRemove subject)).state.resumable := by
  have hpreserved := ResumablePreemption.remove_preserves_wellFormed
    state.resumable subject hwellFormed
  rw [haccepted] at hpreserved
  simp [gate, hmode, operationReply, applyOperation, haccepted,
    installSchedulerRemoval, hpreserved]

/-- Raw voluntary yield has no accepted composite result because it carries no
outgoing context payload.  This theorem records that unreachable contract. -/
theorem gate_scheduleYield_accepted_sound state context next
    (_hmode : state.execution.mode = .running)
    (haccepted : schedulerYield state =
      { state := next, result := .accepted context })
    (_hwellFormed : Scheduler.WellFormed state.scheduler) :
    (gate state .scheduleYield).result =
        .completed (.scheduler (.accepted context)) ∧
      (gate state .scheduleYield).state.scheduler = next ∧
      Scheduler.WellFormed (gate state .scheduleYield).state.scheduler := by
  exact False.elim ((schedulerYield_ne_accepted state context) (by simp [haccepted]))

/-- Raw timer tick likewise has no accepted composite result; resumable timer
switching is owned by the save/select/restore operation. -/
theorem gate_scheduleTick_accepted_sound state context next
    (_hmode : state.execution.mode = .running)
    (haccepted : schedulerTick state =
      { state := next, result := .accepted context })
    (_hwellFormed : Scheduler.WellFormed state.scheduler) :
    (gate state .scheduleTick).result =
        .completed (.scheduler (.accepted context)) ∧
      (gate state .scheduleTick).state.scheduler = next ∧
      Scheduler.WellFormed (gate state .scheduleTick).state.scheduler := by
  exact False.elim ((schedulerTick_ne_accepted state context) (by simp [haccepted]))

/-- Accepted current-subject termination identifies the kernel-selected victim
and publishes the authoritative resumable cleanup for that subject.  This is
deliberately stronger than exposing the raw scheduler post-state: owned address
spaces, translations, mailboxes, transfers, and saved contexts are retired by
the composite mutation too. -/
theorem gate_terminateCurrent_accepted_sound state context next
    (hmode : state.execution.mode = .running)
    (haccepted : Scheduler.terminateCurrent state.scheduler =
      { state := next, result := .accepted context })
    (_hwellFormed : Scheduler.WellFormed state.scheduler) :
    (gate state .terminateCurrent).result =
        .completed (.scheduler (.accepted context)) ∧
      ∃ subject, state.scheduler.lifecycle.current = some subject ∧
        (gate state .terminateCurrent).state =
          installTerminatedSubject state subject
            (ResumablePreemption.cleanupSubject state.resumable subject) := by
  cases hcurrent : state.scheduler.lifecycle.current with
  | none => simp [Scheduler.terminateCurrent, hcurrent, Scheduler.reject] at haccepted
  | some subject =>
      constructor
      · simp [gate, hmode, operationReply, haccepted]
      · refine ⟨subject, rfl, ?_⟩
        simp [gate, hmode, applyOperation, haccepted, hcurrent]

/-- The scheduler-selected spelling reaches the same authoritative deferred
cleanup as explicit termination.  In particular, its accepted post-state
cannot retain a drainable saved context for the selected dead subject. -/
theorem gate_terminateCurrent_accepted_cleans_deferred state context next
    (hmode : state.execution.mode = .running)
    (haccepted : Scheduler.terminateCurrent state.scheduler =
      { state := next, result := .accepted context })
    (hwellFormed : Scheduler.WellFormed state.scheduler) :
    (gate state .terminateCurrent).result =
        .completed (.scheduler (.accepted context)) ∧
      ∃ subject, state.scheduler.lifecycle.current = some subject ∧
        (gate state .terminateCurrent).state.deferredCancels.retained subject = none := by
  obtain ⟨hresult, subject, hcurrent, hstate⟩ :=
    gate_terminateCurrent_accepted_sound state context next hmode haccepted hwellFormed
  refine ⟨hresult, subject, hcurrent, ?_⟩
  rw [hstate]
  exact installTerminatedSubject_deferred_self state subject
    (ResumablePreemption.cleanupSubject state.resumable subject)

end LeanOS.FailStop
