import LeanOS.KernelTransition
import LeanOS.Capability
import LeanOS.FrameAllocator
import LeanOS.FrameBudget
import LeanOS.X86PageTable
import LeanOS.Syscall
import LeanOS.FailStop
import LeanOS.InterruptEntry
import LeanOS.FaultDispatch
import LeanOS.PrivilegeEntryStack
import LeanOS.PrivilegeEntryControl
import LeanOS.ExtendedState
import LeanOS.ScheduledObservation
import LeanOS.DMAQuarantine

/-! # Stable security-claim contract

Each theorem independently restates one advertised proposition. Changes to an
implementation theorem's assumptions or conclusion therefore require an
explicit change here and in `docs/security-claims.md`.
-/
namespace LeanOS.SecurityClaims

/-- SC-DMA-QUARANTINE: an accepted nonempty q35 quarantine plus the explicit
bus-master device-control contract preserves every modeled memory projection. -/
theorem dma_quarantine_preserves_complete_projection
    (accepted : DMAQuarantine.AcceptedSnapshot) (target : DMAQuarantine.BDF)
    (before after : DMAQuarantine.MemoryProjection)
    (hcontract : DMAQuarantine.DeviceContract accepted.snapshot target before after)
    (hknown : ∃ function ∈ accepted.snapshot.functions,
      function.bdf = target ∧ function.status = .present) :
    after.physicalMemory = before.physicalMemory ∧
      after.allocatorOwnership = before.allocatorOwnership ∧
      after.pageTableFrames = before.pageTableFrames ∧
      after.kernelOwnedFrames = before.kernelOwnedFrames ∧
      after.kernelState = before.kernelState ∧
      after.subjectVisible = before.subjectVisible := by
  exact DMAQuarantine.unowned_device_preserves_complete_projection accepted target before after
    hcontract hknown

/-- The pinned q35 manifest has a concrete accepted, nonempty quarantine
snapshot; SC-DMA-QUARANTINE is not discharged by an empty inventory. -/
theorem dma_quarantine_q35_nonvacuous :
    (DMAQuarantine.validate DMAQuarantine.q35Snapshot).isAccepted = true := by
  native_decide

/-- SC-KERNEL-DET: the first modeled transition is deterministic. -/
theorem kernel_transition_deterministic
    (state : KernelTransition.State) (command : KernelTransition.Command)
    (first second : KernelTransition.Outcome)
    (hfirst : KernelTransition.transition state command = first)
    (hsecond : KernelTransition.transition state command = second) : first = second := by
  exact KernelTransition.transition_deterministic state command first second hfirst hsecond

/-- SC-KERNEL-WF: the first modeled transition preserves well-formedness. -/
theorem kernel_transition_preserves_wellFormed
    (state : KernelTransition.State) (command : KernelTransition.Command)
    (hstate : KernelTransition.WellFormed state) :
    KernelTransition.WellFormed (KernelTransition.transition state command).state := by
  exact KernelTransition.transition_preserves_wellFormed state command hstate

/-- SC-CAP-AUTH: capability copying cannot create authority without provenance. -/
theorem capability_copy_no_authority_amplification
    (state : Capability.State) (actor : Capability.SubjectId)
    (source : Capability.SlotId) (destination : Capability.SubjectId)
    (destinationSlot : Capability.SlotId) (requested : Capability.Rights)
    (candidate : Capability.SubjectId) (object : Capability.ObjectId)
    (right : Capability.Right)
    (hauthority : Capability.HasAuthority
      (Capability.copy state actor source destination destinationSlot requested).state
      candidate object right) :
    Capability.HasAuthority state candidate object right ∨
      Capability.HasAuthority state actor object right := by
  exact Capability.copy_no_authority_amplification state actor source destination
    destinationSlot requested candidate object right hauthority

/-- SC-FRAME-OWNER: a frame cannot have two distinct modeled owners. -/
theorem frame_ownership_exclusive
    (state : FrameAllocator.State) (frame : FrameAllocator.FrameId)
    (left right : FrameAllocator.OwnerId)
    (hleft : FrameAllocator.IsOwnedBy state frame left)
    (hright : FrameAllocator.IsOwnedBy state frame right) : left = right := by
  exact FrameAllocator.ownership_exclusive state frame left right hleft hright

/-- SC-FRAME-BUDGET-ISOLATION: an admitted subject with an available committed
frame and valid object/slot inputs can allocate independently of peer usage. -/
theorem admitted_frame_budget_isolation state subject object slot
    (hlive : state.memory.capabilities.subjects subject = true)
    (hslot : slot < CapabilityHandle.slotReserved)
    (hinrange : Capability.slotInRange state.memory.capabilities subject slot = true)
    (hidentity : state.memory.capabilities.nextIdentity ≠ 0)
    (hidentityBound : state.memory.capabilities.nextIdentity <
      CapabilityHandle.generationReserved)
    (hempty : state.memory.capabilities.slots subject slot = none)
    (hunissued : state.memory.issued object = false)
    (havailable : FrameBudget.hasAvailable state subject = true) :
    (FrameBudget.allocate state subject object slot).result = .accepted := by
  exact FrameBudget.available_allocation_accepted state subject object slot hlive hslot
    hinrange hidentity hidentityBound hempty hunissued havailable

/-- SC-PT-SEPARATION: distinct encoded frames yield distinct read walks. -/
theorem page_table_distinct_spaces_separated
    (state : VirtualMapping.State) first second page firstLeaf secondLeaf
    (hfirst : (X86PageTable.encode state first).leaf page = some firstLeaf)
    (hsecond : (X86PageTable.encode state second).leaf page = some secondLeaf)
    (hne : firstLeaf.frame ≠ secondLeaf.frame) :
    X86PageTable.walk (X86PageTable.encode state first) page .read ≠
      X86PageTable.walk (X86PageTable.encode state second) page .read := by
  exact X86PageTable.distinct_spaces_separated state first second page firstLeaf secondLeaf
    hfirst hsecond hne

/-- SC-SYSCALL-CONFINEMENT: untrusted syscall words cannot add capability authority. -/
theorem syscall_authority_confinement
    (state : VirtualMapping.State) (context : Syscall.TrustedContext)
    (call : Syscall.UntrustedCall)
    (subject : Capability.SubjectId) (object : Capability.ObjectId) (right : Capability.Right)
    (hauthority : Capability.HasAuthority
      (Syscall.dispatch state context call).state.memory.capabilities subject object right) :
    Capability.HasAuthority state.memory.capabilities subject object right := by
  exact Syscall.dispatch_authority_provenance state context call subject object right hauthority

/-- SC-FAILSTOP: every proposed suffix is absorbed after a fatal halt. -/
theorem failstop_halted_suffix_absorbing state record proposals
    (hmode : state.execution.mode = .halted record) :
    FailStop.runOperations state proposals = state := by
  exact FailStop.halted_suffix_absorbing state record proposals hmode

/-- SC-COMPOSITE-GATE-WF: the sealed-mailbox rejection path of the public
composite gate preserves the complete runtime invariant and exposes the typed
reason that callers must use capability-transfer acceptance instead.  This is
the first operation-specific preservation slice of the global gate contract. -/
theorem composite_gate_sealed_receive_preserves_runtimeWellFormed
    state handleWord endpoint transfer
    (hstate : FailStop.RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hresolve : CapabilityHandle.resolveCurrent state.transfers.capabilities
      { caller := state.execution.core.context.currentSubject }
      handleWord .endpoint = .ok endpoint)
    (hpending : state.transfers.pending endpoint.capability.object = some transfer) :
    FailStop.RuntimeWellFormed
        (FailStop.gate state (.ipc (.receive handleWord))).state ∧
      (FailStop.gate state (.ipc (.receive handleWord))).result =
        .completed (.ipc .sealedTransferPending) := by
  exact FailStop.gate_sealed_receive_preserves_runtimeWellFormed state handleWord
    endpoint transfer hstate hmode hresolve hpending

/-- SC-COMPOSITE-GATE-SEND-WF: the accepted data-send mutation preserves the
complete runtime invariant while publishing one exact typed success. -/
theorem composite_gate_data_send_preserves_runtimeWellFormed
    state handleWord word0 word1
    (hstate : FailStop.RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hsent : (FailStop.operationReply state
      (.ipc (.send handleWord word0 word1))) = .ipc (.syscall .sent)) :
    FailStop.RuntimeWellFormed
        (FailStop.gate state (.ipc (.send handleWord word0 word1))).state ∧
      (FailStop.gate state (.ipc (.send handleWord word0 word1))).result =
        .completed (.ipc (.syscall .sent)) := by
  apply FailStop.gate_ipc_send_accepted_preserves_runtimeWellFormed
    state handleWord word0 word1 hstate hmode
  simpa [FailStop.operationReply] using hsent

/-- SC-COMPOSITE-GATE-RECEIVE-WF: accepted data receipt preserves the complete
runtime invariant and exposes the exact sender and payload selected by the
kernel-confined endpoint transition. -/
theorem composite_gate_data_receive_preserves_runtimeWellFormed
    state handleWord sender word0 word1
    (hstate : FailStop.RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (hdelivered : FailStop.operationReply state (.ipc (.receive handleWord)) =
      .ipc (.syscall (.delivered sender word0 word1))) :
    FailStop.RuntimeWellFormed
        (FailStop.gate state (.ipc (.receive handleWord))).state ∧
      (FailStop.gate state (.ipc (.receive handleWord))).result =
        .completed (.ipc (.syscall (.delivered sender word0 word1))) := by
  apply FailStop.gate_ipc_receive_accepted_preserves_runtimeWellFormed
    state handleWord sender word0 word1 hstate hmode
  simpa [FailStop.operationReply] using hdelivered

/-- SC-COMPOSITE-BLOCKING-CONTEXT-WF: every typed block, wake, cancellation,
ordinary rejection, and execution-latch rejection preserves the exact
waiter/saved-context agreement.  Successful wake and cancellation additionally
pass through the checked resumable-bank restoration boundary. -/
theorem composite_blocking_gate_preserves_contextWellFormed state operation
    (hstate : FailStop.BlockingReceiveWellFormed state) :
    FailStop.BlockingReceiveWellFormed
      (FailStop.blockingGate state operation).state ∧
    (FailStop.CompositeBlockingGateRejection
        (FailStop.blockingGate state operation).result →
      (FailStop.blockingGate state operation).state = state) ∧
    (∀ reply, (FailStop.blockingGate state operation).result = .completed reply →
      state.execution.mode = .running ∧
        reply = FailStop.blockingOperationReply state operation ∧
        (FailStop.blockingGate state operation).state =
          FailStop.applyBlockingOperation state operation) ∧
    (∀ handleWord frame registers envelope,
      FailStop.BlockingRuntimeWellFormed state →
      (FailStop.blockingGate state (.receive handleWord frame registers)).result =
        .completed (.receive (.delivered envelope)) →
      FailStop.BlockingRuntimeWellFormed
        (FailStop.blockingGate state (.receive handleWord frame registers)).state) ∧
    (∀ handleWord frame registers,
      FailStop.BlockingRuntimeWellFormed state →
      (FailStop.blockingGate state (.receive handleWord frame registers)).result =
        .completed (.receive .blocked) →
      (FailStop.blockingGate state
        (.receive handleWord frame registers)).state.scheduler.lifecycle.current = none →
      FailStop.BlockingRuntimeWellFormed
        (FailStop.blockingGate state (.receive handleWord frame registers)).state) ∧
    (∀ handleWord word0 word1,
      FailStop.RuntimeWellFormed state →
      (FailStop.blockingGate state (.send handleWord word0 word1)).result =
        .completed (.send .sent) →
      FailStop.RuntimeWellFormed
        (FailStop.blockingGate state (.send handleWord word0 word1)).state) ∧
    (∀ handleWord word0 word1 saved,
      FailStop.BlockingRuntimeWellFormed state →
      (FailStop.blockingGate state (.send handleWord word0 word1)).result =
        .completed (.send (.woke saved)) →
      FailStop.BlockingRuntimeWellFormed
        (FailStop.blockingGate state (.send handleWord word0 word1)).state) ∧
    (∀ handleWord word0 word1 saved,
      (FailStop.blockingGate state (.send handleWord word0 word1)).result =
        .completed (.send (.woke saved)) →
      ResumablePreemption.validContext
        (FailStop.blockingGate state (.send handleWord word0 word1)).state.resumable saved) ∧
    (∀ subject saved,
      FailStop.BlockingRuntimeWellFormed state →
      (FailStop.blockingGate state (.cancel subject)).result =
        .completed (.cancel (.cancelled saved)) →
      FailStop.BlockingRuntimeWellFormed
        (FailStop.blockingGate state (.cancel subject)).state) ∧
    (∀ subject saved,
      (FailStop.blockingGate state (.cancel subject)).result =
        .completed (.cancel (.cancelled saved)) →
      ResumablePreemption.validContext
        (FailStop.blockingGate state (.cancel subject)).state.resumable saved) := by
  exact ⟨FailStop.blockingGate_preserves_wellFormed state operation hstate,
    FailStop.blockingGate_rejection_atomic state operation,
    FailStop.blockingGate_completed_sound state operation,
    fun handleWord frame registers envelope hglobal hcompleted =>
      FailStop.blockingGate_receive_delivered_preserves_blockingRuntimeWellFormed
        state handleWord frame registers envelope hglobal hcompleted,
    fun handleWord frame registers hglobal hcompleted hidle =>
      FailStop.blockingGate_receive_idle_block_preserves_blockingRuntimeWellFormed
        state handleWord frame registers hglobal hcompleted hidle,
    fun handleWord word0 word1 hglobal hcompleted =>
      FailStop.blockingGate_send_sent_preserves_runtimeWellFormed
        state handleWord word0 word1 hglobal hcompleted,
    fun handleWord word0 word1 saved hglobal hcompleted =>
      FailStop.blockingGate_send_woke_preserves_blockingRuntimeWellFormed
        state handleWord word0 word1 saved hglobal hcompleted,
    fun handleWord word0 word1 saved hcompleted =>
      FailStop.blockingGate_send_woke_context_valid
        state handleWord word0 word1 saved hcompleted,
    fun subject saved hglobal hcompleted =>
      FailStop.blockingGate_cancel_cancelled_preserves_blockingRuntimeWellFormed
        state subject saved hglobal hcompleted,
    fun subject saved hcompleted =>
      FailStop.blockingGate_cancel_cancelled_context_valid
        state subject saved hcompleted⟩

/-- SC-COMPOSITE-BLOCKING-REJECTION-WF: every finite ordinary denial at the
typed blocking gate preserves the full composite runtime invariant because it
returns the literal pre-state. -/
theorem composite_blocking_gate_rejection_preserves_runtimeWellFormed state operation
    (hstate : FailStop.RuntimeWellFormed state)
    (hrejected : FailStop.CompositeBlockingGateRejection
      (FailStop.blockingGate state operation).result) :
    FailStop.RuntimeWellFormed (FailStop.blockingGate state operation).state := by
  exact FailStop.blockingGate_rejection_preserves_runtimeWellFormed
    state operation hstate hrejected

/-- Concrete non-vacuity for the outer blocking rejection classifier: the
boot-produced empty waiter store classifies cancellation of subject `1` as an
ordinary atomic `notWaiting` denial. -/
theorem composite_blocking_gate_rejection_reachable_witness plan :
    let state := FailStop.bootRuntime plan
    FailStop.CompositeBlockingGateRejection
        (FailStop.blockingGate state (.cancel 1)).result ∧
      (FailStop.blockingGate state (.cancel 1)).state = state := by
  exact ⟨.cancel .notWaiting, rfl⟩

/-- SC-COMPOSITE-TRANSFER-OFFER-WF: every canonical sealed-transfer offer,
including malformed/stale handle rejections and the accepted pending-mailbox
mutation, preserves the complete global runtime invariant. -/
theorem composite_gate_transferOffer_preserves_runtimeWellFormed
    state endpointWord sourceWord sourceKind payload rights
    (hstate : FailStop.RuntimeWellFormed state) :
    FailStop.RuntimeWellFormed
      (FailStop.gate state
        (.transferOffer endpointWord sourceWord sourceKind payload rights)).state := by
  exact FailStop.transferOffer_operationPreservesRuntimeWellFormed endpointWord sourceWord
    sourceKind payload rights state hstate

/-- SC-COMPOSITE-TRANSFER-ACCEPT-WF: every canonical sealed-transfer receipt,
including malformed/stale handle and slot rejections as well as successful
authority installation, preserves the complete global runtime invariant. -/
theorem composite_gate_transferAccept_preserves_runtimeWellFormed
    state endpointWord destinationSlot
    (hstate : FailStop.RuntimeWellFormed state) :
    FailStop.RuntimeWellFormed
      (FailStop.gate state (.transferAccept endpointWord destinationSlot)).state := by
  exact FailStop.transferAccept_operationPreservesRuntimeWellFormed endpointWord
    destinationSlot state hstate

/-- SC-COMPOSITE-GATE-CONTRACT: every completed public gate step identifies
the running latch, exact typed reply, and exact composite post-state; both
gate-level rejection classes and every classified nonfatal subsystem rejection
preserve the complete state, and every classified rejection preserves the
global invariant whenever the pre-state satisfies it. -/
theorem composite_gate_typed_result_contract state operation :
    (∀ reply, (FailStop.gate state operation).result = .completed reply →
      state.execution.mode = .running ∧
        reply = FailStop.operationReply state operation ∧
        (FailStop.gate state operation).state = FailStop.applyOperation state operation) ∧
    (((FailStop.gate state operation).result = .rejectedBusy ∨
      ∃ record, (FailStop.gate state operation).result = .rejectedHalted record) →
      (FailStop.gate state operation).state = state) ∧
    (∀ reply, (FailStop.gate state operation).result = .completed reply →
      FailStop.SubsystemRejection state operation reply →
      (FailStop.gate state operation).state = state ∧
        (FailStop.RuntimeWellFormed state →
          FailStop.RuntimeWellFormed (FailStop.gate state operation).state)) ∧
    ((FailStop.operationReply state operation).isNonfatalRejection = true →
      (FailStop.gate state operation).state = state ∧
        (FailStop.RuntimeWellFormed state →
          FailStop.RuntimeWellFormed (FailStop.gate state operation).state)) := by
  constructor
  · intro reply hcompleted
    exact FailStop.gate_completed_sound state operation reply hcompleted
  constructor
  · exact FailStop.gate_mode_rejection_atomicity state operation
  constructor
  · intro reply hcompleted hrejected
    constructor
    · exact FailStop.gate_subsystem_rejection_atomicity state operation reply
        hcompleted hrejected
    · intro hstate
      exact (FailStop.gate_subsystem_rejection_preserves_runtimeWellFormed
        state operation reply hstate hcompleted hrejected).1
  · intro hrejected
    constructor
    · exact FailStop.gate_classified_rejection_global_atomicity state operation hrejected
    · intro hstate
      exact (FailStop.gate_classified_rejection_preserves_runtimeWellFormed
        state operation hstate hrejected).1

/-- SC-COMPOSITE-AUTHORITY-CONFINEMENT: every public authority-bearing
operation reports the exact subsystem result computed for the current subject
and, where applicable, the active address space selected by the execution
latch.  No operation argument supplies either privileged identity. -/
theorem composite_gate_authority_confinement state
    syscallCall ipcCall endpointWord sourceWord sourceKind payload rights
    source destination destinationSlot authoritySlot victim victimSlot slot page permissions
    (hmode : state.execution.mode = .running) :
    (FailStop.gate state (.syscall syscallCall)).result =
        .completed (.syscall
          (Syscall.dispatch state.virtualMemory state.syscallContext syscallCall).reply) ∧
    (FailStop.gate state (.ipc ipcCall)).result =
        .completed (.ipc (FailStop.authoritativeIPCReply state ipcCall)) ∧
    (FailStop.gate state
        (.transferOffer endpointWord sourceWord sourceKind payload rights)).result =
        .completed (.transferOffer
          (CapabilityTransfer.offerWords state.transfers
            state.execution.core.context.currentSubject endpointWord sourceWord sourceKind
            payload rights).result) ∧
    (FailStop.gate state (.transferAccept endpointWord destinationSlot)).result =
        .completed (.transferAccept
          (CapabilityTransfer.acceptWord state.transfers
            state.execution.core.context.currentSubject endpointWord destinationSlot).result
          (CapabilityTransfer.acceptWord state.transfers
            state.execution.core.context.currentSubject endpointWord destinationSlot).deliveredWord) ∧
    (FailStop.gate state
        (.capabilityCopy source destination destinationSlot rights)).result =
        .completed (.capability
          (Capability.copy state.capabilities
            state.execution.core.context.currentSubject source destination destinationSlot
            rights).result) ∧
    (FailStop.gate state (.capabilityRevoke authoritySlot victim victimSlot)).result =
        .completed (.capability
          (Capability.revokeRuntimeSafe state.capabilities
            state.execution.core.context.currentSubject authoritySlot victim victimSlot).result) ∧
    (FailStop.gate state (.capabilityRevokeSubtree authoritySlot victim victimSlot)).result =
        .completed (.capability
          (Capability.revokeSubtreeRuntimeSafe state.capabilities
            state.execution.core.context.currentSubject authoritySlot victim victimSlot).result) ∧
    (FailStop.gate state (.map slot page permissions)).result =
        .completed (.map
          (VirtualMapping.map state.virtualMemory
            state.execution.core.context.currentSubject slot
            state.execution.core.context.activeAddressSpace page permissions).result) ∧
    (FailStop.gate state (.unmap page)).result =
        .completed (.unmap
          (VirtualMapping.unmap state.virtualMemory
            state.execution.core.context.currentSubject
            state.execution.core.context.activeAddressSpace page).result) := by
  exact FailStop.authority_operations_result_sound state syscallCall ipcCall endpointWord
    sourceWord sourceKind payload rights source destination destinationSlot authoritySlot victim
    victimSlot slot page permissions hmode

/-- SC-COMPOSITE-CONTROL-WF: both control operations preserve the complete
invariant in every execution mode, including the exact sealed-transfer and
resumable states retained by busy and halted gate rejection. -/
theorem composite_gate_control_preserves_runtimeWellFormed state purpose
    (hstate : FailStop.RuntimeWellFormed state) :
    FailStop.RuntimeWellFormed
        (FailStop.gate state (.selectUserReturn purpose)).state ∧
      FailStop.RuntimeWellFormed (FailStop.gate state .restart).state := by
  exact ⟨FailStop.gate_selectUserReturn_preserves_runtimeWellFormed state purpose
      hstate,
    FailStop.gate_restart_preserves_runtimeWellFormed state hstate⟩

/-- SC-COMPOSITE-MAPPING-WF: both kernel-confined raw mapping operations
preserve the complete runtime invariant in every execution mode. -/
theorem composite_gate_mapping_preserves_runtimeWellFormed state slot page permissions
    (hstate : FailStop.RuntimeWellFormed state) :
    FailStop.RuntimeWellFormed
        (FailStop.gate state (.map slot page permissions)).state ∧
      FailStop.RuntimeWellFormed (FailStop.gate state (.unmap page)).state := by
  exact ⟨FailStop.map_operationPreservesRuntimeWellFormed slot page permissions state hstate,
    FailStop.unmap_operationPreservesRuntimeWellFormed page state hstate⟩

/-- SC-COMPOSITE-SYSCALL-WF: every attacker-controlled fixed-width syscall
tuple preserves the complete runtime invariant; privileged caller and address
space selection remain projections of the authoritative execution state. -/
theorem composite_gate_syscall_preserves_runtimeWellFormed state call
    (hstate : FailStop.RuntimeWellFormed state) :
    FailStop.RuntimeWellFormed (FailStop.gate state (.syscall call)).state := by
  exact FailStop.syscall_operationPreservesRuntimeWellFormed call state hstate

/-- SC-COMPOSITE-SCHEDULER-ADMISSION-WF: queue admission is total over public
subject identifiers, rejects a missing kernel-owned context atomically, and
preserves the complete runtime invariant for every typed result. -/
theorem composite_gate_schedulerAdmission_preserves_runtimeWellFormed state subject
    (hstate : FailStop.RuntimeWellFormed state) :
    FailStop.RuntimeWellFormed
      (FailStop.gate state (.scheduleAdd subject)).state := by
  exact FailStop.scheduleAdd_operationPreservesRuntimeWellFormed subject state hstate

/-- SC-COMPOSITE-TERMINATION-WF: every subject identifier is a total public
termination request. Rejections are atomic; acceptance retires the subject's
resources and removes all scheduler, context, mailbox, and sealed-transfer
references while preserving the complete runtime invariant. -/
theorem composite_gate_termination_preserves_runtimeWellFormed state subject
    (hstate : FailStop.RuntimeWellFormed state) :
    FailStop.RuntimeWellFormed
        (FailStop.gate state (.terminateSubject subject)).state ∧
      FailStop.RuntimeWellFormed
        (FailStop.gate state .terminateCurrent).state := by
  exact ⟨FailStop.terminateSubject_operationPreservesRuntimeWellFormed subject state hstate,
    FailStop.terminateCurrent_operationPreservesRuntimeWellFormed state hstate⟩

/-- SC-COMPOSITE-MIXED-TRACE-WF: arbitrary finite interleavings of every
public operation preserve the complete runtime invariant for every accepted,
typed-rejected, busy, halted, or fatal result. -/
theorem composite_universal_mixed_trace_preserves_runtimeWellFormed
    state operations
    (hstate : FailStop.RuntimeWellFormed state) :
    FailStop.RuntimeWellFormed (FailStop.runOperations state operations) := by
  exact FailStop.runOperations_preserves_runtimeWellFormed_universally
    state operations hstate

/-- SC-COMPOSITE-BOOT-WF: every successfully compiled bounded boot page-table
plan produces an idle composite runtime satisfying the complete global
invariant before any subject or trusted return identity is admitted. -/
theorem composite_boot_runtime_wellFormed input plan
    (hcompiled : BootPageTablePlan.compile input = .ok plan) :
    FailStop.RuntimeWellFormed (FailStop.bootRuntime plan) := by
  exact FailStop.bootRuntime_runtimeWellFormed input plan hcompiled

set_option maxRecDepth 100000 in
/-- Concrete non-vacuity witness: the repository's accepted bounded sample
boot input reaches the globally well-formed initial composite runtime. -/
theorem composite_boot_runtime_reachable_witness :
    match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
    | .ok plan => FailStop.RuntimeWellFormed (FailStop.bootRuntime plan)
    | .error _ => False := by
  generalize hresult : BootPageTablePlan.compile BootPageTablePlan.sampleInput = result
  cases result with
  | error reason =>
      have hsuccess :
          (match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
            | .ok _ => true
            | .error _ => false) = true := by
        native_decide
      simp [hresult] at hsuccess
  | ok plan =>
      exact FailStop.bootRuntime_runtimeWellFormed BootPageTablePlan.sampleInput plan hresult

private def registeredMixedTrace : List FailStop.Operation :=
  [.syscall { number := 99, arg0 := 0, arg1 := 0, arg2 := 0 },
   .ipc (.receive 0),
   .transferOffer 0 0 .memory { word0 := 0, word1 := 0 } { read := true },
   .transferAccept 0 0,
   .capabilityCopy 0 1 0 { read := true },
   .capabilityRevoke 0 1 0,
   .capabilityRevokeSubtree 0 1 0,
   .map 0 0 { read := true },
   .unmap 0,
   .createSubject 1,
   .scheduleAdd 1,
   .scheduleRemove 1,
   .terminateSubject 1,
   .terminateCurrent,
   .selectUserReturn .initialDispatch,
   .restart]

private theorem registeredMixedTrace_registered operation
    (hmember : operation ∈ registeredMixedTrace) :
    FailStop.RuntimeTraceOperation operation := by
  simp [registeredMixedTrace] at hmember
  rcases hmember with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst operation
    exact .syscall _
  · subst operation
    exact .ipc _
  · subst operation
    exact .transferOffer _ _ _ _ _
  · subst operation
    exact .transferAccept _ _
  · subst operation
    exact .capabilityCopy _ _ _ _
  · subst operation
    exact .capabilityRevoke _ _ _
  · subst operation
    exact .capabilityRevokeSubtree _ _ _
  · subst operation
    exact .map _ _ _
  · subst operation
    exact .unmap _
  · subst operation
    exact .createSubject _
  · subst operation
    exact .scheduleAdd _
  · subst operation
    exact .scheduleRemove _
  · subst operation
    exact .terminateSubject _
  · subst operation
    exact .terminateCurrent
  · subst operation
    exact .selectUserReturn _
  · subst operation
    exact .restart

set_option maxRecDepth 100000 in
/-- Concrete non-vacuity for the universal mixed-trace contract: the accepted
repository boot plan runs a finite trace containing attacker-controlled
syscall/IPC/sealed-transfer/capability-copy/revocation/mapping words, lifecycle
creation/termination, resumable-aware scheduler cleanup, return selection, and restart
while retaining the global invariant. -/
theorem composite_universal_mixed_trace_reachable_witness :
    match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
    | .ok plan => FailStop.RuntimeWellFormed
        (FailStop.runOperations (FailStop.bootRuntime plan) registeredMixedTrace)
    | .error _ => False := by
  generalize hresult : BootPageTablePlan.compile BootPageTablePlan.sampleInput = result
  cases result with
  | error reason =>
      have hsuccess :
          (match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
            | .ok _ => true
            | .error _ => false) = true := by
        native_decide
      simp [hresult] at hsuccess
  | ok plan =>
      apply composite_universal_mixed_trace_preserves_runtimeWellFormed
      exact FailStop.bootRuntime_runtimeWellFormed
        BootPageTablePlan.sampleInput plan hresult

/-- SC-INTERRUPT-ENTRY-BINDING: every normalized record constructor copies
authority-bearing context fields from the kernel-owned input. -/
theorem interrupt_entry_context_binding entry raw context :
    (InterruptEntry.makeNormalized entry raw context).currentSubject = context.currentSubject ∧
    (InterruptEntry.makeNormalized entry raw context).activeAddressSpace =
      context.activeAddressSpace ∧
    (InterruptEntry.makeNormalized entry raw context).activeCr3 = context.activeCr3 ∧
    (InterruptEntry.makeNormalized entry raw context).stackIdentity = context.stackIdentity := by
  exact InterruptEntry.makeNormalized_binds_context entry raw context

/-- SC-PRIVILEGE-ENTRY-STACK: accepted ordinary-entry stack authorization
names the valid guarded layout exactly and carries a checked byte remainder
without changing the modeled composite state. -/
theorem privilege_entry_stack_budget_sound (State : Type)
    layout reserved request (state : State) budget (acceptedState : State)
    (haccepted : PrivilegeEntryStack.authorize layout reserved request state =
      .accepted budget acceptedState) :
    PrivilegeEntryStack.layoutValid layout reserved = true ∧
      acceptedState = state ∧
      budget.stackIdentity = layout.stackIdentity ∧
      budget.stackFirst = layout.usable.first ∧
      budget.stackPastLast = layout.usable.pastLast ∧
      budget.stackTop = layout.stackTop ∧
      budget.remainingBytes + budget.requiredBytes =
        PrivilegeEntryStack.usableBytes layout := by
  have hconditions := PrivilegeEntryStack.accepted_contract_conditions State
    layout reserved request state budget acceptedState haccepted
  have hbudget := PrivilegeEntryStack.accepted_budget_sound State layout reserved
    request state budget acceptedState haccepted
  exact ⟨hconditions.1, hbudget.1, hbudget.2.1, hbudget.2.2.1,
    hbudget.2.2.2.1, hbudget.2.2.2.2.1, hbudget.2.2.2.2.2.2⟩

/-- SC-PRIVILEGE-ENTRY-CONTROL: every accepted finite CPU/MSR state enables
exactly the reviewed manifest-backed `int 0x80` mechanism. -/
theorem privilege_entry_control_single_mechanism control mechanism
    (haccepted : PrivilegeEntryControl.Accepted control) :
    PrivilegeEntryControl.enabled control mechanism =
      decide (mechanism = .int80) := by
  exact PrivilegeEntryControl.accepted_exactly_int80 control haccepted mechanism

/-- SC-USER-RETURN-CONFINEMENT: an accepted return attests the complete
kernel-selected frame/context tuple and its privilege-critical fields. -/
theorem user_return_context_confinement request attested
    (haccepted : Interrupt.validateUserReturn request = .accepted attested) :
    attested = request ∧
      attested.purpose ≠ .diagnosticKernelRecovery ∧
      attested.executionMode = .running ∧
      attested.hardware.savedPrivilege = .user ∧
      attested.hardware.codeSelector = 0x23 ∧
      attested.hardware.stackSelector = 0x1b ∧
      attested.hardware.canonicalInstructionPointer = true ∧
      attested.hardware.canonicalStackPointer = true ∧
      Interrupt.rawReturnFlagsAllowed attested.hardware.flags = true ∧
      attested.lifecycle.capabilities.subjects attested.expectedSubject = true ∧
      attested.lifecycle.runnable attested.expectedSubject = true ∧
      attested.lifecycle.current = some attested.expectedSubject ∧
      attested.frameSubject = attested.expectedSubject ∧
      attested.lifecycle.addressOwner attested.expectedAddressSpace =
        some attested.expectedSubject ∧
      attested.frameAddressSpace = attested.expectedAddressSpace ∧
      attested.frameCr3 = attested.expectedCr3 ∧
      attested.codeRegion.contains attested.hardware.instructionPointer = true ∧
      attested.stackRegion.containsStackPointer attested.hardware.stackPointer = true := by
  exact Interrupt.accepted_user_return_context_confined request attested haccepted

/-- SC-USER-RETURN-AUTHORITY: the executable target policy accepted by the
terminal gate is exactly the kernel-owned policy, never a proposal copy. -/
theorem user_return_authority_confinement state request attested
    (hstate : FailStop.WellFormed state)
    (haccepted : (FailStop.completeUserReturn state request).action = .accepted attested) :
    FailStop.ReturnAuthorityBound state ∧
      attested.purpose = state.returnAuthority.purpose ∧
      attested.expectedCr3 = state.returnAuthority.expectedCr3 ∧
      attested.codeRegion = state.returnAuthority.codeRegion ∧
      attested.stackRegion = state.returnAuthority.stackRegion := by
  have hbound := FailStop.accepted_user_return_has_bound_authority state request attested
    hstate haccepted
  have hmode := FailStop.accepted_user_return_requires_running state request attested haccepted
  exact ⟨hbound, FailStop.accepted_user_return_uses_authority state request attested
    hmode haccepted⟩

/-- SC-USER-RETURN-LIVE-PLAN: any authority armed by the composite selector
was checked against the active virtual-memory mappings and their physical
bindings, not merely against an attached compiled plan. -/
theorem user_return_authority_requires_live_plan state purpose
    (harmed : (FailStop.selectLiveReturnAuthority state purpose).execution.returnAuthorityArmed =
      true) :
    state.ReturnPlanLive = true := by
  exact FailStop.selectLiveReturnAuthority_armed_implies_live state purpose harmed

private def returnWitnessLifecycle : SubjectLifecycle.State :=
  { capabilities :=
      { subjects := fun subject => subject = 1
        objects := fun object => object = 100 || object = 101
        kinds := fun object => if object = 100 || object = 101 then some .memory else none
        slots := fun _ _ => none }
    issuedSubjects := fun subject => subject = 1
    ownedMemory := fun object =>
      if object = 100 then some (1, 100)
      else if object = 101 then some (1, 101)
      else none
    addressOwner := fun space => if space = 1 then some 1 else none
    mapping := fun space page =>
      if space = 1 ∧ page = 100 then some 100
      else if space = 1 ∧ page = 101 then some 101
      else none
    endpointOwner := fun _ => none
    mailbox := fun _ => none
    frameOwner := fun frame =>
      if frame = 100 then some 1 else if frame = 101 then some 1 else none
    freeFrame := fun frame =>
      if frame = 100 then false else if frame = 101 then false else true
    runnable := fun subject => subject = 1
    current := some 1 }

private def returnWitnessPlan : Option BootPageTablePlan.Plan :=
  (BootPageTablePlan.compile BootPageTablePlan.sampleInput).toOption

private def returnWitnessView : FailStop.ReturnAddressSpace :=
  { subject := 1
    expectedCr3 := 0xa000
    codeRegion := ⟨0x64000, 0x65000⟩
    stackRegion := ⟨0x65000, 0x66000⟩ }

private def returnWitnessBase : FailStop.State :=
  { core :=
      { lifecycle := returnWitnessLifecycle
        context :=
          { currentSubject := 1
            activeAddressSpace := 1
            kernelStack := 0
            entryActive := false } }
    mode := .running
    returnAddressSpace := fun space => if space = 1 then some returnWitnessView else none
    returnPlan := returnWitnessPlan }

private def returnWitnessState : FailStop.State :=
  FailStop.selectReturnAuthority returnWitnessBase .initialDispatch

private def returnWitnessRequest : Interrupt.UserReturnRequest :=
  { hardware :=
      { vector := 0
        errorCode := 0
        savedPrivilege := .user
        instructionPointer := 0x64100
        stackPointer := 0x65ff8
        codeSelector := 0x23
        stackSelector := 0x1b
        flags := 0x202
        canonicalInstructionPointer := true
        canonicalStackPointer := true
        flagsAllowed := true }
    purpose := .initialDispatch
    frameSubject := 1
    frameAddressSpace := 1
    frameCr3 := 0xa000
    expectedSubject := 1
    expectedAddressSpace := 1
    expectedCr3 := 0xa000
    executionMode := .running
    lifecycle := returnWitnessLifecycle
    codeRegion := ⟨0x64000, 0x65000⟩
    stackRegion := ⟨0x65000, 0x66000⟩
    flags :=
      { interruptEnable := true
        direction := false
        alignmentCheck := false
        nestedTask := false
        virtual8086 := false
        ioPrivilegeLevel := 0
        reservedAllowed := true } }

set_option maxRecDepth 100000 in
/-- The authority-selection transition reaches a well-formed armed state whose
complete return gate accepts the matching live frame. -/
theorem user_return_authority_reachable_witness :
    FailStop.WellFormed returnWitnessState ∧
      (FailStop.completeUserReturn returnWitnessState returnWitnessRequest).action =
        .accepted returnWitnessRequest := by
  constructor
  · apply FailStop.selectReturnAuthority_wellFormed
    simp [returnWitnessBase, returnWitnessLifecycle, FailStop.WellFormed,
      Interrupt.WellFormed, SubjectLifecycle.WellFormed]
    intro object subject frame howned
    by_cases h100 : object = 100
    · subst object
      simp at howned
      cases howned
      simp_all
    · by_cases h101 : object = 101
      · subst object
        simp [h100] at howned
        cases howned
        simp_all
      · simp [h100, h101] at howned
  · rfl

private def returnWitnessMemory : MemoryLifecycle.State :=
  { capabilities := returnWitnessLifecycle.capabilities
    allocator :=
      { frames := [100, 101]
        status := fun frame =>
          if frame = 100 then .owned 100
          else if frame = 101 then .owned 101
          else .reserved }
    binding := fun object =>
      if object = 100 then some 100 else if object = 101 then some 101 else none
    issued := fun object => object = 100 || object = 101 }

private def returnWitnessVirtualMemory : VirtualMapping.State :=
  { memory := returnWitnessMemory
    owner := returnWitnessLifecycle.addressOwner
    mappings := fun space page =>
      if space = 1 ∧ page = 100 then
        some { object := 100, permissions := { read := true, write := false } }
      else if space = 1 ∧ page = 101 then
        some { object := 101, permissions := { read := true, write := true } }
      else none
    issuedAddressSpace := fun space => space = 1 }

private def returnWitnessEndpoints : EndpointIPC.State :=
  { capabilities := returnWitnessLifecycle.capabilities
    allocator := returnWitnessMemory.allocator
    binding := returnWitnessMemory.binding
    issued := returnWitnessMemory.issued
    issuedAddressSpace := fun _ => false
    mailbox := fun _ => none
    sendHistory := fun _ => [] }

private def returnWitnessComposite : FailStop.CompositeState :=
  let scheduler : Scheduler.State :=
    { lifecycle := returnWitnessLifecycle, ready := [], capacity := 0 }
  let resumable : ResumablePreemption.State :=
    { scheduler
      contexts := []
      capacity := 0
      translations := { virtual := returnWitnessVirtualMemory, active := some 1, entries := [] } }
  let transfers : CapabilityTransfer.State :=
    { toEndpointState := returnWitnessEndpoints
      pending := fun _ => none }
  { execution := returnWitnessBase
    scheduler
    preemption := { scheduler, timerArmed := false, acceptedTicks := 1 }
    virtualMemory := returnWitnessVirtualMemory
    ipc := { virtualMemory := returnWitnessVirtualMemory, endpoints := returnWitnessEndpoints }
    capabilities := returnWitnessLifecycle.capabilities
    lifecycle := returnWitnessLifecycle
    resumable
    transfers
    blockingIPC :=
      { scheduler
        mailbox := fun _ => none
        waiters := fun _ => []
        waiterEndpoint := fun _ => none
        waiterCapacity := 0
        completion := fun _ => none }
    blockingContexts := fun _ => none }

private def returnWitnessSyscallFrame : Interrupt.HardwareFrame :=
  { returnWitnessRequest.hardware with vector := 128 }

private def returnWitnessSyscallRequest : Interrupt.UserReturnRequest :=
  { returnWitnessRequest with
    hardware := returnWitnessSyscallFrame
    purpose := .syscallResume }

private def returnWitnessSyscallCall : Syscall.UntrustedCall :=
  { number := 2, arg0 := 100, arg1 := 0, arg2 := 0 }

private def returnWitnessRejectedCall : Syscall.UntrustedCall :=
  { number := 99, arg0 := 0, arg1 := 0, arg2 := 0 }

/-- Non-vacuity witness for the composite gate contract: an unknown syscall
is classified as a typed subsystem rejection and preserves the literal
composite pre-state. -/
theorem composite_subsystem_rejection_reachable_witness :
    (FailStop.gate returnWitnessComposite
        (.syscall returnWitnessRejectedCall)).result =
      .completed (.syscall (.rejected (.decode .unknownSyscall))) ∧
    FailStop.SubsystemRejection returnWitnessComposite
      (.syscall returnWitnessRejectedCall)
      (.syscall (.rejected (.decode .unknownSyscall))) ∧
    (FailStop.operationReply returnWitnessComposite
      (.syscall returnWitnessRejectedCall)).isNonfatalRejection = true ∧
    (FailStop.gate returnWitnessComposite
        (.syscall returnWitnessRejectedCall)).state = returnWitnessComposite := by
  have hresult :
      (FailStop.gate returnWitnessComposite
          (.syscall returnWitnessRejectedCall)).result =
        .completed (.syscall (.rejected (.decode .unknownSyscall))) := by
    native_decide
  have hrejected :
      FailStop.SubsystemRejection returnWitnessComposite
        (.syscall returnWitnessRejectedCall)
        (.syscall (.rejected (.decode .unknownSyscall))) :=
    .syscall returnWitnessRejectedCall (.decode .unknownSyscall) (by native_decide)
  have hclassified :
      (FailStop.operationReply returnWitnessComposite
        (.syscall returnWitnessRejectedCall)).isNonfatalRejection = true := by
    native_decide
  exact ⟨hresult, hrejected, hclassified,
    FailStop.gate_classified_rejection_global_atomicity returnWitnessComposite
      (.syscall returnWitnessRejectedCall) hclassified⟩

set_option maxRecDepth 100000 in
/-- Concrete typed composite trace: syscall entry clears old authority, the
syscall body installs its final lifecycle/context and reselects, and the
following return is accepted without changing the composite state. -/
theorem user_return_composite_entry_witness :
    let entered := (FailStop.gate returnWitnessComposite
      (.interrupt returnWitnessSyscallFrame)).state
    let called := (FailStop.gate entered
      (.syscall returnWitnessSyscallCall)).state
    called.ReturnPlanLive = true ∧
      called.execution.returnAuthorityArmed = true ∧
      (FailStop.gate called (.userReturn returnWitnessSyscallRequest)).state = called := by
  dsimp only
  constructor
  · native_decide
  constructor
  · native_decide
  · rfl

set_option maxRecDepth 100000 in
/-- Syscall classification alone cannot authorize a return: the syscall body
must install its final lifecycle/context before authority is reselected. -/
theorem user_return_syscall_entry_cannot_skip_body :
    let entered := (FailStop.gate returnWitnessComposite
      (.interrupt returnWitnessSyscallFrame)).state
    entered.execution.returnAuthorityArmed = false := by
  native_decide

/-- SC-USER-RETURN-FAILSTOP: a rejected outgoing return atomically latches a
typed terminal record, freezes every composite subsystem, and absorbs all
later operations. -/
theorem user_return_rejection_failstop state request reason proposals
    (hmode : state.execution.mode = .running)
    (harmed : state.execution.returnAuthorityArmed = true)
    (hlive : state.ReturnPlanLive = true)
    (hrejected : Interrupt.validateUserReturn
      (FailStop.authoritativeReturnRequest state.execution request) = .rejected reason) :
    let record : FailStop.HaltRecord :=
      { reason := .invalidUserReturn state.execution.returnAuthority.purpose reason
        active := none
        incomingVector := request.hardware.vector
        incomingOrigin := request.hardware.savedPrivilege }
    let next := (FailStop.gate state (.userReturn request)).state
    next.execution.mode = .halted record ∧
      next.execution.core.lifecycle = state.execution.core.lifecycle ∧
      next.scheduler = state.scheduler ∧
      next.preemption = state.preemption ∧
      next.virtualMemory = state.virtualMemory ∧
      next.ipc = state.ipc ∧
      next.capabilities = state.capabilities ∧
      next.lifecycle = state.lifecycle ∧
      FailStop.runOperations next proposals = next := by
  exact FailStop.rejected_user_return_composite_atomicity state request reason proposals
    hmode harmed hlive hrejected

/-- SC-EXTENDED-STATE-DENIAL: a contained unsupported extended-state event is
confined to the authoritative current subject and requires the exact accepted
fail-closed control policy and live address-space binding. -/
theorem extended_state_denial_confined state event subject
    (h : (ExtendedState.classify state event).result = .denied subject) :
    subject = state.currentSubject ∧
      ExtendedState.Denied state.features state.controls ∧
      event.origin = .user ∧
      event.normalizedSubject = state.currentSubject ∧
      event.normalizedAddressSpace = state.activeAddressSpace ∧
      ExtendedState.ContextBound state := by
  exact ExtendedState.denied_subject_confined state event subject h

/-- SC-EXTENDED-STATE-CLEANUP: authoritative denial cleanup removes every
live scheduler and resumable-context reference to the faulting subject. -/
theorem extended_state_denial_cleanup_nonresumable machine subject :
    let cleaned := ResumablePreemption.cleanupSubject machine subject
    cleaned.scheduler.lifecycle.capabilities.subjects subject = false ∧
      subject ∉ cleaned.scheduler.ready ∧
      cleaned.scheduler.lifecycle.current ≠ some subject ∧
      ResumablePreemption.contextFor cleaned.contexts subject = none := by
  exact ExtendedState.denial_cleanup_cannot_resume machine subject

/-- SC-EXTENDED-STATE-GLOBAL: every finite sequence of authoritative composite
operations preserves the exact denied-state predicate. -/
theorem extended_state_global_runtime_preservation state operations
    (hinvariant : ExtendedState.CompositePolicyInvariant state) :
    ExtendedState.CompositePolicyInvariant
      (ExtendedState.runComposite state operations) := by
  exact ExtendedState.runComposite_preserves_policy state operations hinvariant

/-- SC-FAULT-DISPATCH-NONRESUMPTION: every successful atomic user-fault
transition starts from a live, runnable kernel-selected subject and removes it
from live/runnable identity, the ready queue, the current slot, the authoritative
resumable bank, and every address space and mapping it owned. -/
theorem fault_dispatch_success_nonresumption state entry
    (hsuccess : (FaultDispatch.dispatch state entry).action = .idle ∨
      ∃ context, (FaultDispatch.dispatch state entry).action = .dispatch context) :
    ∃ faulting,
      state.scheduler.lifecycle.current = some faulting ∧
        state.scheduler.lifecycle.capabilities.subjects faulting = true ∧
        state.scheduler.lifecycle.runnable faulting = true ∧
        (FaultDispatch.dispatch state entry).state.scheduler.lifecycle.capabilities.subjects
          faulting = false ∧
        (FaultDispatch.dispatch state entry).state.scheduler.lifecycle.runnable
          faulting = false ∧
        faulting ∉ (FaultDispatch.dispatch state entry).state.scheduler.ready ∧
        (FaultDispatch.dispatch state entry).state.scheduler.lifecycle.current ≠ some faulting ∧
        ResumablePreemption.contextFor
          (FaultDispatch.dispatch state entry).state.contexts faulting = none ∧
        ∀ addressSpace,
          state.scheduler.lifecycle.addressOwner addressSpace = some faulting →
            (FaultDispatch.dispatch state entry).state.scheduler.lifecycle.addressOwner
                addressSpace = none ∧
              ∀ page,
                (FaultDispatch.dispatch state entry).state.translations.virtual.mappings
                  addressSpace page = none := by
  exact FaultDispatch.successful_nonresumption state entry hsuccess

/-- SC-SCHEDULED-ISOLATION: equal finite public traces preserve low-equivalence. -/
theorem scheduled_finite_trace_isolation observer left right leftSteps rightSteps
    (hlow : ScheduledObservation.LowEquiv observer left right)
    (hevents : ScheduledObservation.projection observer left leftSteps =
      ScheduledObservation.projection observer right rightSteps) :
    ScheduledObservation.LowEquiv observer
      (ScheduledObservation.run observer left leftSteps).1
      (ScheduledObservation.run observer right rightSteps).1 := by
  exact ScheduledObservation.finite_trace_lowEquiv observer left right leftSteps rightSteps
    hlow hevents

/-- Non-vacuity: a well-formed state and an accepted transition exist. -/
theorem initial_transition_witness :
    KernelTransition.WellFormed KernelTransition.initialState ∧
      (KernelTransition.transition KernelTransition.initialState .initialize).result = .accepted := by
  exact ⟨KernelTransition.initialState_wellFormed, rfl⟩

/-- Concrete non-vacuity witness for the page-table separation contract: the encoder materializes
two leaves for the same page in distinct address spaces and their walks differ. -/
private def pageTableSeparationState : VirtualMapping.State :=
  { memory :=
      { capabilities :=
          { subjects := fun _ => true
            objects := fun object => object = 10 || object = 11
            kinds := fun object =>
              if object = 10 || object = 11 then some .memory else none
            slots := fun _ _ => none }
        allocator :=
          { frames := [4, 5]
            status := fun frame => if frame = 4 then .owned 10
              else if frame = 5 then .owned 11 else .reserved }
        binding := fun object => if object = 10 then some 4
          else if object = 11 then some 5 else none
        issued := fun object => object = 10 || object = 11 }
    owner := fun addressSpace => if addressSpace = 1 then some 1
      else if addressSpace = 2 then some 2 else none
    mappings := fun addressSpace page =>
      if page != 7 then none
      else if addressSpace = 1 then
        some { object := 10, permissions := { read := true } }
      else if addressSpace = 2 then
        some { object := 11, permissions := { read := true } }
      else none
    issuedAddressSpace := fun addressSpace => addressSpace = 1 || addressSpace = 2 }

theorem page_table_separation_witness :
    (X86PageTable.encode pageTableSeparationState 1).leaf 7 =
        some (X86PageTable.Leaf.mk 4 true false true true true) ∧
      (X86PageTable.encode pageTableSeparationState 2).leaf 7 =
        some (X86PageTable.Leaf.mk 5 true false true true true) ∧
      X86PageTable.walk (X86PageTable.encode pageTableSeparationState 1) 7 .read = .ok 4 ∧
      X86PageTable.walk (X86PageTable.encode pageTableSeparationState 2) 7 .read = .ok 5 ∧
      X86PageTable.walk (X86PageTable.encode pageTableSeparationState 1) 7 .read ≠
        X86PageTable.walk (X86PageTable.encode pageTableSeparationState 2) 7 .read := by
  refine ⟨by decide, by decide, by rfl, by rfl, ?_⟩
  simp [pageTableSeparationState, X86PageTable.walk, X86PageTable.encode,
    X86PageTable.encodedLeaf, X86PageTable.userAncestor, X86PageTable.canonicalPage,
    X86PageTable.lowerCanonicalPages, X86PageTable.representableFrame,
    X86PageTable.physicalFrameLimit]

/-- Adversarial executable check: an unsupported command cannot be accepted. -/
example : (KernelTransition.transition KernelTransition.initialState .unsupported).result =
    .rejected := by decide

end LeanOS.SecurityClaims
