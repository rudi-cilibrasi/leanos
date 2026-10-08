import LeanOS.FailStop.Memory

/-!
# Fail-stop composite: per-operation runtime-preservation registry

`OperationPreservesRuntimeWellFormed` is the local obligation contributed by
one public operation.  This module registers the selection, restart,
capability-revocation, syscall, mapping, IPC, and transfer families.
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

/-- The local proof obligation contributed by one public operation to the
universal runtime-preservation theorem.  Keeping this predicate independent of
a particular pre-state lets operation-family proofs be registered once and
then composed over arbitrary mixed traces. -/
def OperationPreservesRuntimeWellFormed (operation : Operation) : Prop :=
  ∀ state, RuntimeWellFormed state →
    RuntimeWellFormed (gate state operation).state

/-- Per-operation preservation composes over the actual sequential gate.  This
is the reusable induction boundary for the universal theorem: after every
`Operation` constructor satisfies `OperationPreservesRuntimeWellFormed`, every
finite mixed runtime trace preserves the global invariant without unfolding
`runOperations` in each operation-family proof. -/
theorem runOperations_preserves_runtimeWellFormed state operations
    (hstate : RuntimeWellFormed state)
    (hoperations : ∀ operation, operation ∈ operations →
      OperationPreservesRuntimeWellFormed operation) :
    RuntimeWellFormed (runOperations state operations) := by
  induction operations generalizing state with
  | nil => simpa [runOperations] using hstate
  | cons operation rest ih =>
      simp only [runOperations]
      apply ih
      · exact hoperations operation (by simp)
          state hstate
      · intro candidate hmember
        exact hoperations candidate (by simp [hmember])

/-- The two fully covered control constructors discharge the new reusable
operation obligation directly. -/
theorem selectUserReturn_operationPreservesRuntimeWellFormed purpose :
    OperationPreservesRuntimeWellFormed (.selectUserReturn purpose) := by
  intro state hstate
  exact gate_selectUserReturn_preserves_runtimeWellFormed state purpose hstate

/-- Outgoing return is now a complete operation-family instance: successful
attestation is atomic and every terminal rejection synchronizes both fail-stop
projections before the trace continues. -/
theorem userReturn_operationPreservesRuntimeWellFormed request :
    OperationPreservesRuntimeWellFormed (.userReturn request) := by
  intro state hstate
  exact gate_userReturn_preserves_runtimeWellFormed state request hstate

theorem restart_operationPreservesRuntimeWellFormed :
    OperationPreservesRuntimeWellFormed .restart := by
  intro state hstate
  exact gate_restart_preserves_runtimeWellFormed state hstate

/-- Capability delegation discharges the reusable operation obligation for
both typed outcomes.  Accepted copy uses the exact fresh subsystem state;
every denial is classified by `SubsystemRejection` and is globally atomic. -/
theorem capabilityCopy_operationPreservesRuntimeWellFormed source destination
    destinationSlot rights :
    OperationPreservesRuntimeWellFormed
      (.capabilityCopy source destination destinationSlot rights) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hcopy : Capability.copy state.capabilities
        state.execution.core.context.currentSubject source destination destinationSlot rights with
    | mk next result =>
        cases result with
        | accepted =>
            exact (gate_capabilityCopy_accepted_preserves_runtimeWellFormed state source
              destination destinationSlot rights next hstate hmode hcopy).1
        | rejected reason =>
            exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
              (.capabilityCopy source destination destinationSlot rights)
              (.capability (.rejected reason)) hstate
              (by simp [gate, hmode, operationReply, hcopy])
              (.capabilityCopy source destination destinationSlot rights reason
                (by simp [hcopy]))).1
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.capabilityCopy source destination destinationSlot rights) hstate hmode

/-- Fail-closed direct revocation is a complete operation family.  The
runtime-safe adapter converts any attempt to remove authority required by live
resources into a typed atomic rejection; every accepted removal supplies the
authority-preservation fact needed by the global invariant. -/
theorem capabilityRevoke_operationPreservesRuntimeWellFormed authoritySlot victim victimSlot :
    OperationPreservesRuntimeWellFormed
      (.capabilityRevoke authoritySlot victim victimSlot) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hrevoke : Capability.revokeRuntimeSafe state.capabilities
        state.execution.core.context.currentSubject authoritySlot victim victimSlot with
    | mk next result =>
        cases result with
        | accepted =>
            exact (gate_capabilityRevoke_accepted_preserves_runtimeWellFormed state
              authoritySlot victim victimSlot next hstate hmode hrevoke).1
        | rejected reason =>
            exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
              (.capabilityRevoke authoritySlot victim victimSlot)
              (.capability (.rejected reason)) hstate
              (by simp [gate, hmode, operationReply, hrevoke])
              (.capabilityRevoke authoritySlot victim victimSlot reason
                (by simp [hrevoke]))).1
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.capabilityRevoke authoritySlot victim victimSlot) hstate hmode

/-- Transitive revocation uses the same fail-closed publication rule while
clearing every descendant admitted by the capability lineage model. -/
theorem capabilityRevokeSubtree_operationPreservesRuntimeWellFormed authoritySlot victim
    victimSlot :
    OperationPreservesRuntimeWellFormed
      (.capabilityRevokeSubtree authoritySlot victim victimSlot) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hrevoke : Capability.revokeSubtreeRuntimeSafe state.capabilities
        state.execution.core.context.currentSubject authoritySlot victim victimSlot with
    | mk next result =>
        cases result with
        | accepted =>
            exact (gate_capabilityRevokeSubtree_accepted_preserves_runtimeWellFormed state
              authoritySlot victim victimSlot next hstate hmode hrevoke).1
        | rejected reason =>
            exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
              (.capabilityRevokeSubtree authoritySlot victim victimSlot)
              (.capability (.rejected reason)) hstate
              (by simp [gate, hmode, operationReply, hrevoke])
              (.capabilityRevokeSubtree authoritySlot victim victimSlot reason
                (by simp [hrevoke]))).1
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.capabilityRevokeSubtree authoritySlot victim victimSlot) hstate hmode

/-- Every raw call that decodes to an access check contributes one complete
operation-family obligation: successful translation is the accepted
non-mutating slice above, while every translation failure is an ordinary
state-preserving subsystem rejection. -/
theorem syscallAccess_operationPreservesRuntimeWellFormed call page access
    (hdecode : Syscall.decode call = .ok (.access page access)) :
    OperationPreservesRuntimeWellFormed (.syscall call) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hreply : (Syscall.dispatch state.virtualMemory state.syscallContext call).reply with
    | accepted =>
        exact (gate_syscall_access_accepted_preserves_runtimeWellFormed state call page access
          hstate hmode hdecode hreply).1
    | rejected reason =>
        exact (gate_subsystem_rejection_preserves_runtimeWellFormed state (.syscall call)
          (.syscall (.rejected reason)) hstate
          (by simp [gate, hmode, operationReply, hreply])
          (.syscall call reason hreply)).1
  · exact gate_rejected_mode_preserves_runtimeWellFormed state (.syscall call) hstate hmode

/-- Every call rejected by the fixed-width decoder is a complete preservation
family, independently of the attacker-controlled words that failed decoding.
The decoder error is surfaced as the exact typed syscall reply and the
composite gate publishes the literal pre-state.  This closes malformed and
unknown syscall numbers at the reusable operation-registration boundary rather
than requiring mixed-trace proofs to reason about them individually. -/
theorem syscallDecodeRejected_operationPreservesRuntimeWellFormed call reason
    (hdecode : Syscall.decode call = .error reason) :
    OperationPreservesRuntimeWellFormed (.syscall call) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · have hreply :
        (Syscall.dispatch state.virtualMemory state.syscallContext call).reply =
          .rejected (.decode reason) := by
      simp [Syscall.dispatch, hdecode]
    exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
      (.syscall call) (.syscall (.rejected (.decode reason))) hstate
      (by simp [gate, hmode, operationReply, hreply])
      (.syscall call (.decode reason) hreply)).1
  · exact gate_rejected_mode_preserves_runtimeWellFormed state (.syscall call) hstate hmode

theorem map_operationPreservesRuntimeWellFormed slot page permissions :
    OperationPreservesRuntimeWellFormed (.map slot page permissions) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hmap : VirtualMapping.map state.virtualMemory
        state.execution.core.context.currentSubject slot
        state.execution.core.context.activeAddressSpace page permissions with
    | mk next result =>
        cases result with
        | accepted =>
            exact (gate_map_accepted_preserves_runtimeWellFormed state slot page permissions
              next hstate hmode hmap).1
        | rejected reason =>
            exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
              (.map slot page permissions) (.map (.rejected reason)) hstate
              (by simp [gate, hmode, operationReply, hmap])
              (.map slot page permissions reason (by simp [hmap]))).1
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.map slot page permissions) hstate hmode

theorem unmap_operationPreservesRuntimeWellFormed page :
    OperationPreservesRuntimeWellFormed (.unmap page) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hunmap : VirtualMapping.unmap state.virtualMemory
        state.execution.core.context.currentSubject
        state.execution.core.context.activeAddressSpace page with
    | mk next result =>
        cases result with
        | accepted =>
            exact (gate_unmap_accepted_invalidates_tlb state page next hmode hunmap hstate).2.1
        | rejected reason =>
            exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
              (.unmap page) (.unmap (.rejected reason)) hstate
              (by simp [gate, hmode, operationReply, hunmap])
              (.unmap page reason (by simp [hunmap]))).1
  · exact gate_rejected_mode_preserves_runtimeWellFormed state (.unmap page) hstate hmode

theorem protect_operationPreservesRuntimeWellFormed page permissions :
    OperationPreservesRuntimeWellFormed (.protect page permissions) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hprotect : TLB.protect state.resumable.translations
        state.execution.core.context.currentSubject
        state.execution.core.context.activeAddressSpace page permissions with
    | mk next result =>
        cases result with
        | accepted =>
            exact (gate_protect_accepted_invalidates_tlb state page permissions
              next hmode hprotect hstate).2.1
        | rejected reason =>
            exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
              (.protect page permissions) (.protect (.rejected reason)) hstate
              (by simp [gate, hmode, operationReply, hprotect])
              (.protect page permissions reason (by simp [hprotect]))).1
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.protect page permissions) hstate hmode

/-- Accepted userspace mapping reuses the raw mapping publication proof after
the generation-bound handle resolves.  The only additional mutation is live
return-authority selection on the already well-formed composite state. -/
theorem syscallMap_operationPreservesRuntimeWellFormed call handleWord page permissions
    (hdecode : Syscall.decode call = .ok (.map handleWord page permissions)) :
    OperationPreservesRuntimeWellFormed (.syscall call) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hreply : (Syscall.dispatch state.virtualMemory state.syscallContext call).reply with
    | rejected reason =>
        exact (gate_subsystem_rejection_preserves_runtimeWellFormed state (.syscall call)
          (.syscall (.rejected reason)) hstate
          (by simp [gate, hmode, operationReply, hreply])
          (.syscall call reason hreply)).1
    | accepted =>
        cases hresolve : CapabilityHandle.resolveCurrent state.virtualMemory.memory.capabilities
            { caller := state.syscallContext.caller } handleWord .memory with
        | error denial =>
            simp only [CompositeState.syscallContext] at hresolve
            simp [Syscall.dispatch, hdecode, Syscall.dispatchDecoded, hresolve,
              CompositeState.syscallContext] at hreply
        | ok resolution =>
            simp only [CompositeState.syscallContext] at hresolve
            cases hmap : (VirtualMapping.map state.virtualMemory state.syscallContext.caller
                resolution.handle.slot state.syscallContext.activeAddressSpace page permissions).result with
            | rejected reason =>
                simp only [CompositeState.syscallContext] at hmap
                simp [Syscall.dispatch, hdecode, Syscall.dispatchDecoded, hresolve, hmap,
                  CompositeState.syscallContext] at hreply
            | accepted =>
                simp only [CompositeState.syscallContext] at hmap
                let next := (VirtualMapping.map state.virtualMemory state.syscallContext.caller
                  resolution.handle.slot state.syscallContext.activeAddressSpace page permissions).state
                have hmemory : next.memory = state.virtualMemory.memory := by
                  exact VirtualMapping.map_memory _ _ _ _ _ _
                have howner : next.owner = state.virtualMemory.owner := by
                  exact VirtualMapping.map_owner _ _ _ _ _ _
                have hvirtual : VirtualMapping.LifecycleWellFormed next :=
                  VirtualMapping.map_preserves_lifecycleWellFormed _ _ _ _ _ _
                    hstate.2.2.2.2.1
                let translations : TLB.State :=
                  { state.resumable.translations with virtual := next }
                have htlb : TLB.Coherent translations := by
                  simpa [translations, TLB.Coherent] using
                    hstate.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2
                have hinstalled := installVirtualMemory_preserves_runtimeWellFormed
                  state next translations hstate hmemory howner hvirtual htlb rfl
                have hselectedGate := gate_selectUserReturn_preserves_runtimeWellFormed
                  (installVirtualMemory state next translations) .syscallResume hinstalled
                have hselected : RuntimeWellFormed
                    (selectLiveReturnAuthority (installVirtualMemory state next translations)
                      .syscallResume) := by
                  simpa [gate, applyOperation, installVirtualMemory, hmode] using hselectedGate
                have houtcome : Syscall.dispatch state.virtualMemory state.syscallContext call =
                    { state := next, reply := .accepted } := by
                  simp [Syscall.dispatch, hdecode, Syscall.dispatchDecoded, hresolve, hmap,
                    CompositeState.syscallContext, next]
                simpa [gate, hmode, applyOperation, houtcome, hdecode,
                  next, translations] using hselected
  · exact gate_rejected_mode_preserves_runtimeWellFormed state (.syscall call) hstate hmode

theorem syscallUnmap_operationPreservesRuntimeWellFormed call page
    (hdecode : Syscall.decode call = .ok (.unmap page)) :
    OperationPreservesRuntimeWellFormed (.syscall call) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hreply : (Syscall.dispatch state.virtualMemory state.syscallContext call).reply with
    | rejected reason =>
        exact (gate_subsystem_rejection_preserves_runtimeWellFormed state (.syscall call)
          (.syscall (.rejected reason)) hstate
          (by simp [gate, hmode, operationReply, hreply])
          (.syscall call reason hreply)).1
    | accepted =>
        cases hunmap : (VirtualMapping.unmap state.virtualMemory state.syscallContext.caller
            state.syscallContext.activeAddressSpace page).result with
        | rejected reason =>
            simp only [CompositeState.syscallContext] at hunmap
            simp [Syscall.dispatch, hdecode, Syscall.dispatchDecoded, hunmap,
              CompositeState.syscallContext] at hreply
        | accepted =>
            simp only [CompositeState.syscallContext] at hunmap
            let next := (VirtualMapping.unmap state.virtualMemory state.syscallContext.caller
              state.syscallContext.activeAddressSpace page).state
            have hmemory : next.memory = state.virtualMemory.memory :=
              VirtualMapping.unmap_memory _ _ _ _
            have howner : next.owner = state.virtualMemory.owner :=
              VirtualMapping.unmap_owner _ _ _ _
            have hvirtual : VirtualMapping.LifecycleWellFormed next :=
              VirtualMapping.unmap_preserves_lifecycleWellFormed _ _ _ _ hstate.2.2.2.2.1
            let translations := TLB.invalidatePage
              { state.resumable.translations with virtual := next }
              state.syscallContext.activeAddressSpace page
            have htlb : TLB.Coherent translations := by
              exact TLB.invalidate_page_preserves_coherent _ _ _
                hstate.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2
            have hinstalled := installVirtualMemory_preserves_runtimeWellFormed
              state next translations hstate hmemory howner hvirtual htlb rfl
            have hselectedGate := gate_selectUserReturn_preserves_runtimeWellFormed
              (installVirtualMemory state next translations) .syscallResume hinstalled
            have hselected : RuntimeWellFormed
                (selectLiveReturnAuthority (installVirtualMemory state next translations)
                  .syscallResume) := by
              simpa [gate, applyOperation, installVirtualMemory, hmode] using hselectedGate
            have houtcome : Syscall.dispatch state.virtualMemory state.syscallContext call =
                { state := next, reply := .accepted } := by
              simp [Syscall.dispatch, hdecode, Syscall.dispatchDecoded, hunmap,
                CompositeState.syscallContext, next]
            simpa [gate, hmode, applyOperation, houtcome, hdecode,
              next, translations] using hselected
  · exact gate_rejected_mode_preserves_runtimeWellFormed state (.syscall call) hstate hmode

/-- Every raw syscall word tuple now satisfies the universal composite
preservation obligation: decoder denial, map, unmap, and access exhaust the
finite decoded vocabulary. -/
theorem syscall_operationPreservesRuntimeWellFormed call :
    OperationPreservesRuntimeWellFormed (.syscall call) := by
  cases hdecode : Syscall.decode call with
  | error reason => exact syscallDecodeRejected_operationPreservesRuntimeWellFormed call reason hdecode
  | ok operation =>
      cases operation with
      | map handleWord page permissions =>
          exact syscallMap_operationPreservesRuntimeWellFormed call handleWord page permissions hdecode
      | unmap page => exact syscallUnmap_operationPreservesRuntimeWellFormed call page hdecode
      | access page access => exact syscallAccess_operationPreservesRuntimeWellFormed call page access hdecode

/-- Arbitrary finite mixtures of accepted and rejected raw syscalls preserve
the global runtime invariant through the actual sequential composite gate. -/
theorem runSyscalls_preserves_runtimeWellFormed state (calls : List Syscall.UntrustedCall)
    (hstate : RuntimeWellFormed state) :
    RuntimeWellFormed (runOperations state (calls.map Operation.syscall)) := by
  apply runOperations_preserves_runtimeWellFormed state _ hstate
  intro operation hmember
  obtain ⟨call, _hcall, rfl⟩ := List.mem_map.mp hmember
  exact syscall_operationPreservesRuntimeWellFormed call

private theorem dispatchIPC_send_classifies state handleWord word0 word1 :
    (dispatchIPC state (.send handleWord word0 word1)).reply = .syscall .sent ∨
      (∃ reason, (dispatchIPC state (.send handleWord word0 word1)).reply =
        .syscall (.sendHandleRejected reason)) ∨
      ∃ reason, (dispatchIPC state (.send handleWord word0 word1)).reply =
        .syscall (.sendRejected reason) := by
  cases hresolve : CapabilityHandle.resolveCurrent state.ipc.endpoints.capabilities
      { caller := state.execution.core.context.currentSubject }
      handleWord .endpoint with
  | error reason =>
      exact Or.inr (Or.inl ⟨reason, by simp [dispatchIPC, IPCSyscall.dispatch, hresolve]⟩)
  | ok resolution =>
      cases hsend : EndpointIPC.send state.ipc.endpoints
          state.execution.core.context.currentSubject resolution.handle.slot
          { word0, word1 } with
      | mk next result =>
          cases result with
          | accepted =>
              exact Or.inl (by simp [dispatchIPC, IPCSyscall.dispatch, hresolve, hsend])
          | rejected reason =>
              exact Or.inr (Or.inr
                ⟨reason, by simp [dispatchIPC, IPCSyscall.dispatch, hresolve, hsend]⟩)

/-- The complete data-send constructor discharges the reusable operation
obligation.  Its unique success reply uses the accepted-send preservation
theorem; every other finite reply is a state-preserving typed rejection. -/
theorem ipcSend_operationPreservesRuntimeWellFormed handleWord word0 word1 :
    OperationPreservesRuntimeWellFormed (.ipc (.send handleWord word0 word1)) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · rcases dispatchIPC_send_classifies state handleWord word0 word1 with
      hsent | ⟨reason, hrejected⟩ | ⟨reason, hrejected⟩
    · exact (gate_ipc_send_accepted_preserves_runtimeWellFormed state
        handleWord word0 word1 hstate hmode hsent).1
    · exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
        (.ipc (.send handleWord word0 word1))
        (.ipc (.syscall (.sendHandleRejected reason))) hstate
        (by simp [gate, hmode, operationReply, hrejected])
        (.ipcSendHandle (.send handleWord word0 word1) reason hrejected)).1
    · exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
        (.ipc (.send handleWord word0 word1))
        (.ipc (.syscall (.sendRejected reason))) hstate
        (by simp [gate, hmode, operationReply, hrejected])
        (.ipcSend (.send handleWord word0 word1) reason hrejected)).1
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.ipc (.send handleWord word0 word1)) hstate hmode

private theorem dispatchIPC_receive_classifies state handleWord :
    (dispatchIPC state (.receive handleWord)).reply = .sealedTransferPending ∨
      (∃ sender word0 word1, (dispatchIPC state (.receive handleWord)).reply =
        .syscall (.delivered sender word0 word1)) ∨
      (∃ reason, (dispatchIPC state (.receive handleWord)).reply =
        .syscall (.receiveHandleRejected reason)) ∨
      ∃ reason, (dispatchIPC state (.receive handleWord)).reply =
        .syscall (.receiveRejected reason) := by
  cases hguard : CapabilityHandle.resolveCurrent state.transfers.capabilities
      { caller := state.execution.core.context.currentSubject }
      handleWord .endpoint with
  | ok endpoint =>
      cases hpending : state.transfers.pending endpoint.capability.object with
      | some transfer =>
          exact Or.inl (by simp [dispatchIPC, hguard, hpending])
      | none =>
          cases hresolve : CapabilityHandle.resolveCurrent state.ipc.endpoints.capabilities
              { caller := state.execution.core.context.currentSubject }
              handleWord .endpoint with
          | error reason =>
              exact Or.inr (Or.inr (Or.inl
                ⟨reason, by simp [dispatchIPC, hguard, hpending,
                  IPCSyscall.dispatch, hresolve]⟩))
          | ok resolution =>
              cases hreceive : EndpointIPC.receive state.ipc.endpoints
                  state.execution.core.context.currentSubject resolution.handle.slot with
              | mk next result =>
                  cases result with
                  | delivered envelope =>
                      exact Or.inr (Or.inl
                        ⟨envelope.sender, envelope.payload.word0, envelope.payload.word1,
                          by simp [dispatchIPC, hguard, hpending,
                            IPCSyscall.dispatch, hresolve, hreceive]⟩)
                  | rejected reason =>
                      exact Or.inr (Or.inr (Or.inr
                        ⟨reason, by simp [dispatchIPC, hguard, hpending,
                          IPCSyscall.dispatch, hresolve, hreceive]⟩))
  | error guardReason =>
      cases hresolve : CapabilityHandle.resolveCurrent state.ipc.endpoints.capabilities
          { caller := state.execution.core.context.currentSubject }
          handleWord .endpoint with
      | error reason =>
          exact Or.inr (Or.inr (Or.inl
            ⟨reason, by simp [dispatchIPC, hguard, IPCSyscall.dispatch, hresolve]⟩))
      | ok resolution =>
          cases hreceive : EndpointIPC.receive state.ipc.endpoints
              state.execution.core.context.currentSubject resolution.handle.slot with
          | mk next result =>
              cases result with
              | delivered envelope =>
                  exact Or.inr (Or.inl
                    ⟨envelope.sender, envelope.payload.word0, envelope.payload.word1,
                      by simp [dispatchIPC, hguard, IPCSyscall.dispatch, hresolve, hreceive]⟩)
              | rejected reason =>
                  exact Or.inr (Or.inr (Or.inr
                    ⟨reason, by simp [dispatchIPC, hguard,
                      IPCSyscall.dispatch, hresolve, hreceive]⟩))

/-- The complete data-receive constructor likewise composes accepted delivery,
sealed-mailbox protection, ordinary endpoint rejection, and outer latch
rejection into one operation-family preservation theorem. -/
theorem ipcReceive_operationPreservesRuntimeWellFormed handleWord :
    OperationPreservesRuntimeWellFormed (.ipc (.receive handleWord)) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · rcases dispatchIPC_receive_classifies state handleWord with
      hsealed | ⟨sender, word0, word1, hdelivered⟩ |
        ⟨reason, hrejected⟩ | ⟨reason, hrejected⟩
    · exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
        (.ipc (.receive handleWord)) (.ipc .sealedTransferPending) hstate
        (by simp [gate, hmode, operationReply, hsealed])
        (.ipcSealed (.receive handleWord) hsealed)).1
    · exact (gate_ipc_receive_accepted_preserves_runtimeWellFormed state
        handleWord sender word0 word1 hstate hmode hdelivered).1
    · exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
        (.ipc (.receive handleWord))
        (.ipc (.syscall (.receiveHandleRejected reason))) hstate
        (by simp [gate, hmode, operationReply, hrejected])
        (.ipcReceiveHandle (.receive handleWord) reason hrejected)).1
    · exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
        (.ipc (.receive handleWord))
        (.ipc (.syscall (.receiveRejected reason))) hstate
        (by simp [gate, hmode, operationReply, hrejected])
        (.ipcReceive (.receive handleWord) reason hrejected)).1
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.ipc (.receive handleWord)) hstate hmode

/-- The public IPC constructor is now one complete universal-preservation
family.  Call-shape case analysis is confined to this registration boundary;
mixed traces can quantify over an arbitrary untrusted IPC call and reuse the
generic `OperationPreservesRuntimeWellFormed` induction contract directly. -/
theorem ipc_operationPreservesRuntimeWellFormed call :
    OperationPreservesRuntimeWellFormed (.ipc call) := by
  cases call with
  | send handleWord word0 word1 =>
      exact ipcSend_operationPreservesRuntimeWellFormed handleWord word0 word1
  | receive handleWord =>
      exact ipcReceive_operationPreservesRuntimeWellFormed handleWord

/-- Every public sealed-transfer offer is now a complete composite operation
family: authority/handle failures are typed atomic rejections, while success
publishes the exact pending descendant and endpoint mailbox without weakening
any runtime invariant. -/
theorem transferOffer_operationPreservesRuntimeWellFormed endpointWord sourceWord sourceKind
    payload rights :
    OperationPreservesRuntimeWellFormed
      (.transferOffer endpointWord sourceWord sourceKind payload rights) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases hoffer : CapabilityTransfer.offerWords state.transfers
        state.execution.core.context.currentSubject endpointWord sourceWord sourceKind payload rights with
    | mk next result =>
        cases result with
        | accepted =>
            exact (gate_transferOffer_accepted_preserves_runtimeWellFormed state endpointWord
              sourceWord sourceKind payload rights hstate hmode (by simp [hoffer])).1
        | rejected reason =>
            exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
              (.transferOffer endpointWord sourceWord sourceKind payload rights)
              (.transferOffer (.rejected reason)) hstate
              (by simp [gate, hmode, operationReply, hoffer])
              (.transferOffer endpointWord sourceWord sourceKind payload rights reason
                (by simp [hoffer]))).1
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.transferOffer endpointWord sourceWord sourceKind payload rights) hstate hmode

/-- Every public sealed-transfer receipt is a complete composite operation
family: malformed, stale, and unavailable receipts reject atomically, while a
delivery consumes the mailbox and installs authority in one globally
well-formed step. -/
theorem transferAccept_operationPreservesRuntimeWellFormed endpointWord destinationSlot :
    OperationPreservesRuntimeWellFormed
      (.transferAccept endpointWord destinationSlot) := by
  intro state hstate
  by_cases hmode : state.execution.mode = .running
  · cases haccept : CapabilityTransfer.acceptWord state.transfers
        state.execution.core.context.currentSubject endpointWord destinationSlot with
    | mk next result deliveredWord =>
        cases result with
        | delivered envelope =>
            exact (gate_transferAccept_delivered_preserves_runtimeWellFormed state
              endpointWord destinationSlot envelope hstate hmode (by simp [haccept])).1
        | rejected reason =>
            exact (gate_subsystem_rejection_preserves_runtimeWellFormed state
              (.transferAccept endpointWord destinationSlot)
              (.transferAccept (.rejected reason) deliveredWord) hstate
              (by simp [gate, hmode, operationReply, haccept])
              (.transferAccept endpointWord destinationSlot reason deliveredWord
                (by simp [haccept]) (by simp [haccept]))).1
  · exact gate_rejected_mode_preserves_runtimeWellFormed state
      (.transferAccept endpointWord destinationSlot) hstate hmode

end LeanOS.FailStop
