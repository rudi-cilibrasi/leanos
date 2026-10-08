import LeanOS.FailStop.Footprint

/-!
# Fail-stop composite: the ordinary gate

The exact typed reply of each `Operation` (`operationReply`), its subsystem
rejection classification, the ordinary `gate`, the DMA control observation,
and the gate's rejection atomicity theorems.
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

theorem applyNmi_preserves_runtimeWellFormed state raw context
    (hstate : RuntimeWellFormed state) :
    RuntimeWellFormed (applyOperation state (.nmi raw context)) := by
  cases hmode : state.execution.mode with
  | halted record => simpa [applyOperation, hmode] using hstate
  | running | handling =>
      simp only [applyOperation, hmode]
      rcases hstate with
        ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
          hscheduler, hpreemption, hresumable, htransfers, _hterminal, hlive,
          hblocking, hports⟩
      have hexecution' :=
        dispatchNmi_preserves_wellFormed state.execution raw context hexecution
      have hnotHalted : ∀ record, state.execution.mode ≠ .halted record := by
        intro record
        simp [hmode]
      have hhalted := dispatchNmi_nonhalted_halts state.execution raw context hnotHalted
      have hdisarmed :=
        dispatchNmi_nonhalted_disarms state.execution raw context hnotHalted
      refine ⟨?_, hexecution', hlifecycle, hcapabilities, hvirtual, hipc, hscheduler,
        hpreemption, ?_, htransfers, ?_, ?_, hblocking, hports⟩
      · simpa [CompositeState.Coherent] using hcoherent
      · simpa using
          (ResumablePreemption.wellFormed_set_halted state.resumable true).2 hresumable
      · simpa using hhalted
      · simp [hdisarmed]

/-- Exact typed observation of the subsystem transition selected by an
operation.  Unlike the former generic `accepted`, this cannot erase an
operation-specific rejection. -/
def operationReply (state : CompositeState) : Operation → OperationReply
  | .interrupt frame =>
      match (dispatchHardware state.execution frame).action with
      | .contained subject =>
          if state.lifecycle.current = some subject then
            .interrupt (.contained subject)
          else .interruptIdentityRejected subject
      | action => .interrupt action
  | .nmi raw context => .nmi (dispatchNmi state.execution raw context).action
  | .selectUserReturn purpose =>
      .returnSelection (selectLiveReturnAuthority state purpose).execution.returnAuthorityArmed
  | .userReturn request =>
      let execution :=
        if state.ReturnPlanLive then state.execution
        else { state.execution with returnAuthorityArmed := false }
      match (completeUserReturn execution request).action with
      | .accepted _ => .userReturn .accepted
      | .fatal record => .userReturn (.fatal record)
      | .alreadyHalted record => .userReturn (.alreadyHalted record)
  | .syscall call => .syscall (Syscall.dispatch state.virtualMemory state.syscallContext call).reply
  | .ipc call => .ipc (dispatchIPC state call).reply
  | .resumePreempt frame registers =>
      let outcome := ResumablePreemption.switch state.resumable state.execution.core
        frame registers
      .resume outcome.restored outcome.error
  | .transferOffer endpointWord sourceWord sourceKind payload rights =>
      .transferOffer
        (CapabilityTransfer.offerWords state.transfers
          state.execution.core.context.currentSubject endpointWord sourceWord sourceKind
          payload rights).result
  | .transferAccept endpointWord destinationSlot =>
      let outcome := CapabilityTransfer.acceptWord state.transfers
        state.execution.core.context.currentSubject endpointWord destinationSlot
      .transferAccept outcome.result outcome.deliveredWord
  | .capabilityCopy source destination destinationSlot rights =>
      .capability
        (Capability.copy state.capabilities state.execution.core.context.currentSubject
          source destination destinationSlot rights).result
  | .capabilityRevoke authoritySlot victim victimSlot =>
      .capability
        (Capability.revokeRuntimeSafe state.capabilities
          state.execution.core.context.currentSubject
          authoritySlot victim victimSlot).result
  | .capabilityRevokeSubtree authoritySlot victim victimSlot =>
      .capability
        (Capability.revokeSubtreeRuntimeSafe state.capabilities
          state.execution.core.context.currentSubject
          authoritySlot victim victimSlot).result
  | .map slot page permissions =>
      .map (VirtualMapping.map state.virtualMemory state.execution.core.context.currentSubject slot
        state.execution.core.context.activeAddressSpace page permissions).result
  | .unmap page =>
      .unmap (VirtualMapping.unmap state.virtualMemory state.execution.core.context.currentSubject
        state.execution.core.context.activeAddressSpace page).result
  | .protect page permissions =>
      .protect (TLB.protect state.resumable.translations
        state.execution.core.context.currentSubject
        state.execution.core.context.activeAddressSpace page permissions).result
  | .createSubject subject => .createSubject (SubjectLifecycle.create state.lifecycle subject).result
  | .terminateSubject subject =>
      .terminateSubject (SubjectLifecycle.terminate state.lifecycle subject).result
  | .scheduleAdd subject => .scheduler (schedulerAdmission state subject).result
  | .scheduleRemove subject =>
      .scheduleRemove (ResumablePreemption.remove state.resumable subject).result
  | .scheduleNext => .scheduler (schedulerDispatch state).result
  | .scheduleYield => .scheduler (schedulerYield state).result
  | .scheduleTick => .scheduler (schedulerTick state).result
  | .terminateCurrent => .scheduler (Scheduler.terminateCurrent state.scheduler).result
  | .restart => .restarted

/-- Evidence that one operation produced one of the finite, ordinary typed
subsystem rejections.  Fatal entry/return results and busy/terminal gate
rejections are deliberately separate. -/
inductive SubsystemRejection (state : CompositeState) : Operation → OperationReply → Prop
  | interruptIdentity frame subject
      (haction : (dispatchHardware state.execution frame).action = .contained subject)
      (hmismatch : state.lifecycle.current ≠ some subject) :
      SubsystemRejection state (.interrupt frame) (.interruptIdentityRejected subject)
  | syscall call reason
      (h : (Syscall.dispatch state.virtualMemory state.syscallContext call).reply = .rejected reason) :
      SubsystemRejection state (.syscall call) (.syscall (.rejected reason))
  | ipcSendHandle call reason
      (h : (dispatchIPC state call).reply = .syscall (.sendHandleRejected reason)) :
      SubsystemRejection state (.ipc call) (.ipc (.syscall (.sendHandleRejected reason)))
  | ipcSend call reason
      (h : (dispatchIPC state call).reply = .syscall (.sendRejected reason)) :
      SubsystemRejection state (.ipc call) (.ipc (.syscall (.sendRejected reason)))
  | ipcReceiveHandle call reason
      (h : (dispatchIPC state call).reply = .syscall (.receiveHandleRejected reason)) :
      SubsystemRejection state (.ipc call) (.ipc (.syscall (.receiveHandleRejected reason)))
  | ipcReceive call reason
      (h : (dispatchIPC state call).reply = .syscall (.receiveRejected reason)) :
      SubsystemRejection state (.ipc call) (.ipc (.syscall (.receiveRejected reason)))
  | ipcSealed call (h : (dispatchIPC state call).reply = .sealedTransferPending) :
      SubsystemRejection state (.ipc call) (.ipc .sealedTransferPending)
  | resumePreempt frame registers reason
      (hnonfatal : reason ≠ .fatalEntry)
      (herror : (ResumablePreemption.switch state.resumable state.execution.core
        frame registers).error = some reason) :
      SubsystemRejection state (.resumePreempt frame registers)
        (.resume none (some reason))
  | transferOffer endpointWord sourceWord sourceKind payload rights reason
      (h : (CapabilityTransfer.offerWords state.transfers
        state.execution.core.context.currentSubject endpointWord sourceWord sourceKind payload rights).result =
          .rejected reason) :
      SubsystemRejection state (.transferOffer endpointWord sourceWord sourceKind payload rights)
        (.transferOffer (.rejected reason))
  | transferAccept endpointWord destinationSlot reason deliveredWord
      (hresult : (CapabilityTransfer.acceptWord state.transfers
        state.execution.core.context.currentSubject endpointWord destinationSlot).result = .rejected reason)
      (hword : (CapabilityTransfer.acceptWord state.transfers
        state.execution.core.context.currentSubject endpointWord destinationSlot).deliveredWord = deliveredWord) :
      SubsystemRejection state (.transferAccept endpointWord destinationSlot)
        (.transferAccept (.rejected reason) deliveredWord)
  | capabilityCopy source destination destinationSlot rights reason
      (h : (Capability.copy state.capabilities state.execution.core.context.currentSubject
        source destination destinationSlot rights).result = .rejected reason) :
      SubsystemRejection state (.capabilityCopy source destination destinationSlot rights)
        (.capability (.rejected reason))
  | capabilityRevoke authoritySlot victim victimSlot reason
      (h : (Capability.revokeRuntimeSafe state.capabilities
        state.execution.core.context.currentSubject
        authoritySlot victim victimSlot).result = .rejected reason) :
      SubsystemRejection state (.capabilityRevoke authoritySlot victim victimSlot)
        (.capability (.rejected reason))
  | capabilityRevokeSubtree authoritySlot victim victimSlot reason
      (h : (Capability.revokeSubtreeRuntimeSafe state.capabilities
        state.execution.core.context.currentSubject
        authoritySlot victim victimSlot).result = .rejected reason) :
      SubsystemRejection state (.capabilityRevokeSubtree authoritySlot victim victimSlot)
        (.capability (.rejected reason))
  | map slot page permissions reason
      (h : (VirtualMapping.map state.virtualMemory state.execution.core.context.currentSubject slot
        state.execution.core.context.activeAddressSpace page permissions).result = .rejected reason) :
      SubsystemRejection state (.map slot page permissions) (.map (.rejected reason))
  | unmap page reason
      (h : (VirtualMapping.unmap state.virtualMemory state.execution.core.context.currentSubject
        state.execution.core.context.activeAddressSpace page).result = .rejected reason) :
      SubsystemRejection state (.unmap page) (.unmap (.rejected reason))
  | protect page permissions reason
      (h : (TLB.protect state.resumable.translations
        state.execution.core.context.currentSubject
        state.execution.core.context.activeAddressSpace page permissions).result =
          .rejected reason) :
      SubsystemRejection state (.protect page permissions) (.protect (.rejected reason))
  | createSubject subject reason
      (h : (SubjectLifecycle.create state.lifecycle subject).result = .rejected reason) :
      SubsystemRejection state (.createSubject subject) (.createSubject (.rejected reason))
  | terminateSubject subject reason
      (h : (SubjectLifecycle.terminate state.lifecycle subject).result = .rejected reason) :
      SubsystemRejection state (.terminateSubject subject) (.terminateSubject (.rejected reason))
  | scheduleAdd subject reason
      (h : (schedulerAdmission state subject).result = .rejected reason) :
      SubsystemRejection state (.scheduleAdd subject) (.scheduler (.rejected reason))
  | scheduleRemove subject reason
      (h : (ResumablePreemption.remove state.resumable subject).result = .rejected reason) :
      SubsystemRejection state (.scheduleRemove subject) (.scheduleRemove (.rejected reason))
  | scheduleNext reason (h : (schedulerDispatch state).result = .rejected reason) :
      SubsystemRejection state .scheduleNext (.scheduler (.rejected reason))
  | scheduleYield reason (h : (schedulerYield state).result = .rejected reason) :
      SubsystemRejection state .scheduleYield (.scheduler (.rejected reason))
  | scheduleTick reason (h : (schedulerTick state).result = .rejected reason) :
      SubsystemRejection state .scheduleTick (.scheduler (.rejected reason))
  | terminateCurrent reason (h : (Scheduler.terminateCurrent state.scheduler).result = .rejected reason) :
      SubsystemRejection state .terminateCurrent (.scheduler (.rejected reason))

/-- A contained user fault is published to both scheduler views in the same
composite step, so neither can select from the pre-termination lifecycle. -/
theorem interrupt_contained_synchronizes_lifecycle state frame subject
    (hcurrent : state.lifecycle.current = some subject)
    (hcontained : (dispatchHardware state.execution frame).action = .contained subject) :
    let next := applyOperation state (.interrupt frame)
    next.scheduler.lifecycle = next.execution.core.lifecycle ∧
      next.preemption.scheduler.lifecycle = next.execution.core.lifecycle := by
  simp [applyOperation, hcontained, hcurrent, publishInterruptCleanup,
    installTerminatedResumable]

/-- A contained user fault publishes the complete terminal post-state for the
faulting identity in one operation.  Every duplicated lifecycle view marks the
subject dead, the scheduler and resumable bank retain no selectable reference,
and the authoritative blocking waiter/context pair is removed together. -/
theorem interrupt_contained_cleans_faulting_subject state frame subject
    (hstate : RuntimeWellFormed state)
    (hcurrent : state.lifecycle.current = some subject)
    (hcontained : (dispatchHardware state.execution frame).action = .contained subject) :
    let next := applyOperation state (.interrupt frame)
    next.lifecycle.capabilities.subjects subject = false ∧
      next.execution.core.lifecycle.capabilities.subjects subject = false ∧
      next.scheduler.lifecycle.capabilities.subjects subject = false ∧
      next.preemption.scheduler.lifecycle.capabilities.subjects subject = false ∧
      next.resumable.scheduler.lifecycle.capabilities.subjects subject = false ∧
      subject ∉ next.scheduler.ready ∧
      next.scheduler.lifecycle.current ≠ some subject ∧
      ResumablePreemption.contextFor next.resumable.contexts subject = none ∧
      next.blockingIPC.waiterEndpoint subject = none ∧
      next.blockingContexts subject = none := by
  have hdead := ResumablePreemption.cleanup_terminates_subject
    state.resumable subject
  have hscheduler := ResumablePreemption.cleanup_removes_scheduler_membership
    state.resumable subject
  have hcontext := ResumablePreemption.cleanup_removes_context
    state.resumable subject
  have hlive : state.lifecycle.capabilities.subjects subject = true :=
    hstate.2.2.1.2.2.2.2.2 subject hcurrent
  have hblockingAccepted :
      (SubjectLifecycle.terminate state.blockingIPC.scheduler.lifecycle subject).result =
        .accepted := by
    rw [hstate.blockingLifecycle]
    simp [SubjectLifecycle.terminate, hstate.2.2.1.1 subject hlive, hlive]
  have hblockingClean := BlockingIPCContext.terminate_accepted_cleans_self
    state.blockingIPCContext subject hblockingAccepted
  have hdetached :
      let detached := BlockingIPCContext.detachInvalidated
        (BlockingIPCContext.terminate state.blockingIPCContext subject)
        state.deferredCancels
        (ResumablePreemption.cleanupSubject state.resumable subject).scheduler
      detached.1.ipc.waiterEndpoint subject = none ∧
        detached.1.blocked subject = none := by
    simp [BlockingIPCContext.detachInvalidated,
      hblockingClean.1, hblockingClean.2]
  simp [applyOperation, hcontained, hcurrent, publishInterruptCleanup,
    installTerminatedResumable, hdead, hscheduler.1, hscheduler.2, hcontext,
    hdetached.1, hdetached.2]

/-- A data-only receive cannot consume the envelope paired with a sealed
descendant.  The composite reply identifies the required transfer operation,
and every authoritative projection remains byte-for-byte unchanged. -/
theorem ipc_receive_preserves_sealed_transfer state handleWord endpoint transfer
    (hresolve : CapabilityHandle.resolveCurrent state.transfers.capabilities
      { caller := state.execution.core.context.currentSubject }
      handleWord .endpoint = .ok endpoint)
    (hpending : state.transfers.pending endpoint.capability.object = some transfer) :
    dispatchIPC state (.receive handleWord) =
      { state, reply := .sealedTransferPending } := by
  simp [dispatchIPC, hresolve, hpending]

/-- Fatal resumable entry latches both the exact #74 state and the composite
execution mode in one transition.  It can therefore no longer leave the
runtime apparently running with a terminal context bank. -/
theorem resumePreempt_halted_latches state frame registers
    (hhalted : (ResumablePreemption.switch state.resumable state.execution.core
      frame registers).state.halted = true) :
    let next := applyOperation state (.resumePreempt frame registers)
    next.resumable.halted = true ∧
      next.execution.mode = (dispatchHardware state.execution frame).state.mode := by
  have herror := ResumablePreemption.halted_reports_fatalEntry
    state.resumable state.execution.core frame registers hhalted
  simp [applyOperation, herror, hhalted, installResumable, installLifecycle]

/-- Resumable save/select/restore republishes the scheduler-selected current
subject as the only execution caller and active address space.  Incoming frame
and register payloads therefore cannot leave the composite execution latch
bound to the preemption victim after an accepted switch. -/
theorem resumePreempt_synchronizes_current_context state frame registers
    (hcoherent : state.Coherent) :
    let next := applyOperation state (.resumePreempt frame registers)
    ∀ subject, next.scheduler.lifecycle.current = some subject →
      next.execution.core.context.currentSubject = subject ∧
      next.execution.core.context.activeAddressSpace = subject := by
  rcases hcoherent with
    ⟨_, hschedulerLifecycle, _, _, _, _, _, _, _, _, hcontext, _, _⟩
  have hcontextScheduler : ∀ subject,
      state.scheduler.lifecycle.current = some subject →
        state.execution.core.context.currentSubject = subject ∧
          state.execution.core.context.activeAddressSpace = subject := by
    intro subject hcurrent
    apply hcontext
    rw [← hschedulerLifecycle]
    exact hcurrent
  simp only [applyOperation]
  generalize hs : ResumablePreemption.switch state.resumable state.execution.core
    frame registers = outcome
  cases herror : outcome.error with
  | none =>
    simp only [herror, installResumable]
    intro subject hcurrent
    simp [hcurrent]
  | some reason =>
    cases reason with
    | fatalEntry =>
      cases hhalted : outcome.state.halted <;>
        simp only [herror, hhalted, Bool.false_eq_true, ite_false, ite_true,
          installResumable]
      · exact hcontextScheduler
      · intro subject hcurrent
        simp [hcurrent]
    | nonTimer | malformedIncoming | noCurrent | contextMismatch | duplicateSave |
        staleActiveSpace | bankFull | schedulerRejected | noDestination | staleDestination =>
      simpa [herror] using hcontextScheduler

/-- The sole composite step computes the post-state by invoking the typed
subsystem transition internally. -/
def gate (state : CompositeState) (operation : Operation) : GateOutcome :=
  match operation with
  | .nmi raw context =>
      match state.execution.mode with
      | .halted record => { state, result := .rejectedHalted record }
      | .running | .handling _ =>
          { state := applyOperation state (.nmi raw context)
            result := .completed (operationReply state (.nmi raw context)) }
  | operation =>
      match state.execution.mode with
      | .running =>
          { state := applyOperation state operation
            result := .completed (operationReply state operation) }
      | .handling _ => { state, result := .rejectedBusy }
      | .halted record => { state, result := .rejectedHalted record }

/-- DMA quarantine reads only the accepted PCI authority and the live control
observation, so it is a predicate over exactly those two projections. -/
theorem CompositeState.dmaQuarantined_dependsOn :
    CompositeState.DependsOn
      (fun projection => decide (projection ∈ [.dmaAccepted, .dmaObserved]))
      CompositeState.DMAQuarantined := by
  intro before after same holds
  have accepted : after.dmaAccepted = before.dmaAccepted := same .dmaAccepted (by decide)
  have observed : after.dmaObserved = before.dmaObserved := same .dmaObserved (by decide)
  unfold CompositeState.DMAQuarantined at holds ⊢
  rw [accepted, observed]
  exact holds

/-- **Gate frame rule.**  Accepted, busy, and halted gate steps all respect the
operation's declared footprint: the accepted branch is `applyOperation` and the
rejection branches stutter. -/
theorem gate_frames state operation :
    CompositeState.Frames operation.footprint state (gate state operation).state := by
  cases operation <;> cases hmode : state.execution.mode <;> simp only [gate, hmode] <;>
    first
      | exact CompositeState.frames_of_eq _ rfl
      | exact applyOperation_frames _ _

/-- **Gate lifting rule.**  A predicate over projections an operation does not
write survives every outcome of the ordinary gate. -/
theorem gate_preserves_of_dependsOn {support : CompositeFootprint.Projection → Bool}
    {predicate : CompositeState → Prop} (dependsOn : CompositeState.DependsOn support predicate)
    (state : CompositeState) (operation : Operation)
    (disjoint : ∀ projection, support projection = true →
      CompositeFootprint.Untouched operation.footprint projection)
    (holds : predicate state) :
    predicate (gate state operation).state :=
  dependsOn state _ (fun projection supported =>
    gate_frames state operation projection (disjoint projection supported)) holds

/-- Typed result of the trusted PCI control re-observation boundary.  A live
invalid or changed observation is fatal, never an ordinary rejection that may
continue to user mode. -/
inductive DMAControlResult where
  | continued
  | fatal (record : HaltRecord)
  | rejectedBusy
  | rejectedHalted (record : HaltRecord)
  deriving DecidableEq, Repr

structure DMAControlOutcome where
  state : CompositeState
  result : DMAControlResult

def dmaHaltRecord (reason : FatalReason) : HaltRecord :=
  { reason
    active := none
    incomingVector := 0
    incomingOrigin := .kernel }

def latchDMAControlFailure (state : CompositeState)
    (snapshot : DMAQuarantine.Snapshot) (reason : FatalReason) :
    DMAControlOutcome :=
  let record := dmaHaltRecord reason
  { state :=
      { state with
        execution :=
          { state.execution with
            core :=
              { state.execution.core with
                context := { state.execution.core.context with entryActive := true } }
            mode := .halted record
            returnAuthorityArmed := false
            copyOverride := false }
        resumable := { state.resumable with halted := true }
        dmaObserved := snapshot }
    result := .fatal record }

/-- Trusted live PCI observation.  The caller supplies a hardware snapshot,
not a device identity or mutation request.  Exact re-observation continues;
identity drift, unreadability, unexpected topology, assignment, or enabled bus
mastering latches the same absorbing execution mode as every other fatal
composite event. -/
def observeDMAControl (state : CompositeState)
    (snapshot : DMAQuarantine.Snapshot) : DMAControlOutcome :=
  match state.execution.mode with
  | .halted record => { state, result := .rejectedHalted record }
  | .handling _ => { state, result := .rejectedBusy }
  | .running =>
      match DMAQuarantine.validate snapshot with
      | .accepted _ =>
          if snapshot == state.dmaAccepted.snapshot then
            { state := { state with dmaObserved := snapshot }, result := .continued }
          else
            latchDMAControlFailure state snapshot .dmaControlSnapshotChanged
      | .rejected _ =>
          latchDMAControlFailure state snapshot .dmaInvalidControlSnapshot

/-- A continuing live observation is byte-for-byte atomic and preserves the
global invariant, including its exact DMA quarantine conjunct. -/
theorem observeDMAControl_continued_unchanged state snapshot
    (hstate : RuntimeWellFormed state)
    (hcontinued : (observeDMAControl state snapshot).result = .continued) :
    observeDMAControl state snapshot =
      { state, result := .continued } := by
  cases hmode : state.execution.mode with
  | handling active => simp [observeDMAControl, hmode] at hcontinued
  | halted record => simp [observeDMAControl, hmode] at hcontinued
  | running =>
      simp only [observeDMAControl, hmode] at hcontinued ⊢
      cases hvalidation : DMAQuarantine.validate snapshot with
      | rejected reason =>
          simp [hvalidation, latchDMAControlFailure] at hcontinued
      | accepted accepted =>
          by_cases heq : snapshot == state.dmaAccepted.snapshot
          · have hsnapshot : snapshot = state.dmaAccepted.snapshot :=
              LawfulBEq.eq_of_beq heq
            have hobserved : snapshot = state.dmaObserved :=
              hsnapshot.trans hstate.dmaQuarantined.symm
            simp only [hvalidation, heq, ite_true]
            rw [hobserved]
          · simp [hvalidation, heq, latchDMAControlFailure] at hcontinued

/-- A validator rejection has one exact global outcome: publish the observed
snapshot for diagnosis and atomically latch the DMA-invalid fatal record. -/
theorem observeDMAControl_invalid_exact_fatal state snapshot reason
    (hrunning : state.execution.mode = .running)
    (hinvalid : DMAQuarantine.validate snapshot = .rejected reason) :
    observeDMAControl state snapshot =
      latchDMAControlFailure state snapshot .dmaInvalidControlSnapshot := by
  simp [observeDMAControl, hrunning, hinvalid]

/-- A valid but changed control snapshot is equally fatal; validation cannot
turn live control drift into an ordinary continuation. -/
theorem observeDMAControl_changed_exact_fatal state snapshot accepted
    (hrunning : state.execution.mode = .running)
    (hvalid : DMAQuarantine.validate snapshot = .accepted accepted)
    (hchanged : snapshot ≠ state.dmaAccepted.snapshot) :
    observeDMAControl state snapshot =
      latchDMAControlFailure state snapshot .dmaControlSnapshotChanged := by
  have hbeq : (snapshot == state.dmaAccepted.snapshot) = false := by
    apply Bool.eq_false_iff.mpr
    intro hequal
    exact hchanged (LawfulBEq.eq_of_beq hequal)
  simp [observeDMAControl, hrunning, hvalid, hbeq]

/-- Busy, halted, accepted, and dependency-rejected gate steps all retain the
exact checked direct-port controls and device projection. -/
@[simp] theorem gate_directPortIO state operation :
    (gate state operation).state.directPortIO = state.directPortIO := by
  cases operation <;> cases hmode : state.execution.mode <;>
    simp [gate, hmode]

/-- No ordinary public operation can replace the accepted PCI authority or
the current live control observation. -/
@[simp] theorem gate_dmaAuthority state operation :
    (gate state operation).state.dmaAccepted = state.dmaAccepted ∧
      (gate state operation).state.dmaObserved = state.dmaObserved := by
  cases operation <;> cases hmode : state.execution.mode <;>
    simp [gate, hmode]

/-- Every ordinary composite step preserves the DMA conjunct already folded
into `RuntimeWellFormed`. -/
theorem gate_preserves_dmaQuarantined state operation
    (hstate : state.DMAQuarantined) :
    (gate state operation).state.DMAQuarantined := by
  apply gate_preserves_of_dependsOn CompositeState.dmaQuarantined_dependsOn state operation
    _ hstate
  intro projection supported
  have authority := Operation.footprint_untouched_authority operation
  cases projection <;>
    first
      | exact absurd supported (by decide)
      | exact authority.2.1
      | exact authority.2.2.1

/-- A running gate exposes the exact typed subsystem observation paired with
the exact composite post-state computed from the same pre-state and operation.
This is the generic soundness law used by operation-specific acceptance proofs;
`completed` does not erase a typed rejection carried by `OperationReply`. -/
theorem gate_running_exact state operation
    (hmode : state.execution.mode = .running) :
    gate state operation =
      { state := applyOperation state operation
        result := .completed (operationReply state operation) } := by
  cases operation <;> simp [gate, hmode]

/-- Both public gate rejection classes are atomic for every operation.  Busy
and halted results retain the identical composite state, including the exact
#71 transfer trace and #74 context bank. -/
theorem gate_mode_rejection_atomicity state operation
    (hrejected : (gate state operation).result = .rejectedBusy ∨
      ∃ record, (gate state operation).result = .rejectedHalted record) :
    (gate state operation).state = state := by
  cases operation <;> cases hmode : state.execution.mode <;>
    simp [gate, hmode] at hrejected ⊢

/-- Any completed result proves that the latch was running and identifies both
the exact typed reply and exact post-state.  Thus a subsystem rejection cannot
be mistaken for a different operation's success, and no caller-selected state
can be paired with an authoritative reply. -/
theorem gate_completed_sound state operation reply
    (hcompleted : (gate state operation).result = .completed reply) :
    (state.execution.mode = .running ∨
        ∃ raw context, operation = .nmi raw context) ∧
      reply = operationReply state operation ∧
      (gate state operation).state = applyOperation state operation := by
  cases operation <;> cases hmode : state.execution.mode <;>
    simp [gate, hmode] at hcompleted ⊢ <;>
    exact hcompleted.symm

/-- Every typed nonfatal subsystem rejection is globally atomic.  The theorem
is intentionally quantified over the finite composite reply classification:
adding a new rejection constructor does not gain this claim until its
`applyOperation` branch explicitly returns the identical pre-state. -/
theorem gate_subsystem_rejection_atomicity state operation reply
    (hresult : (gate state operation).result = .completed reply)
    (hrejected : SubsystemRejection state operation reply) :
    (gate state operation).state = state := by
  cases hrejected <;> cases hmode : state.execution.mode <;>
    simp_all [gate, applyOperation]

/-- Every finite nonfatal subsystem rejection preserves the complete runtime
invariant because the composite gate publishes the literal pre-state.  This
lifts rejection atomicity to the global preservation boundary uniformly over
syscall, IPC, transfer, capability, mapping, lifecycle, and scheduler errors. -/
theorem gate_subsystem_rejection_preserves_runtimeWellFormed state operation reply
    (hstate : RuntimeWellFormed state)
    (hresult : (gate state operation).result = .completed reply)
    (hrejected : SubsystemRejection state operation reply) :
    RuntimeWellFormed (gate state operation).state ∧
      (gate state operation).state = state := by
  have hatomic := gate_subsystem_rejection_atomicity state operation reply
    hresult hrejected
  exact ⟨by simpa [hatomic] using hstate, hatomic⟩

private theorem classified_rejection_is_subsystem state operation
    (hrejected : (operationReply state operation).isNonfatalRejection = true) :
    SubsystemRejection state operation (operationReply state operation) := by
  cases operation with
  | nmi raw context =>
      simp [operationReply, OperationReply.isNonfatalRejection] at hrejected
  | interrupt frame =>
      cases haction : (dispatchHardware state.execution frame).action with
      | contained subject =>
          by_cases hcurrent : state.lifecycle.current = some subject
          · simp [operationReply, haction, hcurrent,
              OperationReply.isNonfatalRejection] at hrejected
          · simpa [operationReply, haction, hcurrent] using
              SubsystemRejection.interruptIdentity frame subject haction hcurrent
      | fatal reason | timer | syscall | rejected reason | alreadyHalted reason =>
          simp [operationReply, haction, OperationReply.isNonfatalRejection] at hrejected
  | selectUserReturn purpose | restart =>
      simp [operationReply, OperationReply.isNonfatalRejection] at hrejected
  | userReturn request =>
      simp only [operationReply] at hrejected
      split at hrejected <;> simp [OperationReply.isNonfatalRejection] at hrejected
  | syscall call =>
      cases hreply : (Syscall.dispatch state.virtualMemory state.syscallContext call).reply with
      | accepted => simp [operationReply, hreply, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hreply] using SubsystemRejection.syscall call reason hreply
  | ipc call =>
      cases hreply : (dispatchIPC state call).reply with
      | sealedTransferPending =>
          simpa [operationReply, hreply] using SubsystemRejection.ipcSealed call hreply
      | syscall reply =>
          cases reply with
          | sent | delivered sender word0 word1 =>
              simp [operationReply, hreply, OperationReply.isNonfatalRejection] at hrejected
          | sendHandleRejected reason =>
              simpa [operationReply, hreply] using
                SubsystemRejection.ipcSendHandle call reason hreply
          | sendRejected reason =>
              simpa [operationReply, hreply] using
                SubsystemRejection.ipcSend call reason hreply
          | receiveHandleRejected reason =>
              simpa [operationReply, hreply] using
                SubsystemRejection.ipcReceiveHandle call reason hreply
          | receiveRejected reason =>
              simpa [operationReply, hreply] using
                SubsystemRejection.ipcReceive call reason hreply
  | resumePreempt frame registers =>
      cases herror : (ResumablePreemption.switch state.resumable state.execution.core
          frame registers).error with
      | none => simp [operationReply, herror, OperationReply.isNonfatalRejection] at hrejected
      | some reason =>
          cases reason <;>
            simp_all [operationReply, OperationReply.isNonfatalRejection,
              ResumablePreemption.rejected_exposes_no_restore]
          all_goals
            apply SubsystemRejection.resumePreempt <;> simp_all
  | transferOffer endpointWord sourceWord sourceKind payload rights =>
      cases hresult : (CapabilityTransfer.offerWords state.transfers
          state.execution.core.context.currentSubject endpointWord sourceWord sourceKind payload rights).result with
      | accepted => simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using SubsystemRejection.transferOffer
            endpointWord sourceWord sourceKind payload rights reason hresult
  | transferAccept endpointWord destinationSlot =>
      cases hresult : (CapabilityTransfer.acceptWord state.transfers
          state.execution.core.context.currentSubject endpointWord destinationSlot).result with
      | delivered envelope =>
          simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using SubsystemRejection.transferAccept
            endpointWord destinationSlot reason _ hresult rfl
  | capabilityCopy source destination destinationSlot rights =>
      cases hresult : (Capability.copy state.capabilities
          state.execution.core.context.currentSubject source destination destinationSlot rights).result with
      | accepted => simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using SubsystemRejection.capabilityCopy
            source destination destinationSlot rights reason hresult
  | capabilityRevoke authoritySlot victim victimSlot =>
      cases hresult : (Capability.revokeRuntimeSafe state.capabilities
          state.execution.core.context.currentSubject authoritySlot victim victimSlot).result with
      | accepted => simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using SubsystemRejection.capabilityRevoke
            authoritySlot victim victimSlot reason hresult
  | capabilityRevokeSubtree authoritySlot victim victimSlot =>
      cases hresult : (Capability.revokeSubtreeRuntimeSafe state.capabilities
          state.execution.core.context.currentSubject authoritySlot victim victimSlot).result with
      | accepted => simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using SubsystemRejection.capabilityRevokeSubtree
            authoritySlot victim victimSlot reason hresult
  | map slot page permissions =>
      cases hresult : (VirtualMapping.map state.virtualMemory
          state.execution.core.context.currentSubject slot
          state.execution.core.context.activeAddressSpace page permissions).result with
      | accepted => simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using
            SubsystemRejection.map slot page permissions reason hresult
  | unmap page =>
      cases hresult : (VirtualMapping.unmap state.virtualMemory
          state.execution.core.context.currentSubject state.execution.core.context.activeAddressSpace
          page).result with
      | accepted => simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using SubsystemRejection.unmap page reason hresult
  | protect page permissions =>
      cases hresult : (TLB.protect state.resumable.translations
          state.execution.core.context.currentSubject
          state.execution.core.context.activeAddressSpace page permissions).result with
      | accepted =>
          simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using
            SubsystemRejection.protect page permissions reason hresult
  | createSubject subject =>
      cases hresult : (SubjectLifecycle.create state.lifecycle subject).result with
      | accepted => simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using
            SubsystemRejection.createSubject subject reason hresult
  | terminateSubject subject =>
      cases hresult : (SubjectLifecycle.terminate state.lifecycle subject).result with
      | accepted => simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using
            SubsystemRejection.terminateSubject subject reason hresult
  | scheduleAdd subject =>
      cases hresult : (schedulerAdmission state subject).result with
      | accepted context => simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using
            SubsystemRejection.scheduleAdd subject reason hresult
  | scheduleRemove subject =>
      cases hresult : (ResumablePreemption.remove state.resumable subject).result with
      | accepted context => simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using
            SubsystemRejection.scheduleRemove subject reason hresult
  | scheduleNext =>
      cases hresult : (schedulerDispatch state).result with
      | accepted context => simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using SubsystemRejection.scheduleNext reason hresult
  | scheduleYield =>
      cases hresult : (schedulerYield state).result with
      | accepted context => simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using SubsystemRejection.scheduleYield reason hresult
  | scheduleTick =>
      cases hresult : (schedulerTick state).result with
      | accepted context => simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using SubsystemRejection.scheduleTick reason hresult
  | terminateCurrent =>
      cases hresult : (Scheduler.terminateCurrent state.scheduler).result with
      | accepted context => simp [operationReply, hresult, OperationReply.isNonfatalRejection] at hrejected
      | rejected reason =>
          simpa [operationReply, hresult] using
            SubsystemRejection.terminateCurrent reason hresult

/-- The total public reply classifier is sufficient to obtain global rejection
atomicity.  Unlike `gate_subsystem_rejection_atomicity`, callers do not need to
construct a matching `SubsystemRejection` witness: every reply constructor is
classified here, and every classified rejection returns the literal pre-state. -/
theorem gate_classified_rejection_atomicity state operation
    (hmode : state.execution.mode = .running)
    (hrejected : (operationReply state operation).isNonfatalRejection = true) :
    (gate state operation).result = .completed (operationReply state operation) ∧
      (gate state operation).state = state := by
  refine ⟨by cases operation <;> simp [gate, hmode], ?_⟩
  exact gate_subsystem_rejection_atomicity state operation
    (operationReply state operation) (by cases operation <;> simp [gate, hmode])
    (classified_rejection_is_subsystem state operation hrejected)

/-- Classified subsystem rejection is globally atomic even when the outer
execution latch is busy or already halted; those modes reject before invoking
the classified subsystem transition. -/
theorem gate_classified_rejection_global_atomicity state operation
    (hrejected : (operationReply state operation).isNonfatalRejection = true) :
    (gate state operation).state = state := by
  cases hmode : state.execution.mode with
  | running => exact (gate_classified_rejection_atomicity state operation hmode hrejected).2
  | handling active =>
      cases operation <;>
        simp [gate, hmode, operationReply, OperationReply.isNonfatalRejection] at hrejected ⊢
  | halted record => cases operation <;> simp [gate, hmode]

/-- A total classified rejection also preserves the complete composite
invariant, as a direct consequence of byte-for-byte state preservation. -/
theorem gate_classified_rejection_preserves_runtimeWellFormed state operation
    (hstate : RuntimeWellFormed state)
    (hrejected : (operationReply state operation).isNonfatalRejection = true) :
    RuntimeWellFormed (gate state operation).state ∧
      (gate state operation).state = state := by
  have hatomic := gate_classified_rejection_global_atomicity state operation hrejected
  exact ⟨by simpa [hatomic] using hstate, hatomic⟩

/-- Every ordinary resumable-preemption error is exposed as its exact typed
reply and leaves the complete composite state byte-for-byte unchanged.  The
distinguished `fatalEntry` error is excluded because it belongs to the
absorbing fatal result class. -/
theorem gate_resumePreempt_rejected_atomic state frame registers reason
    (hmode : state.execution.mode = .running)
    (hnonfatal : reason ≠ .fatalEntry)
    (herror : (ResumablePreemption.switch state.resumable state.execution.core
      frame registers).error = some reason) :
    (gate state (.resumePreempt frame registers)).result =
        .completed (.resume none (some reason)) ∧
      (gate state (.resumePreempt frame registers)).state = state := by
  have hrestored := ResumablePreemption.rejected_exposes_no_restore
    state.resumable state.execution.core frame registers reason herror
  have hresult : (gate state (.resumePreempt frame registers)).result =
      .completed (.resume none (some reason)) := by
    simp [gate, hmode, operationReply, herror, hrestored]
  refine ⟨hresult, ?_⟩
  exact gate_subsystem_rejection_atomicity state
    (.resumePreempt frame registers) (.resume none (some reason)) hresult
    (.resumePreempt frame registers reason hnonfatal herror)

/-- Return-authority selection is a complete operation-family preservation
slice.  In running mode it changes only the execution projection and arms
authority only after the live-plan check; busy and halted modes retain the
exact authoritative #71/#74 states without invoking the selector. -/
theorem gate_selectUserReturn_preserves_runtimeWellFormed state purpose
    (hstate : RuntimeWellFormed state) :
    RuntimeWellFormed (gate state (.selectUserReturn purpose)).state := by
  cases hmode : state.execution.mode with
  | handling active => simpa [gate, hmode] using hstate
  | halted record => simpa [gate, hmode] using hstate
  | running =>
      rcases hstate with
        ⟨hcoherent, hexecution, hlifecycle, hcapabilities, hvirtual, hipc,
          hscheduler, hpreemption, hresumable, htransfers, hhalted, hlive,
          hblockingCoherent⟩
      have hselected := selectLiveReturnAuthority_execution_wellFormed state purpose hexecution
      have harmed := selectLiveReturnAuthority_armed_implies_live state purpose
      simp only [gate, hmode, applyOperation]
      rw [selectLiveReturnAuthority_eq_execution_update]
      refine ⟨?_, hselected, hlifecycle, hcapabilities, hvirtual, hipc,
        hscheduler, hpreemption, hresumable, htransfers, ?_, ?_, ?_⟩
      · simpa [CompositeState.Coherent] using hcoherent
      · simpa using hhalted
      · intro harmedSelected
        have hliveSelected := harmed (by simpa using harmedSelected)
        simpa [CompositeState.ReturnPlanLive] using hliveSelected
      · simpa [CompositeState.BlockingIPCCoherent] using hblockingCoherent

end LeanOS.FailStop
