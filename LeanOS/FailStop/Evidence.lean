import LeanOS.FailStop.AuthoritativeTraces

/-!
# Fail-stop composite: executable evidence and dispatcher seeds

Executable mixed-trace and deferred-cancellation regressions, and the finite
initial states consumed by the generated composite dispatcher.
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

private def demoFrame (vector : Nat) (origin : Interrupt.Privilege) : Interrupt.HardwareFrame :=
  { vector, errorCode := 0, savedPrivilege := origin, instructionPointer := 0x400000,
    stackPointer := 0x500000, codeSelector := 0x23, stackSelector := 0x1b,
    flags := 2, canonicalInstructionPointer := true,
    canonicalStackPointer := true, flagsAllowed := true }

example (core : Interrupt.State) :
    (dispatchHardware { core, mode := .running } (demoFrame 14 .kernel)).action =
      .fatal .kernelFault := by
  simp [dispatchHardware, beginEntry, finishEntry, activeEntry, demoFrame,
    Interrupt.dispatchHardware, Interrupt.decodeVector, mapFatal, halt]

example (core : Interrupt.State) :
    (dispatchHardware { core, mode := .running } (demoFrame 32 .user)).action = .timer := by
  simp [dispatchHardware, beginEntry, finishEntry, activeEntry, demoFrame,
    Interrupt.dispatchHardware, Interrupt.decodeVector]

example (core : Interrupt.State) :
    (dispatchHardware { core, mode := .running } (demoFrame 14 .user)).action =
      .contained core.context.currentSubject := by
  simp [dispatchHardware, beginEntry, finishEntry, activeEntry, demoFrame,
    Interrupt.dispatchHardware, Interrupt.decodeVector]

example (core : Interrupt.State) :
    (dispatchHardware { core, mode := .running } (demoFrame 128 .user)).action =
      .syscall := by
  simp [dispatchHardware, beginEntry, finishEntry, activeEntry, demoFrame,
    Interrupt.dispatchHardware, Interrupt.decodeVector]

example (core : Interrupt.State) :
    (dispatchHardware { core, mode := .running } (demoFrame 77 .user)).action =
      .fatal .unsupportedVector := by
  simp [dispatchHardware, beginEntry, finishEntry, activeEntry, demoFrame,
    Interrupt.dispatchHardware, Interrupt.decodeVector, mapFatal, halt]

example (core : Interrupt.State) :
    let active := activeEntry (demoFrame 14 .kernel)
    (dispatchHardware { core, mode := .handling active } (demoFrame 14 .kernel)).action =
      .fatal .doubleFault := by
  simp [dispatchHardware, activeEntry, demoFrame, escalation, halt]

example (core : Interrupt.State) :
    let active := activeEntry (demoFrame 32 .user)
    (dispatchHardware { core, mode := .handling active } (demoFrame 14 .user)).action =
      .fatal .nestedEntry := by
  simp [dispatchHardware, activeEntry, demoFrame, escalation, halt]

example (state : CompositeState) (record : HaltRecord)
    (hhalted : state.execution.mode = .halted record) :
    (gate state .restart).state = state := by
  simp [gate, hhalted]

example (state : CompositeState) (record : HaltRecord)
    (hhalted : state.execution.mode = .halted record)
    (syscall : Syscall.UntrustedCall) (ipc : IPCSyscall.Call)
    (frame : Interrupt.HardwareFrame) :
    runOperations state [
      .syscall syscall, .interrupt frame, .ipc ipc,
      .capabilityRevoke 0 1 0, .unmap 0, .terminateSubject 0] = state := by
  simp [runOperations, gate, hhalted]

/-! ## Executable mixed-trace regressions

These fixtures exercise the public composite boundaries rather than only the
dependency-local transitions.  The arbitrary compiled plan and unrelated
composite fields are deliberately parametric: evaluation can therefore depend
only on the authoritative state selected by each operation. -/

private def directPortEvidenceTrace (plan : BootPageTablePlan.Plan) : CompositeState :=
  runOperations (bootRuntime plan)
    [.syscall { number := 99, arg0 := 0, arg1 := 0, arg2 := 0 },
     .createSubject 1, .terminateSubject 1,
     .interrupt (demoFrame 14 .kernel), .restart, .scheduleTick]

/-- A mixed accepted/rejected/fatal trace retains both the exact reviewed
controls and every device register from boot, including the post-fatal suffix. -/
example (plan : BootPageTablePlan.Plan) :
    (directPortEvidenceTrace plan).directPortIO = (bootRuntime plan).directPortIO ∧
      (directPortEvidenceTrace plan).directPortIO.controls =
        DirectPortIO.selectedControls := by
  simp [directPortEvidenceTrace, bootRuntime]

private def directPortRelaxedComposite (plan : BootPageTablePlan.Plan) : CompositeState :=
  { bootRuntime plan with
    directPortIO :=
      { (bootRuntime plan).directPortIO with
        controls := { DirectPortIO.selectedControls with ioPrivilegeLevel := 3 } } }

/-- Negative executable regression: a pre-state with relaxed IOPL cannot
advertise the global invariant, and an ordinary composite step preserves the
bad projection literally instead of silently repairing it. -/
example (plan : BootPageTablePlan.Plan) :
    ¬ RuntimeWellFormed (directPortRelaxedComposite plan) ∧
      (gate (directPortRelaxedComposite plan) .restart).state.directPortIO =
        (directPortRelaxedComposite plan).directPortIO := by
  constructor
  · intro hstate
    have hcontrols := hstate.directPortControls
    simp [DirectPortIO.AcceptedControls, directPortRelaxedComposite,
      DirectPortIO.selectedControls] at hcontrols
  · exact gate_directPortIO _ _

private def lifecycleEvidenceCreated (plan : BootPageTablePlan.Plan) : CompositeState :=
  (gate (bootRuntime plan) (.createSubject 1)).state

private def lifecycleEvidenceDuplicate (plan : BootPageTablePlan.Plan) : GateOutcome :=
  gate (lifecycleEvidenceCreated plan) (.createSubject 1)

private def lifecycleEvidenceTerminated (plan : BootPageTablePlan.Plan) : CompositeState :=
  (gate (lifecycleEvidenceDuplicate plan).state (.terminateSubject 1)).state

private def lifecycleEvidenceStaleTermination (plan : BootPageTablePlan.Plan) : GateOutcome :=
  gate (lifecycleEvidenceTerminated plan) (.terminateSubject 1)

/-- One executable trace contains accepted creation, an atomic duplicate
rejection, accepted cross-subsystem cleanup, and an atomic stale-lifetime
rejection.  Issuance remains monotonic while every live projection retires the
subject. -/
example (plan : BootPageTablePlan.Plan) :
    (lifecycleEvidenceDuplicate plan).result =
      .completed (.createSubject (.rejected .alreadyLive)) ∧
    (lifecycleEvidenceStaleTermination plan).result =
      .completed (.terminateSubject (.rejected .alreadyTerminated)) ∧
    (lifecycleEvidenceTerminated plan).lifecycle.issuedSubjects 1 = true ∧
    (lifecycleEvidenceTerminated plan).capabilities.subjects 1 = false ∧
    (lifecycleEvidenceTerminated plan).scheduler.lifecycle.capabilities.subjects 1 = false ∧
    (lifecycleEvidenceTerminated plan).blockingIPC.scheduler.lifecycle.capabilities.subjects 1 =
      false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

private def blockingEvidenceCapability (rights : Capability.Rights) : Capability.Capability :=
  { object := 10, kind := .endpoint, rights, identity := 1 }

private def blockingEvidenceCapabilities : Capability.State :=
  { subjects := fun subject => subject < 4
    objects := fun object => object = 10
    kinds := fun object => if object = 10 then some .endpoint else none
    slots := fun subject slot =>
      if slot != 0 then none
      else if subject = 1 then some (blockingEvidenceCapability { send := true })
      else if subject = 2 || subject = 3 then
        some (blockingEvidenceCapability { receive := true })
      else none }

private def blockingEvidenceLifecycle (current : Option SubjectLifecycle.SubjectId) :
    SubjectLifecycle.State :=
  { capabilities := blockingEvidenceCapabilities
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

private def blockingEvidenceStore : BlockingIPC.State :=
  { scheduler :=
      { lifecycle := blockingEvidenceLifecycle (some 2), ready := [1, 3], capacity := 3 }
    mailbox := fun _ => none
    waiters := fun _ => []
    waiterEndpoint := fun _ => none
    waiterCapacity := 2
    completion := fun _ => none }

private def blockingEvidenceRegisters (marker : UInt64) : ResumableContext.Registers :=
  { accumulator := marker, base := marker, count := marker, data := marker
    source := marker, destination := marker, basePointer := marker
    r8 := marker, r9 := marker, r10 := marker, r11 := marker
    r12 := marker, r13 := marker, r14 := marker, r15 := marker }

private def blockingEvidenceContext (owner : Nat) (marker : UInt64) :
    ResumableContext.Context :=
  { owner
    addressSpace := owner
    frame := { demoFrame 32 .user with
      instructionPointer := 0x400000 + marker
      stackPointer := 0x500000 + marker }
    registers := blockingEvidenceRegisters marker
    kind := .suspended }

private def blockingEvidenceComposite (state : CompositeState) : CompositeState :=
  { state with
    execution := { state.execution with
      core := { state.execution.core with
        lifecycle := blockingEvidenceLifecycle (some 2)
        context := { state.execution.core.context with
          currentSubject := 2, activeAddressSpace := 2 } }
      mode := .running }
    scheduler := blockingEvidenceStore.scheduler
    lifecycle := blockingEvidenceLifecycle (some 2)
    blockingIPC := blockingEvidenceStore }

/-- Evidence state for the typed public blocking boundary.  Subjects 1 and 3
have kernel-owned resumable contexts, subject 2 is current, and the modeled
CR3 names subject 2 before it blocks. -/
private def blockingContextEvidenceComposite (state : CompositeState) : CompositeState :=
  let base := blockingEvidenceComposite state
  { base with
    resumable := { base.resumable with
      scheduler := blockingEvidenceStore.scheduler
      contexts := [blockingEvidenceContext 1 0x10, blockingEvidenceContext 3 0x30]
      capacity := 3
      translations := { base.resumable.translations with
        virtual := { base.resumable.translations.virtual with
          owner := (blockingEvidenceLifecycle (some 2)).addressOwner }
        active := some 2
        entries := [] } }
    blockingContexts := fun _ => none }

private def blockingEvidenceFrame : Interrupt.HardwareFrame := demoFrame 32 .user
private def blockingEvidenceRegisters2 : ResumableContext.Registers :=
  blockingEvidenceRegisters 0x22

private def blockingContextEvidenceRejected (state : CompositeState) :
    CompositeBlockingGateOutcome :=
  blockingGate (blockingContextEvidenceComposite state)
    (.receive 0x0000000000020000 blockingEvidenceFrame blockingEvidenceRegisters2)

private def blockingContextEvidenceBlocked (state : CompositeState) :
    CompositeBlockingGateOutcome :=
  blockingGate (blockingContextEvidenceRejected state).state
    (.receive 0x0000000000010000 blockingEvidenceFrame blockingEvidenceRegisters2)

private def blockingContextEvidenceWoken (state : CompositeState) :
    CompositeBlockingGateOutcome :=
  blockingGate (blockingContextEvidenceBlocked state).state
    (.send 0x0000000000010000 0xCAFE 0xBEEF)

private def blockingContextEvidenceCancelled (state : CompositeState) :
    CompositeBlockingGateOutcome :=
  blockingGate (blockingContextEvidenceBlocked state).state (.cancel 2)

private def authoritativeBlockingCancelSubject1Space : Capability.Capability :=
  { object := 1, kind := .addressSpace, rights := { revoke := true },
    identity := 2 }

private def authoritativeBlockingCancelSubject2Space : Capability.Capability :=
  { object := 2, kind := .addressSpace, rights := { revoke := true },
    identity := 3 }

private def authoritativeBlockingCancelCapabilities : Capability.State :=
  let endpointReceive := blockingEvidenceCapability { receive := true }
  { nextIdentity := 4
    derivations := fun identity =>
      if identity = 1 then
        some (none, 10, .endpoint, { receive := true })
      else if identity = 2 then
        some (none, 1, .addressSpace, { revoke := true })
      else if identity = 3 then
        some (none, 2, .addressSpace, { revoke := true })
      else none
    subjects := fun subject => subject = 1 || subject = 2
    objects := fun object => object = 1 || object = 2 || object = 10
    kinds := fun object =>
      if object = 1 || object = 2 then some .addressSpace
      else if object = 10 then some .endpoint else none
    slots := fun subject slot =>
      if subject = 1 && slot = 0 then some authoritativeBlockingCancelSubject1Space
      else if subject = 2 && slot = 0 then some endpointReceive
      else if subject = 2 && slot = 1 then some authoritativeBlockingCancelSubject2Space
      else none }

private theorem authoritativeBlockingCancelCapabilities_wellFormed :
    Capability.WellFormed authoritativeBlockingCancelCapabilities := by
  simp only [Capability.WellFormed]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro subject slot capability hslot
    simp only [authoritativeBlockingCancelCapabilities,
      authoritativeBlockingCancelSubject1Space,
      authoritativeBlockingCancelSubject2Space, blockingEvidenceCapability] at hslot
    repeat' split at hslot
    all_goals cases hslot <;>
      simp [authoritativeBlockingCancelCapabilities,
        authoritativeBlockingCancelSubject1Space,
        authoritativeBlockingCancelSubject2Space,
        blockingEvidenceCapability, Capability.rightsValid,
        Capability.nonemptyRights]
    all_goals grind
  · intro identity parent object kind rights hderivation
    simp only [authoritativeBlockingCancelCapabilities] at hderivation
    repeat' split at hderivation
    all_goals rcases hderivation with ⟨rfl, rfl, rfl, rfl⟩ <;>
      simp [authoritativeBlockingCancelCapabilities]
    all_goals grind
  · intro subject slot capability otherSubject otherSlot otherCapability
      hslot hother hidentity
    simp only [authoritativeBlockingCancelCapabilities,
      authoritativeBlockingCancelSubject1Space,
      authoritativeBlockingCancelSubject2Space,
      blockingEvidenceCapability] at hslot hother
    repeat' split at hslot
    all_goals repeat' split at hother
    all_goals cases hslot <;> cases hother <;> simp_all
  · intro subject slot hslot
    change 4 ≤ slot at hslot
    have hne0 : slot ≠ 0 := by omega
    have hne1 : slot ≠ 1 := by omega
    simp [authoritativeBlockingCancelCapabilities,
      authoritativeBlockingCancelSubject1Space,
      authoritativeBlockingCancelSubject2Space,
      blockingEvidenceCapability, hne0, hne1]

private def authoritativeBlockingCancelLifecycle : SubjectLifecycle.State :=
  { capabilities := authoritativeBlockingCancelCapabilities
    issuedSubjects := fun subject => subject = 1 || subject = 2
    ownedMemory := fun _ => none
    addressOwner := fun space => if space = 1 || space = 2 then some space else none
    mapping := fun _ _ => none
    endpointOwner := fun object => if object = 10 then some 1 else none
    mailbox := fun _ => none
    frameOwner := fun _ => none
    freeFrame := fun _ => true
    runnable := fun subject => subject = 1 || subject = 2
    current := some 2 }

private def authoritativeBlockingCancelStore : BlockingIPC.State :=
  { scheduler :=
      { lifecycle := authoritativeBlockingCancelLifecycle
        ready := [1], capacity := 2 }
    mailbox := fun _ => none
    waiters := fun _ => []
    waiterEndpoint := fun _ => none
    waiterCapacity := 1
    completion := fun _ => none }

private def authoritativeBlockingCancelEvidence (plan : BootPageTablePlan.Plan) :
    CompositeState :=
  let scheduler := authoritativeBlockingCancelStore.scheduler
  let virtualMemory :=
    { (bootRuntime plan).virtualMemory with
      memory :=
        { (bootRuntime plan).virtualMemory.memory with
          issued := fun object => object = 1 || object = 2 || object = 10 }
      issuedAddressSpace := fun space => space = 1 || space = 2 }
  let base :=
    { blockingEvidenceComposite (bootRuntime plan) with
      scheduler
      lifecycle := authoritativeBlockingCancelLifecycle
      blockingIPC := authoritativeBlockingCancelStore
      virtualMemory
      ipc :=
        { (bootRuntime plan).ipc with
          virtualMemory
          endpoints :=
            { (bootRuntime plan).ipc.endpoints with
              issued := fun object => object = 1 || object = 2 || object = 10 } }
      resumable :=
        { (bootRuntime plan).resumable with
          scheduler
          contexts := [blockingEvidenceContext 1 0x10]
          capacity := 2
          translations :=
            { (bootRuntime plan).resumable.translations with
              virtual :=
                { virtualMemory with
                  owner := authoritativeBlockingCancelLifecycle.addressOwner }
              active := some 2
              entries := [] } }
      blockingContexts := fun _ => none }
  installLifecycle base authoritativeBlockingCancelLifecycle

private def blockingContextEvidenceTerminated (state : CompositeState) : GateOutcome :=
  gate (blockingContextEvidenceBlocked state).state (.terminateSubject 2)

private def blockingContextEvidenceOwnerTerminated (state : CompositeState) : GateOutcome :=
  gate (blockingContextEvidenceBlocked state).state (.terminateSubject 0)

/-- One mixed global blocking-gate trace first rejects a stale handle without
mutation, then blocks subject 2, immediately restores scheduler-selected peer
1 (including the modeled CR3 flush), and finally wakes subject 2 while
restoring its exact saved frame/register context into the resumable bank. -/
example (state : CompositeState) :
    (blockingContextEvidenceRejected state).result =
        .completed (.receive (.handleRejected (.denied .staleHandle))) ∧
      (blockingContextEvidenceRejected state).state =
        blockingContextEvidenceComposite state := by
  exact ⟨rfl, rfl⟩

example (state : CompositeState) :
    (blockingContextEvidenceBlocked state).result = .completed (.receive .blocked) ∧
      (blockingContextEvidenceBlocked state).state.execution.core.context.currentSubject = 1 ∧
      (blockingContextEvidenceBlocked state).state.execution.core.context.activeAddressSpace = 1 ∧
      (blockingContextEvidenceBlocked state).state.resumable.translations.active = some 1 ∧
      (blockingContextEvidenceBlocked state).state.resumable.translations.entries = [] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 800000 in
/-- A boot-rooted authoritative state reaches the successful cancellation
branch: subject 2 blocks with its exact saved context, the blocking transition
preserves the folded invariant, and cancellation returns that context. -/
theorem authoritativeGate_blockingCancel_cancelled_reachable_witness input plan
    (hcompiled : BootPageTablePlan.compile input = .ok plan) :
    let initial := authoritativeBlockingCancelEvidence plan
    let blocked := authoritativeGate initial
      (.blocking (.receive 0x0000000000010000
        blockingEvidenceFrame blockingEvidenceRegisters2))
    AuthoritativeRuntimeWellFormed initial ∧
      AuthoritativeRuntimeWellFormed blocked.state ∧
      blocked.result = .completed (.blocking (.receive .blocked)) ∧
      (authoritativeGate blocked.state (.blocking (.cancel 2))).result =
        .completed (.blocking (.cancel
          (.cancelled (initial.blockingSavedContext
            blockingEvidenceFrame blockingEvidenceRegisters2)))) := by
  have hboot :=
    bootRuntime_deferredBlockingRuntimeWellFormed input plan hcompiled
  have hcontrols := hboot.1.directPortControls
  have hdma := hboot.1.dmaQuarantined
  rcases authoritativeBlockingCancelCapabilities_wellFormed with
    ⟨hslots, hderivations, hidentities, hslotSpaces⟩
  have hspace1 :
      Capability.HasAuthority authoritativeBlockingCancelCapabilities
        1 1 .revoke := by
    exact ⟨0, authoritativeBlockingCancelSubject1Space, rfl, rfl, rfl⟩
  have hspace2 :
      Capability.HasAuthority authoritativeBlockingCancelCapabilities
        2 2 .revoke := by
    exact ⟨1, authoritativeBlockingCancelSubject2Space, rfl, rfl, rfl⟩
  have hlegacy :
      DeferredBlockingRuntimeWellFormed
        (authoritativeBlockingCancelEvidence plan) := by
    simp [DeferredBlockingRuntimeWellFormed,
      authoritativeBlockingCancelEvidence, blockingContextEvidenceComposite,
      blockingEvidenceComposite, blockingEvidenceStore,
      blockingEvidenceLifecycle, blockingEvidenceCapabilities,
      blockingEvidenceCapability, blockingEvidenceContext,
      authoritativeBlockingCancelStore, authoritativeBlockingCancelLifecycle,
      blockingEvidenceRegisters, installLifecycle, synchronizeMemory,
      restrictMappings, restrictMailboxes, CompositeState.Coherent,
      RuntimeWellFormed, WellFormed, Interrupt.WellFormed,
      SubjectLifecycle.WellFormed,
      VirtualMapping.LifecycleWellFormed,
      VirtualMapping.WellFormed, MemoryLifecycle.WellFormed,
      IPCSyscall.WellFormed, EndpointIPC.WellFormed, Scheduler.WellFormed,
      Preemption.WellFormed, ResumablePreemption.WellFormed,
      ResumablePreemption.ReadyContextAgreement,
      ResumablePreemption.TranslationAgreement,
      ResumablePreemption.VirtualAgreement,
      ResumablePreemption.ResourceKindAgreement, CapabilityTransfer.WellFormed,
      TLB.Coherent, CompositeState.ReturnPlanLive,
      CompositeState.blockingIPCContext, CompositeState.BlockingIPCCoherent,
      CompositeState.DeferredCancellationWellFormed,
      BlockingIPCContext.DeferredWellFormed, BlockingIPCContext.WellFormed,
      BlockingIPCContext.ContextAgreement, BlockingIPC.WellFormed,
      BlockingIPC.authorizedReceive, BlockingIPCContext.emptyDeferred,
      BlockingIPCContext.validSaved, Scheduler.ownsAddressSpace,
      ResumablePreemption.contextFor, ResumablePreemption.validContext,
      Capability.hasRight, Capability.rightsValid,
      Capability.rightsSubset, Capability.nonemptyRights, Capability.permits,
      Interrupt.validSavedUserFrame, demoFrame,
      DirectPortIO.AcceptedControls, DMAQuarantine.q35Accepted,
      bootRuntime, bootLifecycle, bootCapabilities, bootVirtualMemory,
      bootMemory, bootEndpoints]
    repeat' apply And.intro
    all_goals first
      | assumption
      | simp_all [authoritativeBlockingCancelCapabilities,
          authoritativeBlockingCancelSubject1Space,
          authoritativeBlockingCancelSubject2Space]
    all_goals grind
  have hinitial :
      AuthoritativeRuntimeWellFormed
        (authoritativeBlockingCancelEvidence plan) :=
    ⟨hlegacy.1, hlegacy.2, InvalidationPublication.initial_wellFormed⟩
  have hdeferred :
      (authoritativeGate (authoritativeBlockingCancelEvidence plan)
        (.blocking (.receive 0x0000000000010000
          blockingEvidenceFrame blockingEvidenceRegisters2))).state.deferredCancels =
        (authoritativeBlockingCancelEvidence plan).deferredCancels := by
    rfl
  have hcontexts :
      (authoritativeGate (authoritativeBlockingCancelEvidence plan)
        (.blocking (.receive 0x0000000000010000
          blockingEvidenceFrame blockingEvidenceRegisters2))).state.resumable.contexts =
        [] := by
    rfl
  refine ⟨hinitial, ?_, rfl, rfl⟩
  apply authoritativeGate_preserves_authoritativeRuntimeWellFormed_of_compatible _ _ hinitial
  change DormantCancellationCompatible _ _
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro subject _
    rw [hdeferred]
    simp [authoritativeBlockingCancelEvidence, blockingContextEvidenceComposite,
      blockingEvidenceComposite, BlockingIPCContext.emptyDeferred,
      installLifecycle, bootRuntime]
  · intro subject saved _
    rw [hcontexts]
    simp [ResumablePreemption.contextFor]
  · intro subject saved hretained
    have : False := by
      simp [authoritativeBlockingCancelEvidence, blockingContextEvidenceComposite,
        blockingEvidenceComposite, BlockingIPCContext.emptyDeferred,
        installLifecycle, bootRuntime] at hretained
    contradiction

set_option maxHeartbeats 800000 in
/-- Explicit global termination consumes the waiter and exact blocked context
created by the public blocking gate; the dead subject is never requeued.  This
is a named theorem rather than an `example` so that its expensive
definitional check is elaborated in parallel with the other evidence. -/
private theorem blockingContextEvidence_termination_consumes_waiter
    (state : CompositeState) :
    (blockingContextEvidenceTerminated state).result =
        .completed (.terminateSubject .accepted) ∧
      (blockingContextEvidenceTerminated state).state.blockingIPC.waiterEndpoint 2 = none ∧
      (blockingContextEvidenceTerminated state).state.blockingContexts 2 = none ∧
      (blockingContextEvidenceTerminated state).state.scheduler.lifecycle.capabilities.subjects
        2 = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 800000 in
/-- Endpoint-owner termination removes the affected peer's waiter and blocked
context together, retains the exact context for a checked cancellation drain,
and clears the retired endpoint mailbox.  No external readiness witness is
used to compute this executable trace.  Named, like the previous trace, so it
is elaborated in parallel. -/
private theorem blockingContextEvidence_ownerTermination_defers_peer
    (state : CompositeState) :
    (blockingContextEvidenceOwnerTerminated state).result =
        .completed (.terminateSubject .accepted) ∧
      (blockingContextEvidenceOwnerTerminated state).state.blockingIPC.waiterEndpoint 2 =
        none ∧
      (blockingContextEvidenceOwnerTerminated state).state.blockingContexts 2 = none ∧
      (blockingContextEvidenceOwnerTerminated state).state.deferredCancels.retained 2 =
        some ((blockingContextEvidenceComposite state).blockingSavedContext
          blockingEvidenceFrame blockingEvidenceRegisters2) ∧
      (blockingContextEvidenceOwnerTerminated state).state.blockingIPC.mailbox 10 = none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A mixed rejected-block-wake trace composes at the authoritative composite
boundary.  The rejected prefix is atomic; both accepted suffix steps preserve
waiter/context coherence; and wake restores the exact released context into
the resumable bank. -/
theorem mixedBlockingWakeTrace_preserves state staleWord liveWord frame registers word0 word1
    saved
    (hstate : BlockingReceiveWellFormed state)
    (hstale : (dispatchBlockingReceive state staleWord frame registers).reply =
      .handleRejected (.denied .staleHandle))
    (_hblocked : (dispatchBlockingReceive state liveWord frame registers).reply = .blocked)
    (hwoke : (dispatchBlockingSend
      (dispatchBlockingReceive state liveWord frame registers).state
      liveWord word0 word1).reply = .woke saved) :
    (dispatchBlockingReceive state staleWord frame registers).state = state ∧
      BlockingReceiveWellFormed
        (dispatchBlockingReceive state liveWord frame registers).state ∧
      BlockingReceiveWellFormed
        (dispatchBlockingSend
          (dispatchBlockingReceive state liveWord frame registers).state
          liveWord word0 word1).state ∧
      ∃ receiver,
        (dispatchBlockingReceive state liveWord frame registers).state.blockingContexts
            receiver = some saved ∧
        ResumablePreemption.contextFor
          (dispatchBlockingSend
            (dispatchBlockingReceive state liveWord frame registers).state
            liveWord word0 word1).state.resumable.contexts receiver = some saved := by
  have hreject := dispatchBlockingReceive_rejected_atomic state staleWord frame registers
    (.handleRejected (.denied .staleHandle))
    (.handle (.denied .staleHandle)) hstale
  have hblockedWf := dispatchBlockingReceive_preserves_wellFormed
    state liveWord frame registers hstate
  have hwokenWf := dispatchBlockingSend_preserves_wellFormed
    (dispatchBlockingReceive state liveWord frame registers).state
    liveWord word0 word1 hblockedWf
  obtain ⟨receiver, hstored, _, hrestored⟩ := dispatchBlockingSend_woke_exact
    (dispatchBlockingReceive state liveWord frame registers).state
    liveWord word0 word1 saved hblockedWf hwoke
  exact ⟨hreject, hblockedWf, hwokenWf, receiver, hstored, hrestored⟩

/-- The corresponding rejected-block-cancel trace has the same preservation
shape and restores the cancelled subject's exact saved context. -/
theorem mixedBlockingCancelTrace_preserves state staleWord liveWord frame registers subject saved
    (hstate : BlockingReceiveWellFormed state)
    (hstale : (dispatchBlockingReceive state staleWord frame registers).reply =
      .handleRejected (.denied .staleHandle))
    (_hblocked : (dispatchBlockingReceive state liveWord frame registers).reply = .blocked)
    (hcancelled : (dispatchBlockingCancel
      (dispatchBlockingReceive state liveWord frame registers).state subject).reply =
        .cancelled saved) :
    (dispatchBlockingReceive state staleWord frame registers).state = state ∧
      BlockingReceiveWellFormed
        (dispatchBlockingReceive state liveWord frame registers).state ∧
      BlockingReceiveWellFormed
        (dispatchBlockingCancel
          (dispatchBlockingReceive state liveWord frame registers).state subject).state ∧
      (dispatchBlockingReceive state liveWord frame registers).state.blockingContexts subject =
        some saved ∧
      ResumablePreemption.contextFor
        (dispatchBlockingCancel
          (dispatchBlockingReceive state liveWord frame registers).state subject).state.resumable.contexts
        subject = some saved := by
  have hreject := dispatchBlockingReceive_rejected_atomic state staleWord frame registers
    (.handleRejected (.denied .staleHandle))
    (.handle (.denied .staleHandle)) hstale
  have hblockedWf := dispatchBlockingReceive_preserves_wellFormed
    state liveWord frame registers hstate
  have hcancelWf := dispatchBlockingCancel_preserves_wellFormed
    (dispatchBlockingReceive state liveWord frame registers).state subject hblockedWf
  obtain ⟨hstored, _, hrestored⟩ := dispatchBlockingCancel_cancelled_exact
    (dispatchBlockingReceive state liveWord frame registers).state subject saved
    hblockedWf hcancelled
  exact ⟨hreject, hblockedWf, hcancelWf, hstored, hrestored⟩

private def blockingEvidenceBlocked (state : CompositeState) : CompositeBlockingIPCOutcome :=
  dispatchBlockingIPC (blockingEvidenceComposite state) (.receive 0x0000000000010000)

private def blockingEvidenceWoken (state : CompositeState) : CompositeBlockingIPCOutcome :=
  dispatchBlockingIPC (blockingEvidenceBlocked state).state
    (.send 0x0000000000010000 0xCAFE 0xBEEF)

/-- The authoritative composite path blocks receiver 2, switches to sender 1,
wakes exactly receiver 2, and reserves the exact delivered envelope. -/
example (state : CompositeState) :
    (blockingEvidenceBlocked state).reply = .receive (.completed .blocked) ∧
    (blockingEvidenceBlocked state).state.execution.core.context.currentSubject = 1 ∧
    (blockingEvidenceWoken state).reply = .woke 2 ∧
    (blockingEvidenceWoken state).state.blockingIPC.waiters 10 = [] ∧
    (blockingEvidenceWoken state).state.blockingIPC.completion 2 = some (.delivered
      { endpoint := 10, sender := 1, payload := { word0 := 0xCAFE, word1 := 0xBEEF } }) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- Stale fixed-width handles are rejected before any blocking state is
published. -/
example (state : CompositeState) :
    (dispatchBlockingIPC (blockingEvidenceComposite state)
      (.receive 0x0000000000020000)).reply =
        .receive (.handleRejected (.denied .staleHandle)) ∧
    (dispatchBlockingIPC (blockingEvidenceComposite state)
      (.receive 0x0000000000020000)).state = blockingEvidenceComposite state := by
  constructor
  · rfl
  · apply dispatchBlockingIPC_rejection_atomic _ _ _
    · exact .receiveHandle (.denied .staleHandle)
    · rfl

/-- Revocation-style cancellation after blocking wakes the receiver exactly
once; subject termination instead removes it without making the dead identity
runnable.  Both cleanup paths are republished through the authoritative
composite scheduler boundary. -/
example (state : CompositeState) :
    let blocked := (blockingEvidenceBlocked state).state
    let cancelled := publishBlockingIPC blocked (BlockingIPC.cancelSubject blocked.blockingIPC 2)
    let terminated := publishBlockingIPC blocked (BlockingIPC.terminate blocked.blockingIPC 2)
    cancelled.blockingIPC.waiters 10 = [] ∧
      cancelled.blockingIPC.completion 2 = some .cancelled ∧
      cancelled.scheduler.lifecycle.runnable 2 = true ∧
      terminated.blockingIPC.waiters 10 = [] ∧
      terminated.scheduler.lifecycle.capabilities.subjects 2 = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-! ## Executable deferred-cancellation regressions

These fixtures exercise the composite drain itself.  The successful case has
one quiescent retained context and room in both finite banks.  The two denial
cases independently exhaust each bank, demonstrating that neither partial
scheduler publication nor partial context publication is observable. -/

private def deferredEvidenceLifecycle : SubjectLifecycle.State :=
  { blockingEvidenceLifecycle (some 2) with
    runnable := fun subject => subject == 2 || subject == 3 }

private def deferredEvidenceScheduler (capacity : Nat) : Scheduler.State :=
  { lifecycle := deferredEvidenceLifecycle, ready := [3], capacity }

private def deferredEvidenceComposite (state : CompositeState)
    (readyCapacity resumableCapacity : Nat) : CompositeState :=
  let scheduler := deferredEvidenceScheduler readyCapacity
  let retained := blockingEvidenceContext 1 0x10
  { blockingContextEvidenceComposite state with
    execution := { state.execution with
      core := { state.execution.core with lifecycle := deferredEvidenceLifecycle }
      mode := .running }
    scheduler
    lifecycle := deferredEvidenceLifecycle
    preemption := { state.preemption with scheduler }
    resumable := { state.resumable with
      scheduler
      contexts := [blockingEvidenceContext 3 0x30]
      capacity := resumableCapacity }
    blockingIPC := { blockingEvidenceStore with scheduler }
    blockingContexts := fun _ => none
    deferredCancels := ⟨fun subject => if subject = 1 then some retained else none⟩ }

private def deferredEvidenceDrained (state : CompositeState) : DeferredDrainOutcome :=
  drainDeferredCancellation (deferredEvidenceComposite state 2 2) 1

private def deferredEvidenceReadyFull (state : CompositeState) : DeferredDrainOutcome :=
  drainDeferredCancellation (deferredEvidenceComposite state 1 2) 1

private def deferredEvidenceBankFull (state : CompositeState) : DeferredDrainOutcome :=
  drainDeferredCancellation (deferredEvidenceComposite state 2 1) 1

private def deferredEvidenceTerminated (state : CompositeState) : GateOutcome :=
  gate (deferredEvidenceComposite state 2 2) (.terminateSubject 1)

/-- Positive executable regression: a valid retained context is consumed once,
the cancellation completion and ready slot are published together, and the
exact saved context is restored to the resumable bank. -/
example (state : CompositeState) :
    (deferredEvidenceDrained state).result =
        .drained (blockingEvidenceContext 1 0x10) ∧
      (deferredEvidenceDrained state).state.deferredCancels.retained 1 = none ∧
      (deferredEvidenceDrained state).state.blockingIPC.completion 1 =
        some .cancelled ∧
      (deferredEvidenceDrained state).state.scheduler.ready = [3, 1] ∧
      (deferredEvidenceDrained state).state.resumable.contexts =
        [blockingEvidenceContext 1 0x10, blockingEvidenceContext 3 0x30] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Negative executable regressions: exhausting either finite publication
bank selects its distinct typed denial and returns the literal pre-state. -/
example (state : CompositeState) :
    (deferredEvidenceReadyFull state).result = .rejected .readyQueueFull ∧
      (deferredEvidenceReadyFull state).state =
        deferredEvidenceComposite state 1 2 ∧
      (deferredEvidenceBankFull state).result = .rejected .resumableBankFull ∧
      (deferredEvidenceBankFull state).state =
        deferredEvidenceComposite state 2 1 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Explicit termination consumes the same retained saved context instead of
leaving a dead identity eligible for a later public drain.  The cleanup is
observable through the ordinary composite gate and the deferred projection of
its single authoritative post-state. -/
example (state : CompositeState) :
    (deferredEvidenceTerminated state).result =
        .completed (.terminateSubject .accepted) ∧
      (deferredEvidenceTerminated state).state.lifecycle.capabilities.subjects 1 =
        false ∧
      (deferredEvidenceTerminated state).state.deferredCancels.retained 1 = none := by
  exact ⟨rfl, rfl, rfl⟩

/-- The same success and follow-up denial are observable through the public
authoritative gate and its finite trace runner, rather than only through the
composite drain helper. -/
example (state : CompositeState) :
    let initial := deferredEvidenceComposite state 2 2
    let first := authoritativeGate initial (.drainDeferred 1)
    first.result = .completed
        (.deferredDrain (.drained (blockingEvidenceContext 1 0x10))) ∧
      (authoritativeGate first.state (.drainDeferred 1)).result =
        .completed (.deferredDrain (.rejected .notDeferred)) ∧
      runAuthoritativeOperations initial [.drainDeferred 1, .drainDeferred 1] =
        first.state := by
  exact ⟨rfl, rfl, rfl⟩

/-- The authoritative trace cannot restore a context after its owner is
retired.  Termination consumes subject `1`'s queued context; the following
timer attempt reports the exact `noDestination` denial, exposes no restored
context, and leaves the terminated post-state unchanged. -/
theorem authoritativeStaleResumableContext_reachable_witness
    input plan (hcompiled : BootPageTablePlan.compile input = .ok plan) :
    let initial := authoritativeBlockingCancelEvidence plan
    let terminated := authoritativeGate initial
      (.ordinary (.terminateSubject 1))
    let attempted := authoritativeGate terminated.state
      (.ordinary (.resumePreempt blockingEvidenceFrame
        blockingEvidenceRegisters2))
    AuthoritativeRuntimeWellFormed initial ∧
      terminated.result =
        .completed (.ordinary (.terminateSubject .accepted)) ∧
      ResumablePreemption.contextFor terminated.state.resumable.contexts 1 =
        none ∧
      attempted.result =
        .completed (.ordinary (.resume none (some .noDestination))) ∧
      attempted.state = terminated.state ∧
      AuthoritativeRuntimeWellFormed attempted.state ∧
      runAuthoritativeOperations initial
        [.ordinary (.terminateSubject 1),
          .ordinary (.resumePreempt blockingEvidenceFrame
            blockingEvidenceRegisters2)] = terminated.state := by
  have hinitial :
      AuthoritativeRuntimeWellFormed
        (authoritativeBlockingCancelEvidence plan) :=
    (authoritativeGate_blockingCancel_cancelled_reachable_witness
      input plan hcompiled).1
  have htrace :=
    runAuthoritativeStaleResumableContextTrace_preserves_authoritativeRuntimeWellFormed
      (authoritativeBlockingCancelEvidence plan) 1 blockingEvidenceFrame
      blockingEvidenceRegisters2 hinitial
  exact ⟨hinitial, rfl, rfl, rfl, rfl, htrace, rfl⟩

private def revokeAfterSendTarget : Capability.Capability :=
  { object := 10, kind := .endpoint, rights := { send := true },
    identity := 4 }

private def revokeAfterSendAuthority : Capability.Capability :=
  { object := 10, kind := .endpoint,
    rights := { send := true, grant := true, revoke := true },
    identity := 5 }

private def revokeAfterSendCapabilities : Capability.State :=
  { nextIdentity := 6
    derivations := fun identity =>
      if identity = 4 then
        some (none, 10, .endpoint, { send := true })
      else if identity = 5 then
        some (none, 10, .endpoint,
          { send := true, grant := true, revoke := true })
      else none
    subjects := fun subject => subject = 2
    objects := fun object => object = 10
    kinds := fun object => if object = 10 then some .endpoint else none
    slots := fun subject slot =>
      if subject = 2 ∧ slot = 2 then some revokeAfterSendTarget
      else if subject = 2 ∧ slot = 3 then some revokeAfterSendAuthority
      else none }

private def revokeAfterSendTransfers : CapabilityTransfer.State :=
  { toEndpointState :=
      { capabilities := revokeAfterSendCapabilities
        allocator := { frames := [], status := fun _ => .reserved }
        binding := fun _ => none
        issued := fun object => object = 10
        issuedAddressSpace := fun _ => false
        mailbox := fun _ => none
        sendHistory := fun _ => [] }
    pending := fun _ => none }

private def revokeAfterSendEvidence (state : CompositeState) :
    CompositeState :=
  { state with
    execution :=
      { state.execution with
        core :=
          { state.execution.core with
            context :=
              { state.execution.core.context with
                currentSubject := 2, activeAddressSpace := 2 } }
        mode := .running }
    capabilities := revokeAfterSendCapabilities
    lifecycle :=
      { state.lifecycle with
        capabilities := revokeAfterSendCapabilities
        current := some 2 }
    transfers := revokeAfterSendTransfers }

/-- A concrete sealed send followed by direct revocation executes both success
branches through the authoritative gate.  The send reserves descendant `6`
and publishes its tagged mailbox; revoking the independent send-only endpoint
slot succeeds without consuming that sealed descendant. -/
theorem authoritativeRevokeAfterSend_reachable_witness
    (state : CompositeState) :
    let initial := revokeAfterSendEvidence state
    let offered := authoritativeGate initial
      (.ordinary (.transferOffer 0x0000000000040002
        0x0000000000050003 .endpoint
        { word0 := 0xCAFE, word1 := 0xBEEF } { send := true }))
    let revoked := authoritativeGate offered.state
      (.ordinary (.capabilityRevoke 3 2 2))
    offered.result = .completed (.ordinary (.transferOffer .accepted)) ∧
      offered.state.transfers.pending 10 = some
        { identity := 6
          parent := 5
          sender := 2
          object := 10
          kind := .endpoint
          rights := { send := true } } ∧
      revoked.result = .completed (.ordinary (.capability .accepted)) ∧
      revoked.state.capabilities.slots 2 2 = none ∧
      revoked.state.transfers.pending 10 =
        offered.state.transfers.pending 10 ∧
      runAuthoritativeOperations initial
        [.ordinary (.transferOffer 0x0000000000040002
          0x0000000000050003 .endpoint
          { word0 := 0xCAFE, word1 := 0xBEEF } { send := true }),
          .ordinary (.capabilityRevoke 3 2 2)] = revoked.state := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A concrete kernel fault latches the runtime before a heterogeneous suffix;
the stale handle, IPC, revoke, unmap, termination, and restart operations are
all absorbed byte-for-byte. -/
example (state : CompositeState) :
    let running := { state with execution := { state.execution with mode := .running } }
    let halted := (gate running (.interrupt (demoFrame 14 .kernel))).state
    halted.execution.mode = .halted
      { reason := .kernelFault
        active := some (activeEntry (demoFrame 14 .kernel))
        incomingVector := 14
        incomingOrigin := .kernel } ∧
    runOperations halted [
      .ipc (.receive 0x0000000000020000),
      .capabilityRevoke 0 2 0, .unmap 0, .terminateSubject 2, .restart] = halted := by
  simp [gate, applyOperation, operationReply, dispatchHardware, beginEntry, finishEntry,
    activeEntry, demoFrame, Interrupt.dispatchHardware, Interrupt.decodeVector, mapFatal,
    halt, installResumable, runOperations]

/-! ## Composite-dispatcher mixed-trace seed

The generated stateful ABI needs one public, finite state that can actually
exercise the accepted Phase 2 operation families.  This seed is not a second
transition system: every successor remains the result of `authoritativeGate`.
The finite functions below only make the complete canonical pre-state
reconstructible without accepting privileged identity from ABI words. -/

private def dispatcherSubjectOneSpace : Capability.Capability :=
  { object := 1, kind := .addressSpace, rights := { revoke := true },
    identity := 1 }

private def dispatcherSubjectOneEndpoint : Capability.Capability :=
  { object := 10, kind := .endpoint,
    rights := { send := true, grant := true },
    identity := 2 }

private def dispatcherSubjectTwoEndpoint : Capability.Capability :=
  { object := 10, kind := .endpoint,
    rights := { send := true, receive := true, grant := true, revoke := true },
    identity := 3 }

private def dispatcherSubjectTwoSpace : Capability.Capability :=
  { object := 2, kind := .addressSpace, rights := { revoke := true },
    identity := 4 }

private def dispatcherSubjectTwoMemory : Capability.Capability :=
  { object := 20, kind := .memory, rights := Capability.allRights,
    identity := 5 }

private def dispatcherCapabilities : Capability.State :=
  { nextIdentity := 6
    derivations := fun identity =>
      if identity = 1 then
        some (none, 1, .addressSpace, { revoke := true })
      else if identity = 2 then
        some (none, 10, .endpoint, { send := true, grant := true })
      else if identity = 3 then
        some (none, 10, .endpoint,
          { send := true, receive := true, grant := true, revoke := true })
      else if identity = 4 then
        some (none, 2, .addressSpace, { revoke := true })
      else if identity = 5 then
        some (none, 20, .memory, Capability.allRights)
      else none
    subjects := fun subject => subject = 1 || subject = 2
    objects := fun object => object = 1 || object = 2 || object = 10 || object = 20
    kinds := fun object =>
      if object = 1 || object = 2 then some .addressSpace
      else if object = 10 then some .endpoint
      else if object = 20 then some .memory
      else none
    slots := fun subject slot =>
      if subject = 1 && slot = 0 then some dispatcherSubjectOneSpace
      else if subject = 1 && slot = 1 then some dispatcherSubjectOneEndpoint
      else if subject = 2 && slot = 0 then some dispatcherSubjectTwoEndpoint
      else if subject = 2 && slot = 1 then some dispatcherSubjectTwoSpace
      else if subject = 2 && slot = 2 then some dispatcherSubjectTwoMemory
      else none }

private theorem dispatcherCapabilities_wellFormed :
    Capability.WellFormed dispatcherCapabilities := by
  simp only [Capability.WellFormed]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro subject slot capability hslot
    simp only [dispatcherCapabilities, dispatcherSubjectOneSpace,
      dispatcherSubjectOneEndpoint, dispatcherSubjectTwoEndpoint,
      dispatcherSubjectTwoSpace, dispatcherSubjectTwoMemory] at hslot
    repeat' split at hslot
    all_goals cases hslot <;>
      simp [dispatcherCapabilities, dispatcherSubjectOneSpace,
        dispatcherSubjectOneEndpoint, dispatcherSubjectTwoEndpoint,
        dispatcherSubjectTwoSpace, dispatcherSubjectTwoMemory,
        Capability.rightsValid, Capability.nonemptyRights,
        Capability.allRights]
    all_goals grind
  · intro identity parent object kind rights hderivation
    simp only [dispatcherCapabilities] at hderivation
    repeat' split at hderivation
    all_goals rcases hderivation with ⟨rfl, rfl, rfl, rfl⟩ <;>
      simp [dispatcherCapabilities]
    all_goals grind
  · intro subject slot capability otherSubject otherSlot otherCapability
      hslot hother hidentity
    simp only [dispatcherCapabilities, dispatcherSubjectOneSpace,
      dispatcherSubjectOneEndpoint, dispatcherSubjectTwoEndpoint,
      dispatcherSubjectTwoSpace, dispatcherSubjectTwoMemory] at hslot hother
    repeat' split at hslot
    all_goals repeat' split at hother
    all_goals cases hslot <;> cases hother <;> simp_all
  · intro subject slot hslot
    change 4 ≤ slot at hslot
    have hne0 : slot ≠ 0 := by omega
    have hne1 : slot ≠ 1 := by omega
    have hne2 : slot ≠ 2 := by omega
    simp [dispatcherCapabilities, hne0, hne1, hne2]

@[simp] private theorem dispatcherCapabilities_subjects (subject : Nat) :
    dispatcherCapabilities.subjects subject = (subject = 1 || subject = 2) := rfl

@[simp] private theorem dispatcherCapabilities_objects (object : Nat) :
    dispatcherCapabilities.objects object =
      (object = 1 || object = 2 || object = 10 || object = 20) := rfl

@[simp] private theorem dispatcherCapabilities_kinds (object : Nat) :
    dispatcherCapabilities.kinds object =
      (if object = 1 || object = 2 then some .addressSpace
       else if object = 10 then some .endpoint
       else if object = 20 then some .memory else none) := rfl

private def dispatcherLifecycle : SubjectLifecycle.State :=
  { capabilities := dispatcherCapabilities
    issuedSubjects := fun subject => subject = 1 || subject = 2
    ownedMemory := fun object => if object = 20 then some (2, 4) else none
    addressOwner := fun space =>
      if space = 1 then some 1 else if space = 2 then some 2 else none
    mapping := fun _ _ => none
    endpointOwner := fun object => if object = 10 then some 1 else none
    mailbox := fun _ => none
    frameOwner := fun frame => if frame = 4 then some 2 else none
    freeFrame := fun frame => frame != 4
    runnable := fun subject => subject = 1 || subject = 2
    current := some 2 }

private def dispatcherMemory : MemoryLifecycle.State :=
  { capabilities := dispatcherCapabilities
    allocator :=
      { frames := [4]
        status := fun frame => if frame = 4 then .owned 20 else .reserved }
    binding := fun object => if object = 20 then some 4 else none
    issued := fun object => object = 1 || object = 2 || object = 10 || object = 20 }

private def dispatcherVirtualMemory : VirtualMapping.State :=
  { memory := dispatcherMemory
    owner := dispatcherLifecycle.addressOwner
    mappings := fun _ _ => none
    issuedAddressSpace := fun space => space = 1 || space = 2 }

private def dispatcherEndpoints : EndpointIPC.State :=
  { capabilities := dispatcherCapabilities
    allocator := dispatcherMemory.allocator
    binding := dispatcherMemory.binding
    issued := dispatcherMemory.issued
    issuedAddressSpace := dispatcherVirtualMemory.issuedAddressSpace
    mailbox := fun _ => none
    sendHistory := fun _ => [] }

private def dispatcherScheduler : Scheduler.State :=
  { lifecycle := dispatcherLifecycle, ready := [1], capacity := 2 }

/-- The canonical, kernel-owned pre-state for the hosted mixed trace. -/
def compositeDispatcherInitial (plan : BootPageTablePlan.Plan) : CompositeState :=
  let base := bootRuntime plan
  let scheduler := dispatcherScheduler
  { base with
    execution :=
      { base.execution with
        core :=
          { lifecycle := dispatcherLifecycle
            context :=
              { base.execution.core.context with
                currentSubject := 2
                activeAddressSpace := 2 } }
        mode := .running }
    scheduler
    preemption := { base.preemption with scheduler }
    virtualMemory := dispatcherVirtualMemory
    ipc := { virtualMemory := dispatcherVirtualMemory, endpoints := dispatcherEndpoints }
    capabilities := dispatcherCapabilities
    lifecycle := dispatcherLifecycle
    resumable :=
      { scheduler
        contexts := [blockingEvidenceContext 1 0x10]
        capacity := 2
        translations :=
          { virtual := dispatcherVirtualMemory
            active := some 2
            entries := [] } }
    transfers := { toEndpointState := dispatcherEndpoints, pending := fun _ => none }
    blockingIPC :=
      { scheduler
        mailbox := fun _ => none
        waiters := fun _ => []
        waiterEndpoint := fun _ => none
        waiterCapacity := 1
        completion := fun _ => none }
    blockingContexts := fun _ => none
    deferredCancels := BlockingIPCContext.emptyDeferred }

/-- Subject 2's canonical memory-read authority has one executable slot.
This small public projection lets outer lifecycle proofs reason about removal
without exposing the dispatcher's private capability fixture. -/
theorem compositeDispatcherInitial_subjectTwo_memory_read_slot
    (plan : BootPageTablePlan.Plan) (slot : Nat)
    (capability : Capability.Capability)
    (hslot : (compositeDispatcherInitial plan).capabilities.slots 2 slot =
      some capability)
    (hobject : capability.object = 20)
    (hread : Capability.hasRight capability.rights .read) :
    slot = 2 := by
  simp only [compositeDispatcherInitial, dispatcherCapabilities,
    dispatcherSubjectOneSpace, dispatcherSubjectOneEndpoint,
    dispatcherSubjectTwoEndpoint, dispatcherSubjectTwoSpace,
    dispatcherSubjectTwoMemory] at hslot
  repeat' split at hslot
  all_goals cases hslot <;>
    simp_all [Capability.hasRight, Capability.permits,
      Capability.allRights]

private theorem dispatcherAddressOwner_some_iff (addressSpace subject : Nat) :
    dispatcherLifecycle.addressOwner addressSpace = some subject ↔
      (addressSpace = 1 ∧ subject = 1) ∨
        (addressSpace = 2 ∧ subject = 2) := by
  constructor
  · intro howner
    by_cases hfirst : addressSpace = 1
    · subst addressSpace
      simp [dispatcherLifecycle] at howner
      exact Or.inl ⟨rfl, howner.symm⟩
    · by_cases hsecond : addressSpace = 2
      · subst addressSpace
        simp [dispatcherLifecycle] at howner
        exact Or.inr ⟨rfl, howner.symm⟩
      · simp [dispatcherLifecycle, hfirst, hsecond] at howner
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      simp [dispatcherLifecycle]

private theorem dispatcherAddressSpace_live (addressSpace : Nat)
    (_hobject : dispatcherCapabilities.objects addressSpace = true)
    (hkind : dispatcherCapabilities.kinds addressSpace = some .addressSpace) :
    addressSpace = 1 ∨ addressSpace = 2 := by
  by_cases hlive : addressSpace = 1 ∨ addressSpace = 2
  · exact hlive
  · have hne1 : addressSpace ≠ 1 := fun heq => hlive (Or.inl heq)
    have hne2 : addressSpace ≠ 2 := fun heq => hlive (Or.inr heq)
    simp only [dispatcherCapabilities, hne1, hne2, ite_false] at hkind
    repeat' split at hkind <;> simp_all

set_option maxHeartbeats 800000 in
/-- The canonical mixed-dispatcher seed inhabits the complete authoritative
runtime invariant independently of the compiled plan retained for later
return selection. -/
theorem compositeDispatcherInitial_authoritativeRuntimeWellFormed
    (plan : BootPageTablePlan.Plan) :
    AuthoritativeRuntimeWellFormed (compositeDispatcherInitial plan) := by
  rcases dispatcherCapabilities_wellFormed with
    ⟨hslots, hderivations, hidentities, hslotSpaces⟩
  have hspace1 :
      Capability.HasAuthority dispatcherCapabilities 1 1 .revoke :=
    ⟨0, dispatcherSubjectOneSpace, rfl, rfl, rfl⟩
  have hspace2 :
      Capability.HasAuthority dispatcherCapabilities 2 2 .revoke :=
    ⟨1, dispatcherSubjectTwoSpace, rfl, rfl, rfl⟩
  have hownerSubject :
      ∀ addressSpace subject,
        dispatcherLifecycle.addressOwner addressSpace = some subject →
          subject = 1 ∨ subject = 2 := by
    intro addressSpace subject howner
    rcases (dispatcherAddressOwner_some_iff addressSpace subject).1 howner with
      ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hownerAuthority :
      ∀ addressSpace subject,
        dispatcherLifecycle.addressOwner addressSpace = some subject →
          Capability.HasAuthority dispatcherCapabilities subject addressSpace .revoke := by
    intro addressSpace subject howner
    rcases (dispatcherAddressOwner_some_iff addressSpace subject).1 howner with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hspace1
    · exact hspace2
  have haddressComplete :
      ∀ addressSpace,
        dispatcherCapabilities.objects addressSpace = true →
          dispatcherCapabilities.kinds addressSpace = some .addressSpace →
            ∃ subject, dispatcherLifecycle.addressOwner addressSpace = some subject := by
    intro addressSpace hobject hkind
    rcases dispatcherAddressSpace_live addressSpace hobject hkind with rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  have hownerAuthorityIf :
      ∀ addressSpace subject,
        (if addressSpace = 1 then some 1
          else if addressSpace = 2 then some 2 else none) = some subject →
          Capability.HasAuthority dispatcherCapabilities subject addressSpace .revoke := by
    intro addressSpace subject howner
    apply hownerAuthority addressSpace subject
    simpa [dispatcherLifecycle] using howner
  suffices hlegacy :
      DeferredBlockingRuntimeWellFormed
        (compositeDispatcherInitial plan) by
    refine ⟨hlegacy.1, hlegacy.2, ?_⟩
    change InvalidationPublication.WellFormed InvalidationPublication.initial
    exact InvalidationPublication.initial_wellFormed
  simp [AuthoritativeRuntimeWellFormed, DeferredBlockingRuntimeWellFormed,
    compositeDispatcherInitial, dispatcherScheduler, dispatcherLifecycle,
    dispatcherVirtualMemory, dispatcherMemory, dispatcherEndpoints,
    blockingEvidenceContext, blockingEvidenceRegisters,
    RuntimeWellFormed, CompositeState.Coherent, WellFormed,
    Interrupt.WellFormed, SubjectLifecycle.WellFormed,
    VirtualMapping.LifecycleWellFormed, VirtualMapping.WellFormed,
    IPCSyscall.WellFormed, EndpointIPC.WellFormed, Scheduler.WellFormed,
    Preemption.WellFormed, ResumablePreemption.WellFormed,
    ResumablePreemption.ReadyContextAgreement,
    ResumablePreemption.TranslationAgreement,
    ResumablePreemption.VirtualAgreement,
    ResumablePreemption.ResourceKindAgreement, CapabilityTransfer.WellFormed,
    TLB.Coherent, CompositeState.ReturnPlanLive,
    CompositeState.blockingIPCContext, CompositeState.BlockingIPCCoherent,
    CompositeState.DeferredCancellationWellFormed,
    BlockingIPCContext.DeferredWellFormed, BlockingIPCContext.WellFormed,
    BlockingIPCContext.ContextAgreement, BlockingIPC.WellFormed,
    BlockingIPC.authorizedReceive, BlockingIPCContext.emptyDeferred,
    BlockingIPCContext.validSaved, Scheduler.ownsAddressSpace,
    ResumablePreemption.contextFor, ResumablePreemption.validContext,
    Capability.hasRight, Capability.rightsValid, Capability.rightsSubset,
    Capability.nonemptyRights, Capability.permits,
    Interrupt.validSavedUserFrame, demoFrame,
    DirectPortIO.AcceptedControls, DMAQuarantine.q35Accepted,
    InvalidationPublication.initial_wellFormed,
    bootRuntime, bootLifecycle, bootCapabilities, bootVirtualMemory,
    bootMemory, bootEndpoints]
  repeat' apply And.intro
  all_goals first
    | assumption
    | simp (config := { failIfUnchanged := false })
        [hownerAuthorityIf, dispatcherSubjectOneSpace,
        dispatcherSubjectOneEndpoint, dispatcherSubjectTwoEndpoint,
        dispatcherSubjectTwoSpace, dispatcherSubjectTwoMemory,
        dispatcherLifecycle, dispatcherMemory, dispatcherVirtualMemory,
        dispatcherEndpoints, dispatcherScheduler]
  all_goals grind

def compositeDispatcherBlockingFrame : Interrupt.HardwareFrame :=
  demoFrame 32 .user

def compositeDispatcherBlockingRegisters : ResumablePreemption.Registers :=
  blockingEvidenceRegisters 0x22

def compositeDispatcherTimerFrame : Interrupt.HardwareFrame :=
  demoFrame 32 .user

def compositeDispatcherTimerRegisters : ResumablePreemption.Registers :=
  blockingEvidenceRegisters 0x11

/-- The machine capability-transfer trace begins in subject 1 by executing one
authoritative resumable switch from the shared dispatcher seed.  This keeps
the caller/address-space binding and the saved subject-2 continuation inside
the same transition system used by every later transfer edge. -/
def capabilityTransferBootInitial (plan : BootPageTablePlan.Plan) : CompositeState :=
  (authoritativeGate (compositeDispatcherInitial plan)
    (.ordinary (.resumePreempt compositeDispatcherTimerFrame
      compositeDispatcherBlockingRegisters))).state

theorem capabilityTransferBootInitial_authoritativeRuntimeWellFormed
    (plan : BootPageTablePlan.Plan) :
    AuthoritativeRuntimeWellFormed (capabilityTransferBootInitial plan) := by
  exact authoritativeGate_preserves_authoritativeRuntimeWellFormed
    (compositeDispatcherInitial plan)
    (.ordinary (.resumePreempt compositeDispatcherTimerFrame
      compositeDispatcherBlockingRegisters))
    (compositeDispatcherInitial_authoritativeRuntimeWellFormed plan)

/-- Seed for the in-flight revocation trace (#175).  From the shared dispatcher
seed, subject 2 delegates a revoke-only authority on endpoint 10 into subject
1's slot 2, then the authoritative timer switch makes subject 1 current with
its subject-2 continuation saved.  Both steps are exact `authoritativeGate`
transitions, so the seed inherits the complete invariant rather than restating
a second capability fixture. -/
def inFlightRevocationInitial (plan : BootPageTablePlan.Plan) : CompositeState :=
  runAuthoritativeOperations (compositeDispatcherInitial plan)
    [.ordinary (.capabilityCopy 0 1 2 { revoke := true }),
     .ordinary (.resumePreempt compositeDispatcherTimerFrame
       compositeDispatcherBlockingRegisters)]

theorem inFlightRevocationInitial_authoritativeRuntimeWellFormed
    (plan : BootPageTablePlan.Plan) :
    AuthoritativeRuntimeWellFormed (inFlightRevocationInitial plan) :=
  runAuthoritativeOperations_preserves_authoritativeRuntimeWellFormed
    (compositeDispatcherInitial plan) _
    (compositeDispatcherInitial_authoritativeRuntimeWellFormed plan)

def compositeDispatcherUserFaultFrame : Interrupt.HardwareFrame :=
  demoFrame 14 .user

def compositeDispatcherKernelFaultFrame : Interrupt.HardwareFrame :=
  demoFrame 14 .kernel

/-- Accepted termination in the canonical dispatcher state retains only
memory bindings whose allocator status names the same object.  This exposes
the lifecycle/allocator fact needed by outer authoritative extensions without
making private synchronized cleanup records part of their trusted surface. -/
theorem compositeDispatcherTerminateSubjectTwo_binding_owned
    (plan : BootPageTablePlan.Plan) :
    ∀ object frame,
      (authoritativeGate (compositeDispatcherInitial plan)
          (.ordinary (.terminateSubject 2))).state.virtualMemory.memory.binding
          object = some frame →
        FrameAllocator.IsOwnedBy
          (authoritativeGate (compositeDispatcherInitial plan)
            (.ordinary (.terminateSubject 2))).state.virtualMemory.memory.allocator
          frame object := by
  intro object frame hbinding
  simp [authoritativeGate_ordinary_state, gate, applyOperation,
    compositeDispatcherInitial, dispatcherLifecycle, dispatcherCapabilities,
    dispatcherVirtualMemory, dispatcherMemory, dispatcherScheduler,
    dispatcherEndpoints, SubjectLifecycle.terminate, installTerminatedSubject,
    installTerminatedResumable, ResumablePreemption.cleanupSubject,
    FrameAllocator.IsOwnedBy] at hbinding ⊢
  rcases hbinding with ⟨rfl, rfl⟩
  rfl

/-- Canonical subject termination retires subject authority but does not
silently release its bound memory object.  Frame 4 remains owned by object 20,
so allocating a fresh object is rejected until a later explicit memory-release
transition crosses its own checked publication boundary. -/
theorem compositeDispatcherTerminateSubjectTwo_requires_explicit_memory_release
    (plan : BootPageTablePlan.Plan) :
    let memory :=
      (authoritativeGate (compositeDispatcherInitial plan)
        (.ordinary (.terminateSubject 2))).state.virtualMemory.memory
    memory.binding 20 = some 4 ∧
      (MemoryLifecycle.allocate memory 21 1 2).result = .rejected .exhausted := by
  simp [authoritativeGate_ordinary_state, gate, applyOperation,
    compositeDispatcherInitial, dispatcherLifecycle, dispatcherCapabilities,
    dispatcherVirtualMemory, dispatcherMemory, dispatcherScheduler,
    dispatcherEndpoints, SubjectLifecycle.terminate, installTerminatedSubject,
    installTerminatedResumable, ResumablePreemption.cleanupSubject,
    MemoryLifecycle.allocate]
  native_decide

/-- Once the canonical subject-2 memory binding has crossed its separate
release boundary, the reclaimed frame admits a real fresh lifetime for
subject 1 in its first unused capability slot.  This projection keeps the
concrete dispatcher fixture private while exposing the exact allocation fact
needed by the outer IOMMU/frame-reuse proof. -/
theorem compositeDispatcherTerminateSubjectTwo_released_memory_allocates_fresh
    (plan : BootPageTablePlan.Plan) :
    let memory :=
      (authoritativeGate (compositeDispatcherInitial plan)
        (.ordinary (.terminateSubject 2))).state.virtualMemory.memory
    let released : MemoryLifecycle.State :=
      { memory with
        allocator := FrameAllocator.setStatus memory.allocator 4 .free
        binding := MemoryLifecycle.setBinding memory.binding 20 none }
    (MemoryLifecycle.allocate released 21 1 2).result = .accepted ∧
      (MemoryLifecycle.allocate released 21 1 2).state.binding 21 = some 4 := by
  simp [authoritativeGate_ordinary_state, gate, applyOperation,
    compositeDispatcherInitial, dispatcherLifecycle, dispatcherCapabilities,
    dispatcherVirtualMemory, dispatcherMemory, dispatcherScheduler,
    dispatcherEndpoints, SubjectLifecycle.terminate, installTerminatedSubject,
    installTerminatedResumable, ResumablePreemption.cleanupSubject,
    MemoryLifecycle.allocate, FrameAllocator.allocate]
  native_decide

/-- Canonical subject termination retires the owned memory-object capability
before the still-bound frame can cross the later receipt-consuming release
boundary.  This exposes the exact capability predicate used by that boundary
without requiring outer proofs to unfold the private dispatcher fixture. -/
theorem compositeDispatcherTerminateSubjectTwo_retires_memory_object
    (plan : BootPageTablePlan.Plan) :
    (authoritativeGate (compositeDispatcherInitial plan)
      (.ordinary (.terminateSubject 2))).state.virtualMemory.memory.capabilities.objects
        20 = false := by
  simp [authoritativeGate_ordinary_state, gate, applyOperation,
    compositeDispatcherInitial, dispatcherLifecycle, dispatcherCapabilities,
    dispatcherVirtualMemory, dispatcherMemory, dispatcherScheduler,
    dispatcherEndpoints, SubjectLifecycle.terminate, installTerminatedSubject,
    installTerminatedResumable, ResumablePreemption.cleanupSubject]
  native_decide

end LeanOS.FailStop
