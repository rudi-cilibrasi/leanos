import LeanOS.FailStop.Latch

/-!
# Fail-stop composite: state, projections, and the runtime invariant

`CompositeState` places every runtime subsystem under the execution latch.
This module names its projections for the `CompositeFootprint` vocabulary,
states the cross-projection coherence and `RuntimeWellFormed` invariants,
builds the boot-produced initial runtime, and defines the lifecycle and
capability publication helpers shared by every operation family.
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

/-- The state of the modeled subsystems whose transitions can run after entry.
Keeping these states under the execution latch makes bypassing it impossible in
the composite transition system. -/
structure CompositeState where
  execution : State
  scheduler : Scheduler.State
  preemption : Preemption.State
  virtualMemory : VirtualMapping.State
  ipc : IPCSyscall.State
  capabilities : Capability.State
  lifecycle : SubjectLifecycle.State
  /-- The exact authoritative context-bank model completed by issue #74. -/
  resumable : ResumablePreemption.State
  /-- The exact authoritative sealed-transfer model completed by issue #71. -/
  transfers : CapabilityTransfer.State
  /-- Authoritative blocking endpoint state.  Its scheduler is published back
  to every composite scheduler projection by `publishBlockingIPC`. -/
  blockingIPC : BlockingIPC.State
  /-- Exact suspended contexts paired with the authoritative waiter index.
  This bank is mutated only together with `blockingIPC` through the typed
  `BlockingIPCContext` transition. -/
  blockingContexts : BlockingIPC.SubjectId → Option ResumableContext.Context
  /-- Valid suspended contexts detached from waiters by contained cleanup.
  They remain quiescent until a capacity-checked drain republishes them. -/
  deferredCancels : BlockingIPCContext.DeferredCancelState :=
    BlockingIPCContext.emptyDeferred
  /-- The checked TSS/IOPL controls and complete finite device projection from
  the direct-port authority model.  Ordinary composite operations retain this
  field literally; trusted, purpose-bound kernel device operations live at the
  separate direct-port boundary. -/
  directPortIO : DirectPortIO.State :=
    { controls := DirectPortIO.selectedControls
      devices := { serial := 0, pic := 0, pit := 0, debugExit := 0 } }
  /-- Boot-validated finite PCI inventory and its proof-carrying deny-all
  quarantine.  This is authority state, not a second memory/runtime model. -/
  dmaAccepted : DMAQuarantine.AcceptedSnapshot := DMAQuarantine.q35Accepted
  /-- Latest authoritative PCI control observation.  Ordinary public
  operations cannot supply or change this snapshot. -/
  dmaObserved : DMAQuarantine.Snapshot := DMAQuarantine.q35Snapshot
  /-- Logical mapping successors remain private here until the machine reports
  completion of the exact invalidation ticket and effect.  Keeping this state
  in the composite runtime prevents publication/reuse ordering from living in
  a disconnected generated-dispatcher fixture. -/
  invalidationPublication : InvalidationPublication.State :=
    InvalidationPublication.initial

/-- The concrete value type owned by each named composite projection.  This is
the first integration boundary between the dependency-free footprint
vocabulary and `CompositeState`; later operation declarations can quantify
over projections without erasing their field types. -/
def CompositeProjectionType : CompositeFootprint.Projection → Type
  | .execution => State
  | .scheduler => Scheduler.State
  | .preemption => Preemption.State
  | .virtualMemory => VirtualMapping.State
  | .ipc => IPCSyscall.State
  | .capabilities => Capability.State
  | .lifecycle => SubjectLifecycle.State
  | .resumable => ResumablePreemption.State
  | .transfers => CapabilityTransfer.State
  | .blockingIPC => BlockingIPC.State
  | .blockingContexts => BlockingIPC.SubjectId → Option ResumableContext.Context
  | .deferredCancels => BlockingIPCContext.DeferredCancelState
  | .directPortIO => DirectPortIO.State
  | .dmaAccepted => DMAQuarantine.AcceptedSnapshot
  | .dmaObserved => DMAQuarantine.Snapshot
  | .invalidationPublication => InvalidationPublication.State

/-- Read one named projection without introducing an untyped sum or a second
copy of composite state. -/
def CompositeState.project (state : CompositeState) :
    (projection : CompositeFootprint.Projection) → CompositeProjectionType projection
  | .execution => state.execution
  | .scheduler => state.scheduler
  | .preemption => state.preemption
  | .virtualMemory => state.virtualMemory
  | .ipc => state.ipc
  | .capabilities => state.capabilities
  | .lifecycle => state.lifecycle
  | .resumable => state.resumable
  | .transfers => state.transfers
  | .blockingIPC => state.blockingIPC
  | .blockingContexts => state.blockingContexts
  | .deferredCancels => state.deferredCancels
  | .directPortIO => state.directPortIO
  | .dmaAccepted => state.dmaAccepted
  | .dmaObserved => state.dmaObserved
  | .invalidationPublication => state.invalidationPublication

/-- A typed frame obligation over the concrete composite state.  The dependent
projection result keeps each equality in its native subsystem type while the
footprint vocabulary remains independent of `CompositeState`. -/
def CompositeState.Frames (footprint : CompositeFootprint.Footprint)
    (before after : CompositeState) : Prop :=
  ∀ projection, CompositeFootprint.Frames footprint projection
    (before.project projection) (after.project projection)

/-- A stuttering composite transition satisfies every declared footprint. -/
theorem CompositeState.frames_of_eq (footprint : CompositeFootprint.Footprint)
    {before after : CompositeState} (preserved : after = before) :
    CompositeState.Frames footprint before after := by
  subst after
  intro projection
  exact CompositeFootprint.frames_of_eq footprint projection rfl

/-- Concrete composite frame obligations compose without erasing projection
types or duplicating the composite state. -/
theorem CompositeState.frames_trans (footprint : CompositeFootprint.Footprint)
    {before middle after : CompositeState}
    (first : CompositeState.Frames footprint before middle)
    (second : CompositeState.Frames footprint middle after) :
    CompositeState.Frames footprint before after := by
  intro projection
  exact CompositeFootprint.frames_trans footprint projection
    (first projection) (second projection)

/-- The blocking store and all composite scheduler views name one scheduler. -/
def CompositeState.BlockingIPCCoherent (state : CompositeState) : Prop :=
  state.blockingIPC.scheduler = state.scheduler ∧
  state.blockingIPC.scheduler.lifecycle = state.lifecycle

/-- The authoritative typed blocking state assembled from its two stored
projections. -/
def CompositeState.blockingIPCContext (state : CompositeState) :
    BlockingIPCContext.State :=
  { ipc := state.blockingIPC, blocked := state.blockingContexts }

/-- The strengthened blocking invariant classifies every saved context as an
indexed waiter or a disjoint, quiescent deferred cancellation. -/
def CompositeState.DeferredCancellationWellFormed (state : CompositeState) : Prop :=
  BlockingIPCContext.DeferredWellFormed state.blockingIPCContext state.deferredCancels ∧
  (forall subject saved, state.blockingContexts subject = some saved →
    ResumablePreemption.contextFor state.resumable.contexts subject = none) ∧
  (∀ subject saved, state.deferredCancels.retained subject = some saved →
    ResumablePreemption.contextFor state.resumable.contexts subject = none)

/-- Replacing the scheduler projection preserves a blocking store when every
field observed by waiter validation is unchanged and the replacement scheduler
is itself well formed. -/
private theorem blockingIPC_wellFormed_replaceScheduler
    (ipc : BlockingIPC.State) (scheduler : Scheduler.State)
    (hstate : BlockingIPC.WellFormed ipc)
    (hscheduler : Scheduler.WellFormed scheduler)
    (hcapabilities : scheduler.lifecycle.capabilities =
      ipc.scheduler.lifecycle.capabilities)
    (hrunnable : scheduler.lifecycle.runnable = ipc.scheduler.lifecycle.runnable)
    (hcurrent : scheduler.lifecycle.current = ipc.scheduler.lifecycle.current)
    (howner : scheduler.lifecycle.addressOwner = ipc.scheduler.lifecycle.addressOwner)
    (hready : scheduler.ready = ipc.scheduler.ready) :
    BlockingIPC.WellFormed { ipc with scheduler } := by
  rcases hstate with
    ⟨_hscheduler, hqueues, hwaiters, hunique, hindex, hmailbox, hcapability⟩
  refine ⟨hscheduler, hqueues, ?_, hunique, hindex, ?_, ?_⟩
  · simpa [BlockingIPC.authorizedReceive, Scheduler.ownsAddressSpace,
      hcapabilities, hrunnable, hcurrent, howner, hready] using hwaiters
  · simpa [hcapabilities] using hmailbox
  · simpa [hcapabilities] using hcapability

theorem blockingIPCContext_wellFormed_replaceScheduler
    (state : CompositeState) (scheduler : Scheduler.State)
    (hstate : BlockingIPCContext.WellFormed state.blockingIPCContext)
    (hscheduler : Scheduler.WellFormed scheduler)
    (hcapabilities : scheduler.lifecycle.capabilities =
      state.blockingIPC.scheduler.lifecycle.capabilities)
    (hrunnable : scheduler.lifecycle.runnable =
      state.blockingIPC.scheduler.lifecycle.runnable)
    (hcurrent : scheduler.lifecycle.current =
      state.blockingIPC.scheduler.lifecycle.current)
    (howner : scheduler.lifecycle.addressOwner =
      state.blockingIPC.scheduler.lifecycle.addressOwner)
    (hready : scheduler.ready = state.blockingIPC.scheduler.ready) :
    BlockingIPCContext.WellFormed
      { ipc := { state.blockingIPC with scheduler }, blocked := state.blockingContexts } := by
  exact ⟨blockingIPC_wellFormed_replaceScheduler state.blockingIPC scheduler hstate.1
    hscheduler hcapabilities hrunnable hcurrent howner hready, hstate.2⟩


/-- A compiled return plan refines the active live virtual-memory view exactly
at the two leaves used by the return gate.  The live object bindings must name
the same physical frames as the compiled user-text/user-stack leaves. -/
def ReturnAddressSpace.liveBound (view : ReturnAddressSpace)
    (addressSpace : Interrupt.AddressSpaceId) (plan : BootPageTablePlan.Plan)
    (virtualMemory : VirtualMapping.State) : Bool :=
  let selected :=
    if view.subject = 1 && addressSpace = 1 then
      some (BootPageTablePlan.Space.subjectA, BootPageTablePlan.Owner.subjectA)
    else if view.subject = 2 && addressSpace = 2 then
      some (BootPageTablePlan.Space.subjectB, BootPageTablePlan.Owner.subjectB)
    else none
  match selected with
  | none => false
  | some (space, owner) =>
      let codePage := view.codeRegion.first.toNat / X86PageTable.pageBytes
      let stackPage := view.stackRegion.first.toNat / X86PageTable.pageBytes
      match virtualMemory.mappings addressSpace codePage,
          virtualMemory.mappings addressSpace stackPage with
      | some codeMapping, some stackMapping =>
          match virtualMemory.memory.binding codeMapping.object,
              virtualMemory.memory.binding stackMapping.object with
          | some codeFrame, some stackFrame =>
              virtualMemory.owner addressSpace = some view.subject &&
                virtualMemory.memory.capabilities.objects codeMapping.object &&
                virtualMemory.memory.capabilities.kinds codeMapping.object = some .memory &&
                virtualMemory.memory.allocator.status codeFrame =
                  .owned codeMapping.object &&
                virtualMemory.memory.capabilities.objects stackMapping.object &&
                virtualMemory.memory.capabilities.kinds stackMapping.object = some .memory &&
                virtualMemory.memory.allocator.status stackFrame =
                  .owned stackMapping.object &&
                codeMapping.permissions.read && !codeMapping.permissions.write &&
                stackMapping.permissions.read && stackMapping.permissions.write &&
                plan.hasPolicyLeafAtFrame space codePage codeFrame .userText owner &&
                plan.hasPolicyLeafAtFrame space stackPage stackFrame .userStack owner
          | _, _ => false
      | _, _ => false

/-- Cross-subsystem refinement checked whenever return authority is selected
or consumed.  A detached compiled plan cannot authorize an unmapped target. -/
def CompositeState.ReturnPlanLive (state : CompositeState) : Bool :=
  match state.execution.returnPlan,
      state.execution.returnAddressSpace state.execution.core.context.activeAddressSpace with
  | some plan, some view =>
      view.liveBound state.execution.core.context.activeAddressSpace plan state.virtualMemory
  | _, _ => false

/-- Select authority only from a compiled plan that agrees with the current
live virtual-memory mappings. -/
def selectLiveReturnAuthority (state : CompositeState)
    (purpose : Interrupt.ReturnPurpose) : CompositeState :=
  if state.ReturnPlanLive then
    { state with execution := selectReturnAuthority state.execution purpose }
  else
    { state with execution := { state.execution with returnAuthorityArmed := false } }

theorem selectLiveReturnAuthority_armed_implies_live state purpose
    (harmed : (selectLiveReturnAuthority state purpose).execution.returnAuthorityArmed = true) :
    state.ReturnPlanLive = true := by
  unfold selectLiveReturnAuthority at harmed
  split at harmed
  · assumption
  · simp at harmed

theorem selectLiveReturnAuthority_eq_execution_update state purpose :
    selectLiveReturnAuthority state purpose =
      { state with execution := (selectLiveReturnAuthority state purpose).execution } := by
  unfold selectLiveReturnAuthority
  split <;> rfl

@[simp] theorem selectLiveReturnAuthority_core state purpose :
    (selectLiveReturnAuthority state purpose).execution.core = state.execution.core := by
  unfold selectLiveReturnAuthority
  split <;> simp

@[simp] theorem selectLiveReturnAuthority_mode state purpose :
    (selectLiveReturnAuthority state purpose).execution.mode = state.execution.mode := by
  unfold selectLiveReturnAuthority
  split <;> simp

@[simp] theorem selectLiveReturnAuthority_execution_returnPlan state purpose :
    (selectLiveReturnAuthority state purpose).execution.returnPlan =
      state.execution.returnPlan := by
  unfold selectLiveReturnAuthority
  split <;> simp

@[simp] theorem selectLiveReturnAuthority_execution_returnAddressSpace state purpose :
    (selectLiveReturnAuthority state purpose).execution.returnAddressSpace =
      state.execution.returnAddressSpace := by
  unfold selectLiveReturnAuthority
  split <;> simp

@[simp] theorem selectLiveReturnAuthority_returnPlanLive state purpose :
    (selectLiveReturnAuthority state purpose).ReturnPlanLive = state.ReturnPlanLive := by
  rw [selectLiveReturnAuthority_eq_execution_update]
  simp [CompositeState.ReturnPlanLive]

theorem selectLiveReturnAuthority_execution_wellFormed state purpose
    (hstate : WellFormed state.execution) :
    WellFormed (selectLiveReturnAuthority state purpose).execution := by
  unfold selectLiveReturnAuthority
  split
  · exact selectReturnAuthority_wellFormed state.execution purpose hstate
  · rcases hstate with ⟨hcore, hbound, hmode⟩
    exact ⟨hcore, by simp, hmode⟩

/-- Every subsystem view is a projection of one authoritative lifecycle.  In
particular, scheduling and interrupt containment cannot disagree about whether
a subject is still live. -/
def CompositeState.Coherent (state : CompositeState) : Prop :=
  state.execution.core.lifecycle = state.lifecycle ∧
  state.scheduler.lifecycle = state.lifecycle ∧
  state.preemption.scheduler = state.scheduler ∧
  state.capabilities = state.lifecycle.capabilities ∧
  state.virtualMemory.memory.capabilities = state.lifecycle.capabilities ∧
  state.ipc.virtualMemory = state.virtualMemory ∧
  state.ipc.endpoints.capabilities = state.lifecycle.capabilities ∧
  state.resumable.scheduler = state.scheduler ∧
  state.resumable.translations.virtual = state.virtualMemory ∧
  state.transfers.toEndpointState = state.ipc.endpoints ∧
  (∀ subject, state.lifecycle.current = some subject →
    state.execution.core.context.currentSubject = subject ∧
    state.execution.core.context.activeAddressSpace = subject) ∧
  (∀ object, state.lifecycle.capabilities.objects object ≠ true →
    state.ipc.endpoints.mailbox object = none) ∧
  (∀ object envelope, state.ipc.endpoints.mailbox object = some envelope →
    state.lifecycle.capabilities.subjects envelope.sender = true)

/-- The live composite publishes a DMA quarantine only while its current
control observation is exactly the boot-accepted finite snapshot.
`AcceptedSnapshot` carries canonical accounting, nonemptiness, unassigned
ownership, and the deny-all bus-master proof. -/
@[simp] def CompositeState.DMAQuarantined (state : CompositeState) : Prop :=
  state.dmaObserved = state.dmaAccepted.snapshot

theorem CompositeState.DMAQuarantined.quarantine {state : CompositeState}
    (hstate : state.DMAQuarantined) :
    DMAQuarantine.quarantine state.dmaObserved = true := by
  rw [hstate]
  exact state.dmaAccepted.quarantineAccepted

/-- The global invariant advertised by the composite runtime boundary.  It
collects every invariant represented in `CompositeState`; cross-view equality
is explicit rather than inferred from repair after a transition. -/
def RuntimeWellFormed (state : CompositeState) : Prop :=
  state.Coherent ∧
  WellFormed state.execution ∧
  SubjectLifecycle.WellFormed state.lifecycle ∧
  Capability.WellFormed state.capabilities ∧
  VirtualMapping.LifecycleWellFormed state.virtualMemory ∧
  IPCSyscall.WellFormed state.ipc ∧
  Scheduler.WellFormed state.scheduler ∧
  Preemption.WellFormed state.preemption ∧
  ResumablePreemption.WellFormed state.resumable ∧
  CapabilityTransfer.WellFormed state.transfers ∧
  (state.resumable.halted = true ↔ ∃ record, state.execution.mode = .halted record) ∧
  (state.execution.returnAuthorityArmed = true → state.ReturnPlanLive = true) ∧
  state.BlockingIPCCoherent ∧
  (DirectPortIO.AcceptedControls state.directPortIO.controls ∧
    state.DMAQuarantined)

/-- The blocking store observes the same authoritative lifecycle as every
other runtime projection. -/
theorem RuntimeWellFormed.blockingLifecycle {state : CompositeState}
    (hstate : RuntimeWellFormed state) :
    state.blockingIPC.scheduler.lifecycle = state.lifecycle := by
  rcases hstate with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hblocking, _⟩
  exact hblocking.2

/-- The authoritative waiter store observes the composite scheduler itself,
not merely a lifecycle projection that happens to agree. -/
theorem RuntimeWellFormed.blockingScheduler {state : CompositeState}
    (hstate : RuntimeWellFormed state) :
    state.blockingIPC.scheduler = state.scheduler := by
  rcases hstate with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hblocking, _⟩
  exact hblocking.1

/-- The global runtime invariant retains the boot-validated deny-all user
direct-port controls. -/
theorem RuntimeWellFormed.directPortControls {state : CompositeState}
    (hstate : RuntimeWellFormed state) :
    DirectPortIO.AcceptedControls state.directPortIO.controls := by
  rcases hstate with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hcontrols, _⟩
  exact hcontrols

/-- The global runtime invariant includes the exact boot-accepted PCI control
observation, rather than treating DMA quarantine as a parallel claim. -/
theorem RuntimeWellFormed.dmaQuarantined {state : CompositeState}
    (hstate : RuntimeWellFormed state) :
    state.DMAQuarantined := by
  rcases hstate with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hdma⟩
  exact hdma

/-! ## Boot-produced initial runtime -/

def bootCapabilities : Capability.State :=
  { subjects := fun _ => false
    objects := fun _ => false
    kinds := fun _ => none
    slots := fun _ _ => none }

def bootLifecycle : SubjectLifecycle.State :=
  { capabilities := bootCapabilities
    issuedSubjects := fun _ => false
    ownedMemory := fun _ => none
    addressOwner := fun _ => none
    mapping := fun _ _ => none
    endpointOwner := fun _ => none
    mailbox := fun _ => none
    frameOwner := fun _ => none
    freeFrame := fun _ => false
    runnable := fun _ => false
    current := none }

def bootMemory : MemoryLifecycle.State :=
  { capabilities := bootCapabilities
    allocator := { frames := [], status := fun _ => .reserved }
    binding := fun _ => none
    issued := fun _ => false }

def bootVirtualMemory : VirtualMapping.State :=
  { memory := bootMemory
    owner := fun _ => none
    mappings := fun _ _ => none
    issuedAddressSpace := fun _ => false }

def bootEndpoints : EndpointIPC.State :=
  { capabilities := bootCapabilities
    allocator := bootMemory.allocator
    binding := bootMemory.binding
    issued := bootMemory.issued
    issuedAddressSpace := fun _ => false
    mailbox := fun _ => none
    sendHistory := fun _ => [] }

/-- The bounded state published after the boot page-table compiler succeeds,
before any subject is admitted.  The compiled plan is retained as evidence for
later return selection, but cannot arm a return until authoritative lifecycle,
mapping, scheduler, and resumable-context state has been installed. -/
def bootRuntime (plan : BootPageTablePlan.Plan) : CompositeState :=
  let scheduler : Scheduler.State :=
    { lifecycle := bootLifecycle, ready := [], capacity := 0 }
  let resumable : ResumablePreemption.State :=
    { scheduler
      contexts := []
      capacity := 0
      translations := { virtual := bootVirtualMemory, active := none, entries := [] } }
  { execution :=
      { core :=
          { lifecycle := bootLifecycle
            context :=
              { currentSubject := 0
                activeAddressSpace := 0
                kernelStack := 0
                entryActive := false } }
        mode := .running
        returnPlan := some plan }
    scheduler
    preemption := { scheduler, timerArmed := false, acceptedTicks := 1 }
    virtualMemory := bootVirtualMemory
    ipc := { virtualMemory := bootVirtualMemory, endpoints := bootEndpoints }
    capabilities := bootCapabilities
    lifecycle := bootLifecycle
    resumable
    transfers := { toEndpointState := bootEndpoints, pending := fun _ => none }
    blockingIPC :=
      { scheduler
        mailbox := fun _ => none
        waiters := fun _ => []
        waiterEndpoint := fun _ => none
        waiterCapacity := 0
        completion := fun _ => none }
    blockingContexts := fun _ => none
    deferredCancels := BlockingIPCContext.emptyDeferred
    directPortIO :=
      { controls := DirectPortIO.selectedControls
        devices := { serial := 0, pic := 0, pit := 0, debugExit := 0 } } }

/-- A successfully compiled bounded boot plan produces a concrete global
invariant witness.  Boot does not synthesize a live subject or trusted return
identity: those remain disabled until later checked runtime admission. -/
theorem bootRuntime_runtimeWellFormed input plan
    (_hcompiled : BootPageTablePlan.compile input = .ok plan) :
    RuntimeWellFormed (bootRuntime plan) := by
  simp [RuntimeWellFormed, bootRuntime, CompositeState.Coherent, WellFormed,
    Interrupt.WellFormed, SubjectLifecycle.WellFormed, Capability.WellFormed,
    Capability.SlotsWellFormed, Capability.DerivationsWellFormed,
    Capability.LiveIdentitiesUnique, Capability.SlotSpacesWellFormed,
    VirtualMapping.LifecycleWellFormed, VirtualMapping.WellFormed,
    MemoryLifecycle.WellFormed, IPCSyscall.WellFormed, EndpointIPC.WellFormed,
    Scheduler.WellFormed, Preemption.WellFormed, ResumablePreemption.WellFormed,
    ResumablePreemption.ReadyContextAgreement,
    ResumablePreemption.TranslationAgreement, ResumablePreemption.VirtualAgreement,
    ResumablePreemption.ResourceKindAgreement, CapabilityTransfer.WellFormed,
    TLB.Coherent, CompositeState.ReturnPlanLive, bootCapabilities, bootLifecycle,
    bootMemory, bootVirtualMemory, bootEndpoints,
    CompositeState.blockingIPCContext, CompositeState.BlockingIPCCoherent,
    BlockingIPCContext.WellFormed, BlockingIPCContext.ContextAgreement,
    BlockingIPC.WellFormed, BlockingIPC.authorizedReceive,
    DirectPortIO.AcceptedControls, DMAQuarantine.q35Accepted]

def restrictMappings (lifecycle : SubjectLifecycle.State)
    (mappings : VirtualMapping.AddressSpaceId → VirtualMapping.VirtualPage →
      Option VirtualMapping.Mapping) :=
  fun space page => match mappings space page with
    | some mapping =>
        if lifecycle.mapping space page = some mapping.object then some mapping else none
    | none => none

def restrictMailboxes (lifecycle : SubjectLifecycle.State)
    (mailbox : EndpointIPC.ObjectId → Option EndpointIPC.Envelope) :=
  fun object => match mailbox object with
    | some envelope =>
        if lifecycle.capabilities.objects object = true ∧
            lifecycle.capabilities.subjects envelope.sender = true then some envelope else none
    | none => none

def synchronizeMemory (lifecycle : SubjectLifecycle.State)
    (memory : MemoryLifecycle.State) : MemoryLifecycle.State :=
  { memory with
    capabilities := lifecycle.capabilities
    binding := fun object => (lifecycle.ownedMemory object).map (·.2)
    allocator := { memory.allocator with
      status := fun frame =>
        match memory.allocator.status frame with
        | .owned object =>
            match lifecycle.ownedMemory object with
            | some (_, ownedFrame) => if ownedFrame = frame then .owned object else .free
            | none => .free
        | status => status } }

/-- Atomically publish a lifecycle change to every overlapping subsystem
projection.  Rich subsystem-only data is retained only while the authoritative
lifecycle still names it. -/
def installLifecycle (state : CompositeState)
    (lifecycle : SubjectLifecycle.State) : CompositeState :=
  let scheduler := { state.scheduler with lifecycle }
  let context := match lifecycle.current with
    | some subject => { state.execution.core.context with
        currentSubject := subject, activeAddressSpace := subject }
    | none => state.execution.core.context
  let virtualMemory := { state.virtualMemory with
    memory := synchronizeMemory lifecycle state.virtualMemory.memory
    owner := lifecycle.addressOwner
    mappings := restrictMappings lifecycle state.virtualMemory.mappings }
  let endpoints := { state.ipc.endpoints with
    capabilities := lifecycle.capabilities
    mailbox := restrictMailboxes lifecycle state.ipc.endpoints.mailbox }
  { state with
    execution := { state.execution with
      core := { state.execution.core with lifecycle, context }
      returnAuthorityArmed := false }
    scheduler
    preemption := { state.preemption with scheduler }
    virtualMemory
    ipc := { state.ipc with
      virtualMemory
      endpoints }
    capabilities := lifecycle.capabilities
    lifecycle
    resumable := { state.resumable with
      scheduler
      translations := { state.resumable.translations with virtual := virtualMemory } }
    transfers := { state.transfers with toEndpointState := endpoints }
    blockingIPC := { state.blockingIPC with scheduler } }

private def installCapabilities (state : CompositeState)
    (capabilities : Capability.State) : CompositeState :=
  installLifecycle state { state.lifecycle with capabilities }

/-- Publish monotonic capability delegation without invoking lifecycle cleanup.
Copy preserves every live registry and only adds one slot/derivation, so memory
bindings, mappings, mailboxes, contexts, and translations remain authoritative
and need only observe the new capability store. -/
def installCopiedCapabilities (state : CompositeState)
    (capabilities : Capability.State) : CompositeState :=
  let lifecycle := { state.lifecycle with capabilities }
  let scheduler := { state.scheduler with lifecycle }
  let virtualMemory := { state.virtualMemory with
    memory := { state.virtualMemory.memory with capabilities } }
  let endpoints := { state.ipc.endpoints with capabilities }
  { state with
    execution := { state.execution with
      core := { state.execution.core with lifecycle }
      returnAuthorityArmed := false }
    scheduler
    preemption := { state.preemption with scheduler }
    virtualMemory
    ipc := { state.ipc with virtualMemory, endpoints }
    capabilities
    lifecycle
    resumable := { state.resumable with
      scheduler
      translations := { state.resumable.translations with virtual := virtualMemory } }
    transfers := { state.transfers with toEndpointState := endpoints }
    blockingIPC := { state.blockingIPC with scheduler } }

/-- Publish subject creation without rebuilding unrelated resources.  Creation
only promotes the subject registry and issuance history, so memory bindings,
mappings, mailboxes, saved contexts, and cached translations remain exact. -/
def installCreatedSubject (state : CompositeState)
    (subject : SubjectLifecycle.SubjectId) : CompositeState :=
  let lifecycle := (SubjectLifecycle.create state.lifecycle subject).state
  let scheduler := { state.scheduler with lifecycle }
  let preemption := { state.preemption with scheduler }
  let virtualMemory := { state.virtualMemory with
    memory := { state.virtualMemory.memory with capabilities := lifecycle.capabilities } }
  let endpoints := { state.ipc.endpoints with capabilities := lifecycle.capabilities }
  { state with
    execution := { state.execution with
      core := { state.execution.core with lifecycle }
      returnAuthorityArmed := false }
    scheduler
    preemption
    virtualMemory
    ipc := { state.ipc with virtualMemory, endpoints }
    capabilities := lifecycle.capabilities
    lifecycle
    resumable := { state.resumable with
      scheduler
      translations := { state.resumable.translations with virtual := virtualMemory } }
    transfers := { state.transfers with toEndpointState := endpoints }
    blockingIPC := { state.blockingIPC with scheduler } }

@[simp] theorem createSubject_current lifecycle subject :
    (SubjectLifecycle.create lifecycle subject).state.current = lifecycle.current := by
  simp only [SubjectLifecycle.create]
  split <;> try rfl
  split <;> rfl

@[simp] theorem createSubject_objects lifecycle subject :
    (SubjectLifecycle.create lifecycle subject).state.capabilities.objects =
      lifecycle.capabilities.objects := by
  simp only [SubjectLifecycle.create]
  split <;> try rfl
  split <;> rfl

@[simp] theorem createSubject_slots lifecycle subject :
    (SubjectLifecycle.create lifecycle subject).state.capabilities.slots =
      lifecycle.capabilities.slots := by
  simp only [SubjectLifecycle.create]
  split <;> try rfl
  split <;> rfl

@[simp] theorem createSubject_kinds lifecycle subject :
    (SubjectLifecycle.create lifecycle subject).state.capabilities.kinds =
      lifecycle.capabilities.kinds := by
  simp only [SubjectLifecycle.create]
  split <;> try rfl
  split <;> rfl

@[simp] theorem createSubject_runnable lifecycle subject :
    (SubjectLifecycle.create lifecycle subject).state.runnable =
      lifecycle.runnable := by
  simp only [SubjectLifecycle.create]
  split <;> try rfl
  split <;> rfl

@[simp] theorem createSubject_addressOwner lifecycle subject :
    (SubjectLifecycle.create lifecycle subject).state.addressOwner =
      lifecycle.addressOwner := by
  simp only [SubjectLifecycle.create]
  split <;> try rfl
  split <;> rfl

theorem createSubject_preserves_live lifecycle subject candidate
    (hlive : lifecycle.capabilities.subjects candidate = true) :
    (SubjectLifecycle.create lifecycle subject).state.capabilities.subjects candidate = true := by
  simp only [SubjectLifecycle.create]
  split <;> try assumption
  split <;> try assumption
  simp only [SubjectLifecycle.setBool]
  split <;> simp_all

theorem installCreatedSubject_coherent state subject
    (hstate : state.Coherent) :
    (installCreatedSubject state subject).Coherent := by
  rcases hstate with
    ⟨hexecution, hscheduler, hpreemption, hcapabilities, hvirtualCapabilities,
      hipcVirtual, hipcCapabilities, hresumableScheduler, hresumableVirtual,
      htransfers, hauthority, hdeadMailbox, hliveSender⟩
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simpa [installCreatedSubject] using hauthority
  · intro object hdead
    apply hdeadMailbox object
    simpa [installCreatedSubject] using hdead
  · intro object envelope hmailbox
    have hmailbox' : state.ipc.endpoints.mailbox object = some envelope := by
      simpa [installCreatedSubject] using hmailbox
    have hold := hliveSender object envelope hmailbox'
    exact createSubject_preserves_live state.lifecycle subject envelope.sender hold

/-- Capability publication has one authoritative result and updates every
consumer in the same composite step.  In particular, legacy scheduler and
preemption views cannot retain the pre-revocation registry while IPC or the
resumable-context path observes the new one. -/
theorem installCapabilities_synchronizes_consumers state capabilities :
    let next := installCapabilities state capabilities
    next.capabilities = capabilities ∧
      next.lifecycle.capabilities = capabilities ∧
      next.execution.core.lifecycle.capabilities = capabilities ∧
      next.virtualMemory.memory.capabilities = capabilities ∧
      next.ipc.endpoints.capabilities = capabilities ∧
      next.scheduler.lifecycle.capabilities = capabilities ∧
      next.preemption.scheduler.lifecycle.capabilities = capabilities ∧
      next.resumable.scheduler.lifecycle.capabilities = capabilities ∧
      next.transfers.capabilities = capabilities := by
  simp [installCapabilities, installLifecycle, synchronizeMemory]

theorem installCopiedCapabilities_synchronizes_consumers state capabilities :
    let next := installCopiedCapabilities state capabilities
    next.capabilities = capabilities ∧
      next.lifecycle.capabilities = capabilities ∧
      next.execution.core.lifecycle.capabilities = capabilities ∧
      next.virtualMemory.memory.capabilities = capabilities ∧
      next.ipc.endpoints.capabilities = capabilities ∧
      next.scheduler.lifecycle.capabilities = capabilities ∧
      next.preemption.scheduler.lifecycle.capabilities = capabilities ∧
      next.resumable.scheduler.lifecycle.capabilities = capabilities ∧
      next.transfers.capabilities = capabilities := by
  simp [installCopiedCapabilities]

def installScheduler (state : CompositeState)
    (scheduler : Scheduler.State) : CompositeState :=
  installLifecycle { state with scheduler, preemption := { state.preemption with scheduler } }
    scheduler.lifecycle

end LeanOS.FailStop
