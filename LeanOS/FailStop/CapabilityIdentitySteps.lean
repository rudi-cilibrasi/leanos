import LeanOS.FailStop.CapabilityIdentities
import LeanOS.FailStop.SpawnChildCleanup

/-!
# Fail-stop composite: identity provenance of every step

`LeanOS.FailStop.CapabilityIdentities` defines `IdentityStep` and proves it
for the capability-store and transfer-store transitions.  This module proves
it for every composite step family from a coherent pre-state:

- every ordinary operation (`applyOperation_identityStep`), hence every
  authoritative operation (`authoritativeGate_identityStep`), every
  invalidation entry point, and issued creation, so every `CompositeStep`
  (`CompositeStep.identityStep`);
- every operation of the public spawn family (`childGate_identityStep`).

`terminateChild_identityRetired` then shows that the identity of every
capability child termination removes is retired, so with
`IdentityStep.retired` and `stale_word_of_retired` a word that named it fails
after every later step.
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

/-! ## Transfer-store transitions -/

theorem CapabilityTransfer.offer_identityFrom (transfers : CapabilityTransfer.State) caller
    endpointSlot sourceSlot payload rights :
    IdentityFrom transfers.capabilities transfers.pending
      (CapabilityTransfer.offer transfers caller endpointSlot sourceSlot payload rights).state.capabilities
      (CapabilityTransfer.offer transfers caller endpointSlot sourceSlot payload rights).state.pending := by
  unfold CapabilityTransfer.offer
  repeat' split
  all_goals first
    | exact IdentityFrom.refl _ _
    | skip
  refine ⟨by simp [CapabilityTransfer.record], fun s slot cap held =>
    Or.inl ⟨s, slot, cap, by simpa [CapabilityTransfer.record] using held, rfl⟩,
    fun e t held => ?_⟩
  simp only [CapabilityTransfer.record, CapabilityTransfer.setPending] at held
  split at held
  · cases held; exact Or.inr (Nat.le_refl _)
  · exact Or.inl ⟨e, t, held, rfl⟩

theorem CapabilityTransfer.offerWords_identityFrom (transfers : CapabilityTransfer.State)
    caller endpointWord sourceWord sourceKind payload rights :
    IdentityFrom transfers.capabilities transfers.pending
      (CapabilityTransfer.offerWords transfers caller endpointWord sourceWord sourceKind payload
        rights).state.capabilities
      (CapabilityTransfer.offerWords transfers caller endpointWord sourceWord sourceKind payload
        rights).state.pending := by
  unfold CapabilityTransfer.offerWords
  repeat' split
  all_goals first
    | exact IdentityFrom.refl _ _
    | exact CapabilityTransfer.offer_identityFrom _ _ _ _ _ _

theorem CapabilityTransfer.accept_identityFrom (transfers : CapabilityTransfer.State) caller
    endpointSlot destinationSlot :
    IdentityFrom transfers.capabilities transfers.pending
      (CapabilityTransfer.accept transfers caller endpointSlot destinationSlot).state.capabilities
      (CapabilityTransfer.accept transfers caller endpointSlot destinationSlot).state.pending := by
  unfold CapabilityTransfer.accept
  repeat' split
  all_goals first
    | exact IdentityFrom.refl _ _
    | (simp only [CapabilityTransfer.deliverData, CapabilityTransfer.record]
       exact IdentityFrom.refl _ _)
    | skip
  rename_i transfer pendingAt _ _ _ _ _ _
  refine ⟨by simp [CapabilityTransfer.deliver, CapabilityTransfer.record, Capability.install],
    fun s slot cap held => ?_, fun e t held => ?_⟩
  · simp only [CapabilityTransfer.deliver, CapabilityTransfer.record, Capability.install] at held
    split at held
    · cases held; exact Or.inr (Or.inl ⟨_, transfer, pendingAt, rfl⟩)
    · exact Or.inl ⟨s, slot, cap, held, rfl⟩
  · simp only [CapabilityTransfer.deliver, CapabilityTransfer.record,
      CapabilityTransfer.setPending] at held
    split at held
    · cases held
    · exact Or.inl ⟨e, t, held, rfl⟩

theorem CapabilityTransfer.acceptWord_identityFrom (transfers : CapabilityTransfer.State) caller
    endpointWord destinationSlot :
    IdentityFrom transfers.capabilities transfers.pending
      (CapabilityTransfer.acceptWord transfers caller endpointWord destinationSlot).state.capabilities
      (CapabilityTransfer.acceptWord transfers caller endpointWord destinationSlot).state.pending := by
  unfold CapabilityTransfer.acceptWord
  repeat' split
  all_goals first
    | exact IdentityFrom.refl _ _
    | exact CapabilityTransfer.accept_identityFrom _ _ _ _

/-! ## Lifecycle and scheduler transitions keep the capability store -/

theorem Scheduler.selectNext_capabilities (state : Scheduler.State) :
    (Scheduler.selectNext state).state.lifecycle.capabilities = state.lifecycle.capabilities := by
  unfold Scheduler.selectNext
  repeat' split
  all_goals simp [Scheduler.reject]

theorem Scheduler.tick_capabilities (state : Scheduler.State) :
    (Scheduler.tick state).state.lifecycle.capabilities = state.lifecycle.capabilities := by
  unfold Scheduler.tick Scheduler.yield
  split
  · simp [Scheduler.reject]
  · split
    · simp [Scheduler.reject]
    · next subject _ _ =>
        have := Scheduler.selectNext_capabilities
          { state with ready := state.ready ++ [subject]
                       lifecycle := { state.lifecycle with current := none } }
        generalize Scheduler.selectNext _ = outcome at this ⊢
        cases outcome with
        | mk next result => cases result <;> simp_all [Scheduler.reject]

theorem ResumablePreemption.switch_capabilities (state : ResumablePreemption.State)
    interruptState frame registers :
    (ResumablePreemption.switch state interruptState frame registers).state.scheduler.lifecycle.capabilities =
      state.scheduler.lifecycle.capabilities := by
  have tick := Scheduler.tick_capabilities state.scheduler
  unfold ResumablePreemption.switch
  generalize Scheduler.tick state.scheduler = scheduled at tick ⊢
  rcases scheduled with ⟨scheduled, result⟩
  rcases result with (_ | selected) | reason
  all_goals (repeat' split) <;>
    try simp_all [ResumablePreemption.reject, ResumablePreemption.halt, TLB.switch]
  all_goals (repeat' split) <;> simp_all [TLB.switch]

theorem SubjectLifecycle.create_capabilities_slots (lifecycle : SubjectLifecycle.State) subject :
    (SubjectLifecycle.create lifecycle subject).state.capabilities.slots =
        lifecycle.capabilities.slots ∧
      (SubjectLifecycle.create lifecycle subject).state.capabilities.nextIdentity =
        lifecycle.capabilities.nextIdentity := by
  unfold SubjectLifecycle.create
  repeat' split
  all_goals simp [SubjectLifecycle.reject]

/-- Subject cleanup only removes capability slots. -/
theorem cleanup_slots_sub (old : SubjectLifecycle.State) subject s slot cap
    (held : (ResumablePreemption.retireOwnedAddressSpaces old subject
      (SubjectLifecycle.terminatedCapabilities old subject)).slots s slot = some cap) :
    old.capabilities.slots s slot = some cap := by
  simp only [ResumablePreemption.retireOwnedAddressSpaces,
    SubjectLifecycle.terminatedCapabilities] at held
  cases hold : old.capabilities.slots s slot with
  | none => simp [hold] at held
  | some original =>
      simp only [hold] at held
      repeat' split at held
      all_goals simp_all

/-! ## Coherence facts -/

theorem CompositeState.Coherent.transfersCapabilities {state : CompositeState}
    (coherent : state.Coherent) : state.transfers.capabilities = state.capabilities := by
  obtain ⟨_, _, _, caps, _, _, ipcCaps, _, _, transfers, _⟩ := coherent
  show state.transfers.toEndpointState.capabilities = _
  rw [transfers, ipcCaps, caps]

theorem CompositeState.Coherent.lifecycleCapabilities {state : CompositeState}
    (coherent : state.Coherent) : state.lifecycle.capabilities = state.capabilities :=
  coherent.2.2.2.1.symm

theorem CompositeState.Coherent.resumableCapabilities {state : CompositeState}
    (coherent : state.Coherent) :
    state.resumable.scheduler.lifecycle.capabilities = state.capabilities := by
  rw [coherent.resumableLifecycle, coherent.lifecycleCapabilities]

/-! ## Composite publications -/

/-- Explicit termination only removes slots and cancels every pending
offer. -/
theorem installTerminatedSubject_shrinks (state : CompositeState) subject
    (coherent : state.Coherent) :
    let next := installTerminatedSubject state subject
      (ResumablePreemption.cleanupSubject state.resumable subject)
    next.capabilities.nextIdentity = state.capabilities.nextIdentity ∧
      (∀ s slot cap, next.capabilities.slots s slot = some cap →
        state.capabilities.slots s slot = some cap) ∧
      ∀ e, next.transfers.pending e = none := by
  have old := coherent.resumableCapabilities
  refine ⟨?_, fun s slot cap held => ?_, fun e => ?_⟩
  · show (ResumablePreemption.retireOwnedAddressSpaces state.resumable.scheduler.lifecycle subject
        (SubjectLifecycle.terminatedCapabilities state.resumable.scheduler.lifecycle
          subject)).nextIdentity = _
    simp [ResumablePreemption.retireOwnedAddressSpaces,
      SubjectLifecycle.terminatedCapabilities, old]
  · have := cleanup_slots_sub state.resumable.scheduler.lifecycle subject s slot cap held
    rwa [old] at this
  · simp [installTerminatedSubject, installTerminatedResumable]

theorem installTerminatedSubject_identityStep (state : CompositeState) subject
    (coherent : state.Coherent) :
    IdentityStep state
      (installTerminatedSubject state subject
        (ResumablePreemption.cleanupSubject state.resumable subject)) := by
  obtain ⟨counter, slots, pending⟩ := installTerminatedSubject_shrinks state subject coherent
  exact IdentityFrom.of_shrink (Nat.le_of_eq counter.symm) slots
    (fun e t held => by rw [pending e] at held; cases held)

theorem publishInterruptCleanup_identityStep (state : CompositeState) subject
    (coherent : state.Coherent) :
    IdentityStep state (publishInterruptCleanup state subject) := by
  have old := coherent.resumableCapabilities
  refine IdentityFrom.of_shrink ?_ (fun s slot cap held => ?_) (fun e t held => ?_)
  · show state.capabilities.nextIdentity ≤
      (ResumablePreemption.retireOwnedAddressSpaces state.resumable.scheduler.lifecycle subject
        (SubjectLifecycle.terminatedCapabilities state.resumable.scheduler.lifecycle
          subject)).nextIdentity
    simp [ResumablePreemption.retireOwnedAddressSpaces,
      SubjectLifecycle.terminatedCapabilities, old]
  · have := cleanup_slots_sub state.resumable.scheduler.lifecycle subject s slot cap held
    rwa [old] at this
  · simp [publishInterruptCleanup, installTerminatedResumable] at held

theorem installTransfers_identityStep (state : CompositeState)
    (transfers : CapabilityTransfer.State) (coherent : state.Coherent)
    (step : IdentityFrom state.transfers.capabilities state.transfers.pending
      transfers.capabilities transfers.pending) :
    IdentityStep state (installTransfers state transfers) := by
  show IdentityFrom _ _ transfers.capabilities transfers.pending
  rw [← coherent.transfersCapabilities]
  exact step

/-! ## Every ordinary operation -/

/-- **Identity provenance of every ordinary operation** from a coherent
state. -/
theorem applyOperation_identityStep (state : CompositeState) (operation : Operation)
    (coherent : state.Coherent) : IdentityStep state (applyOperation state operation) := by
  have resumableCaps := coherent.resumableCapabilities
  cases operation
  case interrupt frame =>
    simp only [applyOperation]
    split
    · split
      · exact publishInterruptCleanup_identityStep state _ coherent
      · exact IdentityStep.refl state
    · exact IdentityStep.of_eq resumableCaps rfl
    all_goals first
      | exact IdentityStep.refl state
      | exact IdentityStep.of_eq rfl rfl
  case nmi | selectUserReturn | userReturn | restart =>
    simp only [applyOperation]
    repeat' split
    all_goals first
      | exact IdentityStep.of_eq rfl rfl
      | exact IdentityStep.refl state
      | (rw [selectLiveReturnAuthority_eq_execution_update]; exact IdentityStep.of_eq rfl rfl)
  case syscall call =>
    simp only [applyOperation]
    repeat' split
    all_goals first
      | exact IdentityStep.refl state
      | (rw [selectLiveReturnAuthority_eq_execution_update]; exact IdentityStep.of_eq rfl rfl)
  case ipc call =>
    simp only [applyOperation]
    have kept : (dispatchIPC state call).state.capabilities = state.capabilities ∧
        (dispatchIPC state call).state.transfers.pending = state.transfers.pending := by
      unfold dispatchIPC
      repeat' split
      all_goals exact ⟨rfl, rfl⟩
    split
    all_goals first
      | exact IdentityStep.refl state
      | exact IdentityStep.of_eq kept.1 kept.2
  case resumePreempt frame registers =>
    simp only [applyOperation]
    have caps := ResumablePreemption.switch_capabilities state.resumable state.execution.core
      frame registers
    rw [resumableCaps] at caps
    repeat' split
    all_goals first
      | exact IdentityStep.refl state
      | exact IdentityStep.of_eq caps rfl
      | exact IdentityStep.of_eq (by simpa using caps) rfl
  case transferOffer endpointWord sourceWord sourceKind payload rights =>
    simp only [applyOperation]
    split
    · exact IdentityStep.refl state
    · exact installTransfers_identityStep state _ coherent
        (CapabilityTransfer.offerWords_identityFrom _ _ _ _ _ _ _)
  case transferAccept endpointWord destinationSlot =>
    simp only [applyOperation]
    split
    · exact IdentityStep.refl state
    · exact installTransfers_identityStep state _ coherent
        (CapabilityTransfer.acceptWord_identityFrom _ _ _ _)
  case capabilityCopy source destination destinationSlot rights =>
    simp only [applyOperation]
    split
    · exact IdentityStep.refl state
    · exact Capability.copy_identityFrom _ _ _ _ _ _ _
  case capabilityRevoke authoritySlot victim victimSlot =>
    simp only [applyOperation]
    split
    · exact IdentityStep.refl state
    · exact Capability.revokeRuntimeSafe_identityFrom _ _ _ _ _ _
  case capabilityRevokeSubtree authoritySlot victim victimSlot =>
    simp only [applyOperation]
    split
    · exact IdentityStep.refl state
    · split
      · obtain ⟨counter, slots⟩ := Capability.revokeSubtreeRuntimeSafe_shrinks
          state.capabilities state.execution.core.context.currentSubject authoritySlot victim
          victimSlot
        exact IdentityFrom.of_shrink (Nat.le_of_eq counter.symm)
          (fun s slot cap held => slots s slot cap held)
          (fun e t held => (CapabilityTransfer.publishSubtreeRevocation_pending_some _ _ _ e t
            held).1)
      · exact IdentityStep.refl state
  case map | unmap | protect =>
    simp only [applyOperation]
    split
    all_goals first
      | exact IdentityStep.refl state
      | exact IdentityStep.of_eq rfl rfl
  case createSubject subject =>
    simp only [applyOperation]
    split
    · exact IdentityStep.refl state
    · obtain ⟨slots, counter⟩ := SubjectLifecycle.create_capabilities_slots state.lifecycle subject
      refine IdentityFrom.of_shrink ?_ (fun s slot cap held => ?_) (fun e t held => held)
      · show state.capabilities.nextIdentity ≤
          (SubjectLifecycle.create state.lifecycle subject).state.capabilities.nextIdentity
        rw [counter, coherent.lifecycleCapabilities]
        exact Nat.le_refl _
      · have : (SubjectLifecycle.create state.lifecycle subject).state.capabilities.slots s slot =
            some cap := held
        rwa [slots, coherent.lifecycleCapabilities] at this
  case terminateSubject subject =>
    simp only [applyOperation]
    split
    · exact IdentityStep.refl state
    · exact installTerminatedSubject_identityStep state subject coherent
  case scheduleAdd subject =>
    simp only [applyOperation]
    split
    · exact IdentityStep.refl state
    · exact IdentityStep.of_eq rfl rfl
  case scheduleRemove subject =>
    simp only [applyOperation]
    split
    · exact IdentityStep.refl state
    · exact IdentityStep.of_eq rfl rfl
  case scheduleNext =>
    simp only [applyOperation]
    split
    · exact IdentityStep.refl state
    · exact IdentityStep.refl state
    · next selected accepted =>
        exact absurd (schedulerDispatch_accepted_is_none state _ accepted) (by simp)
  case scheduleYield =>
    simp only [applyOperation]
    split
    · exact IdentityStep.refl state
    · next context accepted => exact absurd accepted (schedulerYield_ne_accepted state context)
  case scheduleTick =>
    simp only [applyOperation]
    split
    · exact IdentityStep.refl state
    · next context accepted => exact absurd accepted (schedulerTick_ne_accepted state context)
  case terminateCurrent =>
    simp only [applyOperation]
    repeat' split
    all_goals first
      | exact IdentityStep.refl state
      | exact installTerminatedSubject_identityStep state _ coherent

theorem gate_identityStep (state : CompositeState) (operation : Operation)
    (coherent : state.Coherent) : IdentityStep state (gate state operation).state := by
  rcases gate_stutters_or_applies state operation with same | applied
  · rw [same]; exact IdentityStep.refl state
  · rw [applied]; exact applyOperation_identityStep state operation coherent

/-! ## Every authoritative, invalidation, and issued-lifecycle step -/

/-- **Identity provenance of every authoritative operation**, including the
blocking operations, the deferred drain, and busy or halted stutters. -/
theorem authoritativeGate_identityStep (state : CompositeState)
    (operation : AuthoritativeOperation) (coherent : state.Coherent) :
    IdentityStep state (authoritativeGate state operation).state := by
  cases operation with
  | ordinary operation =>
      rw [authoritativeGate_ordinary_state]
      exact gate_identityStep state operation coherent
  | blocking operation =>
      exact IdentityStep.of_frames (authoritativeGate_frames state (.blocking operation))
        (by cases operation <;> simp only [AuthoritativeOperation.footprint,
              CompositeBlockingOperation.footprint] <;> decide)
        (by cases operation <;> simp only [AuthoritativeOperation.footprint,
              CompositeBlockingOperation.footprint] <;> decide)
  | drainDeferred subject =>
      exact IdentityStep.of_frames (authoritativeGate_frames state (.drainDeferred subject))
        (by simp only [AuthoritativeOperation.footprint]; decide)
        (by simp only [AuthoritativeOperation.footprint]; decide)

/-- Every invalidation-publication entry point keeps the capability and
transfer stores. -/
theorem InvalidationOperation.apply_identityStep (state : CompositeState)
    (operation : InvalidationOperation) :
    IdentityStep state (operation.apply state).state :=
  IdentityStep.of_frames (InvalidationOperation.apply_frames state operation)
    (by cases operation <;> simp only [InvalidationOperation.footprint] <;> decide)
    (by cases operation <;> simp only [InvalidationOperation.footprint] <;> decide)

/-- Issued subject creation only adds a live subject. -/
theorem lifecycleGate_identityStep (state : CompositeState) (operation : LifecycleOperation)
    (coherent : state.Coherent) :
    IdentityStep state (lifecycleGate state operation).state := by
  cases operation
  cases hmode : state.execution.mode <;>
    simp only [lifecycleGate, hmode, LifecycleOperation.apply]
  all_goals try exact IdentityStep.refl state
  cases result : (issueSubject state).result with
  | exhausted => rw [issueSubject_exhausted_unchanged state result]; exact IdentityStep.refl state
  | rejected reason =>
      rw [issueSubject_rejected_unchanged state reason result]; exact IdentityStep.refl state
  | issued identity =>
      obtain ⟨_, _, _, eq⟩ := issueSubject_issued state identity result
      rw [eq]
      exact IdentityStep.of_capabilities_eq
        (applyOperation_identityStep state (.createSubject identity) coherent) rfl rfl

/-- **Identity provenance of every composite step** from a coherent state. -/
theorem CompositeStep.identityStep (state : CompositeState) (step : CompositeStep)
    (coherent : state.Coherent) : IdentityStep state (step.apply state) := by
  cases step with
  | lifecycle operation => exact lifecycleGate_identityStep state operation coherent
  | authoritative operation => exact authoritativeGate_identityStep state operation coherent
  | invalidation operation => exact InvalidationOperation.apply_identityStep state operation

/-! ## The public spawn family -/

/-- Replace the source store by one with the same slots and counter. -/
theorem IdentityFrom.congr_left {caps caps' target : Capability.State}
    {pending pending' : Capability.ObjectId → Option CapabilityTransfer.Sealed}
    (slots : caps'.slots = caps.slots) (counter : caps'.nextIdentity = caps.nextIdentity)
    (step : IdentityFrom caps' pending target pending') :
    IdentityFrom caps pending target pending' := by
  refine ⟨counter ▸ step.counter, fun s slot cap held => ?_, fun e t held => ?_⟩
  · rcases step.slots s slot cap held with ⟨s', slot', cap', held', same⟩ | p | fresh
    · exact Or.inl ⟨s', slot', cap', slots ▸ held', same⟩
    · exact Or.inr (Or.inl p)
    · exact Or.inr (Or.inr (counter ▸ fresh))
  · rcases step.pending e t held with p | fresh
    · exact Or.inl p
    · exact Or.inr (counter ▸ fresh)

/-- The address-space stage of spawn installs exactly one root capability
with a fresh identity. -/
theorem spawnSpaced_identityStep (created : CompositeState) (child addressSpace : Nat)
    (published : created.virtualMemory.memory.capabilities = created.capabilities) :
    IdentityStep created (spawnSpaced created child addressSpace) := by
  show IdentityFrom created.capabilities created.transfers.pending
    (addressSpaceCapabilities created.virtualMemory.memory.capabilities addressSpace child
      childAddressSpaceSlot) created.transfers.pending
  rw [published]
  show IdentityFrom created.capabilities created.transfers.pending
    (Capability.installRoot (VirtualMapping.activateAddressSpace created.capabilities addressSpace)
      child childAddressSpaceSlot addressSpace .addressSpace VirtualMapping.addressSpaceRootRights)
    created.transfers.pending
  exact IdentityFrom.congr_left
    (caps' := VirtualMapping.activateAddressSpace created.capabilities addressSpace) rfl rfl
    (Capability.installRoot_identityFrom
    (VirtualMapping.activateAddressSpace created.capabilities addressSpace) child
    childAddressSpaceSlot addressSpace .addressSpace VirtualMapping.addressSpaceRootRights
    created.transfers.pending)

/-- **Explicit spawn** allocates two fresh identities (the address-space root
and the granted endpoint copy) and changes no other capability. -/
theorem spawn_identityStep (state : CompositeState) (request : SpawnRequest)
    (coherent : state.Coherent) : IdentityStep state (spawn state request).state := by
  cases result : (spawn state request).result with
  | rejected reason =>
      rw [spawn_rejected_unchanged state request reason result]; exact IdentityStep.refl state
  | spawned child addressSpace =>
      obtain ⟨_, issued, _, _, resolution, _, _, _, _, stateEq⟩ :=
        spawn_spawned_stages state request child addressSpace result
      obtain ⟨_, _, created, eq⟩ := issueSubject_issued state child issued
      have first : IdentityStep state (issueSubject state).state := by
        rw [eq]
        exact IdentityStep.of_capabilities_eq
          (applyOperation_identityStep state (.createSubject child) coherent) rfl rfl
      have published : (issueSubject state).state.virtualMemory.memory.capabilities =
          (issueSubject state).state.capabilities := by
        rw [eq]; simp [applyOperation, created, installCreatedSubject]
      have second := spawnSpaced_identityStep (issueSubject state).state child addressSpace
        published
      have third : IdentityStep (spawnSpaced (issueSubject state).state child addressSpace)
          (installCopiedCapabilities (spawnSpaced (issueSubject state).state child addressSpace)
            (Capability.copy (spawnSpaced (issueSubject state).state child addressSpace).capabilities
              (spawnParent state) resolution.handle.slot child childEndpointSlot
              request.rights).state) :=
        Capability.copy_identityFrom _ _ _ _ _ _ _
      rw [stateEq]
      exact IdentityStep.of_capabilities_eq (first.trans (second.trans third)) rfl rfl

/-- `releaseChild` keeps the capability store. -/
theorem releaseChild_capabilities (state : CompositeState) (parent slot child : Nat) :
    (releaseChild state parent slot child).capabilities = state.capabilities := rfl

/-- `releaseChild` keeps the pending transfers. -/
theorem releaseChild_pending (state : CompositeState) (parent slot child : Nat) :
    (releaseChild state parent slot child).transfers.pending = state.transfers.pending := rfl

/-- **Identity provenance of every public spawn-family step**, including busy
and halted stutters. -/
theorem childGate_identityStep (state : CompositeState) (operation : ChildOperation)
    (coherent : state.Coherent) : IdentityStep state (childGate state operation).state := by
  cases hmode : state.execution.mode <;> simp only [childGate, hmode]
  case handling => exact IdentityStep.refl state
  case halted => exact IdentityStep.refl state
  cases operation with
  | spawn request =>
      simp only [ChildOperation.apply]
      rcases spawnCharged_shape state request with ⟨same, _⟩ | ⟨child, addressSpace, _, spawned⟩
      · rw [same]; exact IdentityStep.refl state
      · obtain ⟨slot, _, _, _, _, _, _, stateEq⟩ :=
          spawnCharged_spawned state request child addressSpace _ spawned
        rw [stateEq]
        exact IdentityStep.of_capabilities_eq (spawn_identityStep state request coherent) rfl rfl
  | grantFrames control frames =>
      simp only [ChildOperation.apply]
      rcases FailStop.grantFrames_shape state control frames with ⟨same, _⟩ | ⟨child, moved, granted⟩
      · rw [same]; exact IdentityStep.refl state
      · obtain ⟨_, _, _, _, _, _, _, stateEq⟩ :=
          grantFrames_granted state control frames child moved granted
        rw [stateEq]
        exact IdentityStep.of_eq rfl rfl
  | terminateChild control =>
      simp only [ChildOperation.apply]
      rcases FailStop.terminateChild_shape state control with ⟨same, _⟩ |
        ⟨child, returned, terminated⟩
      · rw [same]; exact IdentityStep.refl state
      · obtain ⟨slot, _, _, _, _, stateEq⟩ :=
          terminateChild_terminated state control child returned terminated
        rw [stateEq]
        exact IdentityStep.of_capabilities_eq
          (authoritativeGate_identityStep state _ coherent)
          (releaseChild_capabilities _ _ _ _) (releaseChild_pending _ _ _ _)
  | grantAuthority subject budget =>
      simp only [ChildOperation.apply, grantBudgetedAuthority]
      split
      · exact IdentityStep.of_eq rfl rfl
      · exact IdentityStep.refl state
  | revokeAuthority subject => exact IdentityStep.of_eq rfl rfl

/-! ## Child termination retires the identities it removes -/

/-- The composite termination of a child only removes slots and pending
transfers, and keeps the identity counter. -/
theorem terminatedChild_shrinks (state : CompositeState) (child : Nat)
    (coherent : state.Coherent) :
    (terminatedChild state child).capabilities.nextIdentity = state.capabilities.nextIdentity ∧
      (∀ s slot cap, (terminatedChild state child).capabilities.slots s slot = some cap →
        state.capabilities.slots s slot = some cap) ∧
      ∀ e t, (terminatedChild state child).transfers.pending e = some t →
        state.transfers.pending e = some t := by
  have same : ∀ next : CompositeState, next = state →
      next.capabilities.nextIdentity = state.capabilities.nextIdentity ∧
        (∀ s slot cap, next.capabilities.slots s slot = some cap →
          state.capabilities.slots s slot = some cap) ∧
        ∀ e t, next.transfers.pending e = some t → state.transfers.pending e = some t := by
    intro next eq; subst eq; exact ⟨rfl, fun _ _ _ h => h, fun _ _ h => h⟩
  simp only [terminatedChild, authoritativeGate_ordinary_state]
  cases hmode : state.execution.mode <;> simp only [gate, hmode]
  case handling => exact ⟨trivial, fun _ _ _ h => h, fun _ _ h => h⟩
  case halted => exact ⟨trivial, fun _ _ _ h => h, fun _ _ h => h⟩
  simp only [applyOperation]
  split
  · exact same _ rfl
  · obtain ⟨counter, slots, pending⟩ := installTerminatedSubject_shrinks state child coherent
    exact ⟨counter, slots, fun e t held => by rw [pending e] at held; cases held⟩

/-- **Child termination retires every identity it removes.**  For every
capability that `terminateChild_revokes` removes (one the child held, or one
over an object the child owned), its identity is held by no slot and no
pending transfer afterwards, and is below the counter.  With
`IdentityStep.retired` it stays retired along every later trace, and with
`stale_word_of_retired` every word naming it stays unresolvable. -/
theorem terminateChild_identityRetired (state : CompositeState) (word : UInt64)
    (child returned : Nat)
    (running : state.execution.mode = .running) (holds : ResourceRuntimeWellFormed state)
    (terminated : (terminateChild state word).result = .terminated child returned)
    (holder slot : Nat) (capability : Capability.Capability)
    (held : state.capabilities.slots holder slot = some capability)
    (names : holder = child ∨ OwnedBy state.lifecycle child capability.object) :
    IdentityRetired (terminateChild state word).state capability.identity := by
  have runtime := holds.1.left
  have coherent := runtime.1
  have capsWf := runtime.2.2.2.1
  have transfersWf := runtime.2.2.2.2.2.2.2.2.2.1
  have cleared := terminateChild_revokes state word child returned running holds terminated
    holder slot capability held names
  obtain ⟨childSlot, entry, _, _, _, stateEq⟩ :=
    terminateChild_terminated state word child returned terminated
  obtain ⟨counter, slots, pending⟩ := terminatedChild_shrinks state child coherent
  have below : capability.identity < state.capabilities.nextIdentity :=
    (capsWf.1 holder slot capability held).2.2.2.2.1
  rw [stateEq] at cleared ⊢
  refine ⟨?_, fun s candidate cap heldAfter same => ?_, fun e t heldAfter same => ?_⟩
  · rw [releaseChild_capabilities, counter]; exact below
  · rw [releaseChild_capabilities] at heldAfter
    have before := slots s candidate cap heldAfter
    obtain ⟨rfl, rfl⟩ := capsWf.2.2.1 s candidate cap holder slot capability before held same
    rw [releaseChild_capabilities] at cleared
    rw [cleared] at heldAfter; cases heldAfter
  · rw [releaseChild_pending] at heldAfter
    have before := pending e t heldAfter
    have absent := (transfersWf.2 e t before).2.2.2.2.2.2.2.2.1
    rw [coherent.transfersCapabilities] at absent
    exact absent holder slot capability held same.symm

end LeanOS.FailStop
