import LeanOS.FailStop.Capabilities

/-!
# Fail-stop composite: mapping, unmapping, and protection

Accepted map, unmap, and protect operations publish one virtual-memory state
and invalidate stale translations.  This module also defines `runOperations`,
the sequential composition of the ordinary gate.
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

/-- Accepted mapping publishes only the changed mapping projection.  Memory,
address-space ownership, endpoint state, and every unrelated runtime resource
remain the authoritative pre-state, while all mapping consumers observe the
exact subsystem post-state. -/
theorem gate_map_accepted_preserves_runtimeWellFormed state slot page permissions next
    (hstate : RuntimeWellFormed state)
    (hmode : state.execution.mode = .running)
    (haccepted : VirtualMapping.map state.virtualMemory
      state.execution.core.context.currentSubject slot
      state.execution.core.context.activeAddressSpace page permissions =
        { state := next, result := .accepted }) :
    RuntimeWellFormed (gate state (.map slot page permissions)).state ∧
      (gate state (.map slot page permissions)).result = .completed (.map .accepted) := by
  have hmemory := VirtualMapping.map_memory state.virtualMemory
    state.execution.core.context.currentSubject slot
    state.execution.core.context.activeAddressSpace page permissions
  have howner := VirtualMapping.map_owner state.virtualMemory
    state.execution.core.context.currentSubject slot
    state.execution.core.context.activeAddressSpace page permissions
  have hvirtual := VirtualMapping.map_preserves_lifecycleWellFormed
    state.virtualMemory state.execution.core.context.currentSubject slot
    state.execution.core.context.activeAddressSpace page permissions hstate.2.2.2.2.1
  rw [haccepted] at hmemory howner hvirtual
  let translations : TLB.State := { state.resumable.translations with virtual := next }
  have htlb : TLB.Coherent translations := by
    simpa [translations, TLB.Coherent] using
      hstate.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2
  have hpreserved := installVirtualMemory_preserves_runtimeWellFormed
    state next translations hstate hmemory howner hvirtual htlb rfl
  constructor
  · simpa [gate, hmode, applyOperation, haccepted, translations] using hpreserved
  · simp [gate, hmode, operationReply, haccepted]

/-- An accepted unmap updates the authoritative virtual-memory projection and
invalidates the matching entry in the owned resumable-context TLB before the
new lifecycle is published.  The composite synchronization step cannot retain
a cached translation for the removed page, and the bounded-cache invariant is
preserved. -/
theorem gate_unmap_accepted_invalidates_tlb state page next
    (hmode : state.execution.mode = .running)
    (haccepted : VirtualMapping.unmap state.virtualMemory
      state.execution.core.context.currentSubject
      state.execution.core.context.activeAddressSpace page =
        { state := next, result := .accepted })
    (hstate : RuntimeWellFormed state) :
    (gate state (.unmap page)).result = .completed (.unmap .accepted) ∧
      RuntimeWellFormed (gate state (.unmap page)).state ∧
      (gate state (.unmap page)).state.Coherent ∧
      TLB.Coherent (gate state (.unmap page)).state.resumable.translations ∧
      ∀ context, TLB.lookup
        (gate state (.unmap page)).state.resumable.translations.entries
        { addressSpace := state.execution.core.context.activeAddressSpace, page }
        context = none := by
  have hmemory : next.memory = state.virtualMemory.memory := by
    have h := VirtualMapping.unmap_memory state.virtualMemory
      state.execution.core.context.currentSubject
      state.execution.core.context.activeAddressSpace page
    rw [haccepted] at h
    exact h
  have howner : next.owner = state.virtualMemory.owner := by
    have h := VirtualMapping.unmap_owner state.virtualMemory
      state.execution.core.context.currentSubject
      state.execution.core.context.activeAddressSpace page
    rw [haccepted] at h
    exact h
  have hvirtual := VirtualMapping.unmap_preserves_lifecycleWellFormed
    state.virtualMemory state.execution.core.context.currentSubject
    state.execution.core.context.activeAddressSpace page hstate.2.2.2.2.1
  rw [haccepted] at hvirtual
  let translations := TLB.invalidatePage
    { state.resumable.translations with virtual := next }
    state.execution.core.context.activeAddressSpace page
  have htlb : TLB.Coherent translations := by
    exact TLB.invalidate_page_preserves_coherent
      { state.resumable.translations with virtual := next }
      state.execution.core.context.activeAddressSpace page hstate.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2
  have hpreserved := installVirtualMemory_preserves_runtimeWellFormed
    state next translations hstate hmemory howner hvirtual htlb rfl
  constructor
  · simp [gate, hmode, operationReply, haccepted]
  constructor
  · simpa [gate, hmode, applyOperation, haccepted, translations] using hpreserved
  constructor
  · simpa [gate, hmode, applyOperation, haccepted, translations] using hpreserved.1
  constructor
  · simpa [gate, hmode, applyOperation, haccepted, installVirtualMemory,
      translations, TLB.Coherent] using htlb
  · intro context
    simpa [gate, hmode, applyOperation, haccepted, installVirtualMemory,
      translations, TLB.invalidatePage] using
      (TLB.invalidate_page_absent state.resumable.translations.entries
        { addressSpace := state.execution.core.context.activeAddressSpace, page } context)

/-- Accepted protection reduction is a full authoritative composite
transition: the actor and root come from the execution latch, the exact
permission-restricted virtual state is published to every consumer, and the
affected cached translation is absent before the typed reply is exposed. -/
theorem gate_protect_accepted_invalidates_tlb state page permissions next
    (hmode : state.execution.mode = .running)
    (haccepted : TLB.protect state.resumable.translations
      state.execution.core.context.currentSubject
      state.execution.core.context.activeAddressSpace page permissions =
        { state := next, result := .accepted })
    (hstate : RuntimeWellFormed state) :
    (gate state (.protect page permissions)).result =
        .completed (.protect .accepted) ∧
      RuntimeWellFormed (gate state (.protect page permissions)).state ∧
      (gate state (.protect page permissions)).state.Coherent ∧
      TLB.Coherent
        (gate state (.protect page permissions)).state.resumable.translations ∧
      ∀ context, TLB.lookup
        (gate state (.protect page permissions)).state.resumable.translations.entries
        { addressSpace := state.execution.core.context.activeAddressSpace, page }
        context = none := by
  have hvirtualEq :
      state.resumable.translations.virtual = state.virtualMemory :=
    hstate.1.2.2.2.2.2.2.2.2.1
  have hmemory : next.virtual.memory = state.virtualMemory.memory := by
    have h := TLB.protect_virtual_memory state.resumable.translations
      state.execution.core.context.currentSubject
      state.execution.core.context.activeAddressSpace page permissions
    rw [haccepted] at h
    simpa [hvirtualEq] using h
  have howner : next.virtual.owner = state.virtualMemory.owner := by
    have h := TLB.protect_virtual_owner state.resumable.translations
      state.execution.core.context.currentSubject
      state.execution.core.context.activeAddressSpace page permissions
    rw [haccepted] at h
    simpa [hvirtualEq] using h
  have hpreVirtual :
      VirtualMapping.LifecycleWellFormed state.resumable.translations.virtual := by
    simpa [hvirtualEq] using hstate.2.2.2.2.1
  have hresult :
      (TLB.protect state.resumable.translations
        state.execution.core.context.currentSubject
        state.execution.core.context.activeAddressSpace page permissions).result =
          .accepted := by
    simp [haccepted]
  have hvirtual := TLB.protect_accepted_preserves_virtual_lifecycleWellFormed
    state.resumable.translations state.execution.core.context.currentSubject
    state.execution.core.context.activeAddressSpace page permissions hpreVirtual hresult
  rw [haccepted] at hvirtual
  have htlb : TLB.Coherent next := by
    have hpreCoherent : TLB.Coherent state.resumable.translations :=
      hstate.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2
    have h := TLB.protect_accepted_coherent state.resumable.translations
      state.execution.core.context.currentSubject
      state.execution.core.context.activeAddressSpace page permissions hpreCoherent hresult
    simpa [haccepted] using h
  have hactive : next.active = state.resumable.translations.active := by
    have h := TLB.protect_active state.resumable.translations
      state.execution.core.context.currentSubject
      state.execution.core.context.activeAddressSpace page permissions
    simpa [haccepted] using h
  have hpreserved := installVirtualMemory_preserves_runtimeWellFormed
    state next.virtual next hstate hmemory howner hvirtual htlb hactive
  constructor
  · simp [gate, hmode, operationReply, haccepted]
  constructor
  · simpa [gate, hmode, applyOperation, haccepted] using hpreserved
  constructor
  · simpa [gate, hmode, applyOperation, haccepted] using hpreserved.1
  constructor
  · simpa [gate, hmode, applyOperation, haccepted,
      installVirtualMemory] using htlb
  · intro context
    have habsent := TLB.protect_revokes_before_return state.resumable.translations
      state.execution.core.context.currentSubject
      state.execution.core.context.activeAddressSpace page permissions hresult context
    simpa [gate, hmode, applyOperation, haccepted,
      installVirtualMemory] using habsent

/-- Raw mapping is compatible with the authoritative blocking store for every
typed result.  Rejection is atomic; acceptance changes only mapping and TLB
projections while retaining every waiter-observed scheduler field. -/
theorem gate_map_preserves_blockingRuntimeWellFormed state slot page permissions
    (hstate : BlockingRuntimeWellFormed state) :
    BlockingRuntimeWellFormed
      (gate state (.map slot page permissions)).state := by
  cases hmode : state.execution.mode with
  | handling active => simpa [gate, hmode] using hstate
  | halted record => simpa [gate, hmode] using hstate
  | running =>
      generalize hmap : VirtualMapping.map state.virtualMemory
        state.execution.core.context.currentSubject slot
        state.execution.core.context.activeAddressSpace page permissions = outcome
      cases outcome with
      | mk next result =>
          cases result with
          | rejected reason => simpa [gate, hmode, applyOperation, hmap] using hstate
          | accepted =>
              have hmemory := VirtualMapping.map_memory state.virtualMemory
                state.execution.core.context.currentSubject slot
                state.execution.core.context.activeAddressSpace page permissions
              have howner := VirtualMapping.map_owner state.virtualMemory
                state.execution.core.context.currentSubject slot
                state.execution.core.context.activeAddressSpace page permissions
              have hvirtual := VirtualMapping.map_preserves_lifecycleWellFormed
                state.virtualMemory state.execution.core.context.currentSubject slot
                state.execution.core.context.activeAddressSpace page permissions
                hstate.1.2.2.2.2.1
              rw [hmap] at hmemory howner hvirtual
              let translations : TLB.State :=
                { state.resumable.translations with virtual := next }
              have htlb : TLB.Coherent translations := by
                simpa [translations, TLB.Coherent] using
                  hstate.1.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2
              have hpreserved := installVirtualMemory_preserves_blockingRuntimeWellFormed
                state next translations hstate hmemory howner hvirtual htlb rfl
              simpa [gate, hmode, applyOperation, hmap, translations] using hpreserved

/-- Raw unmapping preserves the complete blocking invariant while invalidating
the selected page from the authoritative resumable-context TLB. -/
theorem gate_unmap_preserves_blockingRuntimeWellFormed state page
    (hstate : BlockingRuntimeWellFormed state) :
    BlockingRuntimeWellFormed (gate state (.unmap page)).state := by
  cases hmode : state.execution.mode with
  | handling active => simpa [gate, hmode] using hstate
  | halted record => simpa [gate, hmode] using hstate
  | running =>
      generalize hunmap : VirtualMapping.unmap state.virtualMemory
        state.execution.core.context.currentSubject
        state.execution.core.context.activeAddressSpace page = outcome
      cases outcome with
      | mk next result =>
          cases result with
          | rejected reason => simpa [gate, hmode, applyOperation, hunmap] using hstate
          | accepted =>
              have hmemory := VirtualMapping.unmap_memory state.virtualMemory
                state.execution.core.context.currentSubject
                state.execution.core.context.activeAddressSpace page
              have howner := VirtualMapping.unmap_owner state.virtualMemory
                state.execution.core.context.currentSubject
                state.execution.core.context.activeAddressSpace page
              have hvirtual := VirtualMapping.unmap_preserves_lifecycleWellFormed
                state.virtualMemory state.execution.core.context.currentSubject
                state.execution.core.context.activeAddressSpace page
                hstate.1.2.2.2.2.1
              rw [hunmap] at hmemory howner hvirtual
              let translations := TLB.invalidatePage
                { state.resumable.translations with virtual := next }
                state.execution.core.context.activeAddressSpace page
              have htlb : TLB.Coherent translations := by
                exact TLB.invalidate_page_preserves_coherent
                  { state.resumable.translations with virtual := next }
                  state.execution.core.context.activeAddressSpace page
                  hstate.1.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2
              have hpreserved := installVirtualMemory_preserves_blockingRuntimeWellFormed
                state next translations hstate hmemory howner hvirtual htlb rfl
              simpa [gate, hmode, applyOperation, hunmap, translations] using hpreserved

/-- Raw protection reduction preserves the complete blocking/deferred-facing
runtime projection while invalidating the selected page in the authoritative
TLB state. -/
theorem gate_protect_preserves_blockingRuntimeWellFormed state page permissions
    (hstate : BlockingRuntimeWellFormed state) :
    BlockingRuntimeWellFormed (gate state (.protect page permissions)).state := by
  cases hmode : state.execution.mode with
  | handling active => simpa [gate, hmode] using hstate
  | halted record => simpa [gate, hmode] using hstate
  | running =>
      generalize hprotect : TLB.protect state.resumable.translations
        state.execution.core.context.currentSubject
        state.execution.core.context.activeAddressSpace page permissions = outcome
      cases outcome with
      | mk next result =>
          cases result with
          | rejected reason =>
              simpa [gate, hmode, applyOperation, hprotect] using hstate
          | accepted =>
              have hvirtualEq :
                  state.resumable.translations.virtual = state.virtualMemory :=
                hstate.1.1.2.2.2.2.2.2.2.2.1
              have hmemory : next.virtual.memory = state.virtualMemory.memory := by
                have h := TLB.protect_virtual_memory state.resumable.translations
                  state.execution.core.context.currentSubject
                  state.execution.core.context.activeAddressSpace page permissions
                rw [hprotect] at h
                simpa [hvirtualEq] using h
              have howner : next.virtual.owner = state.virtualMemory.owner := by
                have h := TLB.protect_virtual_owner state.resumable.translations
                  state.execution.core.context.currentSubject
                  state.execution.core.context.activeAddressSpace page permissions
                rw [hprotect] at h
                simpa [hvirtualEq] using h
              have hresult :
                  (TLB.protect state.resumable.translations
                    state.execution.core.context.currentSubject
                    state.execution.core.context.activeAddressSpace page permissions).result =
                      .accepted := by
                simp [hprotect]
              have hpreVirtual :
                  VirtualMapping.LifecycleWellFormed
                    state.resumable.translations.virtual := by
                simpa [hvirtualEq] using hstate.1.2.2.2.2.1
              have hvirtual :=
                TLB.protect_accepted_preserves_virtual_lifecycleWellFormed
                  state.resumable.translations
                  state.execution.core.context.currentSubject
                  state.execution.core.context.activeAddressSpace page permissions
                  hpreVirtual hresult
              rw [hprotect] at hvirtual
              have htlb : TLB.Coherent next := by
                have hpreCoherent : TLB.Coherent state.resumable.translations :=
                  hstate.1.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2
                have h := TLB.protect_accepted_coherent state.resumable.translations
                  state.execution.core.context.currentSubject
                  state.execution.core.context.activeAddressSpace page permissions
                  hpreCoherent hresult
                simpa [hprotect] using h
              have hactive : next.active = state.resumable.translations.active := by
                have h := TLB.protect_active state.resumable.translations
                  state.execution.core.context.currentSubject
                  state.execution.core.context.activeAddressSpace page permissions
                simpa [hprotect] using h
              have hpreserved := installVirtualMemory_preserves_blockingRuntimeWellFormed
                state next.virtual next hstate hmemory howner hvirtual htlb hactive
              simpa [gate, hmode, applyOperation, hprotect] using hpreserved

private theorem dispatchHardware_running_returnAuthority_unarmed state frame
    (hmode : state.mode = .running) :
    (dispatchHardware state frame).state.returnAuthorityArmed = false := by
  simp only [dispatchHardware, hmode, beginEntry, finishEntry, activeEntry]
  generalize hdispatch : Interrupt.dispatchHardware
    { state.core with context := { state.core.context with entryActive := false } }
    frame = outcome
  cases outcome with
  | mk next action => cases action <;> simp [halt]

theorem dispatchHardware_running_not_alreadyHalted state frame record
    (hmode : state.mode = .running) :
    (dispatchHardware state frame).action ≠ .alreadyHalted record := by
  simp only [dispatchHardware, hmode, beginEntry, finishEntry, activeEntry]
  generalize hdispatch : Interrupt.dispatchHardware
    { state.core with context := { state.core.context with entryActive := false } }
    frame = outcome
  cases outcome with
  | mk next action => cases action <;> simp [halt]

/-- Initial dispatch is also represented by a typed composite step; syscall
and timer paths reselect only after their final context update. -/
theorem select_user_return_is_reachable state purpose
    (hmode : state.execution.mode = .running) :
    (gate state (.selectUserReturn purpose)).state =
      selectLiveReturnAuthority state purpose := by
  simp [gate, hmode, applyOperation]

theorem syscall_entry_leaves_return_unarmed state frame
    (hmode : state.execution.mode = .running)
    (hidentity : ∀ subject,
      (dispatchHardware state.execution frame).action = .contained subject →
        state.lifecycle.current = some subject) :
    (gate state (.interrupt frame)).state.execution.returnAuthorityArmed = false := by
  have hunarmed := dispatchHardware_running_returnAuthority_unarmed
    state.execution frame hmode
  have hnotAlready record := dispatchHardware_running_not_alreadyHalted
    state.execution frame record hmode
  simp only [gate, hmode, applyOperation]
  generalize hdispatch : dispatchHardware state.execution frame = entry at hunarmed
  cases haction : entry.action with
  | contained subject =>
      have hcurrent : state.lifecycle.current = some subject :=
        hidentity subject (by rw [hdispatch]; exact haction)
      simp [hcurrent, publishInterruptCleanup, installTerminatedResumable]
  | fatal reason => simp [installResumable]
  | timer => simpa using hunarmed
  | syscall => simpa using hunarmed
  | rejected reason => simpa using hunarmed
  | alreadyHalted record =>
      apply False.elim
      apply hnotAlready record
      rw [hdispatch]
      exact haction

def runOperations (state : CompositeState) : List Operation → CompositeState
  | [] => state
  | operation :: rest => runOperations (gate state operation).state rest

/-- Arbitrary finite public-operation traces cannot relax the reviewed port
controls or mutate any modeled device, including suffixes after a fatal latch. -/
@[simp] theorem runOperations_directPortIO state operations :
    (runOperations state operations).directPortIO = state.directPortIO := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation rest ih =>
      rw [runOperations, ih, gate_directPortIO]

/-- Arbitrary finite ordinary suffixes preserve the exact accepted/observed
PCI authority and therefore the global DMA quarantine conjunct. -/
theorem runOperations_preserves_dmaQuarantined state operations
    (hstate : state.DMAQuarantined) :
    (runOperations state operations).DMAQuarantined ∧
      DMAQuarantine.quarantine
        (runOperations state operations).dmaObserved = true := by
  induction operations generalizing state with
  | nil => exact ⟨hstate, hstate.quarantine⟩
  | cons operation rest ih =>
      simp only [runOperations]
      exact ih (gate state operation).state
        (gate_preserves_dmaQuarantined state operation hstate)

end LeanOS.FailStop
