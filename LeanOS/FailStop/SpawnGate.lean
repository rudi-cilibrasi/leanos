import LeanOS.FailStop.SpawnAccountingTraces
import LeanOS.FailStop.CapabilityIdentitySteps

/-!
# Fail-stop composite: stale capability words along every later trace

Gate item 4 of ADR 0010 asks that no reference to a terminated child survive.
#491 proved that a capability word naming a terminated child's object is
stale right after the termination and after one later spawn.  This module
proves it along every later trace.

`IdentityStep` (`LeanOS.FailStop.CapabilityIdentities`) says that every
capability identity after a step was already present (in a slot or a pending
sealed transfer) or is fresh, at least the old counter.  Every step of every
family has it: `CompositeStep.identityStep`, `childGate_identityStep`, and,
here, `memoryGate_identityStep`.  So `runChildSteps_identityStep` gives it for
whole traces, and an identity retired by a termination
(`terminateChild_identityRetired`) stays retired at the end of every trace
(`IdentityStep.retired`).  A word naming a retired identity never resolves
(`stale_word_of_retired`): `stale_word_forever`.
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

/-! ## Memory steps -/

/-- An allocation installs exactly one fresh identity, the counter's. -/
theorem allocatedState_identityStep (state : CompositeState) (object owner slot frame : Nat) :
    IdentityStep state (allocatedState state object owner slot frame) := by
  show IdentityFrom _ _ (allocatedCapabilities state.capabilities object owner slot)
    state.transfers.pending
  have base := Capability.installRoot_identityFrom
    (MemoryLifecycle.activateObject state.capabilities object) owner slot object .memory
    Capability.allRights state.transfers.pending
  exact ⟨base.counter, base.slots, base.pending⟩

/-- A release only removes slots and pending transfers. -/
theorem releasedState_identityStep (state : CompositeState) (object frame : Nat) :
    IdentityStep state (releasedState state object frame) := by
  show IdentityFrom _ _ (MemoryLifecycle.retireCapabilities state.capabilities object)
    (releasedTransfers state.transfers
      { state.ipc.endpoints with
        capabilities := MemoryLifecycle.retireCapabilities state.capabilities object }
      object).pending
  refine IdentityFrom.of_shrink (Nat.le_refl _) (fun subject slot capability held => ?_)
    (fun endpoint transfer pending => (releasedTransfers_pending pending).1)
  exact ((retireCapabilities_slots_some _ _).1 held).1

/-- **Identity provenance of every memory step**, including busy and halted
stutters and every rejection. -/
theorem memoryGate_identityStep (state : CompositeState) (operation : MemoryOperation) :
    IdentityStep state (memoryGate state operation).state := by
  rcases memoryGate_state_cases state operation with same | applied
  · rw [same]; exact IdentityStep.refl state
  rw [applied]
  cases operation with
  | allocate slot =>
      simp only [MemoryOperation.apply]
      rcases allocateMemory_shape state slot with ⟨same, _⟩ | ⟨object, frame, allocated⟩
      · rw [same]; exact IdentityStep.refl state
      · rw [(allocateMemory_allocated state slot object frame allocated).2.2.2.2.2.2]
        exact allocatedState_identityStep state object _ slot frame
  | release slot =>
      simp only [MemoryOperation.apply]
      rcases releaseMemory_shape state slot with ⟨same, _⟩ | ⟨object, frame, released⟩
      · rw [same]; exact IdentityStep.refl state
      · obtain ⟨_, _, _, _, _, _, _, _, stateEq⟩ :=
          releaseMemory_released state slot object frame released
        rw [stateEq]
        exact releasedState_identityStep state object frame

/-! ## Whole traces -/

/-- Identity provenance of one trace step from a state satisfying the
combined invariant. -/
theorem ChildTraceStep.identityStep (state : CompositeState) (step : ChildTraceStep)
    (holds : ResourceRuntimeWellFormed state) : IdentityStep state (step.apply state) := by
  have coherent := holds.1.left.1
  cases step with
  | composite step => exact step.identityStep state coherent
  | child operation => exact childGate_identityStep state operation coherent
  | memory operation => exact memoryGate_identityStep state operation

/-- **Identity provenance of every admissible trace.**  Every capability
identity at the end of the trace was present at the start, in a slot or a
pending transfer, or is at least the starting counter. -/
theorem runChildSteps_identityStep (state : CompositeState) (steps : List ChildTraceStep)
    (holds : ResourceRuntimeWellFormed state) (accounting : ChildAccountingWellFormed state)
    (tree : SpawnTreeWellFormed state) (admissible : AdmissibleAlongChild state steps) :
    IdentityStep state (runChildSteps state steps) := by
  induction steps generalizing state with
  | nil => exact IdentityStep.refl state
  | cons step rest ih =>
      obtain ⟨now, later⟩ := admissible
      obtain ⟨nextHolds, nextAccounting, nextTree, _⟩ :=
        step.admissible_preserves state holds accounting tree now
      exact (step.identityStep state holds).trans
        (ih (step.apply state) nextHolds nextAccounting nextTree later)

/-- **Capability words naming a terminated child stay stale along every later
trace** (#491, gate item 4).  If, before an accepted child termination, a
holder's word resolved to a capability the child held, or to a capability
over an object the child owned (for example the parent's endpoint to the
child, or the child's address-space root), then after the termination and
any admissible trace of composite, spawn-family, and memory steps, that word
still does not resolve for any holder and any expected kind: no later spawn,
delegation, transfer, or allocation ever reissues its identity. -/
theorem stale_word_forever (state : CompositeState) (word : UInt64) (child returned : Nat)
    (running : state.execution.mode = .running) (holds : ResourceRuntimeWellFormed state)
    (accounting : ChildAccountingWellFormed state) (tree : SpawnTreeWellFormed state)
    (terminated : (terminateChild state word).result = .terminated child returned)
    (holder : Nat) (handleWord : UInt64) (kind : Capability.ObjectKind)
    (resolution : CapabilityHandle.Resolution)
    (resolved : CapabilityHandle.resolveCurrent state.capabilities { caller := holder } handleWord
      kind = .ok resolution)
    (names : holder = child ∨ OwnedBy state.lifecycle child resolution.capability.object)
    (steps : List ChildTraceStep)
    (admissible : AdmissibleAlongChild (terminateChild state word).state steps)
    (anyHolder : Nat) (anyKind : Capability.ObjectKind) :
    ∃ reason, CapabilityHandle.resolveCurrent
      (runChildSteps (terminateChild state word).state steps).capabilities
      { caller := anyHolder } handleWord anyKind = .error reason := by
  obtain ⟨decoded, _, _, held, identity, _⟩ :=
    CapabilityHandle.resolveCurrent_sound _ _ _ _ _ resolved
  have retired := terminateChild_identityRetired state word child returned running holds
    terminated holder _ _ held names
  obtain ⟨holdsPost, accountingPost, _⟩ := terminateChild_preserves state word holds accounting
  have treePost := terminateChild_spawnTree state word holds accounting tree
  have trace := runChildSteps_identityStep _ steps holdsPost accountingPost treePost admissible
  exact stale_word_of_retired _ _ (trace.retired retired) anyHolder handleWord anyKind
    resolution.handle decoded identity.symm

end LeanOS.FailStop
