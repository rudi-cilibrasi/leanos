import LeanOS.FailStop.SpawnChildCleanup
import LeanOS.FailStop.MemoryOperations

/-!
# Fail-stop composite: children have no children, and cleanup is complete

Gate item 4 of ADR 0010 asks that terminating a child release everything it
was given.  Two gaps remained after #490 and #491: a child's own children
would be orphaned by its termination, and memory the child allocated stayed
allocated after it.

## No grandchildren

Spawn authority is a kernel-granted capability that spawn never passes to the
child (`spawn_registry`), and the public grant refuses a subject that is
itself a spawned child (`grantBudgetedAuthority`).  `SpawnTreeWellFormed`
records the consequence as an invariant of every step:

- every child-table entry's child is recorded as spawned by that parent;
- every holder of spawn authority is an issued subject;
- **a spawned child holds no spawn authority and has an empty child table**.

So a child cannot spawn (`child_spawn_rejected`), and terminating a child
leaves no orphan: it never had children (`terminateChild_no_orphans`).  The
tree of a parent is one level deep, and child termination is its whole
cascading cleanup.

## Complete cleanup

Child termination now also reclaims the child's memory
(`reclaimChildFrames`): every frame committed to the child that backs a dead
object is freed, unbound, and scrubbed before the child's frames return to the
parent.  `terminateChild_releases_everything` collects what the termination
gives back: the child is dead, holds no capability, is not runnable, owns no
address space; every frame committed to it is committed to the parent; every
frame that backed one of its own memory objects is free and scrubbed; and its
table entry and records are gone.
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

/-! ## The invariant -/

structure SpawnTreeWellFormed (state : CompositeState) : Prop where
  recorded : ∀ parent slot entry, state.spawn.children parent slot = some entry →
    state.spawn.parent entry.child = some parent
  authorityIssued : ∀ subject capability, state.spawn.authority subject = some capability →
    state.lifecycle.issuedSubjects subject = true
  leaf : ∀ child parent, state.spawn.parent child = some parent →
    state.spawn.authority child = none ∧ ∀ slot, state.spawn.children child slot = none

/-- The empty spawn registry satisfies the invariant. -/
theorem spawnTree_of_empty (state : CompositeState)
    (children : ∀ parent slot, state.spawn.children parent slot = none)
    (authority : ∀ subject, state.spawn.authority subject = none)
    (parents : ∀ child, state.spawn.parent child = none) :
    SpawnTreeWellFormed state := by
  refine ⟨fun parent slot entry found => ?_, fun subject capability found => ?_,
    fun child parent found => ?_⟩
  · rw [children] at found; cases found
  · rw [authority] at found; cases found
  · rw [parents] at found; cases found

/-- A step that keeps the spawn registry and only grows the subject history
keeps the invariant. -/
theorem spawnTree_of_kept {before after : CompositeState} (tree : SpawnTreeWellFormed before)
    (spawnSame : after.spawn = before.spawn)
    (grows : ∀ subject, before.lifecycle.issuedSubjects subject = true →
      after.lifecycle.issuedSubjects subject = true) :
    SpawnTreeWellFormed after := by
  refine ⟨fun parent slot entry found => ?_, fun subject capability found => ?_,
    fun child parent found => ?_⟩
  · rw [spawnSame] at found ⊢; exact tree.recorded parent slot entry found
  · rw [spawnSame] at found; exact grows subject (tree.authorityIssued subject capability found)
  · rw [spawnSame] at found ⊢; exact tree.leaf child parent found

/-- **A charged child is a leaf.**  Every child in any child table holds no
spawn authority and has an empty child table of its own. -/
theorem charged_child_childless {state : CompositeState} (tree : SpawnTreeWellFormed state)
    {parent slot : Nat} {entry : ChildEntry}
    (found : state.spawn.children parent slot = some entry) :
    state.spawn.authority entry.child = none ∧ ∀ slot, state.spawn.children entry.child slot = none :=
  tree.leaf entry.child parent (tree.recorded parent slot entry found)

/-- A subject with a nonempty child table or with spawn authority was never
spawned. -/
theorem not_recorded_of_authority {state : CompositeState} (tree : SpawnTreeWellFormed state)
    {subject : Nat} {capability : SpawnCapability}
    (held : state.spawn.authority subject = some capability) :
    state.spawn.parent subject = none := by
  cases recordedParent : state.spawn.parent subject with
  | none => rfl
  | some parent =>
      have := (tree.leaf subject parent recordedParent).1
      rw [held] at this; cases this

theorem not_recorded_of_children {state : CompositeState} (tree : SpawnTreeWellFormed state)
    {subject slot : Nat} {entry : ChildEntry}
    (found : state.spawn.children subject slot = some entry) :
    state.spawn.parent subject = none := by
  cases recordedParent : state.spawn.parent subject with
  | none => rfl
  | some parent =>
      have := (tree.leaf subject parent recordedParent).2 slot
      rw [found] at this; cases this

/-- **A child cannot spawn.**  When the current subject is a spawned child,
every charged spawn is rejected for missing spawn authority with the
pre-state. -/
theorem child_spawn_rejected (state : CompositeState) (request : SpawnRequest)
    (tree : SpawnTreeWellFormed state) {parent : Nat}
    (spawnedChild : state.spawn.parent (spawnParent state) = some parent) :
    (spawnCharged state request).result = .spawnRejected (.spawn .missingSpawnRight) ∧
      (spawnCharged state request).state = state := by
  have none := (tree.leaf _ parent spawnedChild).1
  have stage : spawnAuthorize state request.spawnWord = some .missingSpawnRight := by
    unfold spawnAuthorize; split <;> simp_all
  simp [spawnCharged, stage]

/-! ## Every step keeps it -/

theorem CompositeStep.spawnTree (state : CompositeState) (step : CompositeStep)
    (holds : ResourceRuntimeWellFormed state) (admissible : step.Admissible state)
    (tree : SpawnTreeWellFormed state) :
    SpawnTreeWellFormed (step.apply state) :=
  spawnTree_of_kept tree (step.apply_spawn state) (step.admissible_grows state holds admissible).2.2.2

theorem memoryGate_spawnTree (state : CompositeState) (operation : MemoryOperation)
    (tree : SpawnTreeWellFormed state) :
    SpawnTreeWellFormed (memoryGate state operation).state := by
  have keeps := memoryGate_keeps state operation
  exact spawnTree_of_kept tree keeps.spawn (fun subject issued => by
    rw [keeps.issuedSubjects]; exact issued)

/-- The #489 spawn records exactly the new child's parent. -/
theorem spawn_parent_record (state : CompositeState) (request : SpawnRequest)
    (child addressSpace : Nat)
    (spawned : (spawn state request).result = .spawned child addressSpace) (candidate : Nat) :
    (spawn state request).state.spawn.parent candidate =
      if candidate = child then some (spawnParent state) else state.spawn.parent candidate := by
  obtain ⟨_, issued, _, _, _, _, _, _, _, stateEq⟩ :=
    spawn_spawned_stages state request child addressSpace spawned
  obtain ⟨_, _, created, eq⟩ := issueSubject_issued state child issued
  rw [stateEq]
  simp [recordSpawn, installCopiedCapabilities, spawnSpaced, installCreatedAddressSpace, eq,
    applyOperation, created, installCreatedSubject, spawnParent]

theorem spawnCharged_spawnTree (state : CompositeState) (request : SpawnRequest)
    (holds : ResourceRuntimeWellFormed state) (accounting : ChildAccountingWellFormed state)
    (tree : SpawnTreeWellFormed state) :
    SpawnTreeWellFormed (spawnCharged state request).state := by
  rcases spawnCharged_shape state request with ⟨same, _⟩ | ⟨child, addressSpace, control, result⟩
  · rw [same]; exact tree
  obtain ⟨slot, authorized, _, _, _, spawned, _, stateEq⟩ :=
    spawnCharged_spawned state request child addressSpace control result
  obtain ⟨childrenEq, nextEq, authorityEq⟩ := spawn_childTable state request child addressSpace
    spawned
  have unissued := (spawn_fresh_identity state request child addressSpace holds spawned).2.1
  obtain ⟨parentLive, capability, parentAuthority⟩ := spawnAuthorize_live authorized
  have parentIssued := live_issued holds.1.left parentLive
  have parentNe : spawnParent state ≠ child := by
    intro same; rw [same, unissued] at parentIssued; cases parentIssued
  have parentNotRecorded := not_recorded_of_authority tree parentAuthority
  have issuedEq := (spawn_keeps state request child addressSpace
    spawned).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [stateEq]
  refine ⟨fun parent candidateSlot entry found => ?_, fun subject cap found => ?_,
    fun candidate parent found => ?_⟩
  · simp only [installChild, childrenEq] at found ⊢
    rw [spawn_parent_record state request child addressSpace spawned]
    split at found
    · next same =>
      obtain ⟨rfl, rfl⟩ := same
      cases found
      simp
    · have old := tree.recorded parent candidateSlot entry found
      have issuedChild := (accounting.entries parent candidateSlot entry found).2.2.2.1
      have ne : entry.child ≠ child := by
        intro same; rw [same, unissued] at issuedChild; cases issuedChild
      simp [ne, old]
  · simp only [installChild, authorityEq] at found
    show (spawn state request).state.lifecycle.issuedSubjects subject = true
    rw [issuedEq]
    have := tree.authorityIssued subject cap found
    simp only [SubjectLifecycle.setBool]; split <;> simp_all
  · simp only [installChild] at found ⊢
    rw [spawn_parent_record state request child addressSpace spawned] at found
    rw [authorityEq, childrenEq]
    split at found
    · next same =>
      subst same
      refine ⟨?_, fun candidateSlot => ?_⟩
      · cases held : state.spawn.authority candidate with
        | none => rfl
        | some cap =>
            have := tree.authorityIssued candidate cap held
            rw [unissued] at this; cases this
      · simp only [Ne.symm parentNe, false_and, ↓reduceIte]
        exact accounting.fresh candidate candidateSlot unissued
    · obtain ⟨noAuthority, empty⟩ := tree.leaf candidate parent found
      refine ⟨noAuthority, fun candidateSlot => ?_⟩
      have ne : candidate ≠ spawnParent state := by
        intro same; rw [same, parentNotRecorded] at found; cases found
      simp only [ne, false_and, ↓reduceIte]
      exact empty candidateSlot

theorem grantFrames_spawnTree (state : CompositeState) (word : UInt64) (frames : Nat)
    (tree : SpawnTreeWellFormed state) :
    SpawnTreeWellFormed (grantFrames state word frames).state := by
  rcases grantFrames_shape state word frames with ⟨same, _⟩ | ⟨child, moved, result⟩
  · rw [same]; exact tree
  obtain ⟨slot, entry, resolved, _, _, _, _, stateEq⟩ :=
    grantFrames_granted state word frames child moved result
  obtain ⟨_, _, found⟩ := resolveControl_ok resolved
  have parentNotRecorded := not_recorded_of_children tree found
  rw [stateEq]
  refine ⟨fun parent candidateSlot entry' found' => ?_, fun subject cap held => ?_,
    fun candidate parent recordedParent => ?_⟩
  · simp only [setChildEntry] at found' ⊢
    split at found'
    · next same =>
      obtain ⟨rfl, rfl⟩ := same
      cases found'
      exact tree.recorded _ _ entry found
    · exact tree.recorded parent candidateSlot entry' found'
  · exact tree.authorityIssued subject cap held
  · simp only [setChildEntry] at recordedParent ⊢
    obtain ⟨noAuthority, empty⟩ := tree.leaf candidate parent recordedParent
    refine ⟨noAuthority, fun candidateSlot => ?_⟩
    have ne : candidate ≠ spawnParent state := by
      intro same; rw [same, parentNotRecorded] at recordedParent; cases recordedParent
    simp only [ne, false_and, ↓reduceIte]
    exact empty candidateSlot

theorem terminateChild_spawnTree (state : CompositeState) (word : UInt64)
    (holds : ResourceRuntimeWellFormed state) (accounting : ChildAccountingWellFormed state)
    (tree : SpawnTreeWellFormed state) :
    SpawnTreeWellFormed (terminateChild state word).state := by
  rcases terminateChild_shape state word with ⟨same, _⟩ | ⟨child, returned, result⟩
  · rw [same]; exact tree
  obtain ⟨slot, entry, resolved, childEq, _, stateEq⟩ :=
    terminateChild_terminated state word child returned result
  obtain ⟨_, _, found⟩ := resolveControl_ok resolved
  obtain ⟨_, agreesT, spawnT⟩ := terminatedChild_facts state child holds
  have issuedT := agreesT.2.2.2.1
  rw [stateEq]
  refine ⟨fun parent candidateSlot entry' found' => ?_, fun subject cap held => ?_,
    fun candidate parent recordedParent => ?_⟩
  · simp only [releaseChild, reclaimChildFrames, spawnT] at found' ⊢
    split at found'
    · cases found'
    · next notHere =>
      have old := tree.recorded parent candidateSlot entry' found'
      have ne : entry'.child ≠ child := by
        intro same
        exact notHere (accounting.unique _ _ _ _ _ _ found' found (by rw [same, childEq]))
      simp [ne, old]
  · simp only [releaseChild, reclaimChildFrames, spawnT] at held
    show (terminatedChild state child).lifecycle.issuedSubjects subject = true
    rw [issuedT]; exact tree.authorityIssued subject cap held
  · simp only [releaseChild, reclaimChildFrames, spawnT] at recordedParent ⊢
    split at recordedParent
    · cases recordedParent
    · obtain ⟨noAuthority, empty⟩ := tree.leaf candidate parent recordedParent
      refine ⟨noAuthority, fun candidateSlot => ?_⟩
      split
      · rfl
      · exact empty candidateSlot

theorem childGate_spawnTree (state : CompositeState) (operation : ChildOperation)
    (holds : ResourceRuntimeWellFormed state) (accounting : ChildAccountingWellFormed state)
    (tree : SpawnTreeWellFormed state) :
    SpawnTreeWellFormed (childGate state operation).state := by
  cases hmode : state.execution.mode <;> simp only [childGate, hmode]
  case running =>
    cases operation with
    | spawn request => exact spawnCharged_spawnTree state request holds accounting tree
    | grantFrames control frames => exact grantFrames_spawnTree state control frames tree
    | terminateChild control => exact terminateChild_spawnTree state control holds accounting tree
    | grantAuthority subject budget =>
        simp only [ChildOperation.apply]
        unfold grantBudgetedAuthority
        split
        · next admitted =>
          obtain ⟨live, _, _, notRecorded⟩ := admitted
          refine ⟨fun parent slot entry found => tree.recorded parent slot entry found,
            fun candidate cap held => ?_, fun candidate parent recordedParent => ?_⟩
          · simp only at held
            split at held
            · next same => subst same; exact live_issued holds.1.left live
            · exact tree.authorityIssued candidate cap held
          · obtain ⟨noAuthority, empty⟩ := tree.leaf candidate parent recordedParent
            refine ⟨?_, empty⟩
            simp only
            have ne : candidate ≠ subject := by
              intro same; rw [same, notRecorded] at recordedParent; cases recordedParent
            simp [ne, noAuthority]
        · exact tree
    | revokeAuthority subject =>
        simp only [ChildOperation.apply]
        refine ⟨fun parent slot entry found => tree.recorded parent slot entry found,
          fun candidate cap held => ?_, fun candidate parent recordedParent => ?_⟩
        · simp only [revokeSpawnAuthority] at held
          split at held
          · cases held
          · exact tree.authorityIssued candidate cap held
        · obtain ⟨noAuthority, empty⟩ := tree.leaf candidate parent recordedParent
          refine ⟨?_, empty⟩
          simp only [revokeSpawnAuthority]
          split
          · rfl
          · exact noAuthority
  all_goals exact tree

/-! ## No orphans -/

/-- **Terminating a child orphans nothing.**  The terminated child had no
children, and afterwards no entry of any child table names a subject
recorded as the terminated child's child. -/
theorem terminateChild_no_orphans (state : CompositeState) (word : UInt64) (child returned : Nat)
    (holds : ResourceRuntimeWellFormed state) (accounting : ChildAccountingWellFormed state)
    (tree : SpawnTreeWellFormed state)
    (terminated : (terminateChild state word).result = .terminated child returned) :
    (∀ slot, state.spawn.children child slot = none) ∧
      (∀ slot, (terminateChild state word).state.spawn.children child slot = none) ∧
      ∀ parent slot entry, (terminateChild state word).state.spawn.children parent slot =
        some entry → (terminateChild state word).state.spawn.parent entry.child ≠ some child := by
  obtain ⟨slot, entry, resolved, childEq, _, stateEq⟩ :=
    terminateChild_terminated state word child returned terminated
  obtain ⟨_, _, found⟩ := resolveControl_ok resolved
  have childless := (charged_child_childless tree found).2
  rw [childEq] at childless
  have treePost := terminateChild_spawnTree state word holds accounting tree
  refine ⟨childless, fun candidateSlot => ?_, fun parent candidateSlot entry' found' same => ?_⟩
  · have spawnT := (terminatedChild_facts state child holds).2.2
    rw [stateEq]
    simp only [releaseChild, reclaimChildFrames, spawnT]
    split
    · rfl
    · exact childless candidateSlot
  · have recordedEntry := treePost.recorded parent candidateSlot entry' found'
    rw [same] at recordedEntry
    cases recordedEntry
    have spawnT := (terminatedChild_facts state child holds).2.2
    rw [stateEq] at found'
    simp only [releaseChild, reclaimChildFrames, spawnT] at found'
    split at found'
    · cases found'
    · rw [childless candidateSlot] at found'; cases found'

/-! ## Complete cleanup -/

/-- Composite termination of a live subject retires every memory object the
lifecycle records it as owning. -/
theorem terminatedChild_retires_memory (state : CompositeState) (child object frame : Nat)
    (running : state.execution.mode = .running) (holds : ResourceRuntimeWellFormed state)
    (owned : state.lifecycle.ownedMemory object = some (child, frame)) :
    (terminatedChild state child).capabilities.objects object = false := by
  have runtime := holds.1.left
  have coherent := runtime.1
  have lifecycleWf := runtime.2.2.1
  have capsEq : state.capabilities = state.lifecycle.capabilities := coherent.2.2.2.1
  have resumableLifecycle : state.resumable.scheduler.lifecycle = state.lifecycle := by
    rw [coherent.2.2.2.2.2.2.2.1, coherent.2.1]
  have live := (lifecycleWf.2.1 object child frame owned).1
  have issued := lifecycleWf.1 child live
  have accepted : (SubjectLifecycle.terminate state.lifecycle child).result = .accepted := by
    simp [SubjectLifecycle.terminate, issued, live]
  simp only [terminatedChild, authoritativeGate_ordinary_state, gate, running, applyOperation,
    accepted]
  simp [installTerminatedSubject, installTerminatedResumable,
    ResumablePreemption.cleanupSubject, ResumablePreemption.retireOwnedAddressSpaces,
    SubjectLifecycle.terminateState, SubjectLifecycle.terminatedCapabilities,
    resumableLifecycle, owned]

/-- **Terminating a child releases everything it was given** (gate item 4,
completing `terminateChild_releases`).  After an accepted `terminateChild`:

- the child is dead, holds no capability, is not runnable, and owns no
  address space;
- every frame committed to the child is committed to the parent;
- every frame that backed one of the child's own memory objects is free,
  holds only initial bytes, and no longer binds that object;
- the child had no children, and its table entry and spawn records are
  removed. -/
theorem terminateChild_releases_everything (state : CompositeState) (word : UInt64)
    (child returned : Nat) (running : state.execution.mode = .running)
    (holds : ResourceRuntimeWellFormed state) (accounting : ChildAccountingWellFormed state)
    (tree : SpawnTreeWellFormed state)
    (terminated : (terminateChild state word).result = .terminated child returned) :
    (terminateChild state word).state.capabilities.subjects child = false ∧
      (∀ slot, (terminateChild state word).state.capabilities.slots child slot = none) ∧
      (terminateChild state word).state.lifecycle.runnable child = false ∧
      (∀ addressSpace, state.lifecycle.addressOwner addressSpace = some child →
        (terminateChild state word).state.lifecycle.addressOwner addressSpace = none) ∧
      (∀ frame, state.frameBudgets.commitment frame = some child →
        (terminateChild state word).state.frameBudgets.commitment frame =
          some (spawnParent state)) ∧
      (∀ object frame, state.lifecycle.ownedMemory object = some (child, frame) →
        state.frameBudgets.commitment frame = some child →
        state.virtualMemory.memory.allocator.status frame = .owned object →
        (terminateChild state word).state.virtualMemory.memory.allocator.status frame = .free ∧
          (∀ offset, offset < FrameScrub.frameBytes →
            (terminateChild state word).state.scrub.bytes frame offset = FrameScrub.initialByte) ∧
          (terminateChild state word).state.virtualMemory.memory.binding object ≠ some frame) ∧
      (∀ slot, state.spawn.children child slot = none) ∧
      (terminateChild state word).state.spawn.parent child = none ∧
      (terminateChild state word).state.spawn.addressSpace child = none := by
  obtain ⟨dead, slots, runnable, spaces, _, _, _, parentRecord, spaceRecord, _⟩ :=
    terminateChild_releases state word child returned running holds accounting terminated
  obtain ⟨childless, _, _⟩ :=
    terminateChild_no_orphans state word child returned holds accounting tree terminated
  obtain ⟨slot, entry, _, _, _, stateEq⟩ :=
    terminateChild_terminated state word child returned terminated
  obtain ⟨_, agreesT, _⟩ := terminatedChild_facts state child holds
  obtain ⟨_, budgetsT, _, _, _, _, allocatorT, bindingT⟩ := agreesT
  refine ⟨dead, slots, runnable, spaces, fun frame committed => ?_,
    fun object frame owned committed status => ?_, childless, parentRecord, spaceRecord⟩
  · rw [stateEq]
    simp [releaseChild, returnFrames, budgetsT, committed]
  · have retired := terminatedChild_retires_memory state child object frame running holds owned
    have committedT : (terminatedChild state child).frameBudgets.commitment frame = some child := by
      rw [budgetsT]; exact committed
    have statusT : (terminatedChild state child).virtualMemory.memory.allocator.status frame =
        .owned object := by
      rw [allocatorT]; exact status
    obtain ⟨free, unbound, scrubbed, _, _⟩ :=
      reclaimChildFrames_reclaims (terminatedChild state child) child frame object committedT
        statusT retired
    rw [stateEq]
    refine ⟨free, scrubbed, ?_⟩
    show (reclaimChildFrames (terminatedChild state child) child).virtualMemory.memory.binding
      object ≠ some frame
    rcases unbound with none | notBound
    · rw [none]; simp
    · intro boundNow
      apply notBound
      have reclaim : reclaimable (terminatedChild state child) child frame = true := by
        simp [reclaimable, committedT, statusT, retired]
      simp only [reclaimChildFrames, reclaimedVirtualMemory] at boundNow
      cases boundOld : (terminatedChild state child).virtualMemory.memory.binding object with
      | none => rw [boundOld] at boundNow; cases boundNow
      | some oldFrame =>
          rw [boundOld] at boundNow
          simp only at boundNow
          split at boundNow
          · cases boundNow
          · next keep =>
            have same : oldFrame = frame := by simpa using boundNow
            subst same
            rw [reclaim] at keep

end LeanOS.FailStop
