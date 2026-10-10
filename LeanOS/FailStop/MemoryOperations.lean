import LeanOS.FailStop.MemoryRelease

/-!
# Fail-stop composite: budget-charged memory allocation and release

Gate item 1 of ADR 0010 (issues #473, #490).  `MemoryOperation`, run by
`memoryGate` under the running latch, is the composite's memory family.  It
is a separate family, like `LifecycleOperation` and `ChildOperation`: it
changes neither `Operation` nor `applyOperation`.

The acting subject is always the current subject of the execution latch
(`memoryActor`); no command word names who is charged, which frame is used,
or which object identity is issued.

- **`allocate slot`** (`allocateMemory`).  The registry checks of
  `FrameBudget.allocate` run first (`invalidSubject`, `outOfRange`,
  `capabilityIdentityExhausted`, `occupiedSlot`).  The object identity is the
  object issuer's next value (`objectIdentityExhausted`), and it must be
  unused under every kind (`objectUnavailable`).  The frame is the first free
  frame committed to the actor, `FrameBudget.firstAvailable` on the budget
  projection (`frameBudgetExhausted`), and the lifecycle must not attribute
  it to anyone (`frameUnavailable`).  On acceptance the frame is scrubbed,
  the object is published bound to it with a root capability in the actor's
  slot (`installAllocatedMemory`), the lifetime is marked unwritten, and the
  object issuer advances past the identity.
- **`release slot`** (`releaseMemory`).  The checks of
  `MemoryLifecycle.release` (`invalidSubject`, `staleSlot`, `kindMismatch`,
  `missingRevoke`, `retiredObject`, `allocatorMismatch`), and the lifecycle
  must record the actor as the object's owner (`notOwner`).  On acceptance
  the object is retired everywhere (`installReleasedMemory`: every capability,
  mapping, cached translation, and pending transfer naming it) and its frame
  is free and scrubbed.

Every rejection returns the pre-state (`MemoryOperation.apply_rejected_unchanged`).
Both operations keep the combined invariant (`memoryGate_preserves`), declare
footprints that pass the frame rule (`memoryGate_frames`) and the read-set
check (`memoryGate_reads`), and refine the standalone budget model on the
budget projection (`allocateMemory_refines`, `releaseMemory_refines`).
-/
namespace LeanOS.FailStop

open LeanOS
open LeanOS.CompositeFootprint (Projection Footprint)
set_option linter.unusedSimpArgs false

/-! ## The operations -/

/-- The subject on whose behalf memory is allocated or released: the current
subject of the execution latch. -/
def memoryActor (state : CompositeState) : Nat :=
  state.execution.core.context.currentSubject

inductive MemoryError where
  | invalidSubject
  | outOfRange
  | capabilityIdentityExhausted
  | occupiedSlot
  | objectIdentityExhausted
  | objectUnavailable
  | frameBudgetExhausted
  | frameUnavailable
  | staleSlot
  | kindMismatch
  | missingRevoke
  | retiredObject
  | allocatorMismatch
  | notOwner
  deriving DecidableEq, Repr

inductive MemoryResult where
  | allocated (object frame : Nat)
  | released (object frame : Nat)
  | rejected (reason : MemoryError)
  deriving DecidableEq, Repr

structure MemoryOutcome where
  state : CompositeState
  result : MemoryResult

/-- The identity is unused under every kind: never issued as memory or as an
address space, not live, and not recorded as an owned endpoint. -/
def objectAvailable (state : CompositeState) (object : Nat) : Bool :=
  !state.virtualMemory.memory.issued object && !state.virtualMemory.issuedAddressSpace object &&
    !state.capabilities.objects object && state.lifecycle.endpointOwner object == none

/-- The post-state of an accepted allocation: the published object, the
advanced object issuer, and the scrubbed, unwritten frame. -/
def allocatedState (state : CompositeState) (object owner slot frame : Nat) : CompositeState :=
  { installAllocatedMemory state object owner slot frame with
    issuers := { state.issuers with object := { next := object + 1 } }
    scrub :=
      { bytes := FrameScrub.scrubFrame state.scrub.bytes frame
        written := FrameScrub.setWritten state.scrub.written object false } }

/-- The decision of an allocation: which checks pass, and, on acceptance,
the issued object identity and the charged frame. -/
def allocateDecision (state : CompositeState) (slot : Nat) : MemoryResult :=
  if state.capabilities.subjects (memoryActor state) != true then .rejected .invalidSubject
  else if CapabilityHandle.slotReserved ≤ slot ∨
      !Capability.slotInRange state.capabilities (memoryActor state) slot then
    .rejected .outOfRange
  else if state.capabilities.nextIdentity = 0 ∨
      CapabilityHandle.generationReserved ≤ state.capabilities.nextIdentity then
    .rejected .capabilityIdentityExhausted
  else if (state.capabilities.slots (memoryActor state) slot).isSome then .rejected .occupiedSlot
  else match LifetimeIssuer.issue state.issuers.object with
    | .exhausted => .rejected .objectIdentityExhausted
    | .issued object _ =>
        if objectAvailable state object = false then .rejected .objectUnavailable
        else match FrameBudget.firstAvailable state.budgetState (memoryActor state) with
          | none => .rejected .frameBudgetExhausted
          | some frame =>
              if (state.lifecycle.frameOwner frame).isSome then .rejected .frameUnavailable
              else .allocated object frame

/-- **Budget-charged allocation.**  The decision, and on acceptance the
published state; every rejection returns the pre-state. -/
def allocateMemory (state : CompositeState) (slot : Nat) : MemoryOutcome :=
  match allocateDecision state slot with
  | .allocated object frame =>
      { state := allocatedState state object (memoryActor state) slot frame
        result := .allocated object frame }
  | .released object frame => { state, result := .released object frame }
  | .rejected reason => { state, result := .rejected reason }

/-- The post-state of an accepted release: the retired object and the
scrubbed, free frame. -/
def releasedState (state : CompositeState) (object frame : Nat) : CompositeState :=
  { installReleasedMemory state object frame with
    scrub := { state.scrub with bytes := FrameScrub.scrubFrame state.scrub.bytes frame } }

/-- The decision of a release: which checks pass, and, on acceptance, the
released object and its frame. -/
def releaseDecision (state : CompositeState) (slot : Nat) : MemoryResult :=
  match Capability.lookup state.capabilities (memoryActor state) slot with
  | .invalidSubject => .rejected .invalidSubject
  | .staleSlot => .rejected .staleSlot
  | .found capability =>
      if capability.kind != .memory then .rejected .kindMismatch
      else if !capability.rights.revoke then .rejected .missingRevoke
      else match state.virtualMemory.memory.binding capability.object with
        | none => .rejected .retiredObject
        | some frame =>
            if state.virtualMemory.memory.allocator.status frame ≠ .owned capability.object then
              .rejected .allocatorMismatch
            else if state.lifecycle.ownedMemory capability.object ≠
                some (memoryActor state, frame) then
              .rejected .notOwner
            else .released capability.object frame

/-- **Release with scrub.**  The decision, and on acceptance the published
state; every rejection returns the pre-state. -/
def releaseMemory (state : CompositeState) (slot : Nat) : MemoryOutcome :=
  match releaseDecision state slot with
  | .released object frame =>
      { state := releasedState state object frame, result := .released object frame }
  | .allocated object frame => { state, result := .allocated object frame }
  | .rejected reason => { state, result := .rejected reason }

/-- The composite memory family. -/
inductive MemoryOperation where
  | allocate (slot : Nat)
  | release (slot : Nat)
  deriving DecidableEq, Repr

def MemoryOperation.apply (state : CompositeState) : MemoryOperation → MemoryOutcome
  | .allocate slot => allocateMemory state slot
  | .release slot => releaseMemory state slot

inductive MemoryGateResult where
  | completed (result : MemoryResult)
  | rejectedBusy
  | rejectedHalted (record : HaltRecord)
  deriving DecidableEq, Repr

structure MemoryGateOutcome where
  state : CompositeState
  result : MemoryGateResult

/-- The memory family runs only under the running latch. -/
def memoryGate (state : CompositeState) (operation : MemoryOperation) : MemoryGateOutcome :=
  match state.execution.mode with
  | .running =>
      { state := (operation.apply state).state, result := .completed (operation.apply state).result }
  | .handling _ => { state, result := .rejectedBusy }
  | .halted record => { state, result := .rejectedHalted record }

/-! ## Typed rejections leave the state unchanged -/

def MemoryResult.rejectedResult : MemoryResult → Bool
  | .rejected _ => true
  | _ => false

theorem allocateDecision_not_released (state : CompositeState) (slot object frame : Nat) :
    allocateDecision state slot ≠ .released object frame := by
  unfold allocateDecision
  repeat' split
  all_goals simp

theorem releaseDecision_not_allocated (state : CompositeState) (slot object frame : Nat) :
    releaseDecision state slot ≠ .allocated object frame := by
  unfold releaseDecision
  repeat' split
  all_goals simp

@[simp] theorem allocateMemory_result (state : CompositeState) (slot : Nat) :
    (allocateMemory state slot).result = allocateDecision state slot := by
  unfold allocateMemory; split <;> simp_all

@[simp] theorem releaseMemory_result (state : CompositeState) (slot : Nat) :
    (releaseMemory state slot).result = releaseDecision state slot := by
  unfold releaseMemory; split <;> simp_all

theorem allocateMemory_shape (state : CompositeState) (slot : Nat) :
    ((allocateMemory state slot).state = state ∧
      ∃ reason, (allocateMemory state slot).result = .rejected reason) ∨
      ∃ object frame, (allocateMemory state slot).result = .allocated object frame := by
  cases decision : allocateDecision state slot with
  | allocated object frame => exact Or.inr ⟨object, frame, by simp [decision]⟩
  | released object frame => exact absurd decision (allocateDecision_not_released _ _ _ _)
  | rejected reason =>
      exact Or.inl ⟨by simp [allocateMemory, decision], reason, by simp [decision]⟩

theorem releaseMemory_shape (state : CompositeState) (slot : Nat) :
    ((releaseMemory state slot).state = state ∧
      ∃ reason, (releaseMemory state slot).result = .rejected reason) ∨
      ∃ object frame, (releaseMemory state slot).result = .released object frame := by
  cases decision : releaseDecision state slot with
  | released object frame => exact Or.inr ⟨object, frame, by simp [decision]⟩
  | allocated object frame => exact absurd decision (releaseDecision_not_allocated _ _ _ _)
  | rejected reason =>
      exact Or.inl ⟨by simp [releaseMemory, decision], reason, by simp [decision]⟩

/-- **Every rejection returns the pre-state.** -/
theorem MemoryOperation.apply_rejected_unchanged (state : CompositeState)
    (operation : MemoryOperation) (reason : MemoryError)
    (rejected : (operation.apply state).result = .rejected reason) :
    (operation.apply state).state = state := by
  cases operation with
  | allocate slot =>
      simp only [MemoryOperation.apply] at rejected ⊢
      rcases allocateMemory_shape state slot with ⟨same, _⟩ | ⟨_, _, allocated⟩
      · exact same
      · rw [allocated] at rejected; cases rejected
  | release slot =>
      simp only [MemoryOperation.apply] at rejected ⊢
      rcases releaseMemory_shape state slot with ⟨same, _⟩ | ⟨_, _, released⟩
      · exact same
      · rw [released] at rejected; cases rejected

/-- A busy or halted latch rejects every memory operation with the state
unchanged. -/
theorem memoryGate_unchanged_of_not_running (state : CompositeState) (operation : MemoryOperation)
    (notRunning : state.execution.mode ≠ .running) :
    (memoryGate state operation).state = state := by
  cases hmode : state.execution.mode <;> simp_all [memoryGate]

/-! ## Inversion of the accepted outcomes -/

theorem frameState_eq_free_of_beq {status : FrameAllocator.FrameState}
    (beq : (status == .free) = true) : status = .free := by
  cases status
  · contradiction
  · rfl
  · contradiction

/-- Counting under a stronger predicate: if `p` implies `q` on the list and
some element satisfies `q` but not `p`, `p` counts strictly fewer. -/
theorem countP_lt_of_mono {α : Type} (p q : α → Bool) (l : List α)
    (mono : ∀ x, x ∈ l → p x = true → q x = true) (a : α) (mem : a ∈ l)
    (np : p a = false) (hq : q a = true) : l.countP p < l.countP q := by
  induction l with
  | nil => cases mem
  | cons head tail ih =>
      have monoTail : ∀ x, x ∈ tail → p x = true → q x = true :=
        fun x m h => mono x (List.mem_cons_of_mem _ m) h
      have le : tail.countP p ≤ tail.countP q := List.countP_mono_left monoTail
      simp only [List.countP_cons]
      rcases List.mem_cons.1 mem with rfl | inTail
      · simp only [np, hq, Bool.false_eq_true, ↓reduceIte]; omega
      · have lt := ih monoTail inTail
        have hhead := mono head List.mem_cons_self
        cases hp : p head <;> cases hqh : q head <;> simp_all <;> omega

theorem firstAvailable_some {budget : FrameBudget.State} {subject frame : Nat}
    (found : FrameBudget.firstAvailable budget subject = some frame) :
    frame ∈ budget.memory.allocator.frames ∧ budget.commitment frame = some subject ∧
      budget.memory.allocator.status frame = .free := by
  unfold FrameBudget.firstAvailable at found
  have member := List.mem_of_find?_eq_some found
  have holds := List.find?_some found
  simp only [Bool.and_eq_true, decide_eq_true_eq] at holds
  exact ⟨member, holds.1, frameState_eq_free_of_beq holds.2⟩

/-- Everything an accepted allocation checked and did. -/
theorem allocateMemory_allocated (state : CompositeState) (slot object frame : Nat)
    (allocated : (allocateMemory state slot).result = .allocated object frame) :
    object = state.issuers.object.next ∧ LifetimeIssuer.Representable object ∧
      objectAvailable state object = true ∧
      FrameBudget.firstAvailable state.budgetState (memoryActor state) = some frame ∧
      state.lifecycle.frameOwner frame = none ∧
      MemoryAllocatable state object (memoryActor state) slot frame ∧
      (allocateMemory state slot).state =
        allocatedState state object (memoryActor state) slot frame := by
  rw [allocateMemory_result] at allocated
  have stateEq : (allocateMemory state slot).state =
      allocatedState state object (memoryActor state) slot frame := by
    simp [allocateMemory, allocated]
  rw [stateEq]
  unfold allocateDecision at allocated
  split at allocated
  · cases allocated
  next live =>
  split at allocated
  · cases allocated
  next range =>
  split at allocated
  · cases allocated
  next generation =>
  split at allocated
  · cases allocated
  next empty =>
  split at allocated
  · cases allocated
  next issued follower issuedEq =>
  split at allocated
  · cases allocated
  next available =>
  split at allocated
  · cases allocated
  next found foundEq =>
  split at allocated
  · cases allocated
  next unowned =>
  simp only [MemoryResult.allocated.injEq] at allocated
  obtain ⟨rfl, rfl⟩ := allocated
  obtain ⟨hidentity, _, _, _⟩ := LifetimeIssuer.issued_facts issuedEq
  obtain ⟨representable, _⟩ := LifetimeIssuer.issued_representable issuedEq
  obtain ⟨_, _, free⟩ := firstAvailable_some foundEq
  have available' : objectAvailable state issued = true := by simpa using available
  have unowned' : state.lifecycle.frameOwner found = none := by simpa using unowned
  simp only [objectAvailable, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at available'
  obtain ⟨⟨⟨_, _⟩, deadObject⟩, endpointFree⟩ := available'
  have live' : state.capabilities.subjects (memoryActor state) = true := by simpa using live
  have range' : slot < CapabilityHandle.slotReserved ∧
      Capability.slotInRange state.capabilities (memoryActor state) slot = true := by
    simpa [not_or, Nat.not_le] using range
  have generation' : state.capabilities.nextIdentity ≠ 0 ∧
      state.capabilities.nextIdentity < CapabilityHandle.generationReserved := by
    simpa [not_or, Nat.not_le] using generation
  have empty' : state.capabilities.slots (memoryActor state) slot = none := by
    simpa using empty
  exact ⟨hidentity, representable, by simpa using available, foundEq, unowned',
    ⟨live', range'.1, range'.2, generation', empty', deadObject, endpointFree, free, unowned'⟩,
    rfl⟩

/-- Everything an accepted release checked and did. -/
theorem releaseMemory_released (state : CompositeState) (slot object frame : Nat)
    (released : (releaseMemory state slot).result = .released object frame) :
    ∃ capability, Capability.lookup state.capabilities (memoryActor state) slot =
        .found capability ∧ capability.object = object ∧ capability.kind = .memory ∧
      capability.rights.revoke = true ∧
      state.virtualMemory.memory.binding object = some frame ∧
      state.virtualMemory.memory.allocator.status frame = .owned object ∧
      state.lifecycle.ownedMemory object = some (memoryActor state, frame) ∧
      (releaseMemory state slot).state = releasedState state object frame := by
  rw [releaseMemory_result] at released
  have stateEq : (releaseMemory state slot).state = releasedState state object frame := by
    simp [releaseMemory, released]
  rw [stateEq]
  unfold releaseDecision at released
  split at released
  · cases released
  · cases released
  next capability found =>
  split at released
  · cases released
  next kind =>
  split at released
  · cases released
  next revoke =>
  split at released
  · cases released
  next boundFrame bound =>
  split at released
  · cases released
  next owned =>
  split at released
  · cases released
  next owner =>
  simp only [MemoryResult.released.injEq] at released
  obtain ⟨rfl, rfl⟩ := released
  exact ⟨capability, found, rfl, by simpa using kind, by simpa using revoke, bound,
    by simpa using owned, by simpa using owner, rfl⟩

/-! ## Exhaustion is a typed rejection with the pre-state -/

/-- **Frame-budget exhaustion.**  An actor that passes the registry and
identity checks but has no free frame committed to it is rejected with
`frameBudgetExhausted` and the pre-state. -/
theorem allocateMemory_frame_budget_exhausted (state : CompositeState) (slot object : Nat)
    (follower : LifetimeIssuer.Issuer .object)
    (live : state.capabilities.subjects (memoryActor state) = true)
    (inRange : slot < CapabilityHandle.slotReserved ∧
      Capability.slotInRange state.capabilities (memoryActor state) slot = true)
    (generation : state.capabilities.nextIdentity ≠ 0 ∧
      state.capabilities.nextIdentity < CapabilityHandle.generationReserved)
    (empty : state.capabilities.slots (memoryActor state) slot = none)
    (issued : LifetimeIssuer.issue state.issuers.object = .issued object follower)
    (available : objectAvailable state object = true)
    (exhausted : FrameBudget.firstAvailable state.budgetState (memoryActor state) = none) :
    (allocateMemory state slot).result = .rejected .frameBudgetExhausted ∧
      (allocateMemory state slot).state = state := by
  have range : ¬(CapabilityHandle.slotReserved ≤ slot ∨
      !Capability.slotInRange state.capabilities (memoryActor state) slot) := by
    simp [inRange.2, Nat.not_le.2 inRange.1]
  have gen : ¬(state.capabilities.nextIdentity = 0 ∨
      CapabilityHandle.generationReserved ≤ state.capabilities.nextIdentity) := by
    simp [generation.1, Nat.not_le.2 generation.2]
  simp [allocateMemory, allocateDecision, live, inRange.2, Nat.not_le.2 inRange.1, gen, empty,
    issued, available, exhausted]

/-- No free committed frame exists when the actor's usage has reached its
limit. -/
theorem firstAvailable_none_of_full (state : CompositeState) (subject : Nat)
    (full : state.budgetUsage subject = state.budgetLimit subject) :
    FrameBudget.firstAvailable state.budgetState subject = none := by
  unfold FrameBudget.firstAvailable
  rw [List.find?_eq_none]
  intro frame member
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, not_and]
  intro committed free
  simp only [CompositeState.budgetUsage, CompositeState.budgetLimit, FrameBudget.usage,
    FrameBudget.limit] at full
  have all := List.countP_eq_length.1 full
  have inBudget : frame ∈ FrameBudget.budgetFrames state.budgetState subject := by
    simp only [FrameBudget.budgetFrames, List.mem_filter, decide_eq_true_eq]
    exact ⟨member, committed⟩
  have owned := all frame inBudget
  simp only [CompositeState.budgetState] at owned free
  rw [frameState_eq_free_of_beq free] at owned
  cases owned

/-- **A full budget never allocates.**  When the actor's usage equals its
limit, allocation is a typed rejection with the pre-state, whatever the
slot. -/
theorem allocateMemory_full_rejected (state : CompositeState) (slot : Nat)
    (full : state.budgetUsage (memoryActor state) = state.budgetLimit (memoryActor state)) :
    (∃ reason, (allocateMemory state slot).result = .rejected reason) ∧
      (allocateMemory state slot).state = state := by
  rcases allocateMemory_shape state slot with ⟨same, rejected⟩ | ⟨object, frame, allocated⟩
  · exact ⟨rejected, same⟩
  · obtain ⟨_, _, _, found, _⟩ := allocateMemory_allocated state slot object frame allocated
    rw [firstAvailable_none_of_full state _ full] at found
    cases found

/-- **Object-identity exhaustion** is a typed rejection with the pre-state. -/
theorem allocateMemory_object_identity_exhausted (state : CompositeState) (slot : Nat)
    (live : state.capabilities.subjects (memoryActor state) = true)
    (inRange : slot < CapabilityHandle.slotReserved ∧
      Capability.slotInRange state.capabilities (memoryActor state) slot = true)
    (generation : state.capabilities.nextIdentity ≠ 0 ∧
      state.capabilities.nextIdentity < CapabilityHandle.generationReserved)
    (empty : state.capabilities.slots (memoryActor state) slot = none)
    (exhausted : LifetimeIssuer.exhausted state.issuers.object = true) :
    (allocateMemory state slot).result = .rejected .objectIdentityExhausted ∧
      (allocateMemory state slot).state = state := by
  have range : ¬(CapabilityHandle.slotReserved ≤ slot ∨
      !Capability.slotInRange state.capabilities (memoryActor state) slot) := by
    simp [inRange.2, Nat.not_le.2 inRange.1]
  have gen : ¬(state.capabilities.nextIdentity = 0 ∨
      CapabilityHandle.generationReserved ≤ state.capabilities.nextIdentity) := by
    simp [generation.1, Nat.not_le.2 generation.2]
  have issue : LifetimeIssuer.issue state.issuers.object = .exhausted := by
    simp [LifetimeIssuer.issue, exhausted]
  simp [allocateMemory, allocateDecision, live, inRange.2, Nat.not_le.2 inRange.1, gen, empty,
    issue]

/-! ## Footprints, the frame rule, and read sets -/

/-- The declared footprint of each memory operation.  Allocation also reads
the frame commitment (to choose the charged frame) and writes the object
issuer and the frame contents; release writes the frame contents. -/
def MemoryOperation.footprint : MemoryOperation → Footprint
  | .allocate _ => .ofLists [.frameBudgets] (publicationProjections ++ [.issuers, .scrub])
  | .release _ => .ofLists [] (publicationProjections ++ [.scrub])

/-- No memory operation writes the frame commitment or the spawn records. -/
theorem MemoryOperation.footprint_untouched (operation : MemoryOperation) :
    operation.footprint.writes .frameBudgets = false ∧ operation.footprint.writes .spawn = false ∧
      operation.footprint.writes .blockingContexts = false ∧
      operation.footprint.writes .deferredCancels = false ∧
      operation.footprint.writes .invalidationPublication = false := by
  cases operation <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Frame rule.**  Every outcome of the memory gate changes nothing outside
the declared write set. -/
theorem memoryGate_frames (state : CompositeState) (operation : MemoryOperation) :
    CompositeState.Frames operation.footprint state (memoryGate state operation).state := by
  cases hmode : state.execution.mode <;> simp only [memoryGate, hmode]
  case running =>
    cases operation with
    | allocate slot =>
        simp only [MemoryOperation.apply]
        rcases allocateMemory_shape state slot with ⟨same, _⟩ | ⟨object, frame, allocated⟩
        · rw [same]; exact CompositeState.frames_of_eq _ rfl
        · rw [(allocateMemory_allocated state slot object frame allocated).2.2.2.2.2.2]
          simp only [MemoryOperation.footprint, allocatedState, installAllocatedMemory]
          composite_frame
    | release slot =>
        simp only [MemoryOperation.apply]
        rcases releaseMemory_shape state slot with ⟨same, _⟩ | ⟨object, frame, released⟩
        · rw [same]; exact CompositeState.frames_of_eq _ rfl
        · obtain ⟨_, _, _, _, _, _, _, _, stateEq⟩ :=
            releaseMemory_released state slot object frame released
          rw [stateEq]
          simp only [MemoryOperation.footprint, releasedState, installReleasedMemory]
          composite_frame
  all_goals exact CompositeState.frames_of_eq _ rfl

/-- **Read independence.**  Two states that agree on a memory operation's
declared reads give the same result and post-states that agree on its
declared writes. -/
theorem MemoryOperation.apply_reads (left right : CompositeState) (operation : MemoryOperation)
    (agree : CompositeState.AgreeOn operation.footprint.reads left right) :
    (operation.apply left).result = (operation.apply right).result ∧
      CompositeState.AgreeOn operation.footprint.writes
        (operation.apply left).state (operation.apply right).state := by
  have decision : (operation.apply left).result = (operation.apply right).result := by
    cases operation with
    | allocate slot =>
        simp only [MemoryOperation.apply, allocateMemory_result]
        cases left; cases right
        agree_subst agree
        rfl
    | release slot =>
        simp only [MemoryOperation.apply, releaseMemory_result]
        cases left; cases right
        agree_subst agree
        rfl
  refine ⟨decision, ?_⟩
  cases operation with
  | allocate slot =>
      simp only [MemoryOperation.apply] at decision ⊢
      rcases allocateMemory_shape left slot with ⟨same, reason, rejected⟩ |
        ⟨object, frame, allocated⟩
      · rcases allocateMemory_shape right slot with ⟨same', _⟩ | ⟨object', frame', allocated'⟩
        · rw [same, same']; exact agree.writes_of_reads
        · rw [decision, allocated'] at rejected; cases rejected
      · have allocated' := allocated
        rw [decision] at allocated'
        rw [(allocateMemory_allocated left slot object frame allocated).2.2.2.2.2.2,
          (allocateMemory_allocated right slot object frame allocated').2.2.2.2.2.2]
        cases left; cases right
        agree_subst agree
        intro projection written
        cases projection <;> first | exact absurd written Bool.false_ne_true | rfl
  | release slot =>
      simp only [MemoryOperation.apply] at decision ⊢
      rcases releaseMemory_shape left slot with ⟨same, reason, rejected⟩ |
        ⟨object, frame, released⟩
      · rcases releaseMemory_shape right slot with ⟨same', _⟩ | ⟨object', frame', released'⟩
        · rw [same, same']; exact agree.writes_of_reads
        · rw [decision, released'] at rejected; cases rejected
      · have released' := released
        rw [decision] at released'
        obtain ⟨_, _, _, _, _, _, _, _, leftEq⟩ :=
          releaseMemory_released left slot object frame released
        obtain ⟨_, _, _, _, _, _, _, _, rightEq⟩ :=
          releaseMemory_released right slot object frame released'
        rw [leftEq, rightEq]
        cases left; cases right
        agree_subst agree
        intro projection written
        cases projection <;> first | exact absurd written Bool.false_ne_true | rfl

/-- Read independence of the memory gate.  The gate also reads the latch
mode, part of the declared `execution` read. -/
theorem memoryGate_reads (left right : CompositeState) (operation : MemoryOperation)
    (agree : CompositeState.AgreeOn operation.footprint.reads left right) :
    (memoryGate left operation).result = (memoryGate right operation).result ∧
      CompositeState.AgreeOn operation.footprint.writes
        (memoryGate left operation).state (memoryGate right operation).state := by
  have sameExecution : left.execution = right.execution :=
    agree .execution (by cases operation <;> rfl)
  obtain ⟨result, written⟩ := MemoryOperation.apply_reads left right operation agree
  simp only [memoryGate, sameExecution]
  split
  · exact ⟨by rw [result], written⟩
  · exact ⟨by first | rfl | trivial, agree.writes_of_reads⟩
  · exact ⟨by first | rfl | trivial, agree.writes_of_reads⟩

/-! ## The combined invariant -/

/-- Changing only the issuers and the frame contents keeps the authoritative
runtime invariant: no authoritative conjunct reads them. -/
theorem AuthoritativeRuntimeWellFormed.withResources {state : CompositeState}
    (holds : AuthoritativeRuntimeWellFormed state) (issuers : LifecycleIssuers)
    (scrub : FrameContents) :
    AuthoritativeRuntimeWellFormed { state with issuers, scrub } :=
  ⟨holds.left, holds.right, holds.publication⟩

/-- **Allocation keeps the combined invariant.** -/
theorem allocateMemory_preserves (state : CompositeState) (slot : Nat)
    (holds : ResourceRuntimeWellFormed state) :
    ResourceRuntimeWellFormed (allocateMemory state slot).state := by
  rcases allocateMemory_shape state slot with ⟨same, _⟩ | ⟨object, frame, allocated⟩
  · rw [same]; exact holds
  obtain ⟨hobject, representable, _, found, _, allocatable, stateEq⟩ :=
    allocateMemory_allocated state slot object frame allocated
  obtain ⟨frameMember, _, frameFree⟩ := firstAvailable_some found
  simp only [CompositeState.budgetState] at frameMember frameFree
  rw [stateEq]
  refine ⟨(installAllocatedMemory_preserves_authoritativeRuntimeWellFormed state object
    (memoryActor state) slot frame holds.1 allocatable).withResources _ _, ?_⟩
  obtain ⟨issuersHold, agreementHold, budgetHold, scrubHold⟩ :=
    (resourceWellFormed_iff state).1 holds.2
  rw [resourceWellFormed_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [issuersInvariant, allocatedState] at issuersHold ⊢
    refine ⟨issuersHold.1, ?_⟩
    have := representable.2
    omega
  · simp only [issuerAgreementInvariant, allocatedState, installAllocatedMemory,
      CompositeState.lifecycleRuntime, BoundedLifecycle.issuedObject, allocatedMemory,
      allocatedLifecycle] at agreementHold ⊢
    refine ⟨agreementHold.1, ?_⟩
    intro candidate issuedNow
    simp only [MemoryLifecycle.setIssued, Bool.or_eq_true] at issuedNow
    by_cases same : candidate = object
    · subst same
      refine ⟨representable.1, ?_⟩
      show candidate < candidate + 1
      exact Nat.lt_succ_self _
    · simp only [same, ↓reduceIte] at issuedNow
      have := agreementHold.2 candidate (by simpa using issuedNow)
      refine ⟨this.1, ?_⟩
      show candidate < object + 1
      rw [hobject]; exact Nat.lt_succ_of_lt this.2
  · simp only [budgetAgreementInvariant, allocatedState, installAllocatedMemory,
      allocatedMemory, allocatedLifecycle] at budgetHold ⊢
    intro candidate subject committed
    obtain ⟨member, unreserved, issuedBefore⟩ := budgetHold candidate subject committed
    refine ⟨member, ?_, issuedBefore⟩
    simp only [FrameAllocator.IsReserved, FrameAllocator.setStatus]
    split
    · simp
    · exact unreserved
  · simp only [scrubInvariant, FrameScrub.ScrubInvariant, CompositeState.scrubState,
      allocatedState, installAllocatedMemory, allocatedMemory] at scrubHold ⊢
    intro candidate boundFrame bound unwritten
    simp only [MemoryLifecycle.setBinding] at bound
    by_cases same : candidate = object
    · subst same
      simp only [↓reduceIte, Option.some.injEq] at bound
      subst bound
      refine ⟨by simp [FrameAllocator.IsOwnedBy, FrameAllocator.setStatus], ?_⟩
      intro offset inFrame
      exact FrameScrub.scrubFrame_target _ _ _ inFrame
    · simp only [same, ↓reduceIte] at bound
      have unwrittenOld : state.scrub.written candidate = false := by
        simpa [FrameScrub.setWritten, same] using unwritten
      obtain ⟨owned, initial⟩ := scrubHold candidate boundFrame bound unwrittenOld
      have ne : boundFrame ≠ frame := by
        intro eq; rw [eq] at owned
        unfold FrameAllocator.IsOwnedBy at owned
        rw [frameFree] at owned; cases owned
      refine ⟨by simpa [FrameAllocator.IsOwnedBy, FrameAllocator.setStatus, ne] using owned, ?_⟩
      intro offset inFrame
      rw [FrameScrub.scrubFrame_other _ _ _ _ ne]
      exact initial offset inFrame

/-- **Release keeps the combined invariant.** -/
theorem releaseMemory_preserves (state : CompositeState) (slot : Nat)
    (holds : ResourceRuntimeWellFormed state) :
    ResourceRuntimeWellFormed (releaseMemory state slot).state := by
  rcases releaseMemory_shape state slot with ⟨same, _⟩ | ⟨object, frame, released⟩
  · rw [same]; exact holds
  obtain ⟨capability, found, objectEq, kind, _, bound, owned, _, stateEq⟩ :=
    releaseMemory_released state slot object frame released
  have runtime := holds.1.left
  have capabilityKind : state.capabilities.kinds object = some .memory := by
    have held : state.capabilities.slots (memoryActor state) slot = some capability := by
      unfold Capability.lookup at found
      split at found
      · split at found
        · split at found
          · next heldCap => cases found; exact heldCap
          · cases found
        · cases found
      · cases found
    have := (runtime.2.2.2.1.1 _ _ _ held).2.2.1
    rw [objectEq, kind] at this; exact this
  rw [stateEq]
  refine ⟨(installReleasedMemory_preserves_authoritativeRuntimeWellFormed state object frame
    holds.1 ⟨capabilityKind, owned⟩).withResources _ _, ?_⟩
  obtain ⟨issuersHold, agreementHold, budgetHold, scrubHold⟩ :=
    (resourceWellFormed_iff state).1 holds.2
  rw [resourceWellFormed_iff]
  refine ⟨issuersHold, ?_, ?_, ?_⟩
  · simpa [issuerAgreementInvariant, releasedState, installReleasedMemory,
      CompositeState.lifecycleRuntime, BoundedLifecycle.issuedObject, releasedMemory,
      releasedLifecycle] using agreementHold
  · simp only [budgetAgreementInvariant, releasedState, installReleasedMemory,
      releasedMemory, releasedLifecycle] at budgetHold ⊢
    intro candidate subject committed
    obtain ⟨member, unreserved, issuedBefore⟩ := budgetHold candidate subject committed
    refine ⟨member, ?_, issuedBefore⟩
    simp only [FrameAllocator.IsReserved, FrameAllocator.setStatus]
    split
    · simp
    · exact unreserved
  · simp only [scrubInvariant, FrameScrub.ScrubInvariant, CompositeState.scrubState,
      releasedState, installReleasedMemory, releasedMemory] at scrubHold ⊢
    intro candidate boundFrame bindingNow unwritten
    simp only [MemoryLifecycle.setBinding] at bindingNow
    by_cases same : candidate = object
    · simp [same] at bindingNow
    · simp only [same, ↓reduceIte] at bindingNow
      obtain ⟨ownedOld, initial⟩ := scrubHold candidate boundFrame bindingNow unwritten
      have ne : boundFrame ≠ frame := by
        intro eq; rw [eq] at ownedOld
        unfold FrameAllocator.IsOwnedBy at ownedOld
        rw [owned] at ownedOld
        cases ownedOld; exact same rfl
      refine ⟨by simpa [FrameAllocator.IsOwnedBy, FrameAllocator.setStatus, ne] using ownedOld,
        ?_⟩
      intro offset inFrame
      rw [FrameScrub.scrubFrame_other _ _ _ _ ne]
      exact initial offset inFrame

/-- **Every step of the memory family keeps the combined invariant**, on every
outcome, including busy and halted rejections. -/
theorem memoryGate_preserves (state : CompositeState) (operation : MemoryOperation)
    (holds : ResourceRuntimeWellFormed state) :
    ResourceRuntimeWellFormed (memoryGate state operation).state := by
  cases hmode : state.execution.mode <;> simp only [memoryGate, hmode]
  case running =>
    cases operation with
    | allocate slot => exact allocateMemory_preserves state slot holds
    | release slot => exact releaseMemory_preserves state slot holds
  all_goals exact holds

/-! ## Budget accounting -/

/-- The usage of a subject after one frame's allocator status changes,
relative to the old usage, when that frame is not committed to it. -/
theorem budgetUsage_setStatus_other (state after : CompositeState) (frame subject : Nat)
    (commitment : after.frameBudgets = state.frameBudgets)
    (frames : after.virtualMemory.memory.allocator.frames =
      state.virtualMemory.memory.allocator.frames)
    (status : ∀ candidate, candidate ≠ frame →
      after.virtualMemory.memory.allocator.status candidate =
        state.virtualMemory.memory.allocator.status candidate)
    (other : state.frameBudgets.commitment frame ≠ some subject) :
    after.budgetUsage subject = state.budgetUsage subject := by
  simp only [CompositeState.budgetUsage, FrameBudget.usage, FrameBudget.budgetFrames,
    CompositeState.budgetState, commitment, frames]
  apply List.countP_congr
  intro candidate member
  simp only [List.mem_filter, decide_eq_true_eq] at member
  have ne : candidate ≠ frame := by
    intro same; rw [same] at member; exact other member.2
  rw [status candidate ne]

/-- The limit of every subject depends only on the commitment and the frame
list. -/
theorem budgetLimit_of_frames (state after : CompositeState) (subject : Nat)
    (commitment : after.frameBudgets = state.frameBudgets)
    (frames : after.virtualMemory.memory.allocator.frames =
      state.virtualMemory.memory.allocator.frames) :
    after.budgetLimit subject = state.budgetLimit subject := by
  unfold CompositeState.budgetLimit FrameBudget.limit FrameBudget.budgetFrames
    CompositeState.budgetState
  rw [commitment, frames]

/-- **Allocation is charged to the actor.**  An accepted allocation uses a
frame committed to the actor; no subject's limit changes, no other subject's
usage changes, and the actor's usage grows. -/
theorem allocateMemory_charges (state : CompositeState) (slot object frame : Nat)
    (allocated : (allocateMemory state slot).result = .allocated object frame) :
    state.frameBudgets.commitment frame = some (memoryActor state) ∧
      state.virtualMemory.memory.allocator.status frame = .free ∧
      (allocateMemory state slot).state.virtualMemory.memory.allocator.status frame =
        .owned object ∧
      (∀ subject, (allocateMemory state slot).state.budgetLimit subject =
        state.budgetLimit subject) ∧
      (∀ subject, subject ≠ memoryActor state →
        (allocateMemory state slot).state.budgetUsage subject = state.budgetUsage subject) ∧
      state.budgetUsage (memoryActor state) <
        (allocateMemory state slot).state.budgetUsage (memoryActor state) := by
  obtain ⟨_, _, _, found, _, _, stateEq⟩ := allocateMemory_allocated state slot object frame
    allocated
  obtain ⟨member, committed, free⟩ := firstAvailable_some found
  simp only [CompositeState.budgetState] at member committed free
  rw [stateEq]
  have commitmentEq : (allocatedState state object (memoryActor state) slot frame).frameBudgets =
      state.frameBudgets := rfl
  have framesEq : (allocatedState state object (memoryActor state) slot
      frame).virtualMemory.memory.allocator.frames = state.virtualMemory.memory.allocator.frames :=
    rfl
  have statusEq : ∀ candidate, candidate ≠ frame →
      (allocatedState state object (memoryActor state) slot
        frame).virtualMemory.memory.allocator.status candidate =
        state.virtualMemory.memory.allocator.status candidate := by
    intro candidate ne
    simp [allocatedState, installAllocatedMemory, allocatedMemory, FrameAllocator.setStatus, ne]
  refine ⟨committed, free, by simp [allocatedState, installAllocatedMemory, allocatedMemory,
    FrameAllocator.setStatus], fun subject => budgetLimit_of_frames _ _ subject commitmentEq framesEq,
    fun subject ne => budgetUsage_setStatus_other _ _ frame subject commitmentEq framesEq statusEq
      (by rw [committed]; intro h; exact ne (Option.some.inj h).symm), ?_⟩
  simp only [CompositeState.budgetUsage, FrameBudget.usage, FrameBudget.budgetFrames,
    CompositeState.budgetState, commitmentEq, framesEq]
  refine countP_lt_of_mono _ _ _ ?mono frame ?mem ?np ?hq
  case mono =>
    intro candidate _ owned
    by_cases same : candidate = frame
    · subst same
      simp [allocatedState, installAllocatedMemory, allocatedMemory, FrameAllocator.setStatus]
    · rw [statusEq candidate same]; exact owned
  case mem => simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨member, decide_eq_true committed⟩
  case np => simp [free]
  case hq => simp [allocatedState, installAllocatedMemory, allocatedMemory, FrameAllocator.setStatus]

/-- **Release returns the frame to its budget.**  No subject's limit changes,
only the subject the frame is committed to (if any) loses usage, and the frame
is free and scrubbed. -/
theorem releaseMemory_returns (state : CompositeState) (slot object frame : Nat)
    (released : (releaseMemory state slot).result = .released object frame) :
    (releaseMemory state slot).state.virtualMemory.memory.allocator.status frame = .free ∧
      (∀ offset, offset < FrameScrub.frameBytes →
        (releaseMemory state slot).state.scrub.bytes frame offset = FrameScrub.initialByte) ∧
      (∀ subject, (releaseMemory state slot).state.budgetLimit subject =
        state.budgetLimit subject) ∧
      (∀ subject, state.frameBudgets.commitment frame ≠ some subject →
        (releaseMemory state slot).state.budgetUsage subject = state.budgetUsage subject) ∧
      ∀ subject, state.frameBudgets.commitment frame = some subject →
        frame ∈ state.virtualMemory.memory.allocator.frames →
        (releaseMemory state slot).state.budgetUsage subject < state.budgetUsage subject := by
  obtain ⟨_, _, _, _, _, _, owned, _, stateEq⟩ :=
    releaseMemory_released state slot object frame released
  rw [stateEq]
  have commitmentEq : (releasedState state object frame).frameBudgets = state.frameBudgets := rfl
  have framesEq : (releasedState state object frame).virtualMemory.memory.allocator.frames =
      state.virtualMemory.memory.allocator.frames := rfl
  have statusEq : ∀ candidate, candidate ≠ frame →
      (releasedState state object frame).virtualMemory.memory.allocator.status candidate =
        state.virtualMemory.memory.allocator.status candidate := by
    intro candidate ne
    simp [releasedState, installReleasedMemory, releasedMemory, FrameAllocator.setStatus, ne]
  have freeNow : (releasedState state object frame).virtualMemory.memory.allocator.status frame =
      .free := by
    simp [releasedState, installReleasedMemory, releasedMemory, FrameAllocator.setStatus]
  refine ⟨freeNow, ?_, fun subject => budgetLimit_of_frames _ _ subject commitmentEq framesEq,
    fun subject other => budgetUsage_setStatus_other _ _ frame subject commitmentEq framesEq
      statusEq other, ?_⟩
  · intro offset inFrame
    exact FrameScrub.scrubFrame_target _ _ _ inFrame
  · intro subject committed member
    simp only [CompositeState.budgetUsage, FrameBudget.usage, FrameBudget.budgetFrames,
      CompositeState.budgetState, commitmentEq, framesEq]
    refine countP_lt_of_mono _ _ _ ?mono frame ?mem ?np ?hq
    case mono =>
      intro candidate _ ownedNow
      by_cases same : candidate = frame
      · subst same; rw [freeNow] at ownedNow; cases ownedNow
      · rw [statusEq candidate same] at ownedNow; exact ownedNow
    case mem => simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨member, committed⟩
    case np => simp [freeNow]
    case hq => simp [owned]

/-! ## Refinement of the standalone budget model -/

/-- **Allocation refines `FrameBudget.allocate`.**  On the budget projection,
an accepted composite allocation is exactly the standalone model's
allocation of the same object for the same subject and slot: it accepts, and
its post-state is the composite post-state's budget projection. -/
theorem allocateMemory_refines (state : CompositeState) (slot object frame : Nat)
    (coherent : state.virtualMemory.memory.capabilities = state.capabilities)
    (allocated : (allocateMemory state slot).result = .allocated object frame) :
    FrameBudget.allocate state.budgetState (memoryActor state) object slot =
      { state := (allocateMemory state slot).state.budgetState, result := .accepted } := by
  obtain ⟨_, _, available, found, _, allocatable, stateEq⟩ :=
    allocateMemory_allocated state slot object frame allocated
  simp only [objectAvailable, Bool.and_eq_true, Bool.not_eq_true'] at available
  have unissued : state.virtualMemory.memory.issued object = false := available.1.1.1
  rw [stateEq]
  have range : ¬(CapabilityHandle.slotReserved ≤ slot ∨
      !Capability.slotInRange state.capabilities (memoryActor state) slot) := by
    simp [allocatable.slotInRange, Nat.not_le.2 allocatable.slotBounded]
  have gen : ¬(state.capabilities.nextIdentity = 0 ∨
      CapabilityHandle.generationReserved ≤ state.capabilities.nextIdentity) := by
    simp [allocatable.generation.1, Nat.not_le.2 allocatable.generation.2]
  simp only [FrameBudget.allocate, CompositeState.budgetState, coherent, allocatable.ownerLive,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, range, gen, allocatable.slotEmpty,
    Option.isSome_none, unissued]
  simp only [CompositeState.budgetState] at found
  rw [found]
  simp [allocatedState, installAllocatedMemory, allocatedMemory, allocatedCapabilities, coherent,
    allocatedLifecycle]

/-- **Release refines `FrameBudget.release`.**  On the budget projection, an
accepted composite release is exactly the standalone model's release of the
same slot for the same subject. -/
theorem releaseMemory_refines (state : CompositeState) (slot object frame : Nat)
    (coherent : state.virtualMemory.memory.capabilities = state.capabilities)
    (released : (releaseMemory state slot).result = .released object frame) :
    FrameBudget.release state.budgetState (memoryActor state) slot =
      { state := (releaseMemory state slot).state.budgetState, result := .accepted } := by
  obtain ⟨capability, found, objectEq, kind, revoke, bound, owned, _, stateEq⟩ :=
    releaseMemory_released state slot object frame released
  subst objectEq
  rw [stateEq]
  simp only [FrameBudget.release, MemoryLifecycle.release, CompositeState.budgetState, coherent,
    found, kind, revoke, bne_self_eq_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    bound, FrameAllocator.release, owned]
  simp [releasedState, installReleasedMemory, releasedMemory, coherent, releasedLifecycle]

/-! ## Fresh identities and scrubbed frames -/

/-- **A fresh, scrubbed lifetime.**  An accepted allocation issues the object
issuer's current value, which was never issued under any kind and is not
live, advances the issuer past it, and publishes the object bound to a frame
whose every byte is the initial byte, as an unwritten lifetime. -/
theorem allocateMemory_fresh (state : CompositeState) (slot object frame : Nat)
    (allocated : (allocateMemory state slot).result = .allocated object frame) :
    object = state.issuers.object.next ∧
      state.virtualMemory.memory.issued object = false ∧
      state.virtualMemory.issuedAddressSpace object = false ∧
      state.capabilities.objects object = false ∧
      (allocateMemory state slot).state.issuers.object.next = object + 1 ∧
      (allocateMemory state slot).state.issuers.subject = state.issuers.subject ∧
      (allocateMemory state slot).state.virtualMemory.memory.binding object = some frame ∧
      (allocateMemory state slot).state.scrub.written object = false ∧
      ∀ offset, offset < FrameScrub.frameBytes →
        (allocateMemory state slot).state.scrub.bytes frame offset = FrameScrub.initialByte := by
  obtain ⟨hobject, _, available, _, _, _, stateEq⟩ :=
    allocateMemory_allocated state slot object frame allocated
  simp only [objectAvailable, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at available
  obtain ⟨⟨⟨unissued, unissuedSpace⟩, dead⟩, _⟩ := available
  rw [stateEq]
  refine ⟨hobject, unissued, unissuedSpace, dead, rfl, rfl, ?_, ?_, ?_⟩
  · simp [allocatedState, installAllocatedMemory, allocatedMemory, MemoryLifecycle.setBinding]
  · simp [allocatedState, FrameScrub.setWritten]
  · intro offset inFrame
    exact FrameScrub.scrubFrame_target _ _ _ inFrame

/-- The root capability the actor receives names the new object with every
memory right, and no other slot changes. -/
theorem allocateMemory_capability (state : CompositeState) (slot object frame : Nat)
    (allocated : (allocateMemory state slot).result = .allocated object frame) :
    (allocateMemory state slot).state.capabilities.slots (memoryActor state) slot =
        some (memoryRoot state.capabilities object) ∧
      ∀ subject candidateSlot, (subject, candidateSlot) ≠ (memoryActor state, slot) →
        (allocateMemory state slot).state.capabilities.slots subject candidateSlot =
          state.capabilities.slots subject candidateSlot := by
  obtain ⟨_, _, _, _, _, _, stateEq⟩ := allocateMemory_allocated state slot object frame allocated
  rw [stateEq]
  refine ⟨by simp [allocatedState, allocatedCapabilities_slots], ?_⟩
  intro subject candidateSlot ne
  simp only [allocatedState, installAllocatedMemory_capabilities, allocatedCapabilities_slots]
  split
  · next same => exact absurd (by rw [same.1, same.2]) ne
  · rfl

/-- **Release retires the object everywhere and scrubs its frame.** -/
theorem releaseMemory_retires (state : CompositeState) (slot object frame : Nat)
    (released : (releaseMemory state slot).result = .released object frame) :
    (releaseMemory state slot).state.capabilities.objects object = false ∧
      (∀ subject candidateSlot capability,
        (releaseMemory state slot).state.capabilities.slots subject candidateSlot =
          some capability → capability.object ≠ object) ∧
      (∀ space page mapping,
        (releaseMemory state slot).state.virtualMemory.mappings space page = some mapping →
          mapping.object ≠ object) ∧
      (∀ endpoint transfer,
        (releaseMemory state slot).state.transfers.pending endpoint = some transfer →
          transfer.object ≠ object) ∧
      (releaseMemory state slot).state.virtualMemory.memory.binding object = none ∧
      (releaseMemory state slot).state.virtualMemory.memory.allocator.status frame = .free ∧
      (releaseMemory state slot).state.resumable.translations.entries = [] ∧
      (releaseMemory state slot).state.virtualMemory.memory.issued object =
        state.virtualMemory.memory.issued object ∧
      (releaseMemory state slot).state.issuers = state.issuers ∧
      ∀ offset, offset < FrameScrub.frameBytes →
        (releaseMemory state slot).state.scrub.bytes frame offset = FrameScrub.initialByte := by
  obtain ⟨_, _, _, _, _, _, _, _, stateEq⟩ :=
    releaseMemory_released state slot object frame released
  rw [stateEq]
  obtain ⟨dead, slots, mappings, pending, binding, free, entries⟩ :=
    installReleasedMemory_released state object frame
  exact ⟨dead, slots, mappings, pending, binding, free, entries, rfl, rfl,
    fun offset inFrame => FrameScrub.scrubFrame_target _ _ _ inFrame⟩

/-! ## What the memory family keeps -/

/-- The memory gate either stutters or runs the operation. -/
theorem memoryGate_state_cases (state : CompositeState) (operation : MemoryOperation) :
    (memoryGate state operation).state = state ∨
      (memoryGate state operation).state = (operation.apply state).state := by
  cases hmode : state.execution.mode <;> simp [memoryGate, hmode]

/-- What one memory operation keeps. -/
structure MemoryKeeps (before after : CompositeState) : Prop where
  subjectIssuer : after.issuers.subject = before.issuers.subject
  objectIssuer : before.issuers.object.next ≤ after.issuers.object.next
  issuedSubjects : after.lifecycle.issuedSubjects = before.lifecycle.issuedSubjects
  frameBudgets : after.frameBudgets = before.frameBudgets
  frames : after.virtualMemory.memory.allocator.frames =
    before.virtualMemory.memory.allocator.frames
  spawn : after.spawn = before.spawn
  issuedAddressSpace : after.virtualMemory.issuedAddressSpace =
    before.virtualMemory.issuedAddressSpace
  issued : ∀ object, before.virtualMemory.memory.issued object = true →
    after.virtualMemory.memory.issued object = true

theorem MemoryKeeps.refl (state : CompositeState) : MemoryKeeps state state :=
  ⟨rfl, Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, fun _ h => h⟩

theorem MemoryOperation.apply_keeps (state : CompositeState) (operation : MemoryOperation) :
    MemoryKeeps state (operation.apply state).state := by
  cases operation with
  | allocate slot =>
      simp only [MemoryOperation.apply]
      rcases allocateMemory_shape state slot with ⟨same, _⟩ | ⟨object, frame, allocated⟩
      · rw [same]; exact MemoryKeeps.refl state
      · obtain ⟨hobject, _, _, _, _, _, stateEq⟩ :=
          allocateMemory_allocated state slot object frame allocated
        rw [stateEq]
        refine ⟨rfl, by simp [allocatedState, hobject], rfl, rfl, rfl, rfl, rfl, ?_⟩
        intro candidate issued
        simp [allocatedState, installAllocatedMemory, allocatedMemory, MemoryLifecycle.setIssued,
          issued]
  | release slot =>
      simp only [MemoryOperation.apply]
      rcases releaseMemory_shape state slot with ⟨same, _⟩ | ⟨object, frame, released⟩
      · rw [same]; exact MemoryKeeps.refl state
      · obtain ⟨_, _, _, _, _, _, _, _, stateEq⟩ :=
          releaseMemory_released state slot object frame released
        rw [stateEq]
        exact ⟨rfl, Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, fun _ h => h⟩

/-- **What the memory family keeps.**  Every memory step keeps the subject
issuer, the subject history, the frame commitment, the allocator's frame
list, the spawn records, and the address-space history; the object issuer
only advances, and the memory history only grows. -/
theorem memoryGate_keeps (state : CompositeState) (operation : MemoryOperation) :
    MemoryKeeps state (memoryGate state operation).state := by
  rcases memoryGate_state_cases state operation with same | applied
  · rw [same]; exact MemoryKeeps.refl state
  · rw [applied]; exact MemoryOperation.apply_keeps state operation

end LeanOS.FailStop
