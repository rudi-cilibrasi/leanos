import LeanOS.FailStop.SpawnAuthority

/-!
# Fail-stop composite: charged spawn, child control handles, and frame slices

Issues #490 and #491 under ADR 0010.  `ChildOperation`, run by `childGate`
under the running latch, is the public spawn family.  It wraps the explicit
spawn of #489 (`FailStop.spawn`, which is unchanged) with per-parent
accounting, and adds two operations on a child named by a control handle.

## The child table

`CompositeState.spawn.children parent slot` is the parent's child table.
Each entry names the child, the generation of its control handle, and the
number of frames the parent has charged to it.  The table has `childSlots`
slots, exactly the encodable handle slots, and generations come from the
never-reused counter `spawn.nextChildGeneration`.

## Operations

- **`spawn request`** (`spawnCharged`).  After the #489 authorization stage,
  the parent's live children (`childCount`) must be fewer than the subject
  budget carried by its spawn capability (`SpawnCapability.subjectBudget`);
  otherwise the typed rejection is `subjectBudgetExhausted` with the
  pre-state.  The child is built by `FailStop.spawn`, and the first free
  child-table slot records it with charge zero and a fresh generation.  The
  parent receives a control word: a `CapabilityHandle` word whose slot is the
  child-table slot and whose generation is the entry's generation.
- **`grantFrames control frames`** (`grantFrames`).  The parent gives the
  child a slice of its own frame budget: the first `frames` free frames
  committed to the parent are committed to the child instead, and the
  parent's charge for the child grows by the number moved.  No frame is ever
  created or taken from anyone else.  Too few free frames is the typed
  rejection `frameBudgetExhausted` with the pre-state.
- **`terminateChild control`** (`terminateChild`).  The child is terminated
  by the composite termination transition, every frame committed to it is
  committed back to the parent, and the child-table entry and the child's
  spawn records are removed.
- **`grantAuthority subject budget`** and **`revokeAuthority subject`**.
  Trusted kernel operations on the spawn capability.  A grant names the
  subject budget and is rejected if the subject already has more live
  children than that.

Every rejection returns the pre-state.  The proofs that the accounting
invariant holds are in `SpawnAccountingInvariants`.
-/
namespace LeanOS.FailStop

open LeanOS
set_option linter.unusedSimpArgs false

/-! ## Sums over the child table -/

/-- The size of every parent's child table, a fixed kernel table.  Every
subject budget is at most this, and every slot is an encodable
`CapabilityHandle` slot (`childSlots_encodable`). -/
def childSlots : Nat := 64

theorem childSlots_encodable : childSlots < CapabilityHandle.slotReserved := by
  unfold childSlots CapabilityHandle.slotReserved CapabilityHandle.slotRadix
  decide

/-- The sum of a per-slot quantity over the child-table slots. -/
def slotSum (value : Nat → Nat) : Nat := ((List.range childSlots).map value).sum

theorem list_sum_update (values : List Nat) (nodup : values.Nodup) (f g : Nat → Nat) (slot : Nat)
    (same : ∀ other, other ≠ slot → g other = f other) :
    (values.map g).sum + (if slot ∈ values then f slot else 0) =
      (values.map f).sum + (if slot ∈ values then g slot else 0) := by
  induction values with
  | nil => simp
  | cons head rest ih =>
      rw [List.nodup_cons] at nodup
      obtain ⟨notMem, restNodup⟩ := nodup
      by_cases hhead : head = slot
      · subst hhead
        have restSame : (rest.map g).sum = (rest.map f).sum := by
          congr 1
          apply List.map_congr_left
          intro other member
          exact same other (fun eq => notMem (eq ▸ member))
        simp only [List.map_cons, List.sum_cons, List.mem_cons, true_or, ↓reduceIte, restSame]
        omega
      · have step := ih restNodup
        have headSame := same head hhead
        have memIff : slot ∈ head :: rest ↔ slot ∈ rest := by
          simp only [List.mem_cons]
          constructor
          · rintro (eq | member)
            · exact absurd eq.symm hhead
            · exact member
          · exact Or.inr
        simp only [List.map_cons, List.sum_cons, headSame]
        by_cases member : slot ∈ rest
        · have : slot ∈ head :: rest := memIff.2 member
          simp only [this, member, ↓reduceIte] at step ⊢
          omega
        · have : slot ∉ head :: rest := fun h => member (memIff.1 h)
          simp only [this, member, ↓reduceIte] at step ⊢
          omega

/-- **Point update.**  Changing a per-slot quantity at one in-range slot
changes the sum by exactly that slot's change. -/
theorem slotSum_update (f g : Nat → Nat) (slot : Nat) (inRange : slot < childSlots)
    (same : ∀ other, other ≠ slot → g other = f other) :
    slotSum g + f slot = slotSum f + g slot := by
  have := list_sum_update (List.range childSlots) List.nodup_range f g slot same
  have member : slot ∈ List.range childSlots := List.mem_range.2 inRange
  simp only [member, ↓reduceIte] at this
  exact this

theorem slotSum_congr (f g : Nat → Nat) (same : ∀ slot, g slot = f slot) :
    slotSum g = slotSum f := by
  unfold slotSum
  rw [List.map_congr_left (l := List.range childSlots) (fun slot _ => same slot)]

/-! ## The child table, read from the composite -/

/-- One if a child-table slot is occupied. -/
def entryCount (entry : Option ChildEntry) : Nat := if entry.isSome then 1 else 0

/-- The frames charged in a child-table slot. -/
def entryCharge (entry : Option ChildEntry) : Nat := (entry.map ChildEntry.charge).getD 0

/-- The children charged to a parent: its occupied child-table slots. -/
def childCount (state : CompositeState) (parent : Nat) : Nat :=
  slotSum fun slot => entryCount (state.spawn.children parent slot)

/-- The frames a parent has charged to its children. -/
def childCharge (state : CompositeState) (parent : Nat) : Nat :=
  slotSum fun slot => entryCharge (state.spawn.children parent slot)

/-- A subject's frame entitlement: the frames committed to it plus the frames
it has charged to its children. -/
def entitlement (state : CompositeState) (subject : Nat) : Nat :=
  state.budgetLimit subject + childCharge state subject

/-- The subject budget of the parent's spawn capability. -/
def subjectBudget (state : CompositeState) (parent : Nat) : Nat :=
  match state.spawn.authority parent with
  | some capability => capability.subjectBudget
  | none => 0

/-- The first free child-table slot of a parent. -/
def freeChildSlot (state : CompositeState) (parent : Nat) : Option Nat :=
  (List.range childSlots).find? fun slot => (state.spawn.children parent slot).isNone

theorem freeChildSlot_some {state : CompositeState} {parent slot : Nat}
    (found : freeChildSlot state parent = some slot) :
    slot < childSlots ∧ state.spawn.children parent slot = none := by
  have member := List.mem_of_find?_eq_some found
  have free := List.find?_some found
  rw [List.mem_range] at member
  refine ⟨member, ?_⟩
  simpa using free

/-! ## Control handles -/

/-- The control handle of a child-table entry. -/
def controlHandle (slot generation : Nat) : CapabilityHandle.Handle :=
  { slot, identity := generation }

/-- The control word returned to the parent by an accepted spawn. -/
def controlWord (slot generation : Nat) : UInt64 :=
  (CapabilityHandle.encode (controlHandle slot generation)).getD 0

/-- Control generations are positive and encodable. -/
def controlGenerationAvailable (state : CompositeState) : Bool :=
  0 < state.spawn.nextChildGeneration &&
    state.spawn.nextChildGeneration < CapabilityHandle.generationReserved

theorem decode_controlWord (slot generation : Nat) (inRange : slot < childSlots)
    (positive : 0 < generation) (bounded : generation < CapabilityHandle.generationReserved) :
    CapabilityHandle.decode (controlWord slot generation) = .ok (controlHandle slot generation) := by
  have encodable : CapabilityHandle.Encodable { slot, identity := generation } :=
    ⟨Nat.lt_trans inRange childSlots_encodable, positive, bounded⟩
  have encoded : CapabilityHandle.encode (controlHandle slot generation) =
      some (UInt64.ofNat (slot + generation * CapabilityHandle.slotRadix)) := by
    simp only [CapabilityHandle.encode, controlHandle, encodable, ↓reduceIte]
  apply CapabilityHandle.decode_encode
  rw [encoded]
  simp [controlWord, encoded]

/-- Why a control word does not name a child. -/
inductive ControlDenial where
  | invalidParent
  | malformed (reason : CapabilityHandle.DecodeError)
  | stale
  deriving DecidableEq, Repr

/-- Resolve a control word in the current subject's child table.  The word's
generation must equal the entry's generation; a cleared or reused slot never
matches an old word. -/
def resolveControl (state : CompositeState) (word : UInt64) :
    Except ControlDenial (Nat × ChildEntry) :=
  if state.capabilities.subjects (spawnParent state) = true then
    match CapabilityHandle.decode word with
    | .error reason => .error (.malformed reason)
    | .ok handle =>
        match state.spawn.children (spawnParent state) handle.slot with
        | some entry =>
            if entry.generation = handle.identity then .ok (handle.slot, entry) else .error .stale
        | none => .error .stale
  else .error .invalidParent

theorem resolveControl_ok {state : CompositeState} {word : UInt64} {slot : Nat}
    {entry : ChildEntry} (ok : resolveControl state word = .ok (slot, entry)) :
    state.capabilities.subjects (spawnParent state) = true ∧
      CapabilityHandle.decode word = .ok (controlHandle slot entry.generation) ∧
      state.spawn.children (spawnParent state) slot = some entry := by
  unfold resolveControl at ok
  by_cases live : state.capabilities.subjects (spawnParent state) = true
  · simp only [live, ↓reduceIte] at ok
    cases decoded : CapabilityHandle.decode word with
    | error reason => simp [decoded] at ok
    | ok handle =>
        simp only [decoded] at ok
        cases existing : state.spawn.children (spawnParent state) handle.slot with
        | none => simp [existing] at ok
        | some found =>
            simp only [existing] at ok
            by_cases generation : found.generation = handle.identity
            · simp only [generation, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at ok
              obtain ⟨rfl, rfl⟩ := ok
              refine ⟨live, ?_, existing⟩
              rw [generation]
              cases handle
              rfl
            · simp [generation] at ok
  · simp [live] at ok

/-- A control word whose slot holds no entry of its generation is rejected. -/
theorem resolveControl_stale (state : CompositeState) (word : UInt64)
    (handle : CapabilityHandle.Handle) (decoded : CapabilityHandle.decode word = .ok handle)
    (stale : ∀ entry, state.spawn.children (spawnParent state) handle.slot = some entry →
      entry.generation ≠ handle.identity) :
    ∃ reason, resolveControl state word = .error reason := by
  unfold resolveControl
  split
  · simp only [decoded]
    cases found : state.spawn.children (spawnParent state) handle.slot with
    | none => exact ⟨_, rfl⟩
    | some entry => simp [stale entry found]
  · exact ⟨_, rfl⟩

/-! ## The operations -/

inductive ChildSpawnError where
  | spawn (reason : SpawnError)
  | subjectBudgetExhausted
  | controlGenerationExhausted
  deriving DecidableEq, Repr

inductive FrameGrantError where
  | control (reason : ControlDenial)
  | childNotLive
  | frameBudgetExhausted
  deriving DecidableEq, Repr

inductive ChildResult where
  | spawned (child addressSpace : Nat) (control : UInt64)
  | spawnRejected (reason : ChildSpawnError)
  | framesGranted (child moved : Nat)
  | framesRejected (reason : FrameGrantError)
  | terminated (child returned : Nat)
  | terminateRejected (reason : ControlDenial)
  | authorityGranted (generation : Nat)
  | authorityRejected
  | authorityRevoked
  deriving DecidableEq, Repr

structure ChildOutcome where
  state : CompositeState
  result : ChildResult

/-- Record a new child in a parent's child table with charge zero and the next
control generation. -/
def installChild (state : CompositeState) (parent slot child : Nat) : CompositeState :=
  { state with spawn := { state.spawn with
      children := fun candidate candidateSlot =>
        if candidate = parent ∧ candidateSlot = slot then
          some { child, generation := state.spawn.nextChildGeneration, charge := 0 }
        else state.spawn.children candidate candidateSlot
      nextChildGeneration := state.spawn.nextChildGeneration + 1 } }

/-- **Charged spawn.**  The #489 spawn, admitted only within the parent's
subject budget, recorded in the parent's child table. -/
def spawnCharged (state : CompositeState) (request : SpawnRequest) : ChildOutcome :=
  match spawnAuthorize state request.spawnWord with
  | some reason => { state, result := .spawnRejected (.spawn reason) }
  | none =>
      if subjectBudget state (spawnParent state) ≤ childCount state (spawnParent state) then
        { state, result := .spawnRejected .subjectBudgetExhausted }
      else
        match freeChildSlot state (spawnParent state) with
        | none => { state, result := .spawnRejected .subjectBudgetExhausted }
        | some slot =>
            if controlGenerationAvailable state = false then
              { state, result := .spawnRejected .controlGenerationExhausted }
            else
              match (spawn state request).result with
              | .rejected reason => { state, result := .spawnRejected (.spawn reason) }
              | .spawned child addressSpace =>
                  { state := installChild (spawn state request).state (spawnParent state) slot
                      child
                    result := .spawned child addressSpace
                      (controlWord slot state.spawn.nextChildGeneration) }

/-- The parent's free frames, in allocator order: committed to it and not in
use. -/
def availableFrames (state : CompositeState) (parent : Nat) : List FrameAllocator.FrameId :=
  state.virtualMemory.memory.allocator.frames.filter fun frame =>
    decide (state.frameBudgets.commitment frame = some parent) &&
      decide (state.virtualMemory.memory.allocator.status frame = .free)

/-- Commit the listed frames to `target`. -/
def moveFrames (budgets : FrameBudgets) (moved : List FrameAllocator.FrameId) (target : Nat) :
    FrameBudgets :=
  { commitment := fun frame => if moved.contains frame then some target
      else budgets.commitment frame }

/-- The number of allocator frames in a list of moved frames. -/
def movedCount (state : CompositeState) (moved : List FrameAllocator.FrameId) : Nat :=
  state.virtualMemory.memory.allocator.frames.countP moved.contains

/-- Replace one child-table entry. -/
def setChildEntry (state : CompositeState) (parent slot : Nat) (entry : Option ChildEntry) :
    CompositeState :=
  { state with spawn := { state.spawn with
      children := fun candidate candidateSlot =>
        if candidate = parent ∧ candidateSlot = slot then entry
        else state.spawn.children candidate candidateSlot } }

/-- The frames a grant of `frames` frames moves: the first ones free in the
parent's budget. -/
def grantedFrames (state : CompositeState) (parent frames : Nat) : List FrameAllocator.FrameId :=
  (availableFrames state parent).take frames

/-- An entry with its charge raised. -/
def chargeEntry (entry : ChildEntry) (moved : Nat) : ChildEntry :=
  { entry with charge := entry.charge + moved }

/-- **A frame slice for a child.**  The first `frames` free frames committed
to the parent are committed to the child, and the parent's charge for the
child grows by the frames moved. -/
def grantFrames (state : CompositeState) (word : UInt64) (frames : Nat) : ChildOutcome :=
  match resolveControl state word with
  | .error reason => { state, result := .framesRejected (.control reason) }
  | .ok (slot, entry) =>
      if state.capabilities.subjects entry.child = false then
        { state, result := .framesRejected .childNotLive }
      else if (grantedFrames state (spawnParent state) frames).length < frames then
        { state, result := .framesRejected .frameBudgetExhausted }
      else
        { state :=
            { setChildEntry state (spawnParent state) slot (some (chargeEntry entry
                (movedCount state (grantedFrames state (spawnParent state) frames)))) with
              frameBudgets := moveFrames state.frameBudgets
                (grantedFrames state (spawnParent state) frames) entry.child }
          result := .framesGranted entry.child
            (movedCount state (grantedFrames state (spawnParent state) frames)) }

/-- Commit every frame committed to `child` to `parent`. -/
def returnFrames (budgets : FrameBudgets) (child parent : Nat) : FrameBudgets :=
  { commitment := fun frame => if budgets.commitment frame = some child then some parent
      else budgets.commitment frame }

/-- A frame committed to `child` whose allocator owner is a dead object: after
the child's termination, exactly the frames of the memory the child had
allocated. -/
def reclaimable (state : CompositeState) (child frame : Nat) : Bool :=
  state.frameBudgets.commitment frame == some child &&
    match state.virtualMemory.memory.allocator.status frame with
    | .owned object => !state.capabilities.objects object
    | _ => false

/-- The virtual memory with every reclaimable frame of `child` free, and every
binding to such a frame removed. -/
def reclaimedVirtualMemory (state : CompositeState) (child : Nat) : VirtualMapping.State :=
  { state.virtualMemory with
    memory := { state.virtualMemory.memory with
      allocator := { state.virtualMemory.memory.allocator with
        status := fun frame =>
          if reclaimable state child frame then .free
          else state.virtualMemory.memory.allocator.status frame }
      binding := fun object => match state.virtualMemory.memory.binding object with
        | some frame => if reclaimable state child frame then none else some frame
        | none => none } }

/-- **Reclaim a terminated child's memory** (gate item 4).  Every frame
committed to the child that backs a dead object is freed, unbound, and
scrubbed, in every copy of the virtual memory.  Composite termination retires
every memory object the child owned but leaves its frame allocated; this step
gives those frames back before they return to the parent's budget. -/
def reclaimChildFrames (state : CompositeState) (child : Nat) : CompositeState :=
  let virtualMemory := reclaimedVirtualMemory state child
  { state with
    execution := { state.execution with returnAuthorityArmed := false }
    virtualMemory
    ipc := { state.ipc with virtualMemory }
    resumable := { state.resumable with
      translations := { state.resumable.translations with virtual := virtualMemory } }
    scrub := { state.scrub with
      bytes := fun frame offset =>
        if reclaimable state child frame ∧ offset < FrameScrub.frameBytes then
          FrameScrub.initialByte
        else state.scrub.bytes frame offset } }

/-- Reclaim a terminated child's memory, return its frames to its parent, and
remove its records. -/
def releaseChild (state : CompositeState) (parent slot child : Nat) : CompositeState :=
  { reclaimChildFrames state child with
    frameBudgets := returnFrames state.frameBudgets child parent
    spawn := { state.spawn with
      children := fun candidate candidateSlot =>
        if candidate = parent ∧ candidateSlot = slot then none
        else state.spawn.children candidate candidateSlot
      parent := fun candidate => if candidate = child then none else state.spawn.parent candidate
      addressSpace := fun candidate =>
        if candidate = child then none else state.spawn.addressSpace candidate } }

/-- The composite termination of a child, through the authoritative gate. -/
def terminatedChild (state : CompositeState) (child : Nat) : CompositeState :=
  (authoritativeGate state (.ordinary (.terminateSubject child))).state

/-- **Child termination.**  The child is terminated, its frames return to the
parent, and its records are removed. -/
def terminateChild (state : CompositeState) (word : UInt64) : ChildOutcome :=
  match resolveControl state word with
  | .error reason => { state, result := .terminateRejected reason }
  | .ok (slot, entry) =>
      { state := releaseChild (terminatedChild state entry.child) (spawnParent state) slot
          entry.child
        result := .terminated entry.child (state.budgetLimit entry.child) }

/-- Grant a fresh-generation spawn capability carrying a subject budget.  The
budget must fit the child table and cover the subject's live children, and
the subject must not itself be a spawned child: spawn authority is held only
by subjects outside every child table, so a child never has children of its
own (`SpawnTreeWellFormed`). -/
def grantBudgetedAuthority (state : CompositeState) (subject budget : Nat) : ChildOutcome :=
  if state.capabilities.subjects subject = true ∧ budget ≤ childSlots ∧
      childCount state subject ≤ budget ∧ state.spawn.parent subject = none then
    { state := { state with spawn := { state.spawn with
        authority := fun candidate => if candidate = subject then
          some { generation := state.spawn.nextGeneration, subjectBudget := budget }
          else state.spawn.authority candidate
        nextGeneration := state.spawn.nextGeneration + 1 } }
      result := .authorityGranted state.spawn.nextGeneration }
  else { state, result := .authorityRejected }

/-- The public spawn family. -/
inductive ChildOperation where
  | spawn (request : SpawnRequest)
  | grantFrames (control : UInt64) (frames : Nat)
  | terminateChild (control : UInt64)
  | grantAuthority (subject subjectBudget : Nat)
  | revokeAuthority (subject : Nat)
  deriving DecidableEq, Repr

def ChildOperation.apply (state : CompositeState) : ChildOperation → ChildOutcome
  | .spawn request => spawnCharged state request
  | .grantFrames control frames => FailStop.grantFrames state control frames
  | .terminateChild control => FailStop.terminateChild state control
  | .grantAuthority subject budget => grantBudgetedAuthority state subject budget
  | .revokeAuthority subject =>
      { state := revokeSpawnAuthority state subject, result := .authorityRevoked }

inductive ChildGateResult where
  | completed (result : ChildResult)
  | rejectedBusy
  | rejectedHalted (record : HaltRecord)
  deriving DecidableEq, Repr

structure ChildGateOutcome where
  state : CompositeState
  result : ChildGateResult

/-- The public spawn family runs only under the running latch. -/
def childGate (state : CompositeState) (operation : ChildOperation) : ChildGateOutcome :=
  match state.execution.mode with
  | .running =>
      { state := (operation.apply state).state, result := .completed (operation.apply state).result }
  | .handling _ => { state, result := .rejectedBusy }
  | .halted record => { state, result := .rejectedHalted record }

/-! ## Typed rejections leave the state unchanged -/

/-- Whether a result is a rejection. -/
def ChildResult.rejected : ChildResult → Bool
  | .spawnRejected _ | .framesRejected _ | .terminateRejected _ | .authorityRejected => true
  | _ => false

/-- A charged spawn either rejects with the pre-state or spawns. -/
theorem spawnCharged_shape (state : CompositeState) (request : SpawnRequest) :
    ((spawnCharged state request).state = state ∧
      ∃ reason, (spawnCharged state request).result = .spawnRejected reason) ∨
      ∃ child addressSpace control,
        (spawnCharged state request).result = .spawned child addressSpace control := by
  unfold spawnCharged
  repeat' split
  all_goals simp

theorem grantFrames_shape (state : CompositeState) (word : UInt64) (frames : Nat) :
    ((grantFrames state word frames).state = state ∧
      ∃ reason, (grantFrames state word frames).result = .framesRejected reason) ∨
      ∃ child moved, (grantFrames state word frames).result = .framesGranted child moved := by
  unfold grantFrames
  repeat' split
  all_goals simp

theorem terminateChild_shape (state : CompositeState) (word : UInt64) :
    ((terminateChild state word).state = state ∧
      ∃ reason, (terminateChild state word).result = .terminateRejected reason) ∨
      ∃ child returned, (terminateChild state word).result = .terminated child returned := by
  unfold terminateChild
  repeat' split
  all_goals simp

theorem spawnCharged_rejected_unchanged (state : CompositeState) (request : SpawnRequest)
    (reason : ChildSpawnError)
    (rejected : (spawnCharged state request).result = .spawnRejected reason) :
    (spawnCharged state request).state = state := by
  rcases spawnCharged_shape state request with ⟨same, _⟩ | ⟨_, _, _, spawned⟩
  · exact same
  · rw [spawned] at rejected; cases rejected

theorem grantFrames_rejected_unchanged (state : CompositeState) (word : UInt64) (frames : Nat)
    (reason : FrameGrantError)
    (rejected : (grantFrames state word frames).result = .framesRejected reason) :
    (grantFrames state word frames).state = state := by
  rcases grantFrames_shape state word frames with ⟨same, _⟩ | ⟨_, _, granted⟩
  · exact same
  · rw [granted] at rejected; cases rejected

theorem terminateChild_rejected_unchanged (state : CompositeState) (word : UInt64)
    (reason : ControlDenial)
    (rejected : (terminateChild state word).result = .terminateRejected reason) :
    (terminateChild state word).state = state := by
  rcases terminateChild_shape state word with ⟨same, _⟩ | ⟨_, _, terminated⟩
  · exact same
  · rw [terminated] at rejected; cases rejected

theorem grantBudgetedAuthority_rejected_unchanged (state : CompositeState) (subject budget : Nat)
    (rejected : (grantBudgetedAuthority state subject budget).result = .authorityRejected) :
    (grantBudgetedAuthority state subject budget).state = state := by
  unfold grantBudgetedAuthority at rejected ⊢
  split
  · simp_all
  · rfl

theorem spawnCharged_result (state : CompositeState) (request : SpawnRequest) :
    (∃ child addressSpace control,
      (spawnCharged state request).result = .spawned child addressSpace control) ∨
      ∃ reason, (spawnCharged state request).result = .spawnRejected reason := by
  rcases spawnCharged_shape state request with ⟨_, rejected⟩ | spawned
  · exact Or.inr rejected
  · exact Or.inl spawned

theorem grantFrames_result (state : CompositeState) (word : UInt64) (frames : Nat) :
    (∃ child moved, (grantFrames state word frames).result = .framesGranted child moved) ∨
      ∃ reason, (grantFrames state word frames).result = .framesRejected reason := by
  rcases grantFrames_shape state word frames with ⟨_, rejected⟩ | granted
  · exact Or.inr rejected
  · exact Or.inl granted

theorem terminateChild_result (state : CompositeState) (word : UInt64) :
    (∃ child returned, (terminateChild state word).result = .terminated child returned) ∨
      ∃ reason, (terminateChild state word).result = .terminateRejected reason := by
  rcases terminateChild_shape state word with ⟨_, rejected⟩ | terminated
  · exact Or.inr rejected
  · exact Or.inl terminated

/-- **Every rejection returns the pre-state.**  For every operation of the
public spawn family, a typed rejection leaves the composite unchanged. -/
theorem ChildOperation.apply_rejected_unchanged (state : CompositeState)
    (operation : ChildOperation) (rejected : (operation.apply state).result.rejected = true) :
    (operation.apply state).state = state := by
  cases operation with
  | spawn request =>
      simp only [ChildOperation.apply] at rejected ⊢
      rcases spawnCharged_shape state request with ⟨same, _⟩ | ⟨_, _, _, spawned⟩
      · exact same
      · rw [spawned] at rejected; simp [ChildResult.rejected] at rejected
  | grantFrames control frames =>
      simp only [ChildOperation.apply] at rejected ⊢
      rcases FailStop.grantFrames_shape state control frames with ⟨same, _⟩ | ⟨_, _, granted⟩
      · exact same
      · rw [granted] at rejected; simp [ChildResult.rejected] at rejected
  | terminateChild control =>
      simp only [ChildOperation.apply] at rejected ⊢
      rcases FailStop.terminateChild_shape state control with ⟨same, _⟩ | ⟨_, _, terminated⟩
      · exact same
      · rw [terminated] at rejected; simp [ChildResult.rejected] at rejected
  | grantAuthority subject budget =>
      simp only [ChildOperation.apply] at rejected ⊢
      unfold grantBudgetedAuthority at rejected ⊢
      split
      · simp_all [ChildResult.rejected]
      · rfl
  | revokeAuthority subject => simp [ChildOperation.apply, ChildResult.rejected] at rejected

/-- A busy or halted latch rejects every operation of the family with the
state unchanged. -/
theorem childGate_unchanged_of_not_running (state : CompositeState) (operation : ChildOperation)
    (notRunning : state.execution.mode ≠ .running) :
    (childGate state operation).state = state := by
  cases hmode : state.execution.mode <;> simp_all [childGate]

/-! ## Exhaustion of each resource -/

/-- **Subject-budget exhaustion.**  An authorized parent whose live children
already fill its subject budget is rejected with `subjectBudgetExhausted`
and the pre-state: no identity, address space, or child-table entry is
created. -/
theorem spawnCharged_subject_budget_exhausted (state : CompositeState) (request : SpawnRequest)
    (authorized : spawnAuthorize state request.spawnWord = none)
    (full : subjectBudget state (spawnParent state) ≤ childCount state (spawnParent state)) :
    (spawnCharged state request).result = .spawnRejected .subjectBudgetExhausted ∧
      (spawnCharged state request).state = state := by
  simp [spawnCharged, authorized, full]

/-- **Control-generation exhaustion** is a typed rejection with the
pre-state. -/
theorem spawnCharged_control_generation_exhausted (state : CompositeState)
    (request : SpawnRequest) (slot : Nat)
    (authorized : spawnAuthorize state request.spawnWord = none)
    (room : ¬subjectBudget state (spawnParent state) ≤ childCount state (spawnParent state))
    (free : freeChildSlot state (spawnParent state) = some slot)
    (exhausted : controlGenerationAvailable state = false) :
    (spawnCharged state request).result = .spawnRejected .controlGenerationExhausted ∧
      (spawnCharged state request).state = state := by
  simp [spawnCharged, authorized, room, free, exhausted]

/-- **Frame-budget exhaustion.**  A grant of more frames than the parent has
free in its own budget is rejected with `frameBudgetExhausted` and the
pre-state. -/
theorem grantFrames_frame_budget_exhausted (state : CompositeState) (word : UInt64)
    (frames slot : Nat) (entry : ChildEntry)
    (resolved : resolveControl state word = .ok (slot, entry))
    (live : state.capabilities.subjects entry.child = true)
    (short : (availableFrames state (spawnParent state)).length < frames) :
    (grantFrames state word frames).result = .framesRejected .frameBudgetExhausted ∧
      (grantFrames state word frames).state = state := by
  have takeShort : (grantedFrames state (spawnParent state) frames).length < frames := by
    rw [grantedFrames, List.length_take]; omega
  simp [grantFrames, resolved, live, takeShort]

/-- An accepted charged spawn is the #489 spawn followed by the child-table
record. -/
theorem spawnCharged_spawned (state : CompositeState) (request : SpawnRequest)
    (child addressSpace : Nat) (control : UInt64)
    (spawned : (spawnCharged state request).result = .spawned child addressSpace control) :
    ∃ slot, spawnAuthorize state request.spawnWord = none ∧
      childCount state (spawnParent state) < subjectBudget state (spawnParent state) ∧
      freeChildSlot state (spawnParent state) = some slot ∧
      controlGenerationAvailable state = true ∧
      (spawn state request).result = .spawned child addressSpace ∧
      control = controlWord slot state.spawn.nextChildGeneration ∧
      (spawnCharged state request).state =
        installChild (spawn state request).state (spawnParent state) slot child := by
  unfold spawnCharged at spawned ⊢
  split at spawned
  · simp at spawned
  next authorized =>
  split at spawned
  · simp at spawned
  next room =>
  split at spawned
  · simp at spawned
  next slot free =>
  split at spawned
  · simp at spawned
  next generation =>
  split at spawned
  · simp at spawned
  next built builtChild builtSpace result =>
  simp only [ChildResult.spawned.injEq] at spawned
  obtain ⟨rfl, rfl, rfl⟩ := spawned
  refine ⟨slot, authorized, by omega, free, by simpa using generation, result, rfl, ?_⟩
  simp [authorized, room, free, generation, result]

/-- An accepted frame grant, unfolded. -/
theorem grantFrames_granted (state : CompositeState) (word : UInt64) (frames child moved : Nat)
    (granted : (grantFrames state word frames).result = .framesGranted child moved) :
    ∃ slot entry, resolveControl state word = .ok (slot, entry) ∧ entry.child = child ∧
      state.capabilities.subjects child = true ∧
      (grantedFrames state (spawnParent state) frames).length = frames ∧
      moved = movedCount state (grantedFrames state (spawnParent state) frames) ∧
      (grantFrames state word frames).state =
        { setChildEntry state (spawnParent state) slot (some (chargeEntry entry moved)) with
          frameBudgets := moveFrames state.frameBudgets
            (grantedFrames state (spawnParent state) frames) child } := by
  unfold grantFrames at granted ⊢
  split at granted
  · simp at granted
  next slot entry resolved =>
  split at granted
  · simp at granted
  next live =>
  split at granted
  · simp at granted
  next enough =>
  simp only [ChildResult.framesGranted.injEq] at granted
  obtain ⟨rfl, rfl⟩ := granted
  refine ⟨slot, entry, resolved, rfl, by simpa using live, ?_, rfl, ?_⟩
  · have := List.length_take (i := frames) (l := availableFrames state (spawnParent state))
    simp only [grantedFrames] at enough ⊢
    omega
  · simp [live, enough]

/-- An accepted child termination, unfolded. -/
theorem terminateChild_terminated (state : CompositeState) (word : UInt64) (child returned : Nat)
    (terminated : (terminateChild state word).result = .terminated child returned) :
    ∃ slot entry, resolveControl state word = .ok (slot, entry) ∧ entry.child = child ∧
      returned = state.budgetLimit child ∧
      (terminateChild state word).state =
        releaseChild (terminatedChild state child) (spawnParent state) slot child := by
  unfold terminateChild at terminated ⊢
  split at terminated
  · simp at terminated
  next slot entry resolved =>
  simp only [ChildResult.terminated.injEq] at terminated
  obtain ⟨rfl, rfl⟩ := terminated
  exact ⟨slot, entry, resolved, rfl, rfl, rfl⟩

end LeanOS.FailStop
