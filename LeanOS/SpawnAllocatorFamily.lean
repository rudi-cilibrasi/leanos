import LeanOS.SpawnAllocatorWordsNext
import LeanOS.SpawnFamily

/-!
# The spawn family's composite states, read by the allocator (#575)

`Family` is the invariant of the composite states the spawn family's boot
boundary runs on: the combined resource, child-accounting and spawn-tree
invariants, plus the shape of the family.  The parent is subject 2, the
current subject of a running latch; its slots 0 and 1 hold the family's
endpoint (owned by the bystander) and its own address-space root; slots 2 and
3 hold its memory or nothing; its children are in child-table slots 0 to 3,
live, with exactly their charge in frames, all of them free; and the only live
subjects are the bystander, the parent and its children.

This module proves that, on such a state, the composite's readings that the
spawn family's decisions use are the allocator's readings of
`abstraction state`: the child count and first free slot, control-word
resolution, endpoint-handle resolution, and the parent's free frames.
`LeanOS.SpawnAllocatorSimulation` builds the per-command simulation on them.
-/
namespace LeanOS.SpawnAllocator

open LeanOS
open LeanOS.FailStop
open LeanOS.SpawnFamily

set_option linter.unusedSimpArgs false

/-! ## The abstraction of a composite state -/

/-- The parent's memory capability in a slot: its identity, or none. -/
def memoryIn (state : CompositeState) (slot : Nat) : Option Nat :=
  match state.capabilities.slots parent slot with
  | some capability => if capability.kind = .memory then some capability.identity else none
  | none => none

/-- **The allocator record of a composite state.** -/
def abstraction (state : CompositeState) : State :=
  { subjectNext := state.issuers.subject.next
    objectNext := state.issuers.object.next
    capabilityNext := state.capabilities.nextIdentity
    controlNext := state.spawn.nextChildGeneration
    authorityNext := state.spawn.nextGeneration
    authority := (state.spawn.authority parent).map SpawnCapability.generation
    budget := FailStop.subjectBudget state parent
    children := (List.range childCapacity).map fun slot =>
      (state.spawn.children parent slot).map fun entry =>
        { generation := entry.generation, charge := entry.charge }
    memory := [memoryIn state 2, memoryIn state 3]
    parentFrames := state.budgetLimit parent }

/-- The allocator command of a family command, if it is one. -/
def toCommand : FamilyCommand → Option Command
  | .child operation => some (.child operation)
  | .memory operation => some (.memory operation)
  | .switch => none
  | .copy _ _ _ _ => none

/-! ## The family invariant -/

/-- The rights of the parent's endpoint capability. -/
def endpointRights : Capability.Rights :=
  { send := true, receive := true, grant := true, revoke := true }

/-- A parent memory slot: empty, or a memory capability whose object owns a
frame committed to the parent. -/
def MemorySlot (state : CompositeState) (slot : Nat) : Prop :=
  state.capabilities.slots parent slot = none ∨
    ∃ capability frame, state.capabilities.slots parent slot = some capability ∧
      capability.kind = .memory ∧ capability.rights.revoke = true ∧ 0 < capability.identity ∧
      state.virtualMemory.memory.binding capability.object = some frame ∧
      state.virtualMemory.memory.allocator.status frame = .owned capability.object ∧
      state.lifecycle.ownedMemory capability.object = some (parent, frame) ∧
      state.frameBudgets.commitment frame = some parent

/-- **The spawn family's composite states.** -/
structure Family (state : CompositeState) : Prop where
  resources : ResourceRuntimeWellFormed state
  accounting : ChildAccountingWellFormed state
  tree : SpawnTreeWellFormed state
  running : state.execution.mode = .running
  current : state.execution.core.context.currentSubject = parent
  lifecycleCurrent : state.lifecycle.current = some parent
  capacity : ∀ subject, state.capabilities.slotCapacity subject = parentSlots
  parentLive : state.capabilities.subjects parent = true
  parentRoot : state.spawn.parent parent = none
  endpoint : ∃ object, state.capabilities.slots parent 0 =
      some ⟨object, .endpoint, endpointRights, endpointIdentity, none⟩ ∧
    state.capabilities.objects object = true ∧
    state.capabilities.kinds object = some .endpoint ∧
    state.lifecycle.endpointOwner object = some bystander
  space : ∃ capability, state.capabilities.slots parent 1 = some capability ∧
    capability.kind = .addressSpace ∧ capability.identity = spaceIdentity ∧
    state.lifecycle.addressOwner capability.object = some parent
  memory : ∀ slot, slot = 2 ∨ slot = 3 → MemorySlot state slot
  memoryDistinct : ∀ first second, state.capabilities.slots parent 2 = some first →
    state.capabilities.slots parent 3 = some second → first.object ≠ second.object
  childSlots : ∀ slot, childCapacity ≤ slot → state.spawn.children parent slot = none
  authority : ∀ capability, state.spawn.authority parent = some capability →
    capability.subjectBudget ≤ childCapacity ∧ 0 < capability.generation ∧
      capability.generation < state.spawn.nextGeneration
  others : ∀ subject, subject ≠ parent → state.spawn.authority subject = none
  childLive : ∀ slot entry, state.spawn.children parent slot = some entry →
    state.capabilities.subjects entry.child = true ∧ 0 < entry.generation ∧
      state.budgetLimit entry.child = entry.charge
  live : ∀ subject, state.capabilities.subjects subject = true →
    subject = bystander ∨ subject = parent ∨
      ∃ slot entry, state.spawn.children parent slot = some entry ∧ entry.child = subject
  committed : ∀ frame subject, state.frameBudgets.commitment frame = some subject →
    subject = parent ∨
      (state.virtualMemory.memory.allocator.status frame = .free ∧
        state.lifecycle.frameOwner frame = none ∧
        ∃ slot entry, state.spawn.children parent slot = some entry ∧ entry.child = subject)
  framesNodup : state.virtualMemory.memory.allocator.frames.Nodup
  parentNames : ∀ slot capability subject, state.capabilities.slots parent slot = some capability →
    OwnedBy state.lifecycle subject capability.object → state.spawn.parent subject = none
  fresh : ∀ object, state.issuers.object.next ≤ object →
    state.capabilities.objects object = false ∧ state.lifecycle.ownedMemory object = none ∧
      state.lifecycle.endpointOwner object = none
  parentFree : ∀ frame, state.frameBudgets.commitment frame = some parent →
    state.virtualMemory.memory.allocator.status frame = .free →
    state.lifecycle.frameOwner frame = none
  usage : state.budgetUsage parent = (abstraction state).memoryUsed
  capabilityBound : state.capabilities.nextIdentity ≤ CapabilityHandle.generationReserved + 1
  controlBound : state.spawn.nextChildGeneration ≤ CapabilityHandle.generationReserved
  generationBound : 0 < state.spawn.nextGeneration ∧ state.spawn.nextGeneration < wordBound
  frameBound : state.budgetLimit parent + (abstraction state).chargeSum < frameBound

/-! ## The child table -/

theorem sum_range_of_zero (values : Nat → Nat) (low high : Nat) (le : low ≤ high)
    (zero : ∀ index, low ≤ index → values index = 0) :
    ((List.range high).map values).sum = ((List.range low).map values).sum := by
  induction high with
  | zero =>
      have : low = 0 := by omega
      subst this; rfl
  | succ high ih =>
      by_cases same : low = high + 1
      · subst same; rfl
      · rw [List.range_succ, List.map_append, List.sum_append, ih (by omega)]
        simp [zero high (by omega)]

theorem abstraction_children (state : CompositeState) :
    (abstraction state).children = (List.range childCapacity).map fun slot =>
      (state.spawn.children parent slot).map fun entry =>
        ({ generation := entry.generation, charge := entry.charge } : ChildRecord) := rfl

theorem abstraction_childAt (state : CompositeState) (slot : Nat) :
    (abstraction state).childAt slot =
      if slot < childCapacity then
        (state.spawn.children parent slot).map fun entry =>
          ({ generation := entry.generation, charge := entry.charge } : ChildRecord)
      else none := by
  unfold State.childAt
  rw [abstraction_children]
  by_cases inRange : slot < childCapacity
  · simp [inRange]
  · simp [inRange]

/-- **The child count is the allocator's.** -/
theorem childCount_family (state : CompositeState) (family : Family state) :
    childCount state parent = (abstraction state).childCount := by
  unfold childCount slotSum State.childCount
  rw [sum_range_of_zero _ childCapacity childSlots (by decide)]
  · rw [abstraction_children]
    have range : List.range childCapacity = [0, 1, 2, 3] := rfl
    rw [range]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.countP_cons,
      List.countP_nil]
    cases state.spawn.children parent 0 <;> cases state.spawn.children parent 1 <;>
      cases state.spawn.children parent 2 <;> cases state.spawn.children parent 3 <;> rfl
  · intro slot high
    simp [entryCount, family.childSlots slot high]

theorem subjectBudget_family (state : CompositeState) :
    subjectBudget state parent = (abstraction state).budget := rfl

/-- The allocator's view of one composite child entry. -/
def recordOf (entry : ChildEntry) : ChildRecord :=
  { generation := entry.generation, charge := entry.charge }

theorem abstraction_childAt_lt (state : CompositeState) (slot : Nat) (small : slot < childCapacity) :
    (abstraction state).childAt slot = (state.spawn.children parent slot).map recordOf := by
  simp only [abstraction_childAt, small, ↓reduceIte]; rfl

theorem abstraction_childAt_family (state : CompositeState) (family : Family state) (slot : Nat) :
    (abstraction state).childAt slot = (state.spawn.children parent slot).map recordOf := by
  by_cases small : slot < childCapacity
  · exact abstraction_childAt_lt state slot small
  · rw [abstraction_childAt, family.childSlots slot (by omega)]; simp [small]

/-- **The first free child slot is the allocator's**, whenever the allocator
finds one. -/
theorem freeChildSlot_family (state : CompositeState) (slot : Nat)
    (free : (abstraction state).freeSlot = some slot) :
    freeChildSlot state parent = some slot := by
  unfold State.freeSlot at free
  rw [abstraction_children] at free
  unfold freeChildSlot childSlots
  unfold childCapacity at free
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append] at free
  rw [show 64 = 4 + 60 from rfl, List.range_add, List.find?_append]
  have first : (List.range 4).find? (fun candidate =>
      (state.spawn.children parent candidate).isNone) = some slot := by
    have range : List.range 4 = [0, 1, 2, 3] := rfl
    rw [range]
    cases c0 : state.spawn.children parent 0 <;> cases c1 : state.spawn.children parent 1 <;>
      cases c2 : state.spawn.children parent 2 <;> cases c3 : state.spawn.children parent 3 <;>
      simp [c0, c1, c2, c3, List.findIdx?_cons] at free <;>
      subst free <;> simp [List.find?_cons, c0, c1, c2, c3]
  rw [first]
  rfl

/-! ## Control words -/

/-- **Control-word resolution is the allocator's**: the same denial, or the
same slot and the entry the allocator records. -/
theorem resolveControl_family (state : CompositeState) (family : Family state) (word : UInt64) :
    (FailStop.resolveControl state word).map (fun found => (found.1, recordOf found.2)) =
      (abstraction state).resolveControl word := by
  have parentLive := family.parentLive
  have current := family.current
  unfold FailStop.resolveControl State.resolveControl spawnParent
  rw [current]
  simp only [parentLive, ↓reduceIte]
  cases decoded : CapabilityHandle.decode word with
  | error reason => simp [Except.map]
  | ok handle =>
      simp only
      rw [abstraction_childAt_family state family handle.slot]
      cases found : state.spawn.children parent handle.slot with
      | none => simp [Except.map]
      | some entry =>
          simp only [Option.map_some]
          by_cases same : entry.generation = handle.identity
          · simp [same, recordOf, Except.map]
          · simp [same, recordOf, Except.map]

theorem resolveControl_family_error (state : CompositeState) (family : Family state)
    (word : UInt64) (denial : ControlDenial)
    (rejected : (abstraction state).resolveControl word = .error denial) :
    FailStop.resolveControl state word = .error denial := by
  have same := resolveControl_family state family word
  rw [rejected] at same
  cases result : FailStop.resolveControl state word with
  | error other => rw [result] at same; simp [Except.map] at same; rw [same]
  | ok found => rw [result] at same; simp [Except.map] at same

theorem resolveControl_family_ok (state : CompositeState) (family : Family state)
    (word : UInt64) (slot : Nat) (record : ChildRecord)
    (resolved : (abstraction state).resolveControl word = .ok (slot, record)) :
    ∃ entry, FailStop.resolveControl state word = .ok (slot, entry) ∧ recordOf entry = record := by
  have same := resolveControl_family state family word
  rw [resolved] at same
  cases result : FailStop.resolveControl state word with
  | error other => rw [result] at same; simp [Except.map] at same
  | ok found =>
      rw [result] at same
      simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at same
      obtain ⟨foundSlot, foundEntry⟩ := found
      obtain ⟨rfl, rfl⟩ := same
      exact ⟨foundEntry, rfl, rfl⟩

/-! ## Endpoint handles -/

theorem abstraction_memoryAt (state : CompositeState) (slot : Nat) :
    (abstraction state).memoryAt slot =
      if slot = 2 then memoryIn state 2 else if slot = 3 then memoryIn state 3 else none := by
  unfold State.memoryAt abstraction memoryBase
  rcases slot with _ | _ | _ | _ | slot <;> simp

/-- The parent's endpoint capability over `object`. -/
def endpointCapability (object : Nat) : Capability.Capability :=
  ⟨object, .endpoint, endpointRights, endpointIdentity, none⟩

/-- The parent's slots in a capability state, as the allocator reads them. -/
structure ParentSlots (capabilities : Capability.State) (record : State) (object : Nat) : Prop where
  live : capabilities.subjects parent = true
  capacity : capabilities.slotCapacity parent = parentSlots
  endpoint : capabilities.slots parent 0 = some (endpointCapability object)
  objectLive : capabilities.objects object = true
  objectKind : capabilities.kinds object = some .endpoint
  space : ∃ capability, capabilities.slots parent 1 = some capability ∧
    capability.kind = .addressSpace ∧ capability.identity = spaceIdentity
  memory : ∀ slot, slot = 2 ∨ slot = 3 →
    (capabilities.slots parent slot = none ∧ record.memoryAt slot = none) ∨
      ∃ capability, capabilities.slots parent slot = some capability ∧
        capability.kind = .memory ∧ record.memoryAt slot = some capability.identity

/-- **Endpoint-handle resolution is the allocator's**: the parent's endpoint
for exactly the words the allocator accepts, and the same denial otherwise. -/
theorem resolveEndpoint_parentSlots (capabilities : Capability.State) (record : State)
    (object : Nat) (slots : ParentSlots capabilities record object) (word : UInt64) :
    CapabilityHandle.resolveCurrent capabilities { caller := parent } word .endpoint =
      match record.resolveEndpoint word with
      | none => .ok ⟨⟨0, endpointIdentity⟩, endpointCapability object⟩
      | some denial => .error denial := by
  unfold CapabilityHandle.resolveCurrent State.resolveEndpoint
  cases decoded : CapabilityHandle.decode word with
  | error reason => rfl
  | ok handle =>
      simp only
      unfold CapabilityHandle.resolve
      have live := slots.live
      simp only [live, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Capability.slotInRange,
        slots.capacity]
      by_cases out : parentSlots ≤ handle.slot
      · have : ¬handle.slot < parentSlots := Nat.not_lt.2 out
        simp [out, this]
      have inRange : handle.slot < parentSlots := Nat.lt_of_not_le out
      simp only [out, inRange, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases s0 : handle.slot = 0
      · rw [s0, slots.endpoint]
        by_cases same : handle.identity = endpointIdentity
        · have handleEq : handle = ⟨0, endpointIdentity⟩ := by
            cases handle; simp_all
          simp [same, endpointCapability, slots.objectLive, slots.objectKind, handleEq]
        · have different : (endpointIdentity != handle.identity) = true := by
            simp only [bne_iff_ne, ne_eq]; exact fun eq => same eq.symm
          simp [same, endpointCapability, different]
      simp only [s0, ↓reduceIte]
      by_cases s1 : handle.slot = 1
      · obtain ⟨capability, held, kind, identity⟩ := slots.space
        rw [s1, held]
        by_cases same : handle.identity = spaceIdentity
        · simp [same, identity, kind]
        · have different : (capability.identity != handle.identity) = true := by
            simp only [bne_iff_ne, ne_eq, identity]; exact fun eq => same eq.symm
          simp [same, different]
      simp only [s1, ↓reduceIte]
      have memorySlot : handle.slot = 2 ∨ handle.slot = 3 := by
        have lt4 : handle.slot < 4 := inRange
        match hs : handle.slot, lt4 with
        | 0, _ => exact absurd hs s0
        | 1, _ => exact absurd hs s1
        | 2, _ => exact Or.inl rfl
        | 3, _ => exact Or.inr rfl
        | _ + 4, small => exact absurd small (Nat.not_lt.2 (Nat.le_add_left 4 _))
      rcases slots.memory handle.slot memorySlot with ⟨empty, none⟩ | ⟨capability, held, kind, memoryAt⟩
      · rw [empty, none]
      · rw [held, memoryAt]
        by_cases same : handle.identity = capability.identity
        · simp [same, kind]
        · have different : (capability.identity != handle.identity) = true := by
            simp only [bne_iff_ne, ne_eq]; exact fun eq => same eq.symm
          simp [same, different]

/-! ## The parent's frames -/

/-- Committed frames are never reserved (`budgetAgreementInvariant`). -/
theorem family_notReserved (state : CompositeState) (family : Family state) (frame subject : Nat)
    (committed : state.frameBudgets.commitment frame = some subject) :
    state.virtualMemory.memory.allocator.status frame ≠ .reserved := by
  have agreement := ((resourceWellFormed_iff state).1 family.resources.2).2.2.1
  exact (agreement frame subject committed).2.1

/-- The frames committed to a subject (`FrameBudget.budgetFrames` of the
composite). -/
def committedFrames (state : CompositeState) (subject : Nat) : List FrameAllocator.FrameId :=
  state.virtualMemory.memory.allocator.frames.filter fun frame =>
    decide (state.frameBudgets.commitment frame = some subject)

def isFree (state : CompositeState) (frame : FrameAllocator.FrameId) : Bool :=
  decide (state.virtualMemory.memory.allocator.status frame = .free)

def isOwned (state : CompositeState) (frame : FrameAllocator.FrameId) : Bool :=
  match state.virtualMemory.memory.allocator.status frame with
  | .owned _ => true
  | _ => false

theorem budgetLimit_committed (state : CompositeState) (subject : Nat) :
    state.budgetLimit subject = (committedFrames state subject).length := rfl

theorem budgetUsage_committed (state : CompositeState) (subject : Nat) :
    state.budgetUsage subject = (committedFrames state subject).countP (isOwned state) := rfl

theorem availableFrames_committed (state : CompositeState) (subject : Nat) :
    availableFrames state subject = (committedFrames state subject).filter (isFree state) := by
  unfold availableFrames committedFrames isFree
  rw [List.filter_filter]
  apply List.filter_congr
  intro frame _
  simp [Bool.and_comm]

/-- The parent's free frames, counted. -/
theorem availableFrames_length (state : CompositeState) (family : Family state) :
    (availableFrames state parent).length = (abstraction state).available := by
  have usage := family.usage
  unfold State.available
  rw [← usage]
  have limit : (abstraction state).parentFrames = state.budgetLimit parent := rfl
  rw [limit, budgetLimit_committed, budgetUsage_committed, availableFrames_committed,
    ← List.countP_eq_length_filter]
  have split := List.length_eq_countP_add_countP (isFree state) (l := committedFrames state parent)
  have same : (committedFrames state parent).countP (fun frame => decide ¬isFree state frame = true) =
      (committedFrames state parent).countP (isOwned state) := by
    apply List.countP_congr
    intro frame member
    have committed : state.frameBudgets.commitment frame = some parent := by
      unfold committedFrames at member; simpa using (List.mem_filter.1 member).2
    have notReserved := family_notReserved state family frame parent committed
    unfold isFree isOwned
    cases status : state.virtualMemory.memory.allocator.status frame with
    | reserved => exact absurd status notReserved
    | free => simp
    | owned owner => simp
  omega

theorem find_isSome_filter {α : Type} (values : List α) (predicate : α → Bool) :
    (values.find? predicate).isSome = decide (0 < (values.filter predicate).length) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      by_cases holds : predicate head = true
      · simp [List.find?_cons, List.filter_cons, holds]
      · simp only [Bool.not_eq_true] at holds
        simp [List.find?_cons, List.filter_cons, holds, ih]

theorem frameState_beq_free (status : FrameAllocator.FrameState) :
    (status == .free) = decide (status = .free) := by
  cases status <;> rfl

/-- The first free frame committed to the parent exists exactly when the
allocator's parent has a free frame. -/
theorem firstAvailable_family (state : CompositeState) (family : Family state) :
    (FrameBudget.firstAvailable state.budgetState parent).isSome =
      decide (0 < (abstraction state).available) := by
  rw [← availableFrames_length state family]
  unfold FrameBudget.firstAvailable availableFrames
  simp only [CompositeState.budgetState, frameState_beq_free]
  exact find_isSome_filter _ _

/-- The parent's slots of a family state, as the allocator reads them. -/
theorem family_parentSlots (state : CompositeState) (family : Family state) :
    ∃ object, ParentSlots state.capabilities (abstraction state) object ∧
      state.lifecycle.endpointOwner object = some bystander := by
  obtain ⟨object, endpoint, objectLive, objectKind, owner⟩ := family.endpoint
  obtain ⟨capability, held, kind, identity, _⟩ := family.space
  refine ⟨object, ⟨family.parentLive, family.capacity parent, endpoint, objectLive, objectKind,
    ⟨capability, held, kind, identity⟩, fun slot which => ?_⟩, owner⟩
  have memoryAt : (abstraction state).memoryAt slot = memoryIn state slot := by
    rw [abstraction_memoryAt]
    rcases which with rfl | rfl <;> simp
  rcases family.memory slot which with empty | ⟨memoryCapability, frame, found, memoryKind, _⟩
  · left
    refine ⟨empty, ?_⟩
    rw [memoryAt]; unfold memoryIn; rw [empty]
  · right
    refine ⟨memoryCapability, found, memoryKind, ?_⟩
    rw [memoryAt]; unfold memoryIn; rw [found]; simp [memoryKind]

/-- An owner of an object is live. -/
theorem owner_live (state : CompositeState) (family : Family state) (subject object : Nat)
    (owned : OwnedBy state.lifecycle subject object) : state.capabilities.subjects subject = true := by
  have lifecycleWf := family.resources.1.left.2.2.1
  have lifeCaps : state.lifecycle.capabilities = state.capabilities :=
    family.resources.1.left.1.2.2.2.1.symm
  rw [← lifeCaps]
  rcases owned with endpoint | address | memory
  · exact lifecycleWf.2.2.2.1 _ _ endpoint
  · exact lifecycleWf.2.2.1 _ _ address
  · cases found : state.lifecycle.ownedMemory object with
    | none => simp [found] at memory
    | some owner =>
        simp only [found, Option.any_some, decide_eq_true_eq] at memory
        obtain ⟨holder, frame⟩ := owner
        simp only at memory
        subst memory
        exact (lifecycleWf.2.1 _ _ _ found).1

end LeanOS.SpawnAllocator
