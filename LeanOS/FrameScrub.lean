import LeanOS.UserCopy

/-!
# Atomic frame scrubbing on ownership transfer

This executable model extends `MemoryLifecycle` with the finite byte memory
introduced by `UserCopy`. Allocation is the publication point: the selected
frame is completely cleared before the new capability is observable. Release
retires authority but deliberately leaves arbitrary old bytes in place.
-/
namespace LeanOS.FrameScrub

open LeanOS
set_option linter.unusedSimpArgs false

abbrev ObjectId := MemoryLifecycle.ObjectId
abbrev SubjectId := MemoryLifecycle.SubjectId
abbrev SlotId := MemoryLifecycle.SlotId
abbrev FrameId := FrameAllocator.FrameId
abbrev ByteOffset := UserCopy.ByteOffset
abbrev FrameBytes := FrameId → ByteOffset → UInt8

def initialByte : UInt8 := 0
def frameBytes : Nat := X86PageTable.pageBytes

structure State where
  memory : MemoryLifecycle.State
  bytes : FrameBytes
  /-- False means that this lifetime has not performed a modeled write. -/
  written : ObjectId → Bool

def scrubFrame (bytes : FrameBytes) (frame : FrameId) : FrameBytes :=
  fun candidate offset =>
    if candidate = frame ∧ offset < frameBytes then initialByte
    else bytes candidate offset

def setWritten (written : ObjectId → Bool) (object : ObjectId) (value : Bool) :=
  fun candidate => if candidate = object then value else written candidate

def setByte (bytes : FrameBytes) (frame : FrameId) (offset : ByteOffset)
    (value : UInt8) : FrameBytes :=
  fun candidate candidateOffset =>
    if candidate = frame ∧ candidateOffset = offset then value
    else bytes candidate candidateOffset

def Fresh (state : State) (object : ObjectId) : Prop :=
  state.written object = false ∧ ∃ frame, state.memory.binding object = some frame ∧
    ∀ offset, offset < frameBytes → state.bytes frame offset = initialByte

/-- The content/lifetime invariant: every published lifetime not yet written
by its owner has a current owned binding and contains only initial bytes. -/
def ScrubInvariant (state : State) : Prop :=
  ∀ object frame, state.memory.binding object = some frame →
    state.written object = false →
    FrameAllocator.IsOwnedBy state.memory.allocator frame object ∧
      ∀ offset, offset < frameBytes → state.bytes frame offset = initialByte

inductive AllocationError where
  | lifecycle (reason : MemoryLifecycle.AllocationError)
  deriving BEq, DecidableEq, Repr

inductive AccessError where
  | lifecycle (reason : MemoryLifecycle.AccessError) | outsideFrame
  deriving BEq, DecidableEq, Repr

inductive Result (ε : Type) where | accepted | rejected (reason : ε)
  deriving DecidableEq, Repr

structure Outcome (ε : Type) where
  state : State
  result : Result ε

def reject (state : State) (reason : ε) : Outcome ε :=
  { state, result := .rejected reason }

/-- Atomically allocate, scrub, and only then publish the returned state. -/
def allocate (state : State) (object : ObjectId) (subject : SubjectId)
    (slot : SlotId) : Outcome AllocationError :=
  let lifetime := MemoryLifecycle.allocate state.memory object subject slot
  match lifetime.result with
  | .rejected reason => reject state (.lifecycle reason)
  | .accepted =>
      match lifetime.state.binding object with
      | none => reject state (.lifecycle .exhausted) -- unreachable for a conforming lifecycle
      | some frame =>
          { state :=
              { memory := lifetime.state
                bytes := scrubFrame state.bytes frame
                written := setWritten state.written object false }
            result := .accepted }

/-- Release invalidates authority but does not assume old contents are zero. -/
def release (state : State) (subject : SubjectId) (slot : SlotId) :
    Outcome MemoryLifecycle.ReleaseError :=
  let lifetime := MemoryLifecycle.release state.memory subject slot
  match lifetime.result with
  | .rejected reason => reject state reason
  | .accepted =>
      { state := { state with memory := lifetime.state }, result := .accepted }

def readByte (state : State) (subject : SubjectId) (slot : SlotId)
    (offset : ByteOffset) : Except AccessError UInt8 := do
  if !(offset < frameBytes) then throw .outsideFrame
  let frame <- (MemoryLifecycle.authorize state.memory subject slot .read).mapError .lifecycle
  pure (state.bytes frame offset)

def writeByte (state : State) (subject : SubjectId) (slot : SlotId)
    (offset : ByteOffset) (value : UInt8) : Except AccessError State := do
  if !(offset < frameBytes) then throw .outsideFrame
  let frame <- (MemoryLifecycle.authorize state.memory subject slot .write).mapError .lifecycle
  let cap <- match state.memory.capabilities.slots subject slot with
    | some cap => pure cap
    | none => throw (.lifecycle .staleSlot)
  pure {
    memory := state.memory
    bytes := setByte state.bytes frame offset value
    written := setWritten state.written cap.object true }

theorem scrubFrame_target bytes frame offset (h : offset < frameBytes) :
    scrubFrame bytes frame frame offset = initialByte := by
  simp [scrubFrame, h]

/-- Clearing a frame changes no byte of any other frame. -/
theorem scrubFrame_other bytes frame other offset (hne : other ≠ frame) :
    scrubFrame bytes frame other offset = bytes other offset := by
  simp [scrubFrame, hne]

theorem allocate_rejected_unchanged state object subject slot reason
    (h : (allocate state object subject slot).result = .rejected reason) :
    (allocate state object subject slot).state = state := by
  simp only [allocate] at h ⊢
  split <;> simp_all [reject]
  split <;> simp_all

theorem allocation_lifecycle_accepted state object subject slot
    (h : (allocate state object subject slot).result = .accepted) :
    (MemoryLifecycle.allocate state.memory object subject slot).result = .accepted := by
  simp only [allocate] at h
  split at h <;> simp_all [reject]

/-- Accepted publication exposes a current allocator-owned, completely
scrubbed frame, regardless of its firmware or previous-owner contents. -/
theorem allocation_publishes_scrubbed state object subject slot
    (h : (allocate state object subject slot).result = .accepted) :
    Fresh (allocate state object subject slot).state object := by
  simp only [allocate] at h
  split at h <;> try contradiction
  next lifetime hlifetime =>
    split at h <;> try contradiction
    next frame hbinding =>
      simp only [allocate, hlifetime, hbinding, Fresh]
      constructor
      · simp [setWritten]
      · refine ⟨frame, rfl, ?_⟩
        intro offset hoffset
        exact scrubFrame_target state.bytes frame offset hoffset

theorem allocation_publishes_owned state object subject slot
    (h : (allocate state object subject slot).result = .accepted) :
    ∃ frame, (allocate state object subject slot).state.memory.binding object = some frame ∧
      FrameAllocator.IsOwnedBy
        (allocate state object subject slot).state.memory.allocator frame object := by
  have haccept := allocation_lifecycle_accepted state object subject slot h
  simp only [allocate] at h
  split at h <;> try contradiction
  next lifetime hlifetime =>
    split at h <;> try contradiction
    next frame hbinding =>
      simp only [allocate, hlifetime, hbinding]
      refine ⟨frame, rfl, ?_⟩
      obtain ⟨ownedFrame, hownedBinding, howned⟩ :=
        MemoryLifecycle.allocated_binding state.memory object subject slot haccept
      rw [hbinding] at hownedBinding
      injection hownedBinding with heq
      simpa [heq] using howned

theorem release_rejected_unchanged state subject slot reason
    (h : (release state subject slot).result = .rejected reason) :
    (release state subject slot).state = state := by
  simp only [release] at h ⊢
  split <;> simp_all [reject]

/-- Release never silently clears, partially changes, or otherwise relies on
the contents of the retired frame. -/
theorem release_preserves_bytes state subject slot :
    (release state subject slot).state.bytes = state.bytes := by
  simp only [release]
  split <;> rfl

theorem read_fresh_zero state object subject slot frame offset
    (hinvariant : ScrubInvariant state)
    (hsubject : state.memory.capabilities.subjects subject = true)
    (hcap : state.memory.capabilities.slots subject slot = some
      { object, kind := .memory, rights := Capability.allRights })
    (hslotRange : Capability.slotInRange state.memory.capabilities subject slot = true)
    (hbinding : state.memory.binding object = some frame)
    (hunwritten : state.written object = false)
    (hoffset : offset < frameBytes) :
    readByte state subject slot offset = .ok initialByte := by
  have howned := (hinvariant object frame hbinding hunwritten).1
  change state.memory.allocator.status frame = .owned object at howned
  have hauth : MemoryLifecycle.authorize state.memory subject slot .read = .ok frame := by
    simp [MemoryLifecycle.authorize, Capability.lookup, hsubject, hcap, hslotRange, hbinding,
      howned, Capability.permits, Capability.allRights]
  have hzero := (hinvariant object frame hbinding hunwritten).2 offset hoffset
  simp only [readByte, hoffset, Bool.not_true, ↓reduceIte]
  rw [hauth]
  exact congrArg Except.ok hzero

/- Executable adversarial trace: arbitrary sentinels survive release but are
cleared before a fresh object is published on the same physical frame. -/
private def caps : Capability.State :=
  { subjects := fun subject => subject < 2
    objects := fun _ => false
    kinds := fun _ => none
    slots := fun _ _ => none }
private def allocator : FrameAllocator.State :=
  { frames := [4]
    status := fun frame => if frame = 4 then .free else .reserved }
private def initial : State :=
  { memory :=
      { capabilities := caps
        allocator := allocator
        binding := fun _ => none
        issued := fun _ => false }
    bytes := fun _ _ => 0xff
    written := fun _ => false }
private def ownedA := (allocate initial 10 0 0).state
private def writtenA := (writeByte ownedA 0 0 0 0xa5).toOption.getD ownedA
private def releasedA := (release writtenA 0 0).state
private def ownedB := (allocate releasedA 11 1 0).state

example : releasedA.bytes 4 0 = 0xa5 := by native_decide
example : ownedB.memory.binding 11 = some 4 := by native_decide
example : readByte ownedB 1 0 0 = .ok 0 := by rfl
example : readByte ownedB 1 0 (frameBytes - 1) = .ok 0 := by rfl
example : MemoryLifecycle.authorize ownedB.memory 0 0 .read = .error .staleSlot := by rfl
example : (allocate ownedB 12 0 1).result = .rejected (.lifecycle .exhausted) := by native_decide
example : (release releasedA 0 0).result = .rejected .staleSlot := by native_decide

private def releasedB := (release ownedB 1 0).state
private def ownedA2 := (allocate releasedB 12 0 0).state
example : readByte ownedA2 0 0 0 = .ok 0 := by rfl
example : readByte ownedA2 0 0 (frameBytes - 1) = .ok 0 := by rfl

end LeanOS.FrameScrub
