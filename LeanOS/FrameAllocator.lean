/-!
# Physical-frame allocator reference model

Each modeled frame has exactly one state: reserved, free, or owned by one
owner.  Initialization accepts nonempty, nonoverlapping firmware regions.
This is a sequential executable model; firmware truthfulness and the bridge to
boot code are trusted outside it.
-/
namespace LeanOS.FrameAllocator

abbrev FrameId := Nat
abbrev OwnerId := Nat

inductive RegionKind where | reserved | usable
  deriving BEq, DecidableEq, Repr

structure Region where
  start : FrameId
  count : Nat
  kind : RegionKind
  deriving BEq, DecidableEq, Repr

inductive FrameState where
  | reserved | free | owned (owner : OwnerId)
  deriving BEq, DecidableEq, Repr

structure State where
  frames : List FrameId
  status : FrameId → FrameState

def Region.frames (region : Region) : List FrameId :=
  (List.range region.count).map (region.start + ·)

def distinct : List FrameId → Bool
  | [] => true
  | frame :: rest => !rest.contains frame && distinct rest

inductive InitError where | malformedRegion | overlappingRegions
  deriving BEq, DecidableEq, Repr

def init (regions : List Region) : Except InitError State :=
  if regions.any (·.count == 0) then .error .malformedRegion
  else
    let frames := regions.flatMap Region.frames
    if distinct frames then
      .ok {
        frames
        status := fun frame =>
          if regions.any (fun region =>
              region.kind == .reserved && region.frames.contains frame) then
            .reserved
          else .free }
    else .error .overlappingRegions

def IsReserved (state : State) (frame : FrameId) : Prop :=
  state.status frame = .reserved
def IsFree (state : State) (frame : FrameId) : Prop :=
  state.status frame = .free
def IsOwnedBy (state : State) (frame : FrameId) (owner : OwnerId) : Prop :=
  state.status frame = .owned owner

/-- Every modeled frame is in exactly one allocator class. -/
def Conserved (state : State) : Prop :=
  ∀ frame, frame ∈ state.frames →
    IsReserved state frame ∨ IsFree state frame ∨ ∃ owner, IsOwnedBy state frame owner

theorem conservation (state : State) : Conserved state := by
  intro frame _
  cases h : state.status frame with
  | reserved => exact Or.inl h
  | free => exact Or.inr (Or.inl h)
  | owned owner => exact Or.inr (Or.inr ⟨owner, h⟩)

theorem init_establishes_conservation (regions : List Region) (state : State)
    (_hresult : init regions = .ok state) : Conserved state := by
  exact conservation state

theorem reserved_not_free (state : State) (frame : FrameId)
    (hreserved : IsReserved state frame) : ¬IsFree state frame := by
  intro hfree
  unfold IsReserved at hreserved
  unfold IsFree at hfree
  rw [hreserved] at hfree
  contradiction

theorem reserved_not_owned (state : State) (frame : FrameId) (owner : OwnerId)
    (hreserved : IsReserved state frame) : ¬IsOwnedBy state frame owner := by
  intro howned
  unfold IsReserved at hreserved
  unfold IsOwnedBy at howned
  rw [hreserved] at howned
  contradiction

theorem ownership_exclusive (state : State) (frame : FrameId) (left right : OwnerId)
    (hleft : IsOwnedBy state frame left) (hright : IsOwnedBy state frame right) :
    left = right := by
  simp [IsOwnedBy] at hleft hright
  simpa [hleft] using hright

def setStatus (state : State) (frame : FrameId) (value : FrameState) : State :=
  { state with status := fun candidate =>
      if candidate = frame then value else state.status candidate }

inductive AllocationError where | exhausted
  deriving BEq, DecidableEq, Repr

structure Allocation where
  state : State
  frame : FrameId

def allocate (state : State) (owner : OwnerId) : Except AllocationError Allocation :=
  match state.frames.find? (fun frame => state.status frame == .free) with
  | none => .error .exhausted
  | some frame => .ok { state := setStatus state frame (.owned owner), frame }

theorem allocated_is_owned (state : State) (owner : OwnerId) (allocation : Allocation)
    (hresult : allocate state owner = .ok allocation) :
    IsOwnedBy allocation.state allocation.frame owner := by
  simp only [allocate] at hresult
  split at hresult
  · contradiction
  · injection hresult with hallocation
    rw [← hallocation]
    simp [IsOwnedBy, setStatus]

theorem allocated_not_reserved (state : State) (owner : OwnerId)
    (allocation : Allocation) (hresult : allocate state owner = .ok allocation) :
    ¬IsReserved allocation.state allocation.frame := by
  have howned := allocated_is_owned state owner allocation hresult
  intro hreserved
  unfold IsOwnedBy at howned
  unfold IsReserved at hreserved
  rw [hreserved] at howned
  contradiction

theorem allocation_preserves_conservation (state : State) (owner : OwnerId)
    (allocation : Allocation) (_hresult : allocate state owner = .ok allocation) :
    Conserved allocation.state := by
  exact conservation allocation.state

inductive ReleaseError where | invalidRelease
  deriving BEq, DecidableEq, Repr

def release (state : State) (owner : OwnerId) (frame : FrameId) :
    Except ReleaseError State :=
  if state.status frame = .owned owner then
    .ok (setStatus state frame .free)
  else .error .invalidRelease

theorem released_is_free (state next : State) (owner : OwnerId) (frame : FrameId)
    (hresult : release state owner frame = .ok next) : IsFree next frame := by
  simp only [release] at hresult
  split at hresult
  · injection hresult with hnext
    rw [← hnext]
    simp [IsFree, setStatus]
  · contradiction

theorem release_preserves_conservation (state next : State) (owner : OwnerId)
    (frame : FrameId) (_hresult : release state owner frame = .ok next) :
    Conserved next := by
  exact conservation next

theorem invalid_release_explicit (state : State) (owner : OwnerId) (frame : FrameId)
    (hnotowner : state.status frame ≠ .owned owner) :
    release state owner frame = .error .invalidRelease := by
  simp [release, hnotowner]

private def fragmented : List Region :=
  [{ start := 0, count := 2, kind := .reserved },
   { start := 8, count := 1, kind := .usable },
   { start := 20, count := 2, kind := .usable }]

def initError (regions : List Region) : Option InitError :=
  match init regions with | .error reason => some reason | .ok _ => none

example : initError [{ start := 1, count := 0, kind := .usable }] =
    some .malformedRegion := by decide
example : initError [{ start := 1, count := 3, kind := .usable },
    { start := 3, count := 2, kind := .reserved }] = some .overlappingRegions := by decide
example : (init fragmented).isOk = true := by decide

private def tiny : State :=
  { frames := [3], status := fun frame => if frame = 3 then .free else .reserved }

example : (allocate tiny 7).isOk = true := by decide
example : ((allocate tiny 7).toOption.bind fun first =>
    (allocate first.state 8).toOption) = none := by decide
example : (release tiny 7 3).isOk = false := by decide
example : ((allocate tiny 7).toOption.bind fun first =>
    (release first.state 7 first.frame).toOption.bind fun released =>
      (allocate released 8).toOption.map (·.frame)) = some 3 := by decide

end LeanOS.FrameAllocator
