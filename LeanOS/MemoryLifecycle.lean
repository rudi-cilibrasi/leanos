import LeanOS.Capability
import LeanOS.FrameAllocator

/-!
# Capability-safe physical-frame lifetime model

This executable sequential model composes `Capability.State` and
`FrameAllocator.State`. Object identifiers are never reused: `issued` is a
monotonic history. Releasing an object removes its live binding and every
installed capability for it. Access also checks the current binding, so even
an out-of-state copy of an old capability cannot name a later occupant.
-/

namespace LeanOS.MemoryLifecycle

set_option linter.unusedSimpArgs false

open LeanOS
abbrev ObjectId := Capability.ObjectId
abbrev SubjectId := Capability.SubjectId
abbrev SlotId := Capability.SlotId
abbrev FrameId := FrameAllocator.FrameId

structure State where
  capabilities : Capability.State
  allocator : FrameAllocator.State
  binding : ObjectId → Option FrameId
  issued : ObjectId → Bool

/-- Live objects, installed capabilities, bindings, and allocator ownership agree. -/
def WellFormed (state : State) : Prop :=
  Capability.WellFormed state.capabilities ∧
  (∀ subject slot cap, state.capabilities.slots subject slot = some cap →
    ∃ frame, state.binding cap.object = some frame ∧
      FrameAllocator.IsOwnedBy state.allocator frame cap.object) ∧
  (∀ object frame, state.binding object = some frame →
    state.capabilities.objects object = true ∧
      FrameAllocator.IsOwnedBy state.allocator frame object ∧ state.issued object = true) ∧
  (∀ object, state.capabilities.objects object = true → ∃ frame,
    state.binding object = some frame)

inductive AllocationError where
  | invalidSubject | occupiedSlot | objectAlreadyIssued | exhausted
  deriving BEq, DecidableEq, Repr

inductive ReleaseError where
  | invalidSubject | staleSlot | missingRevoke | retiredObject | allocatorMismatch
  deriving BEq, DecidableEq, Repr

inductive AccessError where
  | invalidSubject | staleSlot | missingRight | retiredObject | allocatorMismatch
  deriving BEq, DecidableEq, Repr

inductive Result (ε : Type) where | accepted | rejected (reason : ε)
  deriving DecidableEq, Repr

structure Outcome (ε : Type) where
  state : State
  result : Result ε

def reject (state : State) (reason : ε) : Outcome ε :=
  { state, result := .rejected reason }

def setObject (objects : ObjectId → Bool) (object : ObjectId) (live : Bool) :=
  fun candidate => if candidate = object then live else objects candidate

def setBinding (binding : ObjectId → Option FrameId) (object : ObjectId)
    (frame : Option FrameId) :=
  fun candidate => if candidate = object then frame else binding candidate

def setIssued (issued : ObjectId → Bool) (object : ObjectId) :=
  fun candidate => if candidate = object then true else issued candidate

def retireCapabilities (state : Capability.State) (object : ObjectId) : Capability.State :=
  { state with
    objects := setObject state.objects object false
    slots := fun subject slot =>
      match state.slots subject slot with
      | some cap => if cap.object = object then none else some cap
      | none => none }

def activateObject (state : Capability.State) (object : ObjectId) : Capability.State :=
  { state with objects := setObject state.objects object true }

/-- Allocate a free frame to a never-before-issued object and install its root cap. -/
def allocate (state : State) (object : ObjectId) (subject : SubjectId)
    (slot : SlotId) : Outcome AllocationError :=
  if state.capabilities.subjects subject != true then reject state .invalidSubject
  else if (state.capabilities.slots subject slot).isSome then reject state .occupiedSlot
  else if state.issued object then reject state .objectAlreadyIssued
  else match FrameAllocator.allocate state.allocator object with
    | .error .exhausted => reject state .exhausted
    | .ok allocation =>
      { state :=
          { capabilities := Capability.install (activateObject state.capabilities object)
              subject slot { object, rights := Capability.allRights }
            allocator := allocation.state
            binding := setBinding state.binding object (some allocation.frame)
            issued := setIssued state.issued object }
        result := .accepted }

/-- Retire the object named by a revoke-capability and release its frame. -/
def release (state : State) (subject : SubjectId) (slot : SlotId) :
    Outcome ReleaseError :=
  match Capability.lookup state.capabilities subject slot with
  | .invalidSubject => reject state .invalidSubject
  | .staleSlot => reject state .staleSlot
  | .found cap =>
      if !cap.rights.revoke then reject state .missingRevoke
      else match state.binding cap.object with
        | none => reject state .retiredObject
        | some frame => match FrameAllocator.release state.allocator cap.object frame with
          | .error .invalidRelease => reject state .allocatorMismatch
          | .ok allocator =>
            { state :=
                { capabilities := retireCapabilities state.capabilities cap.object
                  allocator := allocator
                  binding := setBinding state.binding cap.object none
                  issued := state.issued }
              result := .accepted }

/-- Validate a capability against the current live binding and allocator owner. -/
def authorize (state : State) (subject : SubjectId) (slot : SlotId)
    (right : Capability.Right) : Except AccessError FrameId :=
  match Capability.lookup state.capabilities subject slot with
  | .invalidSubject => .error .invalidSubject
  | .staleSlot => .error .staleSlot
  | .found cap =>
      if !Capability.permits cap.rights right then .error .missingRight
      else match state.binding cap.object with
        | none => .error .retiredObject
        | some frame =>
          if state.allocator.status frame = .owned cap.object then .ok frame
          else .error .allocatorMismatch

theorem allocate_rejected_unchanged (state : State) (object subject slot) (reason)
    (h : (allocate state object subject slot).result = .rejected reason) :
    (allocate state object subject slot).state = state := by
  simp only [allocate] at h ⊢
  split <;> try simp_all [reject]
  split <;> try simp_all [reject]
  split <;> try simp_all [reject]
  split <;> simp_all [reject]

theorem release_rejected_unchanged (state : State) (subject slot) (reason)
    (h : (release state subject slot).result = .rejected reason) :
    (release state subject slot).state = state := by
  simp only [release] at h ⊢
  split <;> try simp_all [reject]
  next cap =>
    split <;> try simp_all [reject]
    split <;> try simp_all [reject]
    next frame => split <;> simp_all [reject]

/-- Successful allocation binds only the requested fresh object. -/
theorem allocated_binding (state : State) (object subject slot)
    (ha : (allocate state object subject slot).result = .accepted) :
    ∃ frame, (allocate state object subject slot).state.binding object = some frame ∧
      FrameAllocator.IsOwnedBy (allocate state object subject slot).state.allocator
        frame object := by
  simp only [allocate] at ha ⊢
  split <;> simp_all [reject]
  split <;> simp_all [reject]
  split <;> simp_all [reject]
  next =>
    split <;> simp_all [reject]
    next allocation hresult =>
      refine ⟨allocation.frame, by simp [setBinding], ?_⟩
      exact FrameAllocator.allocated_is_owned state.allocator object allocation hresult

theorem allocated_not_reserved (state : State) (object subject slot)
    (ha : (allocate state object subject slot).result = .accepted) :
    ∃ frame, (allocate state object subject slot).state.binding object = some frame ∧
      ¬FrameAllocator.IsReserved (allocate state object subject slot).state.allocator frame := by
  obtain ⟨frame, hbind, howned⟩ := allocated_binding state object subject slot ha
  exact ⟨frame, hbind, fun hr => FrameAllocator.reserved_not_owned
    (allocate state object subject slot).state.allocator frame object hr howned⟩

/-- Issued IDs are monotonic, so an accepted allocation can never reuse one. -/
theorem allocation_requires_unissued (state : State) (object subject slot)
    (ha : (allocate state object subject slot).result = .accepted) :
    state.issued object = false := by
  simp only [allocate] at ha
  split at ha <;> try contradiction
  split at ha <;> try contradiction
  split at ha <;> try contradiction
  next hissued => simp_all

/-- No operation can allocate an identifier once its lifetime has been issued. -/
theorem issued_identifier_never_reallocated (state : State) (object subject slot)
    (hissued : state.issued object = true) :
    (allocate state object subject slot).result ≠ .accepted := by
  simp only [allocate]
  split <;> simp_all [reject]
  split <;> simp_all [reject]

/-- Allocation installs full root authority for exactly the requested object. -/
theorem allocated_root_capability (state : State) (object subject slot)
    (ha : (allocate state object subject slot).result = .accepted) :
    (allocate state object subject slot).state.capabilities.slots subject slot =
      some { object, rights := Capability.allRights } := by
  simp only [allocate] at ha ⊢
  split <;> simp_all [reject]
  split <;> simp_all [reject]
  split <;> simp_all [reject]
  split <;> simp_all [reject, Capability.install]

/-- The allocator representation makes successful ownership exclusive. -/
theorem allocated_owner_exclusive (state : State) (object subject slot frame owner)
    (ha : (allocate state object subject slot).result = .accepted)
    (hbinding : (allocate state object subject slot).state.binding object = some frame)
    (howner : FrameAllocator.IsOwnedBy
      (allocate state object subject slot).state.allocator frame owner) :
    owner = object := by
  obtain ⟨bound, hbound, hobject⟩ := allocated_binding state object subject slot ha
  rw [hbinding] at hbound
  injection hbound with hframe
  subst bound
  exact FrameAllocator.ownership_exclusive _ _ _ _ howner hobject

/-- Release never clears the monotonic identifier-lifetime history. -/
theorem release_preserves_issued (state : State) (subject slot) :
    (release state subject slot).state.issued = state.issued := by
  simp only [release]
  split <;> try rfl
  next cap =>
    split <;> try rfl
    split <;> try rfl
    next frame => split <;> rfl

/-- Release removes every installed capability for the retired object. -/
theorem release_invalidates (state : State) (subject slot)
    (ha : (release state subject slot).result = .accepted) :
    ∃ object, (release state subject slot).state.binding object = none ∧
      (release state subject slot).state.capabilities.objects object = false ∧
      ∀ candidate candidateSlot cap,
        (release state subject slot).state.capabilities.slots candidate candidateSlot = some cap →
        cap.object ≠ object := by
  simp only [release] at ha ⊢
  split <;> simp_all [reject]
  next cap hlookup =>
    split <;> simp_all [reject]
    split <;> simp_all [reject]
    next frame =>
      split <;> simp_all [reject]
      next allocator =>
        refine ⟨cap.object, by simp [setBinding], by simp [retireCapabilities, setObject], ?_⟩
        intro candidate candidateSlot found hslot heq
        cases hsource : state.capabilities.slots candidate candidateSlot with
        | none => simp [retireCapabilities, hsource] at hslot
        | some existing =>
          by_cases hretired : existing.object = cap.object
          · simp [retireCapabilities, hsource, hretired] at hslot
          · have hfound : existing = found := by
              simpa [retireCapabilities, hsource, hretired] using hslot
            subst found
            exact hretired heq

/-- Any authorized access names the allocator's current owner binding. -/
theorem authorized_current_binding (state : State) (subject slot right frame)
    (h : authorize state subject slot right = .ok frame) :
    ∃ cap, state.capabilities.slots subject slot = some cap ∧
      state.binding cap.object = some frame ∧
      FrameAllocator.IsOwnedBy state.allocator frame cap.object := by
  simp only [authorize] at h
  split at h <;> try contradiction
  next cap hlookup =>
    split at h <;> try contradiction
    split at h <;> try contradiction
    next bound hbinding =>
      split at h <;> try contradiction
      injection h with hframe
      subst frame
      exact ⟨cap, Capability.lookup_found_slot state.capabilities subject slot cap hlookup,
        hbinding, by assumption⟩

private def subjects : SubjectId → Bool := fun subject => subject < 3
private def emptyCaps : Capability.State :=
  { subjects, objects := fun _ => false, slots := fun _ _ => none }
private def oneFrame : FrameAllocator.State :=
  { frames := [4], status := fun frame => if frame = 4 then .free else .reserved }
private def initial : State :=
  { capabilities := emptyCaps, allocator := oneFrame
    binding := fun _ => none, issued := fun _ => false }
private def delegated : State :=
  (Capability.copy (allocate initial 10 0 0).state.capabilities
    0 0 1 0 (Capability.oneRight .read)).state |> fun caps =>
    { (allocate initial 10 0 0).state with capabilities := caps }
private def released : State := (release delegated 0 0).state
private def reused : State := (allocate released 11 2 0).state

example : (release delegated 0 0).result = .accepted := by native_decide
example : reused.binding 11 = some 4 := by native_decide
example : authorize reused 1 0 .read = .error .staleSlot := by rfl
example : (allocate released 10 2 0).result = .rejected .objectAlreadyIssued := by native_decide

end LeanOS.MemoryLifecycle
