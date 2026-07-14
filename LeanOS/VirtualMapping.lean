import LeanOS.MemoryLifecycle

/-!
# Capability-bounded virtual mappings

This finite, sequential model adds subject-owned address spaces and virtual
pages to `MemoryLifecycle`.  Mappings contain only read/write permission,
are created from a current capability, and translation revalidates the live
object binding and allocator owner.  Release clears the mapping relation,
which is conservative but makes stale translations impossible.
-/
namespace LeanOS.VirtualMapping

set_option linter.unusedSimpArgs false

open LeanOS
abbrev SubjectId := Capability.SubjectId
abbrev SlotId := Capability.SlotId
abbrev ObjectId := Capability.ObjectId
abbrev FrameId := FrameAllocator.FrameId
abbrev AddressSpaceId := Nat
abbrev VirtualPage := Nat

inductive Access where | read | write
  deriving BEq, DecidableEq, Repr

structure Permissions where
  read : Bool := false
  write : Bool := false
  deriving BEq, DecidableEq, Repr

def Permissions.nonempty (permissions : Permissions) : Bool :=
  permissions.read || permissions.write

def Permissions.permits (permissions : Permissions) : Access → Bool
  | .read => permissions.read
  | .write => permissions.write

def Access.right : Access → Capability.Right
  | .read => .read
  | .write => .write

structure Mapping where
  object : ObjectId
  permissions : Permissions
  deriving BEq, DecidableEq, Repr

structure State where
  memory : MemoryLifecycle.State
  owner : AddressSpaceId → Option SubjectId
  mappings : AddressSpaceId → VirtualPage → Option Mapping

/-- All mappings belong to a valid subject, carry authority that subject has,
and name the allocator's current live object/frame binding. -/
def WellFormed (state : State) : Prop :=
  (∀ addressSpace subject, state.owner addressSpace = some subject →
    state.memory.capabilities.subjects subject = true) ∧
  ∀ addressSpace page mapping,
    state.mappings addressSpace page = some mapping →
    ∃ subject frame, state.owner addressSpace = some subject ∧
      mapping.permissions.nonempty = true ∧
      state.memory.binding mapping.object = some frame ∧
      FrameAllocator.IsOwnedBy state.memory.allocator frame mapping.object ∧
      (mapping.permissions.read = true →
        Capability.HasAuthority state.memory.capabilities subject mapping.object .read) ∧
      (mapping.permissions.write = true →
        Capability.HasAuthority state.memory.capabilities subject mapping.object .write)

inductive MapError where
  | invalidAddressSpace | notOwner | staleSlot | occupiedPage | emptyPermissions
  | rightsNotSubset | kindMismatch | retiredObject | allocatorMismatch
  deriving BEq, DecidableEq, Repr

inductive UnmapError where | invalidAddressSpace | notOwner | unmappedPage
  deriving BEq, DecidableEq, Repr

inductive TranslationError where
  | invalidAddressSpace | notOwner | unmappedPage | missingPermission
  | kindMismatch | retiredObject | allocatorMismatch
  deriving BEq, DecidableEq, Repr

inductive Result (ε : Type) where | accepted | rejected (reason : ε)
  deriving DecidableEq, Repr

structure Outcome (ε : Type) where
  state : State
  result : Result ε

def reject (state : State) (reason : ε) : Outcome ε :=
  { state, result := .rejected reason }

def setMapping (state : State) (addressSpace : AddressSpaceId)
    (page : VirtualPage) (mapping : Option Mapping) : State :=
  { state with mappings := fun candidate candidatePage =>
      if candidate = addressSpace ∧ candidatePage = page then mapping
      else state.mappings candidate candidatePage }

def clearMappings (state : State) : State :=
  { state with mappings := fun _ _ => none }

def permissionsSubset (permissions : Permissions) (rights : Capability.Rights) : Bool :=
  (!permissions.read || rights.read) && (!permissions.write || rights.write)

/-- Install one mapping using the actor's current capability authority. -/
def map (state : State) (actor : SubjectId) (slot : SlotId)
    (addressSpace : AddressSpaceId) (page : VirtualPage)
    (permissions : Permissions) : Outcome MapError :=
  match state.owner addressSpace with
  | none => reject state .invalidAddressSpace
  | some owner => if owner != actor then reject state .notOwner else
    match Capability.lookup state.memory.capabilities actor slot with
    | .invalidSubject => reject state .notOwner
    | .staleSlot => reject state .staleSlot
    | .found cap =>
      if cap.kind != .memory then reject state .kindMismatch
      else if (state.mappings addressSpace page).isSome then reject state .occupiedPage
      else if !permissions.nonempty then reject state .emptyPermissions
      else if !permissionsSubset permissions cap.rights then reject state .rightsNotSubset
      else match state.memory.binding cap.object with
      | none => reject state .retiredObject
      | some frame =>
        if state.memory.allocator.status frame ≠ .owned cap.object then
          reject state .allocatorMismatch
        else { state := setMapping state addressSpace page
                 (some { object := cap.object, permissions }), result := .accepted }

/-- Remove one mapping; only the address-space owner may mutate it. -/
def unmap (state : State) (actor : SubjectId) (addressSpace : AddressSpaceId)
    (page : VirtualPage) : Outcome UnmapError :=
  match state.owner addressSpace with
  | none => reject state .invalidAddressSpace
  | some owner => if owner != actor then reject state .notOwner
    else if (state.mappings addressSpace page).isNone then reject state .unmappedPage
    else { state := setMapping state addressSpace page none, result := .accepted }

/-- Translate only in an address space owned by the calling subject. -/
def translate (state : State) (actor : SubjectId) (addressSpace : AddressSpaceId)
    (page : VirtualPage) (access : Access) : Except TranslationError FrameId :=
  match state.owner addressSpace with
  | none => .error .invalidAddressSpace
  | some owner => if owner != actor then .error .notOwner else
    match state.mappings addressSpace page with
    | none => .error .unmappedPage
    | some mapping => if !mapping.permissions.permits access then .error .missingPermission
      else if state.memory.capabilities.kinds mapping.object != some .memory then
        .error .kindMismatch
      else match state.memory.binding mapping.object with
      | none => .error .retiredObject
      | some frame => if state.memory.allocator.status frame = .owned mapping.object
        then .ok frame else .error .allocatorMismatch

/-- Release is composed atomically with conservative invalidation of mappings. -/
def release (state : State) (subject : SubjectId) (slot : SlotId) :
    Outcome MemoryLifecycle.ReleaseError :=
  let outcome := MemoryLifecycle.release state.memory subject slot
  match outcome.result with
  | .rejected reason => reject state reason
  | .accepted =>
      { state := clearMappings { state with memory := outcome.state }, result := .accepted }

theorem map_rejected_unchanged (state : State) actor slot addressSpace page permissions reason
    (h : (map state actor slot addressSpace page permissions).result = .rejected reason) :
    (map state actor slot addressSpace page permissions).state = state := by
  simp only [map] at h ⊢
  split <;> try simp_all [reject]
  next owner =>
    split <;> try simp_all [reject]
    split <;> try simp_all [reject]
    next cap => split <;> try simp_all [reject]
                split <;> try simp_all [reject]
                split <;> try simp_all [reject]
                split <;> try simp_all [reject]
                split <;> try simp_all [reject]
                next frame => split <;> simp_all [reject]

theorem unmap_rejected_unchanged (state : State) actor addressSpace page reason
    (h : (unmap state actor addressSpace page).result = .rejected reason) :
    (unmap state actor addressSpace page).state = state := by
  simp only [unmap] at h ⊢
  split <;> try simp_all [reject]
  split <;> try simp_all [reject]
  split <;> simp_all [reject]

theorem release_rejected_unchanged (state : State) subject slot reason
    (h : (release state subject slot).result = .rejected reason) :
    (release state subject slot).state = state := by
  simp only [release] at h ⊢
  split <;> simp_all [reject]

/-- A successful translation returns the current frame owned by its live object. -/
theorem translated_current_frame (state : State) actor addressSpace page access frame
    (h : translate state actor addressSpace page access = .ok frame) :
    ∃ mapping, state.mappings addressSpace page = some mapping ∧
      state.memory.binding mapping.object = some frame ∧
      FrameAllocator.IsOwnedBy state.memory.allocator frame mapping.object := by
  simp only [translate] at h
  split at h <;> try contradiction
  next owner => split at h <;> try contradiction
                split at h <;> try contradiction
                next mapping hmapping =>
                  split at h <;> try contradiction
                  split at h <;> try contradiction
                  split at h <;> try contradiction
                  next bound hbinding =>
                    split at h <;> try contradiction
                    injection h with heq
                    subst bound
                    exact ⟨mapping, hmapping, hbinding, by assumption⟩

/-- Translation is confined to the selected address-space/page lookup. -/
theorem translated_selected_mapping (state : State) actor addressSpace page access frame
    (h : translate state actor addressSpace page access = .ok frame) :
    ∃ mapping, state.owner addressSpace = some actor ∧
      state.mappings addressSpace page = some mapping ∧
      mapping.permissions.permits access = true := by
  simp only [translate] at h
  split at h <;> try contradiction
  next owner howner =>
    split at h <;> try contradiction
    next hsame =>
      have : owner = actor := by simp_all
      subst owner
      split at h <;> try contradiction
      next mapping hmapping =>
        split at h <;> try contradiction
        exact ⟨mapping, howner, hmapping, by simp_all⟩

/-- In a well-formed state, every successful translation remains backed by the
current read/write authority of the address-space owner. -/
theorem translated_capability_authority (state : State) actor addressSpace page access frame
    (hstate : WellFormed state)
    (h : translate state actor addressSpace page access = .ok frame) :
    ∃ mapping, state.mappings addressSpace page = some mapping ∧
      Capability.HasAuthority state.memory.capabilities actor mapping.object access.right := by
  obtain ⟨mapping, howner, hmapping, hpermission⟩ :=
    translated_selected_mapping state actor addressSpace page access frame h
  obtain ⟨subject, _bound, hsubject, _nonempty, _binding, _owned, hread, hwrite⟩ :=
    hstate.2 addressSpace page mapping hmapping
  have : subject = actor := by simp_all
  subst subject
  refine ⟨mapping, hmapping, ?_⟩
  cases access with
  | read => exact hread hpermission
  | write => exact hwrite hpermission

/-- A different subject cannot translate another subject's address space. -/
theorem other_subject_cannot_translate (state : State) owner actor addressSpace page access
    (howner : state.owner addressSpace = some owner) (hne : actor ≠ owner) :
    ∃ reason, translate state actor addressSpace page access = .error reason := by
  refine ⟨.notOwner, ?_⟩
  have hne' : owner ≠ actor := Ne.symm hne
  simp [translate, howner, hne']

/-- Accepted map permission is no greater than the actor's pre-state cap. -/
theorem map_permission_authority (state : State) actor slot addressSpace page permissions
    (h : (map state actor slot addressSpace page permissions).result = .accepted) :
    (permissions.read = true →
      ∃ object, Capability.HasAuthority state.memory.capabilities actor object .read) ∧
    (permissions.write = true →
      ∃ object, Capability.HasAuthority state.memory.capabilities actor object .write) := by
  simp only [map] at h
  split at h <;> try contradiction
  next owner => split at h <;> try contradiction
                split at h <;> try contradiction
                next cap hlookup =>
                  split at h <;> try contradiction
                  split at h <;> try contradiction
                  split at h <;> try contradiction
                  split at h <;> try contradiction
                  next hsubset =>
                    split at h <;> try contradiction
                    next frame =>
                      split at h <;> try contradiction
                      have hslot := Capability.lookup_found_slot
                        state.memory.capabilities actor slot cap hlookup
                      constructor <;> intro hp
                      · exact ⟨cap.object, slot, cap, hslot, rfl, by
                          simp [permissionsSubset] at hsubset
                          simp [Capability.hasRight, Capability.permits, hp, hsubset]⟩
                      · exact ⟨cap.object, slot, cap, hslot, rfl, by
                          simp [permissionsSubset] at hsubset
                          simp [Capability.hasRight, Capability.permits, hp, hsubset]⟩

theorem map_preserves_wellFormed (state : State) actor slot addressSpace page permissions
    (hstate : WellFormed state) :
    WellFormed (map state actor slot addressSpace page permissions).state := by
  simp only [map]
  split <;> try simpa [reject] using hstate
  next owner howner =>
    split <;> try simpa [reject] using hstate
    next hactor =>
      split <;> try simpa [reject] using hstate
      next cap hlookup =>
        split <;> try simpa [reject] using hstate
        split <;> try simpa [reject] using hstate
        split <;> try simpa [reject] using hstate
        next hnonempty =>
          split <;> try simpa [reject] using hstate
          next hsubset =>
            split <;> try simpa [reject] using hstate
            next frame hbinding =>
              split
              · simpa [reject] using hstate
              next howned =>
              change WellFormed (setMapping state addressSpace page
                (some { object := cap.object, permissions }))
              rcases hstate with ⟨howners, hmappings⟩
              refine ⟨?_, ?_⟩
              · simpa [setMapping] using howners
              · intro candidate candidatePage mapping hmapped
                by_cases htarget : candidate = addressSpace ∧ candidatePage = page
                · rcases htarget with ⟨rfl, rfl⟩
                  have heq : mapping = { object := cap.object, permissions } := by
                    symm
                    simpa [setMapping] using hmapped
                  subst mapping
                  have heqOwner : owner = actor := by simp_all
                  subst owner
                  have hnonempty' : permissions.nonempty = true := by simp_all
                  have hstatus : state.memory.allocator.status frame = .owned cap.object := by
                    simpa using howned
                  simp [setMapping]
                  refine ⟨actor, howner, hnonempty', frame, hbinding,
                    (show FrameAllocator.IsOwnedBy state.memory.allocator frame cap.object from hstatus),
                    ?_, ?_⟩
                  · intro hp
                    exact ⟨slot, cap,
                      Capability.lookup_found_slot state.memory.capabilities actor slot cap hlookup,
                      rfl, by
                        simp [permissionsSubset] at hsubset
                        show cap.rights.read = true
                        exact hsubset.1 hp⟩
                  · intro hp
                    exact ⟨slot, cap,
                      Capability.lookup_found_slot state.memory.capabilities actor slot cap hlookup,
                      rfl, by
                        simp [permissionsSubset] at hsubset
                        show cap.rights.write = true
                        exact hsubset.2 hp⟩
                · simpa [setMapping] using hmappings candidate candidatePage mapping
                    (by simpa [setMapping, htarget] using hmapped)

theorem unmap_preserves_wellFormed (state : State) actor addressSpace page
    (hstate : WellFormed state) : WellFormed (unmap state actor addressSpace page).state := by
  simp only [unmap]
  split <;> try simpa [reject] using hstate
  split <;> try simpa [reject] using hstate
  split <;> try simpa [reject] using hstate
  rcases hstate with ⟨howners, hmappings⟩
  refine ⟨by simpa [setMapping] using howners, ?_⟩
  intro candidate candidatePage mapping hmapped
  by_cases htarget : candidate = addressSpace ∧ candidatePage = page
  · simp [setMapping, htarget] at hmapped
  · exact hmappings candidate candidatePage mapping
      (by simpa [setMapping, htarget] using hmapped)

theorem memory_release_preserves_subjects (memory : MemoryLifecycle.State) subject slot :
    (MemoryLifecycle.release memory subject slot).state.capabilities.subjects =
      memory.capabilities.subjects := by
  simp only [MemoryLifecycle.release]
  split <;> try rfl
  next cap =>
    split <;> try rfl
    split <;> try rfl
    split <;> try rfl
    next frame => split <;> rfl

theorem release_preserves_wellFormed (state : State) subject slot
    (hstate : WellFormed state) : WellFormed (release state subject slot).state := by
  simp only [release]
  split
  · simpa [reject] using hstate
  · constructor
    · intro addressSpace candidate howner
      change (MemoryLifecycle.release state.memory subject slot).state.capabilities.subjects
        candidate = true
      rw [memory_release_preserves_subjects]
      exact hstate.1 addressSpace candidate howner
    · intro addressSpace page mapping hmapped
      simp [clearMappings] at hmapped

private def subjects : SubjectId → Bool := fun subject => subject < 3
private def caps : Capability.State :=
  { subjects, objects := fun object => object = 10
    kinds := fun object => if object = 10 then some .memory else none
    slots := fun subject slot =>
      if subject = 0 ∧ slot = 0 then
        some (Capability.Capability.mk 10 .memory Capability.allRights)
      else none }
private def allocator : FrameAllocator.State :=
  { frames := [4], status := fun frame => if frame = 4 then .owned 10 else .reserved }
private def memory : MemoryLifecycle.State :=
  { capabilities := caps, allocator, binding := fun object => if object = 10 then some 4 else none
    issued := fun object => object = 10 }
private def initial : State :=
  { memory, owner := fun space => if space = 5 then some 0 else if space = 6 then some 1 else none
    mappings := fun _ _ => none }
private def readOnly := (map initial 0 0 5 7 { read := true }).state
private def readRights : Capability.Rights := { read := true }
private def readSlots (subject : SubjectId) (slot : SlotId) : Option Capability.Capability :=
  if subject = 0 ∧ slot = 0 then
    some (Capability.Capability.mk 10 .memory readRights)
  else none
private def readCapMemory : MemoryLifecycle.State :=
  { memory with capabilities :=
      { caps with slots := readSlots } }
private def readCapInitial : State := { initial with memory := readCapMemory }
private def retired : State := (release readOnly 0 0).state
private def reused : State :=
  { retired with memory := (MemoryLifecycle.allocate retired.memory 11 0 0).state }

example : translate readOnly 0 5 7 .read = .ok 4 := by rfl
example : translate readOnly 0 5 7 .write = .error .missingPermission := by rfl
example : (map readCapInitial 0 0 5 8 { write := true }).result =
    .rejected .rightsNotSubset := by native_decide
example : (map readOnly 0 0 5 7 { read := true }).result = .rejected .occupiedPage := by native_decide
example : (map initial 1 0 5 7 { read := true }).result = .rejected .notOwner := by native_decide
example : translate readOnly 1 5 7 .read = .error .notOwner := by rfl
example : (unmap readOnly 0 5 7).result = .accepted := by native_decide
example : (MemoryLifecycle.allocate retired.memory 11 0 0).result = .accepted := by native_decide
example : reused.memory.binding 11 = some 4 := by native_decide
example : translate reused 0 5 7 .read = .error .unmappedPage := by rfl

end LeanOS.VirtualMapping
