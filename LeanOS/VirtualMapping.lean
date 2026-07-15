import LeanOS.MemoryLifecycle

/-!
# Capability-bounded virtual mappings

This finite, sequential model adds subject-owned address spaces and virtual
pages to `MemoryLifecycle`.  Mappings contain only read/write permission,
are created from a current capability, and translation revalidates the live
object binding and allocator owner. Address-space identifiers are kernel
objects with monotonic issuance, and release invalidates only mappings of the
retired memory object.
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
  issuedAddressSpace : AddressSpaceId → Bool

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

/-- The lifecycle composition adds registry type safety, monotonic identity,
and an exact correspondence between live address-space objects and owners. -/
def LifecycleWellFormed (state : State) : Prop :=
  WellFormed state ∧ Capability.WellFormed state.memory.capabilities ∧
  (∀ addressSpace subject, state.owner addressSpace = some subject →
    state.memory.capabilities.objects addressSpace = true ∧
    state.memory.capabilities.kinds addressSpace = some .addressSpace ∧
    state.issuedAddressSpace addressSpace = true ∧
    state.memory.issued addressSpace = true ∧
    Capability.HasAuthority state.memory.capabilities subject addressSpace .revoke) ∧
  (∀ addressSpace, state.memory.capabilities.objects addressSpace = true →
    state.memory.capabilities.kinds addressSpace = some .addressSpace →
    ∃ subject, state.owner addressSpace = some subject)

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

def clearAddressSpaceMappings (state : State) (addressSpace : AddressSpaceId) : State :=
  { state with mappings := fun candidate page =>
      if candidate = addressSpace then none else state.mappings candidate page }

def invalidateObjectMappings (state : State) (object : ObjectId) : State :=
  { state with mappings := fun addressSpace page =>
      match state.mappings addressSpace page with
      | some mapping => if mapping.object = object then none else some mapping
      | none => none }

def setOwner (owners : AddressSpaceId → Option SubjectId) (addressSpace : AddressSpaceId)
    (owner : Option SubjectId) :=
  fun candidate => if candidate = addressSpace then owner else owners candidate

def setIssuedAddressSpace (issued : AddressSpaceId → Bool) (addressSpace : AddressSpaceId) :=
  fun candidate => if candidate = addressSpace then true else issued candidate

def activateAddressSpace (state : Capability.State) (object : ObjectId) : Capability.State :=
  { state with
    objects := MemoryLifecycle.setObject state.objects object true
    kinds := fun candidate => if candidate = object then some .addressSpace else state.kinds candidate }

def retireAddressSpace (state : Capability.State) (object : ObjectId) : Capability.State :=
  MemoryLifecycle.retireCapabilities state object

def addressSpaceRootRights : Capability.Rights := { grant := true, revoke := true }

inductive CreateError where
  | invalidSubject | occupiedSlot | identifierAlreadyIssued | identifierLive
  deriving BEq, DecidableEq, Repr

inductive DestroyError where
  | invalidSubject | staleSlot | kindMismatch | missingRevoke
  | invalidAddressSpace | notOwner
  deriving BEq, DecidableEq, Repr

/-- Create one never-before-issued address-space object and its root authority. -/
def createAddressSpace (state : State) (addressSpace : AddressSpaceId)
    (subject : SubjectId) (slot : SlotId) : Outcome CreateError :=
  if state.memory.capabilities.subjects subject != true then reject state .invalidSubject
  else if (state.memory.capabilities.slots subject slot).isSome then reject state .occupiedSlot
  else if state.issuedAddressSpace addressSpace || state.memory.issued addressSpace then
    reject state .identifierAlreadyIssued
  else if state.memory.capabilities.objects addressSpace then reject state .identifierLive
  else
    let capabilities := Capability.installRoot
      (activateAddressSpace state.memory.capabilities addressSpace) subject slot
      addressSpace .addressSpace addressSpaceRootRights
    { state := clearAddressSpaceMappings
        { state with
          memory := { state.memory with
            capabilities
            issued := MemoryLifecycle.setIssued state.memory.issued addressSpace }
          owner := setOwner state.owner addressSpace (some subject)
          issuedAddressSpace := setIssuedAddressSpace state.issuedAddressSpace addressSpace }
        addressSpace
      result := .accepted }

/-- Destroy requires the owner's live revoke-capability for this address space. -/
def destroyAddressSpace (state : State) (subject : SubjectId) (slot : SlotId) :
    Outcome DestroyError :=
  match Capability.lookup state.memory.capabilities subject slot with
  | .invalidSubject => reject state .invalidSubject
  | .staleSlot => reject state .staleSlot
  | .found cap =>
      if cap.kind != .addressSpace then reject state .kindMismatch
      else if !cap.rights.revoke then reject state .missingRevoke
      else match state.owner cap.object with
      | none => reject state .invalidAddressSpace
      | some owner => if owner != subject then reject state .notOwner
        else
          { state := clearAddressSpaceMappings
              { state with
                memory := { state.memory with
                  capabilities := retireAddressSpace state.memory.capabilities cap.object }
                owner := setOwner state.owner cap.object none }
              cap.object
            result := .accepted }

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

/-- Release atomically invalidates exactly mappings naming the retired object. -/
def release (state : State) (subject : SubjectId) (slot : SlotId) :
    Outcome MemoryLifecycle.ReleaseError :=
  let outcome := MemoryLifecycle.release state.memory subject slot
  match outcome.result with
  | .rejected reason => reject state reason
  | .accepted => match Capability.lookup state.memory.capabilities subject slot with
    | .found cap =>
      { state := invalidateObjectMappings { state with memory := outcome.state } cap.object
        result := .accepted }
    | _ => { state := { state with memory := outcome.state }, result := .accepted }

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
  split <;> try simp_all [reject]
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

theorem map_preserves_lifecycleWellFormed (state : State) actor slot addressSpace page permissions
    (hstate : LifecycleWellFormed state) :
    LifecycleWellFormed (map state actor slot addressSpace page permissions).state := by
  rcases hstate with ⟨hmap, hcaps, howners, hlive⟩
  have hmemory : (map state actor slot addressSpace page permissions).state.memory =
      state.memory := by
    simp only [map]
    split <;> try rfl
    split <;> try rfl
    split <;> try rfl
    next cap =>
      split <;> try rfl
      split <;> try rfl
      split <;> try rfl
      split <;> try rfl
      split <;> try rfl
      next frame => split <;> rfl
  have howner : (map state actor slot addressSpace page permissions).state.owner =
      state.owner := by
    simp only [map]
    split <;> try rfl
    split <;> try rfl
    split <;> try rfl
    next cap =>
      split <;> try rfl
      split <;> try rfl
      split <;> try rfl
      split <;> try rfl
      split <;> try rfl
      next frame => split <;> rfl
  have hissued : (map state actor slot addressSpace page permissions).state.issuedAddressSpace =
      state.issuedAddressSpace := by
    simp only [map]
    split <;> try rfl
    split <;> try rfl
    split <;> try rfl
    next cap =>
      split <;> try rfl
      split <;> try rfl
      split <;> try rfl
      split <;> try rfl
      split <;> try rfl
      next frame => split <;> rfl
  refine ⟨map_preserves_wellFormed state actor slot addressSpace page permissions hmap, ?_⟩
  simpa [hmemory, howner, hissued] using And.intro hcaps (And.intro howners hlive)

theorem unmap_preserves_lifecycleWellFormed (state : State) actor addressSpace page
    (hstate : LifecycleWellFormed state) :
    LifecycleWellFormed (unmap state actor addressSpace page).state := by
  rcases hstate with ⟨hmap, hcaps, howners, hlive⟩
  have hmemory : (unmap state actor addressSpace page).state.memory = state.memory := by
    simp only [unmap]
    split <;> try rfl
    split <;> try rfl
    split <;> rfl
  have howner : (unmap state actor addressSpace page).state.owner = state.owner := by
    simp only [unmap]
    split <;> try rfl
    split <;> try rfl
    split <;> rfl
  have hissued : (unmap state actor addressSpace page).state.issuedAddressSpace =
      state.issuedAddressSpace := by
    simp only [unmap]
    split <;> try rfl
    split <;> try rfl
    split <;> rfl
  refine ⟨unmap_preserves_wellFormed state actor addressSpace page hmap, ?_⟩
  simpa [hmemory, howner, hissued] using And.intro hcaps (And.intro howners hlive)

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

theorem create_rejected_unchanged (state : State) addressSpace subject slot reason
    (h : (createAddressSpace state addressSpace subject slot).result = .rejected reason) :
    (createAddressSpace state addressSpace subject slot).state = state := by
  simp only [createAddressSpace] at h ⊢
  split <;> simp_all [reject]
  split <;> simp_all [reject]
  split <;> simp_all [reject]
  split <;> simp_all [reject]

theorem destroy_rejected_unchanged (state : State) subject slot reason
    (h : (destroyAddressSpace state subject slot).result = .rejected reason) :
    (destroyAddressSpace state subject slot).state = state := by
  simp only [destroyAddressSpace] at h ⊢
  split <;> try simp_all [reject]
  next cap =>
    split <;> try simp_all [reject]
    split <;> try simp_all [reject]
    split <;> try simp_all [reject]
    split <;> simp_all [reject]

theorem cleared_address_space (state : State) addressSpace page :
    (clearAddressSpaceMappings state addressSpace).mappings addressSpace page = none := by
  simp [clearAddressSpaceMappings]

/-- Creation installs a fresh root capability, records the identifier in the
shared monotonic lifetime history, and starts with no mappings. -/
theorem created_fresh_empty_root (state : State) addressSpace subject slot
    (h : (createAddressSpace state addressSpace subject slot).result = .accepted) :
    state.memory.issued addressSpace = false ∧
      state.issuedAddressSpace addressSpace = false ∧
      (createAddressSpace state addressSpace subject slot).state.memory.issued addressSpace = true ∧
      (createAddressSpace state addressSpace subject slot).state.owner addressSpace = some subject ∧
      (createAddressSpace state addressSpace subject slot).state.memory.capabilities.slots subject slot =
        some (⟨addressSpace, .addressSpace, addressSpaceRootRights,
          state.memory.capabilities.nextIdentity, none⟩ : Capability.Capability) ∧
      ∀ page, (createAddressSpace state addressSpace subject slot).state.mappings
        addressSpace page = none := by
  simp only [createAddressSpace] at h ⊢
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  next hfresh =>
    have hboth : state.issuedAddressSpace addressSpace = false ∧
        state.memory.issued addressSpace = false := by
      simp_all
    split at h <;> try contradiction
    rcases hboth with ⟨haddress, hglobal⟩
    simp_all [createAddressSpace, clearAddressSpaceMappings, setOwner, setIssuedAddressSpace,
      MemoryLifecycle.setIssued, Capability.installRoot, Capability.install, haddress, hglobal,
      activateAddressSpace, MemoryLifecycle.setObject]

/-- Destruction retires the object, every capability naming it, its owner, and
all of its mappings. -/
theorem destroyed_complete_cleanup (state : State) subject slot cap
    (hlookup : Capability.lookup state.memory.capabilities subject slot = .found cap)
    (h : (destroyAddressSpace state subject slot).result = .accepted) :
    (destroyAddressSpace state subject slot).state.owner cap.object = none ∧
      (destroyAddressSpace state subject slot).state.memory.capabilities.objects cap.object = false ∧
      (∀ page, (destroyAddressSpace state subject slot).state.mappings cap.object page = none) ∧
      ∀ candidate candidateSlot found,
        (destroyAddressSpace state subject slot).state.memory.capabilities.slots
          candidate candidateSlot = some found → found.object ≠ cap.object := by
  simp only [destroyAddressSpace, hlookup] at h ⊢
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  next owner =>
    split at h <;> try contradiction
    simp_all [destroyAddressSpace, hlookup]
    constructor
    · simp [clearAddressSpaceMappings, setOwner]
    constructor
    · simp [clearAddressSpaceMappings, retireAddressSpace,
        MemoryLifecycle.retireCapabilities, MemoryLifecycle.setObject]
    constructor
    · intro page
      simp [clearAddressSpaceMappings]
    · intro candidate candidateSlot found hfound heq
      cases hsource : state.memory.capabilities.slots candidate candidateSlot with
      | none =>
          simp [clearAddressSpaceMappings, retireAddressSpace,
            MemoryLifecycle.retireCapabilities, hsource] at hfound
      | some existing =>
          by_cases hretired : existing.object = cap.object
          · simp [clearAddressSpaceMappings, retireAddressSpace,
              MemoryLifecycle.retireCapabilities, hsource, hretired] at hfound
          · have hexisting : existing = found := by
              simpa [clearAddressSpaceMappings, retireAddressSpace,
                MemoryLifecycle.retireCapabilities, hsource, hretired] using hfound
            subst found
            exact hretired heq

/-- Destroying one address space preserves every other owner's identity and mappings. -/
theorem destroy_preserves_other_address_space (state : State) subject slot cap other
    (hlookup : Capability.lookup state.memory.capabilities subject slot = .found cap)
    (hne : other ≠ cap.object) :
    (destroyAddressSpace state subject slot).result = .accepted →
      (destroyAddressSpace state subject slot).state.owner other = state.owner other ∧
      (destroyAddressSpace state subject slot).state.mappings other = state.mappings other := by
  intro h
  simp only [destroyAddressSpace, hlookup] at h ⊢
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  next owner =>
    split at h <;> try contradiction
    simp_all [destroyAddressSpace, hlookup]
    constructor
    · simp [clearAddressSpaceMappings, setOwner, hne]
    · funext page
      simp [clearAddressSpaceMappings, hne]

theorem clear_address_space_preserves_other (state : State) addressSpace other
    (hne : other ≠ addressSpace) :
    (clearAddressSpaceMappings state addressSpace).mappings other = state.mappings other := by
  funext page
  simp [clearAddressSpaceMappings, hne]

theorem invalidated_object_mapping (state : State) object addressSpace page mapping
    (h : state.mappings addressSpace page = some mapping) (heq : mapping.object = object) :
    (invalidateObjectMappings state object).mappings addressSpace page = none := by
  simp [invalidateObjectMappings, h, heq]

/-- Selective release preserves every mapping that names a different object. -/
theorem release_preserves_unrelated_mapping (state : State) subject slot cap addressSpace page
    mapping
    (hlookup : Capability.lookup state.memory.capabilities subject slot = .found cap)
    (hne : mapping.object ≠ cap.object) :
    (release state subject slot).result = .accepted →
      state.mappings addressSpace page = some mapping →
      (release state subject slot).state.mappings addressSpace page = some mapping := by
  intro haccepted hmapping
  simp only [release, MemoryLifecycle.release, hlookup] at haccepted ⊢
  split at * <;> try contradiction
  split at * <;> try contradiction
  split at * <;> try contradiction
  next frame =>
    split at * <;> try contradiction
    simp [invalidateObjectMappings, hmapping, hne]

private def subjects : SubjectId → Bool := fun subject => subject < 3
private def caps : Capability.State :=
  { subjects, objects := fun object => object = 10
    kinds := fun object => if object = 10 then some .memory else none
    slots := fun subject slot =>
      if subject = 0 ∧ slot = 0 then
        some ({ object := 10, kind := .memory, rights := Capability.allRights } :
          Capability.Capability)
      else none }
private def allocator : FrameAllocator.State :=
  { frames := [4], status := fun frame => if frame = 4 then .owned 10 else .reserved }
private def memory : MemoryLifecycle.State :=
  { capabilities := caps, allocator, binding := fun object => if object = 10 then some 4 else none
    issued := fun object => object = 10 }
private def initial : State :=
  { memory, owner := fun space => if space = 5 then some 0 else if space = 6 then some 1 else none
    mappings := fun _ _ => none
    issuedAddressSpace := fun space => space = 5 || space = 6 }
private def readOnly := (map initial 0 0 5 7 { read := true }).state
private def readRights : Capability.Rights := { read := true }
private def readSlots (subject : SubjectId) (slot : SlotId) : Option Capability.Capability :=
  if subject = 0 ∧ slot = 0 then
    some ({ object := 10, kind := .memory, rights := readRights } :
      Capability.Capability)
  else none
private def readCapMemory : MemoryLifecycle.State :=
  { memory with capabilities :=
      { caps with slots := readSlots } }
private def readCapInitial : State := { initial with memory := readCapMemory }
private def retired : State := (release readOnly 0 0).state
private def reused : State :=
  { retired with memory := (MemoryLifecycle.allocate retired.memory 11 0 0).state }

private def created := createAddressSpace initial 20 0 1
private def createdMapped := map created.state 0 0 20 9 { read := true }
private def destroyed := destroyAddressSpace createdMapped.state 0 1
private def twoSpaces := createAddressSpace created.state 21 1 0
private def firstDestroyed := destroyAddressSpace twoSpaces.state 0 1
private def delegatedAddressSpace : State :=
  let copied := Capability.copy created.state.memory.capabilities 0 1 1 0
    (Capability.oneRight .revoke)
  { created.state with memory := { created.state.memory with capabilities := copied.state } }

private def twoObjectCaps : Capability.State :=
  { subjects
    objects := fun object => object = 10 || object = 11
    kinds := fun object => if object = 10 || object = 11 then some .memory else none
    slots := fun subject slot =>
      if subject = 0 ∧ slot = 0 then
        some ({ object := 10, kind := .memory, rights := Capability.allRights } :
          Capability.Capability)
      else if subject = 1 ∧ slot = 0 then
        some ({ object := 11, kind := .memory, rights := Capability.allRights } :
          Capability.Capability)
      else none }
private def twoObjectMemory : MemoryLifecycle.State :=
  { capabilities := twoObjectCaps
    allocator :=
      { frames := [4, 5]
        status := fun frame => if frame = 4 then .owned 10
          else if frame = 5 then .owned 11 else .reserved }
    binding := fun object => if object = 10 then some 4 else if object = 11 then some 5 else none
    issued := fun object => object = 10 || object = 11 }
private def selectiveInitial : State :=
  { memory := twoObjectMemory
    owner := fun space => if space = 20 then some 0 else if space = 21 then some 1 else none
    mappings := fun space page =>
      if space = 20 ∧ page = 1 then some { object := 10, permissions := { read := true } }
      else if space = 21 ∧ page = 2 then some { object := 11, permissions := { read := true } }
      else none
    issuedAddressSpace := fun space => space = 20 || space = 21 }
private def selectivelyReleased := release selectiveInitial 0 0

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
example : created.result = .accepted := by native_decide
example : createdMapped.result = .accepted := by native_decide
example : destroyed.result = .accepted := by native_decide
example : translate destroyed.state 0 20 9 .read = .error .invalidAddressSpace := by rfl
example : (createAddressSpace destroyed.state 20 0 1).result =
    .rejected .identifierAlreadyIssued := by native_decide
example : twoSpaces.result = .accepted := by native_decide
example : firstDestroyed.state.owner 21 = some 1 := by native_decide
example : (destroyAddressSpace delegatedAddressSpace 1 0).result = .rejected .notOwner := by
  native_decide
example : (destroyAddressSpace destroyed.state 0 1).result = .rejected .staleSlot := by
  native_decide
example : selectivelyReleased.result = .accepted := by native_decide
example : selectivelyReleased.state.mappings 20 1 = none := by native_decide
example : selectivelyReleased.state.mappings 21 2 =
    some { object := 11, permissions := { read := true } } := by native_decide
example : translate selectivelyReleased.state 1 21 2 .read = .ok 5 := by rfl

end LeanOS.VirtualMapping
