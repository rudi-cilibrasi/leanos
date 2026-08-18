import LeanOS.DMAQuarantine
import LeanOS.FailStop
import LeanOS.CapabilityHandle
import LeanOS.FrameScrub
import LeanOS.LifetimeIssuer

/-!
# Finite static IOMMU confinement model

This module is a static model of device assignment, IOVA mappings, and
device-visible reads and writes.  It does not program an IOMMU, model IOTLB
state, or prove any property of PCIe requester IDs, VT-d, generated code,
QEMU, or hardware.  `DeviceSemantics` below is the explicit boundary at which
a real platform is assumed to submit the source identity and transfer that
the model checks.

The existing `DMAQuarantine` model remains the deny-all baseline.  This module
adds a separate, proof-carrying authority projection so the old accepted q35
snapshot does not silently start accepting assigned bus masters.
-/

namespace LeanOS.IOMMU

def maxOwners : Nat := 4
def maxDevices : Nat := 8
def maxSources : Nat := 8
def maxDomains : Nat := 8
def maxFrames : Nat := 16
def maxCapabilities : Nat := 16
def maxMappings : Nat := 16
def pageSize : Nat := 16
def maxIOVA : Nat := 4096
def generationReserved : Nat := LifetimeIssuer.identityReserved

abbrev OwnerId := Nat
abbrev DeviceId := Nat
abbrev SourceId := Nat
abbrev DomainId := Nat
abbrev FrameId := Nat
abbrev SlotId := Nat
abbrev Generation := Nat
abbrev IOVA := Nat

structure Permission where
  read : Bool
  write : Bool
  deriving BEq, DecidableEq, Repr, Inhabited

def Permission.nonempty (permission : Permission) : Bool :=
  permission.read || permission.write

def Permission.attenuates (child parent : Permission) : Bool :=
  (!child.read || parent.read) && (!child.write || parent.write)

def readOnly : Permission := ⟨true, false⟩
def writeOnly : Permission := ⟨false, true⟩
def readWrite : Permission := ⟨true, true⟩

theorem Permission.attenuates_refl (permission : Permission) :
    permission.attenuates permission = true := by
  rcases permission with ⟨read, write⟩
  cases read <;> cases write <;> native_decide

theorem Permission.attenuates_trans
    (child middle parent : Permission)
    (hchild : child.attenuates middle = true)
    (hmiddle : middle.attenuates parent = true) :
    child.attenuates parent = true := by
  rcases child with ⟨childRead, childWrite⟩
  rcases middle with ⟨middleRead, middleWrite⟩
  rcases parent with ⟨parentRead, parentWrite⟩
  cases childRead <;> cases childWrite <;>
    cases middleRead <;> cases middleWrite <;>
    cases parentRead <;> cases parentWrite <;>
    simp_all [Permission.attenuates]

theorem Permission.attenuation_cannot_add_read
    (child parent : Permission) (hattenuates : child.attenuates parent = true)
    (hdenied : parent.read = false) : child.read = false := by
  cases child <;> cases parent <;> simp_all [Permission.attenuates]

theorem Permission.attenuation_cannot_add_write
    (child parent : Permission) (hattenuates : child.attenuates parent = true)
    (hdenied : parent.write = false) : child.write = false := by
  cases child <;> cases parent <;> simp_all [Permission.attenuates]

structure AssignmentHandle where
  slot : SlotId
  generation : Generation
  deriving BEq, DecidableEq, Repr, Inhabited

structure DomainHandle where
  slot : DomainId
  generation : Generation
  deriving BEq, DecidableEq, Repr, Inhabited

structure MappingHandle where
  slot : SlotId
  generation : Generation
  deriving BEq, DecidableEq, Repr, Inhabited

structure FrameHandle where
  frame : FrameId
  generation : Generation
  deriving BEq, DecidableEq, Repr, Inhabited

/-- The platform-owned source table.  An assignment operation names only a
bounded device slot; the source identity is selected by this kernel table. -/
structure DeviceDescriptor where
  device : DeviceId
  source : SourceId
  deriving BEq, DecidableEq, Repr, Inhabited

def deviceTable : List DeviceDescriptor :=
  [⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨3, 3⟩, ⟨4, 4⟩, ⟨5, 5⟩, ⟨6, 6⟩, ⟨7, 7⟩]

def findDevice (device : DeviceId) : Option DeviceDescriptor :=
  deviceTable.find? (·.device == device)

structure Assignment where
  handle : AssignmentHandle
  device : DeviceId
  source : SourceId
  domain : DomainHandle
  owner : OwnerId
  deriving BEq, DecidableEq, Repr, Inhabited

structure Frame where
  handle : FrameHandle
  owner : OwnerId
  live : Bool
  kernelOwned : Bool
  pageTable : Bool
  allocatorMetadata : Bool
  size : Nat
  deriving BEq, DecidableEq, Repr, Inhabited

structure Capability where
  slot : SlotId
  identity : Nat
  owner : OwnerId
  object : LeanOS.Capability.ObjectId
  frame : FrameHandle
  offset : Nat
  length : Nat
  permission : Permission
  deriving BEq, DecidableEq, Repr, Inhabited

structure Mapping where
  handle : MappingHandle
  assignment : AssignmentHandle
  domain : DomainHandle
  owner : OwnerId
  iova : IOVA
  length : Nat
  frame : FrameHandle
  frameOffset : Nat
  permission : Permission
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Physical bytes are a separate projection.  The finite frame and mapping
registries bound authority; byte offsets are range-checked against a finite
live frame before they can be observed or changed. -/
structure Core where
  currentOwner : OwnerId
  nextAssignmentGeneration : Generation
  nextDomainGeneration : Generation
  nextMappingGeneration : Generation
  assignments : List Assignment
  mappings : List Mapping
  frames : List Frame
  capabilityAuthority : LeanOS.Capability.State
  /-- Kernel-selected exact object-to-frame-lifetime binding.  Capabilities
  cannot authorize an arbitrary same-owner live frame. -/
  frameAuthority : LeanOS.Capability.ObjectId → Option FrameHandle
  capabilities : List Capability
  memory : FrameId → Nat → UInt8

def findAssignment (core : Core) (handle : AssignmentHandle) : Option Assignment :=
  core.assignments.find? (·.handle == handle)

def findAssignmentBySource (core : Core) (source : SourceId)
    (generation : Generation) : Option Assignment :=
  core.assignments.find? fun assignment =>
    assignment.source == source && assignment.handle.generation == generation

def findFrame (core : Core) (handle : FrameHandle) : Option Frame :=
  core.frames.find? (·.handle == handle)

def Capability.handle (capability : Capability) : CapabilityHandle.Handle :=
  ⟨capability.slot, capability.identity⟩

def findCapability (core : Core) (owner : OwnerId)
    (handle : CapabilityHandle.Handle) : Option Capability :=
  core.capabilities.find? fun capability =>
    capability.owner == owner && capability.slot == handle.slot &&
      capability.identity == handle.identity

def findMapping (core : Core) (handle : MappingHandle) : Option Mapping :=
  core.mappings.find? (·.handle == handle)

def rangesOverlap (firstBase firstLength secondBase secondLength : Nat) : Bool :=
  firstBase < secondBase + secondLength && secondBase < firstBase + firstLength

def rangeContained (base length outerBase outerLength : Nat) : Bool :=
  0 < length && outerBase ≤ base && base + length ≤ outerBase + outerLength

def aligned (value : Nat) : Bool := value % pageSize == 0

def generationLive (generation next : Generation) : Bool :=
  0 < generation && generation < next && next ≤ generationReserved

def descriptorMatches (assignment : Assignment) : Bool :=
  match findDevice assignment.device with
  | some descriptor => descriptor.source == assignment.source
  | none => false

def assignmentValid (core : Core) (assignment : Assignment) : Bool :=
  assignment.handle.slot < maxDevices &&
    assignment.device < maxDevices &&
    assignment.source < maxSources &&
    assignment.domain.slot < maxDomains &&
    assignment.owner < maxOwners &&
    assignment.handle.slot == assignment.device &&
    assignment.domain.slot == assignment.handle.slot &&
    descriptorMatches assignment &&
    generationLive assignment.handle.generation core.nextAssignmentGeneration &&
    generationLive assignment.domain.generation core.nextDomainGeneration

def frameValid (frame : Frame) : Bool :=
  frame.handle.frame < maxFrames &&
    0 < frame.handle.generation && frame.handle.generation < generationReserved &&
    frame.owner < maxOwners && 0 < frame.size && frame.size ≤ maxIOVA

def capabilityValid (core : Core) (capability : Capability) : Bool :=
  capability.slot < maxCapabilities &&
    (CapabilityHandle.encode capability.handle).isSome &&
    capability.owner < maxOwners &&
    capability.permission.nonempty &&
    match LeanOS.Capability.lookup core.capabilityAuthority
        capability.owner capability.slot, core.frameAuthority capability.object,
        findFrame core capability.frame with
    | .found source, some authorizedFrame, some frame =>
        source.object == capability.object &&
          decide (source.kind = .memory) &&
          source.identity == capability.identity &&
          authorizedFrame == capability.frame &&
          (!capability.permission.read || source.rights.read) &&
          (!capability.permission.write || source.rights.write) &&
          frame.live && !frame.kernelOwned && !frame.pageTable &&
          !frame.allocatorMetadata && frame.owner == capability.owner &&
          rangeContained capability.offset capability.length 0 frame.size
    | _, _, _ => false

def mappingValid (core : Core) (mapping : Mapping) : Bool :=
  mapping.handle.slot < maxMappings &&
    mapping.owner < maxOwners &&
    mapping.permission.nonempty &&
    generationLive mapping.handle.generation core.nextMappingGeneration &&
    aligned mapping.iova && aligned mapping.length && aligned mapping.frameOffset &&
    mapping.iova + mapping.length ≤ maxIOVA &&
    match findAssignment core mapping.assignment, findFrame core mapping.frame with
    | some assignment, some frame =>
        assignment.domain == mapping.domain &&
          assignment.owner == mapping.owner &&
          frame.live && !frame.kernelOwned && !frame.pageTable && !frame.allocatorMetadata &&
          frame.owner == mapping.owner &&
          rangeContained mapping.frameOffset mapping.length 0 frame.size
    | _, _ => false

def uniqueAssignmentSlots (assignments : List Assignment) : Bool :=
  assignments.all fun assignment =>
    (assignments.filter (·.handle.slot == assignment.handle.slot)).length == 1

def uniqueAssignmentSources (assignments : List Assignment) : Bool :=
  assignments.all fun assignment =>
    (assignments.filter (·.source == assignment.source)).length == 1

def uniqueAssignmentDomains (assignments : List Assignment) : Bool :=
  assignments.all fun assignment =>
    (assignments.filter (·.domain.slot == assignment.domain.slot)).length == 1

def uniqueMappingSlots (mappings : List Mapping) : Bool :=
  mappings.all fun mapping =>
    (mappings.filter (·.handle.slot == mapping.handle.slot)).length == 1

def uniqueFrameHandles (frames : List Frame) : Bool :=
  frames.all fun frame =>
    (frames.filter (·.handle == frame.handle)).length == 1

/-- Physical memory is keyed by `FrameId`, so two live lifetime records may
not name the same physical frame even when their generations differ. -/
def LiveFrameIdsExclusive (frames : List Frame) : Prop :=
  ∀ first, first ∈ frames → first.live = true →
    ∀ second, second ∈ frames → second.live = true →
      first.handle.frame = second.handle.frame → first = second

def uniqueLiveFrameIds (frames : List Frame) : Bool :=
  frames.all fun first =>
    frames.all fun second =>
      !first.live || !second.live ||
        first.handle.frame != second.handle.frame || decide (first = second)

def uniqueCapabilities (capabilities : List Capability) : Bool :=
  capabilities.all fun capability =>
    (capabilities.filter fun candidate =>
      candidate.owner == capability.owner &&
        candidate.slot == capability.slot).length == 1

def mappingsDisjoint (mappings : List Mapping) : Bool :=
  mappings.all fun first =>
    mappings.all fun second =>
      first.assignment != second.assignment ||
        first.handle == second.handle ||
        !rangesOverlap first.iova first.length second.iova second.length

/-- The validator is finite, total, deterministic, and independent of memory
contents.  The `State` wrapper below makes this validation result part of the
authoritative state rather than an assumption supplied to each operation. -/
def validateCore (core : Core) : Bool :=
  core.currentOwner < maxOwners &&
    0 < core.nextAssignmentGeneration &&
    core.nextAssignmentGeneration ≤ generationReserved &&
    0 < core.nextDomainGeneration &&
    core.nextDomainGeneration ≤ generationReserved &&
    0 < core.nextMappingGeneration &&
    core.nextMappingGeneration ≤ generationReserved &&
    core.assignments.length ≤ maxDevices &&
    core.mappings.length ≤ maxMappings &&
    core.frames.length ≤ maxFrames &&
    core.capabilities.length ≤ maxCapabilities &&
    uniqueAssignmentSlots core.assignments &&
    uniqueAssignmentSources core.assignments &&
    uniqueAssignmentDomains core.assignments &&
    uniqueMappingSlots core.mappings &&
    uniqueFrameHandles core.frames &&
    uniqueCapabilities core.capabilities &&
    core.assignments.all (assignmentValid core) &&
    core.frames.all frameValid &&
    core.capabilities.all (capabilityValid core) &&
    core.mappings.all (mappingValid core) &&
    mappingsDisjoint core.mappings &&
    uniqueLiveFrameIds core.frames

theorem validateCore_total (core : Core) :
    validateCore core = true ∨ validateCore core = false := by
  cases validateCore core <;> simp

theorem validateCore_deterministic (core : Core) (first second : Bool)
    (hfirst : validateCore core = first)
    (hsecond : validateCore core = second) : first = second := by
  rw [← hfirst, ← hsecond]

structure State where
  core : Core
  valid : validateCore core = true
  capabilityWellFormed : LeanOS.Capability.WellFormed core.capabilityAuthority

def State.Invariant (state : State) : Prop :=
  validateCore state.core = true ∧
    LeanOS.Capability.WellFormed state.core.capabilityAuthority

theorem State.invariant (state : State) : state.Invariant :=
  ⟨state.valid, state.capabilityWellFormed⟩

theorem State.liveFrameIdsExclusive (state : State) :
    LiveFrameIdsExclusive state.core.frames := by
  have hvalid := state.valid
  unfold validateCore at hvalid
  simp only [Bool.and_eq_true] at hvalid
  have hunique := hvalid.2
  intro first hfirst hfirstLive second hsecond hsecondLive hframe
  have hfirstAll := List.all_eq_true.mp hunique first hfirst
  have hsecondAll := List.all_eq_true.mp hfirstAll second hsecond
  exact of_decide_eq_true (by
    simpa [hfirstLive, hsecondLive, hframe] using hsecondAll)

def generationAvailable (next : Generation) : Bool :=
  0 < next && next < generationReserved

/-- The assignment, domain, and mapping counters all use this exact
non-wrapping issuance rule in separate namespaces. -/
def issueGeneration (next : Generation) : Option (Generation × Generation) :=
  if generationAvailable next then some (next, next + 1) else none

theorem issueGeneration_exact next generation follower
    (hissued : issueGeneration next = some (generation, follower)) :
    generation = next ∧ follower = next + 1 ∧
      0 < next ∧ next < generationReserved := by
  simp only [issueGeneration] at hissued
  split at hissued
  · next hlive =>
      injection hissued with hpair
      cases hpair
      simp only [generationAvailable, Bool.and_eq_true, decide_eq_true_eq] at hlive
      exact ⟨rfl, rfl, hlive⟩
  · contradiction

theorem consecutive_generations_never_reuse
    (next first follower second final : Generation)
    (hfirst : issueGeneration next = some (first, follower))
    (hsecond : issueGeneration follower = some (second, final)) :
    first ≠ second := by
  have hfirstFacts := issueGeneration_exact _ _ _ hfirst
  have hsecondFacts := issueGeneration_exact _ _ _ hsecond
  rw [hfirstFacts.1, hsecondFacts.1, hfirstFacts.2.1]
  exact Nat.ne_of_lt (Nat.lt_succ_self next)

def firstFreeSlotAux (used : Nat → Bool) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, candidate =>
      if used candidate then firstFreeSlotAux used fuel (candidate + 1)
      else some candidate

def firstFreeMappingSlot (core : Core) : Option SlotId :=
  firstFreeSlotAux
    (fun slot => core.mappings.any (·.handle.slot == slot))
    maxMappings 0

inductive RejectReason where
  | ownerOutOfRange
  | deviceOutOfRange
  | deviceUnknown
  | alreadyAssigned
  | assignmentExhausted
  | domainExhausted
  | mappingExhausted
  | mappingSlotsExhausted
  | staleAssignment
  | staleMapping
  | wrongOwner
  | capabilityMissing
  | staleFrame
  | invalidRange
  | invalidAlignment
  | permissionDenied
  | permissionAmplification
  | duplicateOrOverlappingIOVA
  | activeMappings
  | frameStillReachable
  | protectedFrame
  | kernelBusy
  | kernelHalted
  | authoritativeLifecycleRequired
  | invariantViolation
  deriving BEq, DecidableEq, Repr

structure AssignRequest where
  device : DeviceId
  deriving BEq, DecidableEq, Repr

/-- No owner, source, domain, or physical frame appears in a grant request.
The assignment handle and capability slot resolve all privileged identity from
the authoritative state. -/
structure GrantRequest where
  assignment : AssignmentHandle
  capability : CapabilityHandle.Handle
  iova : IOVA
  capabilityOffset : Nat
  length : Nat
  permission : Permission
  deriving BEq, DecidableEq, Repr

structure AttenuateRequest where
  mapping : MappingHandle
  offset : Nat
  length : Nat
  permission : Permission
  deriving BEq, DecidableEq, Repr

inductive Operation where
  | assign (request : AssignRequest)
  | grant (request : GrantRequest)
  | attenuate (request : AttenuateRequest)
  | unmap (mapping : MappingHandle)
  | teardown (assignment : AssignmentHandle)
  | releaseFrame (frame : FrameHandle)
  | terminateCurrentOwner
  deriving BEq, DecidableEq, Repr

def Operation.isControlOnly : Operation → Prop
  | .releaseFrame _ | .terminateCurrentOwner => False
  | _ => True

inductive AcceptedReply where
  | assigned (assignment : AssignmentHandle) (domain : DomainHandle)
  | mapped (mapping : MappingHandle)
  | attenuated (mapping : MappingHandle)
  | unmapped
  | tornDown
  | frameReleased
  | ownerTerminated
  deriving BEq, DecidableEq, Repr

/-- A rejection contains no post-state at all.  Its state projection is
definitionally the input state, making complete-state rejection stutter part
of the result type rather than a theorem that can accidentally omit fields. -/
inductive Outcome (before : State) where
  | accepted (after : State) (reply : AcceptedReply)
  | rejected (reason : RejectReason)

def Outcome.state {before : State} : Outcome before → State
  | .accepted after _ => after
  | .rejected _ => before

def Outcome.isAccepted {before : State} : Outcome before → Bool
  | .accepted _ _ => true
  | .rejected _ => false

def Outcome.reason {before : State} : Outcome before → Option RejectReason
  | .accepted _ _ => none
  | .rejected reason => some reason

def commit (before : State) (candidate : Core)
    (hcapability :
      LeanOS.Capability.WellFormed candidate.capabilityAuthority)
    (reply : AcceptedReply) : Outcome before :=
  if hvalid : validateCore candidate = true then
    .accepted ⟨candidate, hvalid, hcapability⟩ reply
  else .rejected .invariantViolation

def eraseAssignment (assignments : List Assignment) (handle : AssignmentHandle) :
    List Assignment :=
  assignments.filter (·.handle != handle)

def eraseAssignmentMappings (mappings : List Mapping) (handle : AssignmentHandle) :
    List Mapping :=
  mappings.filter (·.assignment != handle)

def eraseMapping (mappings : List Mapping) (handle : MappingHandle) : List Mapping :=
  mappings.filter (·.handle != handle)

def setFrameLive (frames : List Frame) (handle : FrameHandle) (live : Bool) :
    List Frame :=
  frames.map fun frame => if frame.handle == handle then { frame with live := live } else frame

def clearFrameAuthority
    (authority : LeanOS.Capability.ObjectId → Option FrameHandle)
    (handles : List FrameHandle) : LeanOS.Capability.ObjectId → Option FrameHandle :=
  fun object =>
    match authority object with
    | some handle => if handles.any (· == handle) then none else some handle
    | none => none

def mappingOverlaps (core : Core) (assignment : AssignmentHandle)
    (iova length : Nat) (ignore : Option MappingHandle := none) : Bool :=
  core.mappings.any fun mapping =>
    mapping.assignment == assignment &&
      !(ignore == some mapping.handle) &&
      rangesOverlap mapping.iova mapping.length iova length

def gate (state : State) : Operation → Outcome state
  | .assign request =>
      if _howner : state.core.currentOwner < maxOwners then
        if _hdevice : request.device < maxDevices then
          match findDevice request.device with
          | none => .rejected .deviceUnknown
          | some descriptor =>
              if state.core.assignments.any (·.device == request.device) then
                .rejected .alreadyAssigned
              else if !generationAvailable state.core.nextAssignmentGeneration then
                .rejected .assignmentExhausted
              else if !generationAvailable state.core.nextDomainGeneration then
                .rejected .domainExhausted
              else
                let assignmentHandle :=
                  { slot := request.device
                    generation := state.core.nextAssignmentGeneration }
                let domainHandle :=
                  { slot := request.device
                    generation := state.core.nextDomainGeneration }
                let assignment :=
                  { handle := assignmentHandle
                    device := request.device
                    source := descriptor.source
                    domain := domainHandle
                    owner := state.core.currentOwner }
                commit state
                  { state.core with
                    nextAssignmentGeneration := state.core.nextAssignmentGeneration + 1
                    nextDomainGeneration := state.core.nextDomainGeneration + 1
                    assignments := state.core.assignments ++ [assignment] }
                  state.capabilityWellFormed
                  (.assigned assignmentHandle domainHandle)
        else .rejected .deviceOutOfRange
      else .rejected .ownerOutOfRange
  | .grant request =>
      match findAssignment state.core request.assignment with
      | none => .rejected .staleAssignment
      | some assignment =>
          if assignment.owner != state.core.currentOwner then .rejected .wrongOwner
          else
            match findCapability state.core state.core.currentOwner request.capability with
            | none => .rejected .capabilityMissing
            | some capability =>
                match findFrame state.core capability.frame with
                | none => .rejected .staleFrame
                | some frame =>
                    if !frame.live || frame.owner != assignment.owner ||
                        frame.kernelOwned || frame.pageTable || frame.allocatorMetadata then
                      .rejected .staleFrame
                    else if !request.permission.nonempty ||
                        !request.permission.attenuates capability.permission then
                      .rejected .permissionDenied
                    else if !aligned request.iova || !aligned request.capabilityOffset ||
                        !aligned request.length then
                      .rejected .invalidAlignment
                    else if !rangeContained
                        (capability.offset + request.capabilityOffset) request.length
                        capability.offset capability.length ||
                        request.iova + request.length > maxIOVA then
                      .rejected .invalidRange
                    else if mappingOverlaps state.core assignment.handle
                        request.iova request.length then
                      .rejected .duplicateOrOverlappingIOVA
                    else if !generationAvailable state.core.nextMappingGeneration then
                      .rejected .mappingExhausted
                    else
                      match firstFreeMappingSlot state.core with
                      | none => .rejected .mappingSlotsExhausted
                      | some slot =>
                          let mappingHandle :=
                            { slot, generation := state.core.nextMappingGeneration }
                          let mapping :=
                            { handle := mappingHandle
                              assignment := assignment.handle
                              domain := assignment.domain
                              owner := assignment.owner
                              iova := request.iova
                              length := request.length
                              frame := capability.frame
                              frameOffset := capability.offset + request.capabilityOffset
                              permission := request.permission }
                          commit state
                            { state.core with
                              nextMappingGeneration := state.core.nextMappingGeneration + 1
                              mappings := state.core.mappings ++ [mapping] }
                            state.capabilityWellFormed
                            (.mapped mappingHandle)
  | .attenuate request =>
      match findMapping state.core request.mapping with
      | none => .rejected .staleMapping
      | some mapping =>
          if mapping.owner != state.core.currentOwner then .rejected .wrongOwner
          else if !request.permission.nonempty then .rejected .permissionDenied
          else if !request.permission.attenuates mapping.permission then
            .rejected .permissionAmplification
          else if !aligned request.offset || !aligned request.length then
            .rejected .invalidAlignment
          else if !rangeContained request.offset request.length 0 mapping.length then
            .rejected .invalidRange
          else
            let next :=
              { mapping with
                iova := mapping.iova + request.offset
                frameOffset := mapping.frameOffset + request.offset
                length := request.length
                permission := request.permission }
            let mappings :=
              state.core.mappings.map fun candidate =>
                if candidate.handle == mapping.handle then next else candidate
            commit state { state.core with mappings := mappings }
              state.capabilityWellFormed (.attenuated mapping.handle)
  | .unmap handle =>
      match findMapping state.core handle with
      | none => .rejected .staleMapping
      | some mapping =>
          if mapping.owner != state.core.currentOwner then .rejected .wrongOwner
          else commit state { state.core with mappings := eraseMapping state.core.mappings handle }
            state.capabilityWellFormed .unmapped
  | .teardown handle =>
      match findAssignment state.core handle with
      | none => .rejected .staleAssignment
      | some assignment =>
          if assignment.owner != state.core.currentOwner then .rejected .wrongOwner
          else
            commit state
              { state.core with
                assignments := eraseAssignment state.core.assignments handle
                mappings := eraseAssignmentMappings state.core.mappings handle }
              state.capabilityWellFormed
              .tornDown
  | .releaseFrame handle =>
      match findFrame state.core handle with
      | none => .rejected .staleFrame
      | some frame =>
          if frame.owner != state.core.currentOwner then .rejected .wrongOwner
          else if !frame.live then .rejected .staleFrame
          else if frame.kernelOwned || frame.pageTable || frame.allocatorMetadata then
            .rejected .protectedFrame
          else if state.core.mappings.any (·.frame == handle) then
            .rejected .frameStillReachable
          else
            commit state
              { state.core with
                frames := setFrameLive state.core.frames handle false
                frameAuthority :=
                  clearFrameAuthority state.core.frameAuthority [handle]
                capabilities := state.core.capabilities.filter (·.frame != handle) }
              state.capabilityWellFormed
              .frameReleased
  | .terminateCurrentOwner =>
      let owner := state.core.currentOwner
      let ownedAssignments := state.core.assignments.filter (·.owner == owner)
      let retainedAssignments := state.core.assignments.filter (·.owner != owner)
      let retainedMappings := state.core.mappings.filter fun mapping =>
        !(ownedAssignments.any (·.handle == mapping.assignment))
      let retainedCapabilities := state.core.capabilities.filter (·.owner != owner)
      let retiredHandles := state.core.frames.filterMap fun frame =>
        if frame.owner == owner && !frame.kernelOwned && !frame.pageTable &&
            !frame.allocatorMetadata then some frame.handle else none
      let frames := state.core.frames.map fun frame =>
        if frame.owner == owner && !frame.kernelOwned && !frame.pageTable &&
            !frame.allocatorMetadata then
          { frame with live := false }
        else frame
      commit state
        { state.core with
          assignments := retainedAssignments
          mappings := retainedMappings
          frameAuthority :=
            clearFrameAuthority state.core.frameAuthority retiredHandles
          capabilities := retainedCapabilities
          frames := frames }
        state.capabilityWellFormed
        .ownerTerminated

theorem gate_total (state : State) (operation : Operation) :
    ∃ outcome, gate state operation = outcome := ⟨gate state operation, rfl⟩

theorem gate_deterministic (state : State) (operation : Operation)
    (first second : Outcome state)
    (hfirst : gate state operation = first)
    (hsecond : gate state operation = second) : first = second := by
  rw [← hfirst, ← hsecond]

theorem accepted_preserves_invariant (state : State) (operation : Operation)
    (after : State) (reply : AcceptedReply)
    (_hgate : gate state operation = .accepted after reply) :
    after.Invariant := by
  exact after.invariant

theorem rejected_state_unchanged (state : State) (operation : Operation)
    (reason : RejectReason) (hgate : gate state operation = .rejected reason) :
    (gate state operation).state = state := by
  rw [hgate]
  rfl

/-! ## Device translation, read observations, and write transitions -/

inductive Direction where
  | read | write
  deriving BEq, DecidableEq, Repr

def directionAllowed : Permission → Direction → Bool
  | permission, .read => permission.read
  | permission, .write => permission.write

/-- Source is supplied by the trusted device/IOMMU boundary.  PCIe transactions
do not carry the model's assignment generation: the trusted remapping context
must look up and authenticate the active software lifetime tag for that source
and attach it to the modeled request.  The tag prevents retirement followed by
reuse of the same device BDF and source from reviving an old request.  There is
deliberately no domain, owner, or physical-frame field. -/
structure TransferRequest where
  source : SourceId
  assignmentGeneration : Generation
  iova : IOVA
  length : Nat
  deriving BEq, DecidableEq, Repr

/-- Explicit platform assumption, intentionally weaker than confinement: the
trusted boundary supplies the requester/source identity and transfer range
faithfully and attaches the active software assignment-generation tag obtained
from its authenticated remapping context.  PCIe does not supply that tag.
Authorization is still decided by `translate`; this assumption does not state
that a transfer is allowed, translated correctly, or confined. -/
def DeviceSemantics (hardware modeled : TransferRequest) : Prop :=
  hardware = modeled

structure Translation (state : State) (request : TransferRequest)
    (direction : Direction) where
  assignment : Assignment
  mapping : Mapping
  frame : Frame
  assignmentFound :
    findAssignmentBySource state.core request.source
      request.assignmentGeneration = some assignment
  mappingFound :
    state.core.mappings.find? (fun candidate =>
      candidate.assignment == assignment.handle &&
        rangeContained request.iova request.length
          candidate.iova candidate.length) = some mapping
  frameFound : findFrame state.core mapping.frame = some frame
  sourceBound : assignment.source = request.source
  assignmentGenerationBound :
    assignment.handle.generation = request.assignmentGeneration
  mappingAssignmentBound : mapping.assignment = assignment.handle
  domainBound : mapping.domain = assignment.domain
  ownerBound : mapping.owner = assignment.owner
  frameHandleBound : frame.handle = mapping.frame
  frameOwnerBound : frame.owner = assignment.owner
  frameLive : frame.live = true
  frameNotKernel : frame.kernelOwned = false
  frameNotPageTable : frame.pageTable = false
  frameNotAllocatorMetadata : frame.allocatorMetadata = false
  transferContained :
    rangeContained request.iova request.length mapping.iova mapping.length = true
  backingContained :
    rangeContained
      (mapping.frameOffset + (request.iova - mapping.iova))
      request.length 0 frame.size = true
  directionPermitted : directionAllowed mapping.permission direction = true

def translate (state : State) (request : TransferRequest) (direction : Direction) :
    Except RejectReason (Translation state request direction) :=
  if request.source ≥ maxSources || request.length = 0 ||
      request.iova + request.length > maxIOVA then
    .error .invalidRange
  else
    match hassignmentFound : findAssignmentBySource state.core request.source
        request.assignmentGeneration with
    | none => .error .staleAssignment
    | some assignment =>
        if hassignment :
            assignment.source = request.source ∧
              assignment.handle.generation = request.assignmentGeneration then
          match hmappingFound : state.core.mappings.find? fun mapping =>
              mapping.assignment == assignment.handle &&
                rangeContained request.iova request.length mapping.iova mapping.length with
          | none => .error .invalidRange
          | some mapping =>
              if hmapping :
                  mapping.assignment = assignment.handle ∧
                    mapping.domain = assignment.domain ∧
                    mapping.owner = assignment.owner ∧
                    rangeContained request.iova request.length
                      mapping.iova mapping.length = true then
                if hpermission : directionAllowed mapping.permission direction = true then
                  match hframeFound : findFrame state.core mapping.frame with
                  | none => .error .staleFrame
                  | some frame =>
                      if hframe :
                          frame.handle = mapping.frame ∧
                            frame.owner = assignment.owner ∧
                            frame.live = true ∧
                            frame.kernelOwned = false ∧
                            frame.pageTable = false ∧
                            frame.allocatorMetadata = false ∧
                            rangeContained
                              (mapping.frameOffset + (request.iova - mapping.iova))
                              request.length 0 frame.size = true then
                        .ok
                          { assignment
                            mapping
                            frame
                            assignmentFound := hassignmentFound
                            mappingFound := hmappingFound
                            frameFound := hframeFound
                            sourceBound := hassignment.1
                            assignmentGenerationBound := hassignment.2
                            mappingAssignmentBound := hmapping.1
                            domainBound := hmapping.2.1
                            ownerBound := hmapping.2.2.1
                            frameHandleBound := hframe.1
                            frameOwnerBound := hframe.2.1
                            frameLive := hframe.2.2.1
                            frameNotKernel := hframe.2.2.2.1
                            frameNotPageTable := hframe.2.2.2.2.1
                            frameNotAllocatorMetadata := hframe.2.2.2.2.2.1
                            transferContained := hmapping.2.2.2
                            backingContained := hframe.2.2.2.2.2.2
                            directionPermitted := hpermission }
                      else .error .staleFrame
                else .error .permissionDenied
              else .error .staleAssignment
        else .error .staleAssignment

def readBytes (memory : FrameId → Nat → UInt8) (frame : FrameId)
    (offset : Nat) : Nat → List UInt8
  | 0 => []
  | length + 1 => memory frame offset :: readBytes memory frame (offset + 1) length

def writeMemory (memory : FrameId → Nat → UInt8) (frame : FrameId)
    (offset : Nat) (bytes : List UInt8) : FrameId → Nat → UInt8 :=
  fun candidate index =>
    if candidate = frame ∧ offset ≤ index ∧ index < offset + bytes.length then
      bytes[index - offset]!
    else memory candidate index

def Core.withMemory (core : Core) (memory : FrameId → Nat → UInt8) : Core :=
  { core with memory := memory }

@[simp] theorem validateCore_withMemory core memory :
    validateCore (core.withMemory memory) = validateCore core := rfl

inductive ReadOutcome (state : State) (request : TransferRequest) where
  | observed (translation : Translation state request .read) (bytes : List UInt8)
  | rejected (reason : RejectReason)

def deviceRead (state : State) (request : TransferRequest) : ReadOutcome state request :=
  match translate state request .read with
  | .error reason => .rejected reason
  | .ok translation =>
      .observed translation
        (readBytes state.core.memory translation.frame.handle.frame
          (translation.mapping.frameOffset +
            (request.iova - translation.mapping.iova)) request.length)

inductive WriteOutcome (state : State) (request : TransferRequest) where
  | written (after : State) (translation : Translation state request .write)
  | rejected (reason : RejectReason)

def deviceWrite (state : State) (request : TransferRequest)
    (bytes : List UInt8) : WriteOutcome state request :=
  if bytes.length != request.length then .rejected .invalidRange
  else
    match translate state request .write with
    | .error reason => .rejected reason
    | .ok translation =>
        let offset :=
          translation.mapping.frameOffset + (request.iova - translation.mapping.iova)
        let memory :=
          writeMemory state.core.memory translation.frame.handle.frame offset bytes
        have hvalid : validateCore (state.core.withMemory memory) = true := by
          simpa using state.valid
        .written ⟨state.core.withMemory memory, hvalid,
          state.capabilityWellFormed⟩ translation

theorem read_observation_authorized (state : State) (request : TransferRequest)
    (translation : Translation state request .read) (bytes : List UInt8)
    (hread : deviceRead state request = .observed translation bytes) :
    bytes =
      readBytes state.core.memory translation.frame.handle.frame
        (translation.mapping.frameOffset +
          (request.iova - translation.mapping.iova)) request.length ∧
      translation.mapping.assignment = translation.assignment.handle ∧
      translation.mapping.domain = translation.assignment.domain ∧
      translation.frame.owner = translation.assignment.owner ∧
      translation.mapping.permission.read = true := by
  simp only [deviceRead] at hread
  cases htranslate : translate state request .read with
  | error reason => simp [htranslate] at hread
  | ok actual =>
      simp [htranslate] at hread
      rcases hread with ⟨rfl, rfl⟩
      exact ⟨rfl, actual.mappingAssignmentBound, actual.domainBound,
        actual.frameOwnerBound, actual.directionPermitted⟩

theorem readBytes_eq_of_authorized_range_eq
    (first second : FrameId → Nat → UInt8) (frame offset length : Nat)
    (hequal : ∀ index, offset ≤ index → index < offset + length →
      first frame index = second frame index) :
    readBytes first frame offset length = readBytes second frame offset length := by
  induction length generalizing offset with
  | zero => rfl
  | succ length ih =>
      simp only [readBytes]
      congr 1
      · exact hequal offset (by omega) (by omega)
      · apply ih
        intro index hlower hupper
        exact hequal index (by omega) (by omega)

/-- One-step confidentiality: bytes outside the authorized readable backing
range cannot affect the observed result.  The theorem assumes equality only
inside that exact range, not equality of unrelated frames. -/
theorem read_confidentiality (state : State) (request : TransferRequest)
    (translation : Translation state request .read)
    (alternateMemory : FrameId → Nat → UInt8)
    (hequal : ∀ index,
      translation.mapping.frameOffset +
          (request.iova - translation.mapping.iova) ≤ index →
      index <
          translation.mapping.frameOffset +
            (request.iova - translation.mapping.iova) + request.length →
      state.core.memory translation.frame.handle.frame index =
        alternateMemory translation.frame.handle.frame index) :
    readBytes state.core.memory translation.frame.handle.frame
        (translation.mapping.frameOffset +
          (request.iova - translation.mapping.iova)) request.length =
      readBytes alternateMemory translation.frame.handle.frame
        (translation.mapping.frameOffset +
          (request.iova - translation.mapping.iova)) request.length := by
  exact readBytes_eq_of_authorized_range_eq _ _ _ _ _ hequal

theorem writeMemory_other_frame memory target offset bytes candidate
    (hne : candidate ≠ target) :
    writeMemory memory target offset bytes candidate = memory candidate := by
  funext index
  simp [writeMemory, hne]

theorem writeMemory_outside_range memory frame offset bytes index
    (houtside : index < offset ∨ offset + bytes.length ≤ index) :
    writeMemory memory frame offset bytes frame index = memory frame index := by
  simp only [writeMemory]
  split
  · next hinside =>
      rcases hinside with ⟨_, hlower, hupper⟩
      omega
  · rfl

/-- One-step integrity and projection confinement: a successful write changes
only the exact authorized backing range.  All authority registries, ownership,
kernel/page-table/allocator flags, issuers, and the current owner stutter. -/
theorem write_integrity (state : State) (request : TransferRequest)
    (bytes : List UInt8) (after : State)
    (translation : Translation state request .write)
    (hwrite : deviceWrite state request bytes = .written after translation) :
    after.core.currentOwner = state.core.currentOwner ∧
      after.core.nextAssignmentGeneration = state.core.nextAssignmentGeneration ∧
      after.core.nextDomainGeneration = state.core.nextDomainGeneration ∧
      after.core.nextMappingGeneration = state.core.nextMappingGeneration ∧
      after.core.assignments = state.core.assignments ∧
      after.core.mappings = state.core.mappings ∧
      after.core.frames = state.core.frames ∧
      after.core.capabilityAuthority = state.core.capabilityAuthority ∧
      after.core.frameAuthority = state.core.frameAuthority ∧
      after.core.capabilities = state.core.capabilities ∧
      (∀ candidate, candidate ≠ translation.frame.handle.frame →
        after.core.memory candidate = state.core.memory candidate) ∧
      (∀ index,
        index <
            translation.mapping.frameOffset +
              (request.iova - translation.mapping.iova) ∨
          translation.mapping.frameOffset +
              (request.iova - translation.mapping.iova) + bytes.length ≤ index →
        after.core.memory translation.frame.handle.frame index =
          state.core.memory translation.frame.handle.frame index) := by
  simp only [deviceWrite] at hwrite
  split at hwrite
  · contradiction
  · next hlength =>
      cases htranslate : translate state request .write with
      | error reason => simp [htranslate] at hwrite
      | ok actual =>
          simp [htranslate] at hwrite
          rcases hwrite with ⟨rfl, rfl⟩
          refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
          · intro candidate hne
            exact writeMemory_other_frame _ _ _ _ _ hne
          · intro index houtside
            exact writeMemory_outside_range _ _ _ _ _ houtside

/-- Non-forgery follows directly from a successful translation witness:
source, assignment generation, domain, owner, and backing frame are all the
ones already bound in kernel state. -/
theorem translation_nonforgery (translation : Translation state request direction) :
    findAssignmentBySource state.core request.source
        request.assignmentGeneration = some translation.assignment ∧
      state.core.mappings.find? (fun candidate =>
        candidate.assignment == translation.assignment.handle &&
          rangeContained request.iova request.length
            candidate.iova candidate.length) = some translation.mapping ∧
      findFrame state.core translation.mapping.frame = some translation.frame ∧
      translation.assignment.source = request.source ∧
      translation.assignment.handle.generation = request.assignmentGeneration ∧
      translation.mapping.assignment = translation.assignment.handle ∧
      translation.mapping.domain = translation.assignment.domain ∧
      translation.mapping.owner = translation.assignment.owner ∧
      translation.frame.handle = translation.mapping.frame ∧
      translation.frame.owner = translation.assignment.owner :=
  ⟨translation.assignmentFound, translation.mappingFound, translation.frameFound,
    translation.sourceBound, translation.assignmentGenerationBound,
    translation.mappingAssignmentBound, translation.domainBound,
    translation.ownerBound, translation.frameHandleBound,
    translation.frameOwnerBound⟩

theorem no_translation_without_live_assignment
    (state : State) (request : TransferRequest) (direction : Direction)
    (habsent : findAssignmentBySource state.core request.source
      request.assignmentGeneration = none) :
    ¬ Nonempty (Translation state request direction) := by
  rintro ⟨translation⟩
  have hfound := translation.assignmentFound
  simp [habsent] at hfound

/-- A source assignment cannot translate to a frame record owned by a
different subject. -/
theorem translation_owner_isolation
    (translation : Translation state request direction)
    (otherOwner : OwnerId)
    (hother : otherOwner ≠ translation.assignment.owner) :
    translation.frame.owner ≠ otherOwner := by
  rw [translation.frameOwnerBound]
  exact Ne.symm hother

/-- Since memory is keyed by physical `FrameId`, the live-frame uniqueness
invariant upgrades record-level owner agreement to physical-memory owner
isolation: every other live record naming the translated physical frame is
the translated record itself. -/
theorem translation_physical_frame_owner_isolation
    (translation : Translation state request direction)
    (candidate : Frame) (hcandidate : candidate ∈ state.core.frames)
    (hlive : candidate.live = true)
    (hsame : candidate.handle.frame = translation.frame.handle.frame) :
    candidate.owner = translation.assignment.owner := by
  have htranslation : translation.frame ∈ state.core.frames := by
    exact List.mem_of_find?_eq_some (by
      simpa [findFrame] using translation.frameFound)
  have hequal := state.liveFrameIdsExclusive
    translation.frame htranslation translation.frameLive
    candidate hcandidate hlive hsame.symm
  rw [← hequal]
  exact translation.frameOwnerBound

/-- A successful device write cannot alter a live physical frame belonging to
another owner.  This bridge uses physical-frame-ID uniqueness before applying
the range-local one-step integrity theorem. -/
theorem write_integrity_other_owner_frame
    (state : State) (request : TransferRequest) (bytes : List UInt8)
    (after : State) (translation : Translation state request .write)
    (hwrite : deviceWrite state request bytes = .written after translation)
    (candidate : Frame) (hcandidate : candidate ∈ state.core.frames)
    (hlive : candidate.live = true)
    (hother : candidate.owner ≠ translation.assignment.owner) :
    after.core.memory candidate.handle.frame =
      state.core.memory candidate.handle.frame := by
  have hphysical :
      candidate.handle.frame ≠ translation.frame.handle.frame := by
    intro hsame
    exact hother
      (translation_physical_frame_owner_isolation
        translation candidate hcandidate hlive hsame)
  have hintegrity := write_integrity state request bytes after translation hwrite
  rcases hintegrity with
    ⟨_, _, _, _, _, _, _, _, _, _, hotherFrame, _⟩
  exact hotherFrame candidate.handle.frame hphysical

theorem read_only_translation_never_writable
    (translation : Translation state request .write)
    (hreadonly : translation.mapping.permission = readOnly) : False := by
  have hpermitted := translation.directionPermitted
  simp [directionAllowed, hreadonly, readOnly] at hpermitted

/-! ## Finite device traces -/

inductive DeviceEvent where
  | read (request : TransferRequest)
  | write (request : TransferRequest) (bytes : List UInt8)

inductive DeviceObservation where
  | read (result : Except RejectReason (List UInt8))
  | write (result : Option RejectReason)
  deriving Repr

structure DeviceStepOutcome where
  state : State
  observation : DeviceObservation
  touchedFrame : Option FrameId

def deviceStep (state : State) : DeviceEvent → DeviceStepOutcome
  | .read request =>
      match deviceRead state request with
      | .rejected reason =>
          ⟨state, .read (.error reason), none⟩
      | .observed _ bytes =>
          ⟨state, .read (.ok bytes), none⟩
  | .write request bytes =>
      match deviceWrite state request bytes with
      | .rejected reason =>
          ⟨state, .write (some reason), none⟩
      | .written after translation =>
          ⟨after, .write none, some translation.frame.handle.frame⟩

def runDeviceTrace : State → List DeviceEvent → State × List DeviceObservation
  | state, [] => (state, [])
  | state, event :: rest =>
      let outcome := deviceStep state event
      let suffix := runDeviceTrace outcome.state rest
      (suffix.1, outcome.observation :: suffix.2)

def TraceDoesNotTouch : State → List DeviceEvent → FrameId → Prop
  | _, [], _ => True
  | state, event :: rest, frame =>
      let outcome := deviceStep state event
      outcome.touchedFrame ≠ some frame ∧
        TraceDoesNotTouch outcome.state rest frame

def ProtectedLiveFrame (state : State) (frame : FrameId) : Prop :=
  ∃ candidate ∈ state.core.frames,
    candidate.live = true ∧ candidate.handle.frame = frame ∧
      (candidate.kernelOwned = true ∨ candidate.pageTable = true ∨
        candidate.allocatorMetadata = true)

def UnassignedLiveFrame (state : State) (frame : FrameId) : Prop :=
  (∃ candidate ∈ state.core.frames,
    candidate.live = true ∧ candidate.handle.frame = frame) ∧
  ∀ mapping ∈ state.core.mappings, mapping.frame.frame ≠ frame

def DeviceStepWritesOwnedBy
    (state : State) (event : DeviceEvent) (owner : OwnerId) : Prop :=
  match event with
  | .read _ => True
  | .write request bytes =>
      match deviceWrite state request bytes with
      | .rejected _ => True
      | .written _ translation => translation.assignment.owner = owner

def TraceWritesOwnedBy : State → List DeviceEvent → OwnerId → Prop
  | _, [], _ => True
  | state, event :: rest, owner =>
      let outcome := deviceStep state event
      DeviceStepWritesOwnedBy state event owner ∧
        TraceWritesOwnedBy outcome.state rest owner

def OtherOwnerLiveFrame
    (state : State) (frame : FrameId) (owner : OwnerId) : Prop :=
  ∃ candidate ∈ state.core.frames,
    candidate.live = true ∧ candidate.handle.frame = frame ∧
      candidate.owner ≠ owner

def FrameIsolatedFromTrace
    (state : State) (events : List DeviceEvent) (frame : FrameId) : Prop :=
  ProtectedLiveFrame state frame ∨
    UnassignedLiveFrame state frame ∨
      ∃ owner, OtherOwnerLiveFrame state frame owner ∧
        TraceWritesOwnedBy state events owner

theorem deviceStep_authority_stutters (state : State) (event : DeviceEvent) :
    (deviceStep state event).state.core.mappings = state.core.mappings ∧
      (deviceStep state event).state.core.frames = state.core.frames := by
  cases event with
  | read request =>
      cases hread : deviceRead state request <;> simp [deviceStep, hread]
  | write request bytes =>
      cases hwrite : deviceWrite state request bytes with
      | rejected reason => simp [deviceStep, hwrite]
      | written after translation =>
          simp only [deviceStep, hwrite]
          have hintegrity :=
            write_integrity state request bytes after translation hwrite
          exact ⟨hintegrity.2.2.2.2.2.1,
            hintegrity.2.2.2.2.2.2.1⟩

theorem protectedLiveFrame_deviceStep
    (state : State) (event : DeviceEvent) (frame : FrameId)
    (hprotected : ProtectedLiveFrame state frame) :
    ProtectedLiveFrame (deviceStep state event).state frame := by
  rcases hprotected with ⟨candidate, hmember, hlive, hframe, hprotected⟩
  refine ⟨candidate, ?_, hlive, hframe, hprotected⟩
  rw [deviceStep_authority_stutters state event |>.2]
  exact hmember

theorem unassignedLiveFrame_deviceStep
    (state : State) (event : DeviceEvent) (frame : FrameId)
    (hunassigned : UnassignedLiveFrame state frame) :
    UnassignedLiveFrame (deviceStep state event).state frame := by
  rcases hunassigned with
    ⟨⟨candidate, hmember, hlive, hframe⟩, hmappings⟩
  constructor
  · refine ⟨candidate, ?_, hlive, hframe⟩
    rw [deviceStep_authority_stutters state event |>.2]
    exact hmember
  · intro mapping hmember
    apply hmappings mapping
    rw [deviceStep_authority_stutters state event |>.1] at hmember
    exact hmember

theorem otherOwnerLiveFrame_deviceStep
    (state : State) (event : DeviceEvent) (frame : FrameId) (owner : OwnerId)
    (hother : OtherOwnerLiveFrame state frame owner) :
    OtherOwnerLiveFrame (deviceStep state event).state frame owner := by
  rcases hother with ⟨candidate, hmember, hlive, hframe, howner⟩
  refine ⟨candidate, ?_, hlive, hframe, howner⟩
  rw [deviceStep_authority_stutters state event |>.2]
  exact hmember

theorem protectedLiveFrame_deviceStep_untouched
    (state : State) (event : DeviceEvent) (frame : FrameId)
    (hprotected : ProtectedLiveFrame state frame) :
    (deviceStep state event).touchedFrame ≠ some frame := by
  cases event with
  | read request =>
      cases hread : deviceRead state request <;> simp [deviceStep, hread]
  | write request bytes =>
      cases hwrite : deviceWrite state request bytes with
      | rejected reason => simp [deviceStep, hwrite]
      | written after translation =>
          simp only [deviceStep, hwrite]
          intro hframe
          injection hframe with hphysical
          rcases hprotected with
            ⟨candidate, hmember, hlive, hcandFrame, hprotected⟩
          have htranslation : translation.frame ∈ state.core.frames := by
            exact List.mem_of_find?_eq_some (by
              simpa [findFrame] using translation.frameFound)
          have hequal := state.liveFrameIdsExclusive
            candidate hmember hlive translation.frame htranslation
              translation.frameLive (hcandFrame.trans hphysical.symm)
          subst candidate
          rcases hprotected with hkernel | hpage | hmetadata
          · simp [translation.frameNotKernel] at hkernel
          · simp [translation.frameNotPageTable] at hpage
          · simp [translation.frameNotAllocatorMetadata] at hmetadata

theorem unassignedLiveFrame_deviceStep_untouched
    (state : State) (event : DeviceEvent) (frame : FrameId)
    (hunassigned : UnassignedLiveFrame state frame) :
    (deviceStep state event).touchedFrame ≠ some frame := by
  cases event with
  | read request =>
      cases hread : deviceRead state request <;> simp [deviceStep, hread]
  | write request bytes =>
      cases hwrite : deviceWrite state request bytes with
      | rejected reason => simp [deviceStep, hwrite]
      | written after translation =>
          simp only [deviceStep, hwrite]
          intro hframe
          injection hframe with hphysical
          have hmapping : translation.mapping ∈ state.core.mappings := by
            exact List.mem_of_find?_eq_some translation.mappingFound
          exact hunassigned.2 translation.mapping hmapping
            (by rw [← translation.frameHandleBound, hphysical])

theorem otherOwnerLiveFrame_deviceStep_untouched
    (state : State) (event : DeviceEvent) (frame : FrameId) (owner : OwnerId)
    (hother : OtherOwnerLiveFrame state frame owner)
    (howned : DeviceStepWritesOwnedBy state event owner) :
    (deviceStep state event).touchedFrame ≠ some frame := by
  cases event with
  | read request =>
      cases hread : deviceRead state request <;> simp [deviceStep, hread]
  | write request bytes =>
      cases hwrite : deviceWrite state request bytes with
      | rejected reason => simp [deviceStep, hwrite]
      | written after translation =>
          simp only [deviceStep, hwrite]
          intro hframe
          injection hframe with hphysical
          rcases hother with
            ⟨candidate, hmember, hlive, hcandFrame, howner⟩
          have htranslation : translation.frame ∈ state.core.frames := by
            exact List.mem_of_find?_eq_some (by
              simpa [findFrame] using translation.frameFound)
          have hequal := state.liveFrameIdsExclusive
            candidate hmember hlive translation.frame htranslation
              translation.frameLive (hcandFrame.trans hphysical.symm)
          have htranslationOwner :
              translation.frame.owner = owner := by
            rw [translation.frameOwnerBound]
            simpa [DeviceStepWritesOwnedBy, hwrite] using howned
          exact howner (by rw [hequal, htranslationOwner])

theorem protected_trace_does_not_touch
    (state : State) (events : List DeviceEvent) (frame : FrameId)
    (hprotected : ProtectedLiveFrame state frame) :
    TraceDoesNotTouch state events frame := by
  induction events generalizing state with
  | nil => trivial
  | cons event rest ih =>
      constructor
      · exact protectedLiveFrame_deviceStep_untouched
          state event frame hprotected
      · exact ih (deviceStep state event).state
          (protectedLiveFrame_deviceStep state event frame hprotected)

theorem unassigned_trace_does_not_touch
    (state : State) (events : List DeviceEvent) (frame : FrameId)
    (hunassigned : UnassignedLiveFrame state frame) :
    TraceDoesNotTouch state events frame := by
  induction events generalizing state with
  | nil => trivial
  | cons event rest ih =>
      constructor
      · exact unassignedLiveFrame_deviceStep_untouched
          state event frame hunassigned
      · exact ih (deviceStep state event).state
          (unassignedLiveFrame_deviceStep state event frame hunassigned)

theorem other_owner_trace_does_not_touch
    (state : State) (events : List DeviceEvent) (frame : FrameId)
    (owner : OwnerId)
    (hother : OtherOwnerLiveFrame state frame owner)
    (howned : TraceWritesOwnedBy state events owner) :
    TraceDoesNotTouch state events frame := by
  induction events generalizing state with
  | nil => trivial
  | cons event rest ih =>
      constructor
      · exact otherOwnerLiveFrame_deviceStep_untouched
          state event frame owner hother howned.1
      · exact ih (deviceStep state event).state
          (otherOwnerLiveFrame_deviceStep state event frame owner hother)
          howned.2

theorem deviceStep_untouched_frame (state : State) (event : DeviceEvent)
    (frame : FrameId)
    (huntouched : (deviceStep state event).touchedFrame ≠ some frame) :
    (deviceStep state event).state.core.memory frame = state.core.memory frame := by
  cases event with
  | read request =>
      cases hread : deviceRead state request <;> simp [deviceStep, hread]
  | write request bytes =>
      cases hwrite : deviceWrite state request bytes with
      | rejected reason => simp [deviceStep, hwrite]
      | written after translation =>
          simp only [deviceStep, hwrite] at huntouched ⊢
          have hne : translation.frame.handle.frame ≠ frame := by
            intro hequal
            apply huntouched
            simp [hequal]
          have hintegrity := write_integrity state request bytes after translation hwrite
          rcases hintegrity with
            ⟨_, _, _, _, _, _, _, _, _, _, hotherFrame, _⟩
          exact hotherFrame frame hne.symm

/-- Low-level finite-trace integrity: if no successful authorized write names
a frame, every byte of that frame is identical after the trace.  The
classification lemmas above derive this premise for the advertised frame
classes; callers should normally use `isolated_trace_integrity`. -/
theorem trace_integrity (state : State) (events : List DeviceEvent) (frame : FrameId)
    (huntouched : TraceDoesNotTouch state events frame) :
    (runDeviceTrace state events).1.core.memory frame = state.core.memory frame := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      simp only [TraceDoesNotTouch] at huntouched
      simp only [runDeviceTrace]
      let outcome := deviceStep state event
      have hhead : outcome.state.core.memory frame = state.core.memory frame :=
        deviceStep_untouched_frame state event frame huntouched.1
      have htail := ih outcome.state huntouched.2
      exact htail.trans hhead

/-- The advertised finite-trace boundary derives no-touch from an invariant
frame class: protected, physically unassigned, or live and owned by someone
other than the owner of every successful write in the trace. -/
theorem isolated_trace_integrity
    (state : State) (events : List DeviceEvent) (frame : FrameId)
    (hisolated : FrameIsolatedFromTrace state events frame) :
    (runDeviceTrace state events).1.core.memory frame =
      state.core.memory frame := by
  apply trace_integrity
  rcases hisolated with hprotected | hunassigned | ⟨owner, hother, howned⟩
  · exact protected_trace_does_not_touch state events frame hprotected
  · exact unassigned_trace_does_not_touch state events frame hunassigned
  · exact other_owner_trace_does_not_touch
      state events frame owner hother howned

structure AuthorizedReadView (state : State) where
  request : TransferRequest
  translation : Translation state request .read
  bytes : List UInt8
  observed : deviceRead state request = .observed translation bytes

def AuthorizedReadView.frame {state : State}
    (view : AuthorizedReadView state) : FrameId :=
  view.translation.frame.handle.frame

def AuthorizedReadView.offset {state : State}
    (view : AuthorizedReadView state) : Nat :=
  view.translation.mapping.frameOffset +
    (view.request.iova - view.translation.mapping.iova)

def AuthorizedReadView.length {state : State}
    (view : AuthorizedReadView state) : Nat :=
  view.request.length

def observeReadViews {state : State} (memory : FrameId → Nat → UInt8) :
    List (AuthorizedReadView state) → List (List UInt8)
  | [] => []
  | view :: rest =>
      readBytes memory view.frame view.offset view.length ::
        observeReadViews memory rest

def actualReadObservations {state : State} :
    List (AuthorizedReadView state) → List (List UInt8)
  | [] => []
  | view :: rest => view.bytes :: actualReadObservations rest

theorem actualReadObservations_eq_observeReadViews (state : State)
    (views : List (AuthorizedReadView state)) :
    actualReadObservations views = observeReadViews state.core.memory views := by
  induction views with
  | nil => rfl
  | cons view rest ih =>
      simp only [actualReadObservations, observeReadViews]
      have hauthorized :=
        read_observation_authorized state view.request view.translation
          view.bytes view.observed
      rw [ih]
      simpa [AuthorizedReadView.frame, AuthorizedReadView.offset,
        AuthorizedReadView.length] using congrArg (fun bytes => bytes ::
          observeReadViews state.core.memory rest) hauthorized.1

def ReadViewsEquivalent {state : State} (first second : FrameId → Nat → UInt8)
    (views : List (AuthorizedReadView state)) : Prop :=
  ∀ view ∈ views, ∀ index,
    view.offset ≤ index → index < view.offset + view.length →
      first view.frame index = second view.frame index

/-- Finite-read-trace confidentiality: a sequence of authorized observations
is insensitive to every byte outside the union of its readable views. -/
theorem read_trace_confidentiality (state : State)
    (first second : FrameId → Nat → UInt8)
    (views : List (AuthorizedReadView state))
    (hequivalent : ReadViewsEquivalent first second views) :
    observeReadViews first views = observeReadViews second views := by
  induction views with
  | nil => rfl
  | cons view rest ih =>
      simp only [observeReadViews]
      congr 1
      · apply readBytes_eq_of_authorized_range_eq
        intro index hlower hupper
        exact hequivalent view (by simp) index hlower hupper
      · apply ih
        intro candidate hmember index hlower hupper
        exact hequivalent candidate (by simp [hmember]) index hlower hupper

/-- The published finite confidentiality boundary starts with the bytes
actually returned by `deviceRead`, not caller-fabricated translations or
observations. -/
theorem actual_read_trace_confidentiality (state : State)
    (alternateMemory : FrameId → Nat → UInt8)
    (views : List (AuthorizedReadView state))
    (hequivalent :
      ReadViewsEquivalent state.core.memory alternateMemory views) :
    actualReadObservations views = observeReadViews alternateMemory views := by
  rw [actualReadObservations_eq_observeReadViews]
  exact read_trace_confidentiality state state.core.memory alternateMemory
    views hequivalent

/-! ## Lifecycle and deny-all composition facts -/

theorem teardown_removes_all_mappings (state : State) (handle : AssignmentHandle)
    (after : State)
    (haccepted : gate state (.teardown handle) = .accepted after .tornDown) :
    after.core.mappings.all (·.assignment != handle) = true := by
  cases hfind : findAssignment state.core handle with
  | none =>
      simp [gate, hfind] at haccepted
  | some assignment =>
      by_cases howner : assignment.owner != state.core.currentOwner
      · simp [gate, hfind, howner] at haccepted
      · simp only [gate, hfind, howner, Bool.false_eq_true, if_false,
          commit] at haccepted
        split at haccepted
        · cases haccepted
          simp [eraseAssignmentMappings]
        · contradiction

theorem unmap_removes_mapping (state : State) (handle : MappingHandle)
    (after : State)
    (haccepted : gate state (.unmap handle) = .accepted after .unmapped) :
    after.core.mappings.all (·.handle != handle) = true := by
  cases hfind : findMapping state.core handle with
  | none =>
      simp [gate, hfind] at haccepted
  | some mapping =>
      by_cases howner : mapping.owner != state.core.currentOwner
      · simp [gate, hfind, howner] at haccepted
      · simp only [gate, hfind, howner, Bool.false_eq_true, if_false,
          commit] at haccepted
        split at haccepted
        · cases haccepted
          simp [eraseMapping]
        · contradiction

theorem release_rejects_reachable_frame (state : State) (handle : FrameHandle)
    (hreachable : state.core.mappings.any (·.frame == handle) = true) :
    ∃ reason, gate state (.releaseFrame handle) = .rejected reason := by
  simp only [gate]
  cases hfind : findFrame state.core handle with
  | none => exact ⟨.staleFrame, rfl⟩
  | some frame =>
      by_cases howner : frame.owner != state.core.currentOwner
      · exact ⟨.wrongOwner, by simp [howner]⟩
      · by_cases hlive : frame.live
        · by_cases hprotected :
              frame.kernelOwned || frame.pageTable || frame.allocatorMetadata
          · exact ⟨.protectedFrame, by simp [howner, hlive, hprotected]⟩
          · exact ⟨.frameStillReachable,
              by simp [howner, hlive, hprotected, hreachable]⟩
        · exact ⟨.staleFrame, by simp [howner, hlive]⟩

theorem retired_assignment_generation_rejects (state : State)
    (request : TransferRequest) (direction : Direction)
    (habsent : findAssignmentBySource state.core request.source
      request.assignmentGeneration = none) :
    ∃ reason, translate state request direction = .error reason := by
  simp only [translate]
  split
  · exact ⟨.invalidRange, rfl⟩
  · split
    · exact ⟨.staleAssignment, rfl⟩
    · next assignment hfound =>
        rw [habsent] at hfound
        contradiction

def DenyAll (state : State) : Prop :=
  state.core.assignments = [] ∧ state.core.mappings = []

structure QuarantineExtension where
  quarantine : DMAQuarantine.RuntimeState
  iommu : State

def QuarantineExtension.Invariant (state : QuarantineExtension) : Prop :=
  DMAQuarantine.RuntimeInvariant state.quarantine ∧ state.iommu.Invariant

def QuarantineExtension.DenyAllCompatible (state : QuarantineExtension) : Prop :=
  state.Invariant ∧ DenyAll state.iommu

theorem deny_all_unassigned_device_stutters
    (state : QuarantineExtension) (_hdeny : state.DenyAllCompatible)
    (after : DMAQuarantine.MemoryProjection)
    (hstep : DMAQuarantine.UnownedDeviceStep
      state.quarantine.accepted state.quarantine.memory after) :
    after = state.quarantine.memory :=
  DMAQuarantine.unowned_device_step_unchanged hstep

/-- Static composition with the sole #104 authoritative runtime. -/
structure AuthoritativeExtension where
  kernel : FailStop.CompositeState
  iommu : State
  scrub : FrameScrub.State

/-- Cross-projection authority coherence.  The selected owner is the exact
kernel-selected subject, capability provenance is the authoritative kernel
capability state, and every retained device authority owner is live. -/
def AuthoritativeExtension.Coherent (state : AuthoritativeExtension) : Prop :=
  state.iommu.core.currentOwner =
      state.kernel.execution.core.context.currentSubject ∧
    state.iommu.core.capabilityAuthority = state.kernel.capabilities ∧
    state.scrub.memory = state.kernel.virtualMemory.memory ∧
    state.iommu.core.memory = state.scrub.bytes ∧
    FrameScrub.ScrubInvariant state.scrub ∧
    (∀ assignment ∈ state.iommu.core.assignments,
      state.kernel.capabilities.subjects assignment.owner = true) ∧
    (∀ capability ∈ state.iommu.core.capabilities,
      state.kernel.capabilities.subjects capability.owner = true ∧
        state.kernel.virtualMemory.memory.binding capability.object =
          some capability.frame.frame) ∧
    (∀ mapping ∈ state.iommu.core.mappings,
      state.kernel.capabilities.subjects mapping.owner = true ∧
        ∃ capability ∈ state.iommu.core.capabilities,
          capability.owner = mapping.owner ∧
            capability.frame = mapping.frame ∧
            rangeContained mapping.frameOffset mapping.length
              capability.offset capability.length = true ∧
            mapping.permission.attenuates capability.permission = true) ∧
    (∀ frame ∈ state.iommu.core.frames,
      frame.live = true → frame.kernelOwned = false →
        frame.pageTable = false → frame.allocatorMetadata = false →
        state.kernel.capabilities.subjects frame.owner = true)

def AuthoritativeExtension.Invariant (state : AuthoritativeExtension) : Prop :=
  FailStop.AuthoritativeRuntimeWellFormed state.kernel ∧
    state.iommu.Invariant ∧ state.Coherent

def retireDeadOwnerFrames (kernel : FailStop.CompositeState)
    (frames : List Frame) : List Frame :=
  frames.map fun frame =>
    if !kernel.capabilities.subjects frame.owner &&
        !frame.kernelOwned && !frame.pageTable && !frame.allocatorMetadata then
      { frame with live := false }
    else frame

/-- Reconcile the frame-scrub lifecycle projection with an authoritative
kernel successor while retaining the byte contents and truthful per-lifetime
write history.  The complete outer coherence gate still checks that the
resulting scrub invariant holds before publishing the candidate. -/
def reconcileScrubMemory (kernel : FailStop.CompositeState)
    (scrub : FrameScrub.State) : FrameScrub.State :=
  { scrub with memory := kernel.virtualMemory.memory }

/-- Reconcile a kernel transition with device authority.  A scheduler-only
transition retains authority and synchronizes the selected subject.  If the
kernel capability projection changes, all DMA mappings and cached capability
records are revoked, dead-owner assignments are removed, and their ordinary
frames are retired before the new projection is admitted.  Any failed
validation stutters the IOMMU projection; the outer atomic gate below then
stutters the complete extension if coherence was not restored. -/
noncomputable def reconcileKernelAuthority
    (kernel : FailStop.CompositeState) (state : State) : State := by
  classical
  let authorityChanged :=
    ¬ kernel.capabilities = state.core.capabilityAuthority
  let candidate : Core :=
    if authorityChanged then
      { state.core with
        currentOwner := kernel.execution.core.context.currentSubject
        assignments := state.core.assignments.filter
          (fun assignment => kernel.capabilities.subjects assignment.owner)
        mappings := []
        frames := retireDeadOwnerFrames kernel state.core.frames
        capabilityAuthority := kernel.capabilities
        capabilities := [] }
    else
      { state.core with
        currentOwner := kernel.execution.core.context.currentSubject
        capabilityAuthority := kernel.capabilities }
  if hwell : LeanOS.Capability.WellFormed candidate.capabilityAuthority then
    if hvalid : validateCore candidate = true then
      exact ⟨candidate, hvalid, hwell⟩
    else exact state
  else exact state

/-- Kernel and IOMMU projections commit atomically.  In particular, lifecycle,
capability, mapping, and scheduler/current-subject operations cannot publish a
kernel post-state paired with stale device authority. -/
noncomputable def applyKernelOperation (state : AuthoritativeExtension)
    (operation : FailStop.AuthoritativeOperation) : AuthoritativeExtension := by
  classical
  let kernel := (FailStop.authoritativeGate state.kernel operation).state
  let candidate : AuthoritativeExtension :=
    { kernel, iommu := reconcileKernelAuthority kernel state.iommu
      scrub := reconcileScrubMemory kernel state.scrub }
  if candidate.Coherent then exact candidate else exact state

theorem kernel_operation_preserves_authoritative_extension
    (state : AuthoritativeExtension) (operation : FailStop.AuthoritativeOperation)
    (hstate : state.Invariant) :
    (applyKernelOperation state operation).Invariant := by
  classical
  simp only [applyKernelOperation]
  split
  · next hcoherent =>
      exact
        ⟨FailStop.authoritativeGate_preserves_authoritativeRuntimeWellFormed
            state.kernel operation hstate.1,
          (reconcileKernelAuthority
            (FailStop.authoritativeGate state.kernel operation).state
            state.iommu).invariant,
          hcoherent⟩
  · exact hstate

theorem kernel_operation_current_owner_coherent
    (state : AuthoritativeExtension) (operation : FailStop.AuthoritativeOperation)
    (hstate : state.Invariant) :
    (applyKernelOperation state operation).iommu.core.currentOwner =
      (applyKernelOperation state operation).kernel.execution.core.context.currentSubject :=
  (kernel_operation_preserves_authoritative_extension state operation hstate).2.2.1

theorem mismatched_current_owner_is_not_coherent
    (state : AuthoritativeExtension)
    (hmismatch : state.iommu.core.currentOwner ≠
      state.kernel.execution.core.context.currentSubject) :
    ¬ state.Coherent := by
  intro hcoherent
  exact hmismatch hcoherent.1

theorem detached_capability_authority_is_not_coherent
    (state : AuthoritativeExtension)
    (hmismatch : state.iommu.core.capabilityAuthority ≠ state.kernel.capabilities) :
    ¬ state.Coherent := by
  intro hcoherent
  exact hmismatch hcoherent.2.1

/-- The public control result carries the complete authoritative extension and
its preserved invariant.  Rejection has no post-state constructor. -/
inductive AuthoritativeOutcome (before : AuthoritativeExtension) where
  | accepted (after : AuthoritativeExtension) (invariant : after.Invariant)
      (reply : AcceptedReply)
  | rejected (reason : RejectReason)

def AuthoritativeOutcome.state {before : AuthoritativeExtension} :
    AuthoritativeOutcome before → AuthoritativeExtension
  | .accepted after _ _ => after
  | .rejected _ => before

theorem AuthoritativeOutcome.invariant {before : AuthoritativeExtension}
    (hbefore : before.Invariant) :
    (outcome : AuthoritativeOutcome before) → outcome.state.Invariant
  | .accepted _ hinvariant _ => hinvariant
  | .rejected _ => hbefore

def AuthoritativeOutcome.isAccepted {before : AuthoritativeExtension} :
    AuthoritativeOutcome before → Bool
  | .accepted _ _ _ => true
  | .rejected _ => false

def AuthoritativeOutcome.reason {before : AuthoritativeExtension} :
    AuthoritativeOutcome before → Option RejectReason
  | .accepted _ _ _ => none
  | .rejected reason => some reason

/-- Public IOMMU control requires the invariant of the coherent authoritative
kernel/IOMMU pair.  A locally valid but detached IOMMU projection cannot call
this gate.  Accepted IOMMU changes commit only when coherence with the same
kernel state is preserved atomically. -/
noncomputable def gatedByKernel (state : AuthoritativeExtension)
    (hstate : state.Invariant) (operation : Operation) :
    AuthoritativeOutcome state := by
  classical
  exact
    match state.kernel.execution.mode with
    | .running =>
        match operation with
        | .releaseFrame _ | .terminateCurrentOwner =>
            .rejected .authoritativeLifecycleRequired
        | operation =>
            match gate state.iommu operation with
            | .rejected reason => .rejected reason
            | .accepted after reply =>
                let candidate : AuthoritativeExtension :=
                  { kernel := state.kernel, iommu := after, scrub := state.scrub }
                if hcoherent : candidate.Coherent then
                  .accepted candidate ⟨hstate.1, after.invariant, hcoherent⟩ reply
                else
                  .rejected .invariantViolation
    | .handling _ => .rejected .kernelBusy
    | .halted _ => .rejected .kernelHalted

theorem gatedByKernel_preserves_authoritative_extension
    (state : AuthoritativeExtension) (hstate : state.Invariant)
    (operation : Operation) :
    (gatedByKernel state hstate operation).state.Invariant :=
  (gatedByKernel state hstate operation).invariant hstate

theorem gated_lifecycle_operations_require_authoritative_boundary
    (state : AuthoritativeExtension) (hstate : state.Invariant)
    (handle : FrameHandle)
    (hmode : state.kernel.execution.mode = .running) :
    gatedByKernel state hstate (.releaseFrame handle) =
        .rejected .authoritativeLifecycleRequired ∧
      gatedByKernel state hstate .terminateCurrentOwner =
        .rejected .authoritativeLifecycleRequired ∧
      (gatedByKernel state hstate (.releaseFrame handle)).state = state ∧
      (gatedByKernel state hstate .terminateCurrentOwner).state = state := by
  constructor
  · simp [gatedByKernel, hmode]
  constructor
  · simp [gatedByKernel, hmode]
  constructor
  · simp only [gatedByKernel, hmode]
    change state = state
    rfl
  · simp only [gatedByKernel, hmode]
    change state = state
    rfl

theorem gated_teardown_removes_all_mappings
    (state : AuthoritativeExtension) (hstate : state.Invariant)
    (handle : AssignmentHandle) (after : AuthoritativeExtension)
    (hafter : after.Invariant)
    (haccepted :
      gatedByKernel state hstate (.teardown handle) =
        .accepted after hafter .tornDown) :
    after.iommu.core.mappings.all (·.assignment != handle) = true := by
  classical
  cases hmode : state.kernel.execution.mode with
  | running =>
      cases hgate : gate state.iommu (.teardown handle) with
      | rejected reason =>
          simp [gatedByKernel, hmode, hgate] at haccepted
      | accepted iommuAfter reply =>
          simp only [gatedByKernel, hmode, hgate] at haccepted
          split at haccepted
          · next hcoherent =>
              cases haccepted
              exact teardown_removes_all_mappings
                state.iommu handle iommuAfter hgate
          · contradiction
  | handling entry =>
      simp [gatedByKernel, hmode] at haccepted
  | halted record =>
      simp [gatedByKernel, hmode] at haccepted

theorem gated_release_rejects_reachable_frame
    (state : AuthoritativeExtension) (hstate : state.Invariant)
    (handle : FrameHandle)
    (_hreachable : state.iommu.core.mappings.any (·.frame == handle) = true) :
    ∃ reason,
      gatedByKernel state hstate (.releaseFrame handle) = .rejected reason := by
  cases hmode : state.kernel.execution.mode with
  | running =>
      exact ⟨.authoritativeLifecycleRequired,
        by simp [gatedByKernel, hmode]⟩
  | handling entry =>
      exact ⟨.kernelBusy, by simp [gatedByKernel, hmode]⟩
  | halted record =>
      exact ⟨.kernelHalted, by simp [gatedByKernel, hmode]⟩

theorem halted_iommu_absorbing (state : AuthoritativeExtension)
    (hstate : state.Invariant) (operation : Operation)
    (record : FailStop.HaltRecord)
    (hhalted : state.kernel.execution.mode = .halted record) :
    gatedByKernel state hstate operation = .rejected .kernelHalted := by
  classical
  simp [gatedByKernel, hhalted]

/-! ## Atomic authoritative memory publication

Device writes and frame-lifetime transitions touch projections that the
control-only gate above deliberately retains.  This boundary derives every
post-state from the checked lower transition, synchronizes the overlapping
kernel, scrub, and IOMMU projections in one candidate, and publishes that
candidate only with the complete extension invariant. -/

inductive AuthoritativeMemoryOperation where
  | deviceWrite (request : TransferRequest) (bytes : List UInt8)
  | release (subject : FrameScrub.SubjectId) (slot : FrameScrub.SlotId)
  | allocate (object : FrameScrub.ObjectId)
      (subject : FrameScrub.SubjectId) (slot : FrameScrub.SlotId)

inductive AuthoritativeMemoryReply where
  | deviceWritten | released | allocated
  deriving DecidableEq, Repr

inductive AuthoritativeMemoryReject where
  | device (reason : RejectReason)
  | release (reason : MemoryLifecycle.ReleaseError)
  | allocation (reason : FrameScrub.AllocationError)
  | wrongOwner | missingAuthority | invariantViolation
  | kernelBusy | kernelHalted
  deriving DecidableEq, Repr

inductive AuthoritativeMemoryOutcome (before : AuthoritativeExtension) where
  | accepted (after : AuthoritativeExtension) (invariant : after.Invariant)
      (reply : AuthoritativeMemoryReply)
  | rejected (reason : AuthoritativeMemoryReject)

def AuthoritativeMemoryOutcome.state {before : AuthoritativeExtension} :
    AuthoritativeMemoryOutcome before → AuthoritativeExtension
  | .accepted after _ _ => after
  | .rejected _ => before

theorem AuthoritativeMemoryOutcome.invariant
    {before : AuthoritativeExtension} (hbefore : before.Invariant) :
    (outcome : AuthoritativeMemoryOutcome before) → outcome.state.Invariant
  | .accepted _ hinvariant _ => hinvariant
  | .rejected _ => hbefore

def AuthoritativeMemoryOutcome.isAccepted {before : AuthoritativeExtension} :
    AuthoritativeMemoryOutcome before → Bool
  | .accepted _ _ _ => true
  | .rejected _ => false

def AuthoritativeMemoryOutcome.reason {before : AuthoritativeExtension} :
    AuthoritativeMemoryOutcome before → Option AuthoritativeMemoryReject
  | .accepted _ _ _ => none
  | .rejected reason => some reason

private def setOwnedMemory
    (owned : SubjectLifecycle.ObjectId →
      Option (SubjectLifecycle.SubjectId × SubjectLifecycle.FrameId))
    (object : SubjectLifecycle.ObjectId)
    (value : Option (SubjectLifecycle.SubjectId × SubjectLifecycle.FrameId)) :=
  fun candidate => if candidate = object then value else owned candidate

private def setFrameOwner
    (owners : SubjectLifecycle.FrameId → Option SubjectLifecycle.SubjectId)
    (frame : SubjectLifecycle.FrameId)
    (value : Option SubjectLifecycle.SubjectId) :=
  fun candidate => if candidate = frame then value else owners candidate

private def setFreeFrame (free : SubjectLifecycle.FrameId → Bool)
    (frame : SubjectLifecycle.FrameId) (value : Bool) :=
  fun candidate => if candidate = frame then value else free candidate

private def retireMemoryFromLifecycle (lifecycle : SubjectLifecycle.State)
    (memory : MemoryLifecycle.State) (object : MemoryLifecycle.ObjectId)
    (frame : MemoryLifecycle.FrameId) : SubjectLifecycle.State :=
  { lifecycle with
    capabilities := memory.capabilities
    ownedMemory := setOwnedMemory lifecycle.ownedMemory object none
    mapping := fun addressSpace page =>
      match lifecycle.mapping addressSpace page with
      | some candidate => if candidate = object then none else some candidate
      | none => none
    frameOwner := setFrameOwner lifecycle.frameOwner frame none
    freeFrame := setFreeFrame lifecycle.freeFrame frame true }

private def allocateMemoryToLifecycle (lifecycle : SubjectLifecycle.State)
    (memory : MemoryLifecycle.State) (object : MemoryLifecycle.ObjectId)
    (subject : MemoryLifecycle.SubjectId) (frame : MemoryLifecycle.FrameId) :
    SubjectLifecycle.State :=
  { lifecycle with
    capabilities := memory.capabilities
    ownedMemory := setOwnedMemory lifecycle.ownedMemory object
      (some (subject, frame))
    frameOwner := setFrameOwner lifecycle.frameOwner frame (some subject)
    freeFrame := setFreeFrame lifecycle.freeFrame frame false }

private def retainLiveVirtualMappings (memory : MemoryLifecycle.State)
    (mappings : VirtualMapping.AddressSpaceId → VirtualMapping.VirtualPage →
      Option VirtualMapping.Mapping) :=
  fun addressSpace page =>
    match mappings addressSpace page with
    | some mapping =>
        if (memory.binding mapping.object).isSome then some mapping else none
    | none => none

private def retainLiveEndpointMailboxes (capabilities : LeanOS.Capability.State)
    (mailbox : EndpointIPC.ObjectId → Option EndpointIPC.Envelope) :=
  fun object =>
    if capabilities.objects object then mailbox object else none

/-- Publish one checked memory-lifecycle state through every overlapping
kernel projection.  No byte projection lives in the kernel, so bytes remain
solely in `FrameScrub` and the IOMMU candidate assembled by the outer gate. -/
private def publishKernelMemory (kernel : FailStop.CompositeState)
    (memory : MemoryLifecycle.State) (lifecycle : SubjectLifecycle.State) :
    FailStop.CompositeState :=
  let scheduler := { kernel.scheduler with lifecycle }
  let virtualMemory :=
    { kernel.virtualMemory with
      memory
      mappings :=
        retainLiveVirtualMappings memory kernel.virtualMemory.mappings }
  let endpoints :=
    { kernel.ipc.endpoints with
      capabilities := memory.capabilities
      allocator := memory.allocator
      binding := memory.binding
      issued := memory.issued
      mailbox := retainLiveEndpointMailboxes memory.capabilities
        kernel.ipc.endpoints.mailbox }
  { kernel with
    execution := { kernel.execution with
      core := { kernel.execution.core with lifecycle }
      returnAuthorityArmed := false }
    scheduler
    preemption := { kernel.preemption with scheduler }
    virtualMemory
    ipc := { kernel.ipc with virtualMemory, endpoints }
    capabilities := memory.capabilities
    lifecycle
    resumable := { kernel.resumable with
      scheduler
      translations := { kernel.resumable.translations with
        virtual := virtualMemory } }
    transfers := { kernel.transfers with toEndpointState := endpoints }
    blockingIPC := { kernel.blockingIPC with scheduler } }

private def nextFrameGeneration (frames : List Frame) (frame : FrameId) :
    Generation :=
  frames.foldl (fun next candidate =>
    if candidate.handle.frame = frame then
      max next (candidate.handle.generation + 1)
    else next) 1

private def setFrameAuthority
    (authority : LeanOS.Capability.ObjectId → Option FrameHandle)
    (object : LeanOS.Capability.ObjectId) (value : Option FrameHandle) :=
  fun candidate => if candidate = object then value else authority candidate

private def releaseMemoryCore (core : Core) (scrub : FrameScrub.State)
    (object : FrameScrub.ObjectId) (handle : FrameHandle) : Core :=
  { core with
    mappings := core.mappings.filter (·.frame != handle)
    frames := setFrameLive core.frames handle false
    capabilityAuthority := scrub.memory.capabilities
    frameAuthority := setFrameAuthority core.frameAuthority object none
    capabilities := core.capabilities.filter (·.object != object)
    memory := scrub.bytes }

private def allocateMemoryCore (core : Core) (scrub : FrameScrub.State)
    (object : FrameScrub.ObjectId) (subject : FrameScrub.SubjectId)
    (slot : FrameScrub.SlotId) (frame : FrameScrub.FrameId)
    (capability : LeanOS.Capability.Capability) : Core :=
  let handle : FrameHandle :=
    ⟨frame, nextFrameGeneration core.frames frame⟩
  let permission : Permission :=
    ⟨capability.rights.read, capability.rights.write⟩
  { core with
    frames := core.frames ++
      [⟨handle, subject, true, false, false, false, FrameScrub.frameBytes⟩]
    capabilityAuthority := scrub.memory.capabilities
    frameAuthority := setFrameAuthority core.frameAuthority object (some handle)
    capabilities := core.capabilities ++
      [⟨slot, capability.identity, subject, object, handle, 0,
        FrameScrub.frameBytes, permission⟩]
    memory := scrub.bytes }

private def findMappingCapability (core : Core) (mapping : Mapping) :
    Option Capability :=
  core.capabilities.find? fun capability =>
    capability.owner == mapping.owner &&
      capability.frame == mapping.frame &&
      rangeContained mapping.frameOffset mapping.length
        capability.offset capability.length

private noncomputable def commitAuthoritativeMemory
    (before : AuthoritativeExtension) (kernel : FailStop.CompositeState)
    (core : Core) (scrub : FrameScrub.State)
    (reply : AuthoritativeMemoryReply) :
    AuthoritativeMemoryOutcome before := by
  classical
  if hcapability :
      LeanOS.Capability.WellFormed core.capabilityAuthority then
    if hvalid : validateCore core = true then
      let iommu : State := ⟨core, hvalid, hcapability⟩
      let candidate : AuthoritativeExtension := { kernel, iommu, scrub }
      if hinvariant : candidate.Invariant then
        exact .accepted candidate hinvariant reply
      else exact .rejected .invariantViolation
    else exact .rejected .invariantViolation
  else exact .rejected .invariantViolation

/-- Public memory/data boundary for the authoritative extension.  Successful
device writes update IOMMU bytes and the scrub byte/written projections in
the same accepted constructor.  Successful release/allocation candidates
derive from `FrameScrub` and atomically republish the resulting lifecycle. -/
noncomputable def gatedMemoryByKernel (state : AuthoritativeExtension)
    (hstate : state.Invariant) (operation : AuthoritativeMemoryOperation) :
    AuthoritativeMemoryOutcome state := by
  classical
  match state.kernel.execution.mode with
  | .handling _ => exact .rejected .kernelBusy
  | .halted _ => exact .rejected .kernelHalted
  | .running =>
      match operation with
      | .deviceWrite request bytes =>
          match deviceWrite state.iommu request bytes with
          | .rejected reason => exact .rejected (.device reason)
          | .written iommu translation =>
              match findMappingCapability state.iommu.core
                  translation.mapping with
              | none => exact .rejected .missingAuthority
              | some capability =>
                  let scrub : FrameScrub.State :=
                    { state.scrub with
                      bytes := iommu.core.memory
                      written := FrameScrub.setWritten state.scrub.written
                        capability.object true }
                  let candidate : AuthoritativeExtension :=
                    { kernel := state.kernel, iommu, scrub }
                  if hcoherent : candidate.Coherent then
                    exact .accepted candidate
                      ⟨hstate.1, iommu.invariant, hcoherent⟩ .deviceWritten
                  else exact .rejected .invariantViolation
      | .release subject slot =>
          if howner :
              subject = state.kernel.execution.core.context.currentSubject then
            let outcome := FrameScrub.release state.scrub subject slot
            match outcome.result with
            | .rejected reason => exact .rejected (.release reason)
            | .accepted =>
                match LeanOS.Capability.lookup
                    state.scrub.memory.capabilities subject slot with
                | .invalidSubject | .staleSlot =>
                    exact .rejected .missingAuthority
                | .found capability =>
                    match state.scrub.memory.binding capability.object with
                    | none => exact .rejected .missingAuthority
                    | some frame =>
                        match state.iommu.core.frameAuthority
                            capability.object with
                        | none => exact .rejected .missingAuthority
                        | some handle =>
                            if hframe : handle.frame = frame then
                              match findFrame state.iommu.core handle with
                              | none => exact .rejected .missingAuthority
                              | some retained =>
                                  if retained.live then
                                    let lifecycle :=
                                      retireMemoryFromLifecycle state.kernel.lifecycle
                                        outcome.state.memory capability.object frame
                                    let kernel :=
                                      publishKernelMemory state.kernel
                                        outcome.state.memory lifecycle
                                    let core :=
                                      releaseMemoryCore state.iommu.core outcome.state
                                        capability.object handle
                                    exact commitAuthoritativeMemory state kernel core
                                      outcome.state .released
                                  else exact .rejected .missingAuthority
                            else exact .rejected .missingAuthority
          else exact .rejected .wrongOwner
      | .allocate object subject slot =>
          if howner :
              subject = state.kernel.execution.core.context.currentSubject then
            let outcome := FrameScrub.allocate state.scrub object subject slot
            match outcome.result with
            | .rejected reason => exact .rejected (.allocation reason)
            | .accepted =>
                match outcome.state.memory.binding object with
                | none => exact .rejected .missingAuthority
                | some frame =>
                    match LeanOS.Capability.lookup
                        outcome.state.memory.capabilities subject slot with
                    | .invalidSubject | .staleSlot =>
                        exact .rejected .missingAuthority
                    | .found capability =>
                        let lifecycle :=
                          allocateMemoryToLifecycle state.kernel.lifecycle
                            outcome.state.memory object subject frame
                        let kernel :=
                          publishKernelMemory state.kernel
                            outcome.state.memory lifecycle
                        let core :=
                          allocateMemoryCore state.iommu.core outcome.state
                            object subject slot frame capability
                        exact commitAuthoritativeMemory state kernel core
                          outcome.state .allocated
          else exact .rejected .wrongOwner

theorem gatedMemoryByKernel_preserves_authoritative_extension
    (state : AuthoritativeExtension) (hstate : state.Invariant)
    (operation : AuthoritativeMemoryOperation) :
    (gatedMemoryByKernel state hstate operation).state.Invariant :=
  (gatedMemoryByKernel state hstate operation).invariant hstate

theorem gatedMemory_release_rejects_mismatched_authority
    (state : AuthoritativeExtension) (hstate : state.Invariant)
    (subject : FrameScrub.SubjectId) (slot : FrameScrub.SlotId)
    (capability : LeanOS.Capability.Capability)
    (frame : FrameScrub.FrameId) (handle : FrameHandle)
    (hmode : state.kernel.execution.mode = .running)
    (howner : subject =
      state.kernel.execution.core.context.currentSubject)
    (hrelease : (FrameScrub.release state.scrub subject slot).result =
      .accepted)
    (hlookup : LeanOS.Capability.lookup
      state.scrub.memory.capabilities subject slot = .found capability)
    (hbinding : state.scrub.memory.binding capability.object = some frame)
    (hauthority :
      state.iommu.core.frameAuthority capability.object = some handle)
    (hmismatch : handle.frame ≠ frame) :
    (gatedMemoryByKernel state hstate
      (.release subject slot)).reason = some .missingAuthority := by
  classical
  subst subject
  simp [gatedMemoryByKernel, hmode, hrelease, hlookup, hbinding,
    hauthority, hmismatch]
  rfl

theorem gatedMemory_release_rejects_dangling_authority
    (state : AuthoritativeExtension) (hstate : state.Invariant)
    (subject : FrameScrub.SubjectId) (slot : FrameScrub.SlotId)
    (capability : LeanOS.Capability.Capability)
    (frame : FrameScrub.FrameId) (handle : FrameHandle)
    (hmode : state.kernel.execution.mode = .running)
    (howner : subject =
      state.kernel.execution.core.context.currentSubject)
    (hrelease : (FrameScrub.release state.scrub subject slot).result =
      .accepted)
    (hlookup : LeanOS.Capability.lookup
      state.scrub.memory.capabilities subject slot = .found capability)
    (hbinding : state.scrub.memory.binding capability.object = some frame)
    (hauthority :
      state.iommu.core.frameAuthority capability.object = some handle)
    (hframe : handle.frame = frame)
    (hdangling : findFrame state.iommu.core handle = none) :
    (gatedMemoryByKernel state hstate
      (.release subject slot)).reason = some .missingAuthority := by
  classical
  subst subject
  simp [gatedMemoryByKernel, hmode, hrelease, hlookup, hbinding,
    hauthority, hframe, hdangling]
  rfl

private theorem gatedMemory_deviceWrite_accepted_of
    (state : AuthoritativeExtension) (hstate : state.Invariant)
    (request : TransferRequest) (bytes : List UInt8)
    (after : State) (translation : Translation state.iommu request .write)
    (capability : Capability)
    (hmode : state.kernel.execution.mode = .running)
    (hwrite : deviceWrite state.iommu request bytes =
      .written after translation)
    (hcapability :
      findMappingCapability state.iommu.core translation.mapping =
        some capability)
    (hcoherent :
      ({ kernel := state.kernel
         iommu := after
         scrub :=
           { state.scrub with
             bytes := after.core.memory
             written := FrameScrub.setWritten state.scrub.written
               capability.object true } } :
        AuthoritativeExtension).Coherent) :
    (gatedMemoryByKernel state hstate
      (.deviceWrite request bytes)).isAccepted = true := by
  classical
  simp [gatedMemoryByKernel, hmode, hwrite, hcapability, hcoherent]
  rfl

private theorem gatedMemory_deviceWrite_state_of
    (state : AuthoritativeExtension) (hstate : state.Invariant)
    (request : TransferRequest) (bytes : List UInt8)
    (after : State) (translation : Translation state.iommu request .write)
    (capability : Capability)
    (hmode : state.kernel.execution.mode = .running)
    (hwrite : deviceWrite state.iommu request bytes =
      .written after translation)
    (hcapability :
      findMappingCapability state.iommu.core translation.mapping =
        some capability)
    (hcoherent :
      ({ kernel := state.kernel
         iommu := after
         scrub :=
           { state.scrub with
             bytes := after.core.memory
             written := FrameScrub.setWritten state.scrub.written
               capability.object true } } :
        AuthoritativeExtension).Coherent) :
    (gatedMemoryByKernel state hstate
      (.deviceWrite request bytes)).state =
      { kernel := state.kernel
        iommu := after
        scrub :=
          { state.scrub with
            bytes := after.core.memory
            written := FrameScrub.setWritten state.scrub.written
              capability.object true } } := by
  classical
  simp [gatedMemoryByKernel, hmode, hwrite, hcapability, hcoherent]
  rfl

noncomputable def runGated : (state : AuthoritativeExtension) → state.Invariant →
    List Operation → AuthoritativeExtension
  | state, _, [] => state
  | state, hstate, operation :: rest =>
      let outcome := gatedByKernel state hstate operation
      runGated outcome.state (outcome.invariant hstate) rest

theorem halted_iommu_suffix_absorbing (state : AuthoritativeExtension)
    (hstate : state.Invariant) (operations : List Operation)
    (record : FailStop.HaltRecord)
    (hhalted : state.kernel.execution.mode = .halted record) :
    runGated state hstate operations = state := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation rest ih =>
      simp only [runGated]
      rw [halted_iommu_absorbing state hstate operation record hhalted]
      exact ih state hstate hhalted

/-! ## Executable accepted and edge vectors -/

def zeroMemory : FrameId → Nat → UInt8 := fun frame offset =>
  UInt8.ofNat (frame * 16 + offset)

def sampleFrames : List Frame :=
  [⟨⟨0, 1⟩, 0, true, false, false, false, 64⟩,
   ⟨⟨1, 1⟩, 1, true, false, false, false, 64⟩,
   ⟨⟨2, 1⟩, 0, true, true, false, false, 64⟩,
   ⟨⟨3, 1⟩, 0, true, false, true, false, 64⟩,
   ⟨⟨4, 1⟩, 0, true, false, false, true, 64⟩]

def sampleRootCapability : LeanOS.Capability.Capability :=
  { object := 10
    kind := .memory
    rights := LeanOS.Capability.allRights
    identity := 1
    parent := none }

def sampleCapabilityAuthority : LeanOS.Capability.State :=
  { nextIdentity := 2
    derivations := fun identity =>
      if identity = 1 then
        some (none, 10, .memory, LeanOS.Capability.allRights)
      else none
    subjects := fun subject => decide (subject = 0)
    objects := fun object => decide (object = 10)
    kinds := fun object => if object = 10 then some .memory else none
    slotCapacity := fun subject => if subject = 0 then 1 else 0
    slots := fun subject slot =>
      if subject = 0 ∧ slot = 0 then some sampleRootCapability else none }

theorem sampleCapabilityAuthority_wellFormed :
    LeanOS.Capability.WellFormed sampleCapabilityAuthority := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro subject slot capability hslot
    simp [sampleCapabilityAuthority] at hslot
    rcases hslot with ⟨⟨rfl, rfl⟩, rfl⟩
    simp [sampleCapabilityAuthority, sampleRootCapability,
      LeanOS.Capability.rightsValid, LeanOS.Capability.nonemptyRights,
      LeanOS.Capability.allRights]
  · intro identity parent object kind rights hderivation
    simp [sampleCapabilityAuthority] at hderivation
    rcases hderivation with ⟨rfl, rfl, rfl, ⟨rfl, rfl⟩⟩
    simp [sampleCapabilityAuthority]
  · intro subject slot capability otherSubject otherSlot otherCapability
      hfirst hsecond _hidentity
    simp [sampleCapabilityAuthority] at hfirst hsecond
    rcases hfirst with ⟨⟨rfl, rfl⟩, rfl⟩
    rcases hsecond with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨rfl, rfl⟩
  · intro subject slot hbound
    by_cases hsubject : subject = 0
    · subst subject
      simp [sampleCapabilityAuthority] at hbound
      have hslot : slot ≠ 0 := by omega
      simp [sampleCapabilityAuthority, hslot]
    · simp [sampleCapabilityAuthority, hsubject]

def sampleCapabilities : List Capability :=
  [⟨0, 1, 0, 10, ⟨0, 1⟩, 0, 64, readWrite⟩]

def emptyCore : Core :=
  { currentOwner := 0
    nextAssignmentGeneration := 1
    nextDomainGeneration := 1
    nextMappingGeneration := 1
    assignments := []
    mappings := []
    frames := sampleFrames
    capabilityAuthority := sampleCapabilityAuthority
    frameAuthority := fun object =>
      if object == 10 then some ⟨0, 1⟩ else none
    capabilities := sampleCapabilities
    memory := zeroMemory }

def emptyState : State :=
  ⟨emptyCore, by native_decide, sampleCapabilityAuthority_wellFormed⟩

def assignedState : State :=
  (gate emptyState (.assign ⟨0⟩)).state

def assignment0 : AssignmentHandle := ⟨0, 1⟩
def domain0 : DomainHandle := ⟨0, 1⟩
def mapping0 : MappingHandle := ⟨0, 1⟩

def readOnlyGrant : GrantRequest :=
  ⟨assignment0, ⟨0, 1⟩, 0, 0, 16, readOnly⟩

def writeOnlyGrant : GrantRequest :=
  ⟨assignment0, ⟨0, 1⟩, 16, 16, 16, writeOnly⟩

def readWriteGrant : GrantRequest :=
  ⟨assignment0, ⟨0, 1⟩, 32, 32, 16, readWrite⟩

def readOnlyState : State := (gate assignedState (.grant readOnlyGrant)).state

def writeOnlyState : State := (gate assignedState (.grant writeOnlyGrant)).state

def readWriteState : State := (gate assignedState (.grant readWriteGrant)).state

example : (gate emptyState (.assign ⟨0⟩)).isAccepted = true := by native_decide
example : assignedState.core.assignments.head!.source = 0 := by native_decide
example : assignedState.core.assignments.head!.owner = emptyState.core.currentOwner := by
  native_decide +revert
example : assignedState.core.assignments.head!.domain = domain0 := by native_decide
example : (gate assignedState (.grant readOnlyGrant)).isAccepted = true := by native_decide
example : (gate assignedState (.grant writeOnlyGrant)).isAccepted = true := by native_decide
example : (gate assignedState (.grant readWriteGrant)).isAccepted = true := by native_decide

def readRequest : TransferRequest := ⟨0, 1, 0, 16⟩
def writeRequest : TransferRequest := ⟨0, 1, 16, 16⟩

def ReadOutcome.isObserved {state request} : ReadOutcome state request → Bool
  | .observed _ _ => true
  | .rejected _ => false

def ReadOutcome.reason {state request} : ReadOutcome state request → Option RejectReason
  | .observed _ _ => none
  | .rejected reason => some reason

def WriteOutcome.isWritten {state request} : WriteOutcome state request → Bool
  | .written _ _ => true
  | .rejected _ => false

def WriteOutcome.reason {state request} : WriteOutcome state request → Option RejectReason
  | .written _ _ => none
  | .rejected reason => some reason

def WriteOutcome.byteAt {state request} (frame offset : Nat) :
    WriteOutcome state request → Option UInt8
  | .written after _ => some (after.core.memory frame offset)
  | .rejected _ => none

example : (deviceRead readOnlyState readRequest).isObserved = true := by native_decide

example :
    (deviceWrite writeOnlyState writeRequest
      (List.replicate 16 0xaa)).byteAt 0 16 = some 0xaa := by native_decide

example :
    (deviceRead writeOnlyState writeRequest).reason =
      some .permissionDenied := by native_decide

example :
    (deviceWrite readOnlyState readRequest
      (List.replicate 16 0xaa)).reason = some .permissionDenied := by native_decide

example :
    (deviceRead readOnlyState { readRequest with length := 17 }).reason =
      some .invalidRange := by native_decide

example :
    (deviceRead readOnlyState { readRequest with source := 1 }).reason =
      some .staleAssignment := by native_decide

example :
    (gate readOnlyState (.grant readOnlyGrant)).reason =
      some .duplicateOrOverlappingIOVA := by native_decide

example :
    (gate readOnlyState
      (.attenuate ⟨mapping0, 0, 16, readWrite⟩)).reason =
        some .permissionAmplification := by native_decide

def attenuatedState : State :=
  (gate readWriteState (.attenuate ⟨mapping0, 0, 16, readOnly⟩)).state

example : attenuatedState.core.mappings.head!.permission = readOnly := by native_decide

def tornDownState : State := (gate readOnlyState (.teardown assignment0)).state

example : tornDownState.core.assignments = [] ∧ tornDownState.core.mappings = [] := by
  native_decide

def translationRejected (state : State) (request : TransferRequest)
    (direction : Direction) : Bool :=
  match translate state request direction with
  | .error _ => true
  | .ok _ => false

example : translationRejected tornDownState readRequest .read = true := by native_decide

example :
    (gate readOnlyState (.releaseFrame ⟨0, 1⟩)).reason =
      some .frameStillReachable := by native_decide

example :
    let released := (gate tornDownState (.releaseFrame ⟨0, 1⟩)).state
    released.core.frames.head!.live = false := by native_decide

example :
    let released := (gate tornDownState (.releaseFrame ⟨0, 1⟩)).state
    (gate released (.releaseFrame ⟨0, 1⟩)).reason = some .staleFrame := by
  native_decide

def ownerOneState : State :=
  { emptyState with
    core := { emptyState.core with currentOwner := 1 }
    valid := by native_decide }

example : (gate ownerOneState (.grant readOnlyGrant)).reason = some .staleAssignment := by
  native_decide

def switchedOwnerState : State :=
  { readOnlyState with
    core := { readOnlyState.core with currentOwner := 1 }
    valid := by native_decide }

example :
    (gate switchedOwnerState (.grant
      { readOnlyGrant with iova := 16 })).reason = some .wrongOwner := by
  native_decide

example :
    (gate tornDownState (.releaseFrame ⟨0, 2⟩)).reason = some .staleFrame := by
  native_decide

example :
    (gate emptyState (.releaseFrame ⟨2, 1⟩)).reason = some .protectedFrame := by
  native_decide

def generationExhaustedState : State :=
  { emptyState with
    core := { emptyState.core with nextAssignmentGeneration := generationReserved }
    valid := by native_decide }

example :
    (gate generationExhaustedState (.assign ⟨0⟩)).reason =
      some .assignmentExhausted := by native_decide

def mappingExhaustedState : State :=
  { assignedState with
    core := { assignedState.core with nextMappingGeneration := generationReserved }
    valid := by native_decide }

example :
    (gate mappingExhaustedState (.grant readOnlyGrant)).reason =
      some .mappingExhausted := by native_decide

def terminatedState : State := (gate readOnlyState .terminateCurrentOwner).state

example : terminatedState.core.assignments = [] ∧
    terminatedState.core.mappings = [] ∧
    terminatedState.core.capabilities.all (·.owner != 0) = true := by
  native_decide

/-! ## Coherent public-gate non-vacuity -/

def scrubbedMemory : FrameId → Nat → UInt8 := fun _ _ => FrameScrub.initialByte

/-- Match the repository's canonical mixed-dispatcher runtime: subject `2`
holds memory object `20`, which the authoritative virtual-memory projection
binds to physical frame `4`. -/
def authoritativeSampleCore (plan : BootPageTablePlan.Plan) : Core :=
  let kernel := FailStop.compositeDispatcherInitial plan
  { currentOwner := 2
    nextAssignmentGeneration := 1
    nextDomainGeneration := 1
    nextMappingGeneration := 1
    assignments := []
    mappings := []
    frames := [⟨⟨4, 1⟩, 2, true, false, false, false, 64⟩]
    capabilityAuthority := kernel.capabilities
    frameAuthority := fun object =>
      if object == 20 then some ⟨4, 1⟩ else none
    capabilities := [⟨2, 5, 2, 20, ⟨4, 1⟩, 0, 64, readWrite⟩]
    memory := scrubbedMemory }

def authoritativeSampleIOMMU (plan : BootPageTablePlan.Plan) : State :=
  { core := authoritativeSampleCore plan
    valid := by
      simp [authoritativeSampleCore, FailStop.compositeDispatcherInitial]
      native_decide
    capabilityWellFormed :=
      (FailStop.compositeDispatcherInitial_authoritativeRuntimeWellFormed
        plan).1.2.2.2.1 }

def authoritativeSampleScrub (plan : BootPageTablePlan.Plan) : FrameScrub.State :=
  { memory :=
      (FailStop.compositeDispatcherInitial plan).virtualMemory.memory
    bytes := scrubbedMemory
    written := fun _ => false }

theorem authoritativeSampleScrub_invariant (plan : BootPageTablePlan.Plan) :
    FrameScrub.ScrubInvariant (authoritativeSampleScrub plan) := by
  intro object frame hbinding _hunwritten
  change (if object = 20 then some 4 else none) = some frame at hbinding
  by_cases hobject : object = 20
  · subst object
    simp at hbinding
    subst frame
    constructor
    · rfl
    · intro offset _hoffset
      rfl
  · simp [hobject] at hbinding

def authoritativeSample (plan : BootPageTablePlan.Plan) :
    AuthoritativeExtension :=
  { kernel := FailStop.compositeDispatcherInitial plan
    iommu := authoritativeSampleIOMMU plan
    scrub := authoritativeSampleScrub plan }

theorem authoritativeSample_invariant (plan : BootPageTablePlan.Plan) :
    (authoritativeSample plan).Invariant := by
  refine
    ⟨FailStop.compositeDispatcherInitial_authoritativeRuntimeWellFormed plan,
      (authoritativeSampleIOMMU plan).invariant, ?_⟩
  refine ⟨rfl, rfl, rfl, rfl,
    authoritativeSampleScrub_invariant plan, ?_⟩
  simp [authoritativeSample,
    authoritativeSampleIOMMU, authoritativeSampleCore,
    FailStop.compositeDispatcherInitial]
  native_decide

/-- Exercise device assignment through the public coherent boundary. -/
noncomputable def authoritativeAssignedOutcome (plan : BootPageTablePlan.Plan) :=
  gatedByKernel (authoritativeSample plan) (authoritativeSample_invariant plan)
    (.assign ⟨0⟩)

noncomputable def authoritativeAssigned (plan : BootPageTablePlan.Plan) :
    AuthoritativeExtension :=
  (authoritativeAssignedOutcome plan).state

theorem authoritativeAssigned_invariant (plan : BootPageTablePlan.Plan) :
    (authoritativeAssigned plan).Invariant :=
  (authoritativeAssignedOutcome plan).invariant
    (authoritativeSample_invariant plan)

private theorem gatedByKernel_isAccepted_of_gate
    (state : AuthoritativeExtension) (hstate : state.Invariant)
    (operation : Operation)
    (hcontrol : operation.isControlOnly)
    (hmode : state.kernel.execution.mode = .running)
    (hgate : (gate state.iommu operation).isAccepted = true)
    (hcoherent :
      ({ kernel := state.kernel
         iommu := (gate state.iommu operation).state
         scrub := state.scrub } :
        AuthoritativeExtension).Coherent) :
    (gatedByKernel state hstate operation).isAccepted = true := by
  unfold gatedByKernel
  rw [hmode]
  generalize houtcome : gate state.iommu operation = outcome
  cases outcome with
  | rejected reason =>
      simp [Outcome.isAccepted, houtcome] at hgate
  | accepted after reply =>
      have hc :
          ({ kernel := state.kernel, iommu := after, scrub := state.scrub } :
            AuthoritativeExtension).Coherent := by
        rw [houtcome] at hcoherent
        exact hcoherent
      cases operation <;>
        simp_all [Operation.isControlOnly, AuthoritativeOutcome.isAccepted]

private def authoritativeAssignedCore (plan : BootPageTablePlan.Plan) : Core :=
  { authoritativeSampleCore plan with
    nextAssignmentGeneration := 2
    nextDomainGeneration := 2
    assignments :=
      [⟨⟨0, 1⟩, 0, 0, ⟨0, 1⟩, 2⟩] }

private def authoritativeAssignedIOMMU (plan : BootPageTablePlan.Plan) : State :=
  { core := authoritativeAssignedCore plan
    valid := by
      simp [authoritativeAssignedCore, authoritativeSampleCore,
        FailStop.compositeDispatcherInitial]
      native_decide
    capabilityWellFormed :=
      (authoritativeSampleIOMMU plan).capabilityWellFormed }

private theorem authoritative_assign_gate (plan : BootPageTablePlan.Plan) :
    gate (authoritativeSampleIOMMU plan) (.assign ⟨0⟩) =
      .accepted (authoritativeAssignedIOMMU plan)
        (.assigned ⟨0, 1⟩ ⟨0, 1⟩) := by
  rfl

private theorem authoritative_assign_state_core (plan : BootPageTablePlan.Plan) :
    (gate (authoritativeSampleIOMMU plan) (.assign ⟨0⟩)).state.core =
      authoritativeAssignedCore plan := by
  rfl

private theorem authoritative_assign_coherent (plan : BootPageTablePlan.Plan) :
    ({ kernel := (authoritativeSample plan).kernel
       iommu := (gate (authoritativeSample plan).iommu (.assign ⟨0⟩)).state
       scrub := (authoritativeSample plan).scrub } :
      AuthoritativeExtension).Coherent := by
  simp only [AuthoritativeExtension.Coherent, authoritativeSample]
  rw [authoritative_assign_state_core]
  refine ⟨rfl, rfl, rfl, rfl,
    authoritativeSampleScrub_invariant plan, ?_⟩
  simp [authoritativeAssignedCore, authoritativeSampleCore,
    FailStop.compositeDispatcherInitial]
  native_decide

theorem authoritative_assign_accepted (plan : BootPageTablePlan.Plan) :
    (authoritativeAssignedOutcome plan).isAccepted = true := by
  classical
  apply gatedByKernel_isAccepted_of_gate
  · trivial
  · rfl
  · rfl
  · exact authoritative_assign_coherent plan

private def authoritativeAssignedWitness (plan : BootPageTablePlan.Plan) :
    AuthoritativeExtension :=
      { kernel := (authoritativeSample plan).kernel
        iommu := authoritativeAssignedIOMMU plan
        scrub := (authoritativeSample plan).scrub }

private theorem authoritativeAssignedWitness_invariant
    (plan : BootPageTablePlan.Plan) :
    (authoritativeAssignedWitness plan).Invariant := by
  refine
    ⟨(authoritativeSample_invariant plan).1,
      (authoritativeAssignedIOMMU plan).invariant, ?_⟩
  simp only [authoritativeAssignedWitness, AuthoritativeExtension.Coherent]
  refine ⟨rfl, rfl, rfl, rfl,
    authoritativeSampleScrub_invariant plan, ?_⟩
  simp [authoritativeSample,
    authoritativeAssignedIOMMU, authoritativeAssignedCore,
    authoritativeSampleCore, FailStop.compositeDispatcherInitial]
  rfl

/-- The grant names only the accepted assignment and the kernel capability
handle.  Owner, memory object, and frame lifetime are all derived by the gate. -/
def authoritativeGrant : GrantRequest :=
  ⟨⟨0, 1⟩, ⟨2, 5⟩, 0, 0, pageSize, readWrite⟩

private def authoritativeGrantedCore (plan : BootPageTablePlan.Plan) : Core :=
  { authoritativeAssignedCore plan with
    nextMappingGeneration := 2
    mappings :=
      [⟨⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, 2, 0, pageSize,
        ⟨4, 1⟩, 0, readWrite⟩] }

private def authoritativeGrantedIOMMU (plan : BootPageTablePlan.Plan) : State :=
  { core := authoritativeGrantedCore plan
    valid := by
      simp [authoritativeGrantedCore, authoritativeAssignedCore,
        authoritativeSampleCore, FailStop.compositeDispatcherInitial]
      native_decide
    capabilityWellFormed :=
      (authoritativeSampleIOMMU plan).capabilityWellFormed }

private theorem authoritative_grant_gate (plan : BootPageTablePlan.Plan) :
    gate (authoritativeAssignedIOMMU plan) (.grant authoritativeGrant) =
      .accepted (authoritativeGrantedIOMMU plan) (.mapped ⟨0, 1⟩) := by
  have hassignment :
      ((⟨0, 1⟩ : AssignmentHandle) == ⟨0, 1⟩) = true := by native_decide
  have hframe :
      ((⟨4, 1⟩ : FrameHandle) == ⟨4, 1⟩) = true := by native_decide
  have hfree :
      firstFreeSlotAux (fun _ => false) maxMappings 0 = some 0 := by
    native_decide
  have hgeneration :
      ¬LifetimeIssuer.identityReserved ≤ 1 := by native_decide
  have hvalid :
      validateCore (authoritativeGrantedCore plan) = true :=
    (authoritativeGrantedIOMMU plan).valid
  simp [gate, authoritativeGrant, authoritativeAssignedIOMMU,
    authoritativeAssignedCore, authoritativeSampleCore, commit,
    authoritativeGrantedIOMMU, authoritativeGrantedCore,
    FailStop.compositeDispatcherInitial, findAssignment, findCapability,
    findFrame, firstFreeMappingSlot, mappingOverlaps, pageSize,
    hassignment, hframe, hfree, Permission.nonempty,
    Permission.attenuates, aligned, rangeContained, generationAvailable,
    maxIOVA, generationReserved,
    readWrite]
  split
  · next hbad =>
      exact False.elim (hgeneration hbad)
  · split
    · rfl
    · next hfalse =>
        exact False.elim (hfalse hvalid)

private theorem authoritative_grant_coherent (plan : BootPageTablePlan.Plan) :
    ({ kernel := (authoritativeSample plan).kernel
       iommu :=
         (gate (authoritativeAssignedIOMMU plan)
           (.grant authoritativeGrant)).state
       scrub := (authoritativeSample plan).scrub } :
      AuthoritativeExtension).Coherent := by
  rw [authoritative_grant_gate]
  simp only [Outcome.state, AuthoritativeExtension.Coherent,
    authoritativeSample]
  refine ⟨rfl, rfl, rfl, rfl,
    authoritativeSampleScrub_invariant plan, ?_⟩
  simp [authoritativeGrantedIOMMU, authoritativeGrantedCore,
    authoritativeAssignedCore, authoritativeSampleCore,
    FailStop.compositeDispatcherInitial, pageSize,
    rangeContained, Permission.attenuates]
  native_decide

noncomputable def authoritativeGrantedOutcome (plan : BootPageTablePlan.Plan) :=
  gatedByKernel (authoritativeAssignedWitness plan)
    (authoritativeAssignedWitness_invariant plan) (.grant authoritativeGrant)

theorem authoritative_grant_accepted (plan : BootPageTablePlan.Plan) :
    (authoritativeGrantedOutcome plan).isAccepted = true := by
  classical
  unfold authoritativeGrantedOutcome
  apply gatedByKernel_isAccepted_of_gate
  · trivial
  · rfl
  · change
      (gate (authoritativeAssignedIOMMU plan)
        (.grant authoritativeGrant)).isAccepted = true
    rw [authoritative_grant_gate]
    rfl
  · change
      ({ kernel := (authoritativeSample plan).kernel
         iommu :=
           (gate (authoritativeAssignedIOMMU plan)
             (.grant authoritativeGrant)).state
         scrub := (authoritativeSample plan).scrub } :
        AuthoritativeExtension).Coherent
    exact authoritative_grant_coherent plan

private def authoritativeGrantedWitness (plan : BootPageTablePlan.Plan) :
    AuthoritativeExtension :=
  { kernel := (authoritativeSample plan).kernel
    iommu := authoritativeGrantedIOMMU plan
    scrub := (authoritativeSample plan).scrub }

private theorem authoritativeGrantedWitness_invariant
    (plan : BootPageTablePlan.Plan) :
    (authoritativeGrantedWitness plan).Invariant := by
  refine
    ⟨(authoritativeSample_invariant plan).1,
      (authoritativeGrantedIOMMU plan).invariant, ?_⟩
  have hcoherent := authoritative_grant_coherent plan
  rw [authoritative_grant_gate] at hcoherent
  simp only [Outcome.state] at hcoherent
  simpa [authoritativeGrantedWitness] using hcoherent

/-! ## Scrubbed lifetime reuse non-vacuity -/

private def lifecycleWriteRequest : TransferRequest :=
  ⟨0, 1, 0, 1⟩

private noncomputable def lifecycleWriteOutcome
    (plan : BootPageTablePlan.Plan) :=
  gatedMemoryByKernel (authoritativeGrantedWitness plan)
    (authoritativeGrantedWitness_invariant plan)
    (.deviceWrite lifecycleWriteRequest [0xa5])

private noncomputable def lifecycleWritten
    (plan : BootPageTablePlan.Plan) : AuthoritativeExtension :=
  (lifecycleWriteOutcome plan).state

private def lifecycleWrittenBytes : FrameId → Nat → UInt8 :=
  writeMemory scrubbedMemory 4 0 [0xa5]

private def writeOutcomeState {before : State} {request : TransferRequest} :
    WriteOutcome before request → State
  | .rejected _ => before
  | .written after _ => after

private def lifecycleWrittenIOMMU (plan : BootPageTablePlan.Plan) : State :=
  writeOutcomeState
    (deviceWrite (authoritativeGrantedIOMMU plan)
      lifecycleWriteRequest [0xa5])

private def lifecycleWrittenScrub (plan : BootPageTablePlan.Plan) :
    FrameScrub.State :=
  { (authoritativeSampleScrub plan) with
    bytes := (lifecycleWrittenIOMMU plan).core.memory
    written := FrameScrub.setWritten
      (authoritativeSampleScrub plan).written 20 true }

private def lifecycleWrittenWitness (plan : BootPageTablePlan.Plan) :
    AuthoritativeExtension :=
  { kernel := (authoritativeSample plan).kernel
    iommu := lifecycleWrittenIOMMU plan
    scrub := lifecycleWrittenScrub plan }

private theorem lifecycleWrittenScrub_invariant
    (plan : BootPageTablePlan.Plan) :
    FrameScrub.ScrubInvariant (lifecycleWrittenScrub plan) := by
  intro object frame hbinding hunwritten
  have hobject : object ≠ 20 := by
    intro hequal
    subst object
    simp [lifecycleWrittenScrub, authoritativeSampleScrub,
      FrameScrub.setWritten] at hunwritten
  change (if object = 20 then some 4 else none) = some frame at hbinding
  simp [hobject] at hbinding

private theorem lifecycleWrittenWitness_coherent
    (plan : BootPageTablePlan.Plan) :
    (lifecycleWrittenWitness plan).Coherent := by
  have hcoherent := authoritative_grant_coherent plan
  rw [authoritative_grant_gate] at hcoherent
  simp only [Outcome.state] at hcoherent
  rcases hcoherent with
    ⟨howner, hcapability, hmemory, _hbytes, _hscrub,
      hassignments, hcapabilities, hmappings, hframes⟩
  refine
    ⟨howner, hcapability, hmemory, rfl,
      lifecycleWrittenScrub_invariant plan, ?_, ?_, ?_, ?_⟩
  · exact hassignments
  · exact hcapabilities
  · exact hmappings
  · exact hframes

private theorem lifecycleWrittenWitness_invariant
    (plan : BootPageTablePlan.Plan) :
    (lifecycleWrittenWitness plan).Invariant :=
  ⟨(authoritativeSample_invariant plan).1,
    (lifecycleWrittenIOMMU plan).invariant,
    lifecycleWrittenWitness_coherent plan⟩

private theorem lifecycle_write_state_exact
    (plan : BootPageTablePlan.Plan) :
    (lifecycleWriteOutcome plan).state = lifecycleWrittenWitness plan := by
  classical
  let before := authoritativeGrantedWitness plan
  have hwritten :
      (deviceWrite before.iommu lifecycleWriteRequest [0xa5]).isWritten =
        true := by
    change
      (deviceWrite (authoritativeGrantedIOMMU plan)
        lifecycleWriteRequest [0xa5]).isWritten = true
    rfl
  generalize hwrite :
      deviceWrite before.iommu lifecycleWriteRequest [0xa5] = outcome
  cases outcome with
  | rejected reason =>
      simp [WriteOutcome.isWritten, hwrite] at hwritten
  | written after translation =>
      have hmappingMember :
          translation.mapping ∈ before.iommu.core.mappings :=
        List.mem_of_find?_eq_some translation.mappingFound
      have hmapping :
          translation.mapping =
            { handle := ⟨0, 1⟩
              assignment := ⟨0, 1⟩
              domain := ⟨0, 1⟩
              owner := 2
              iova := 0
              length := pageSize
              frame := ⟨4, 1⟩
              frameOffset := 0
              permission := readWrite } := by
        simpa [before, authoritativeGrantedWitness,
          authoritativeGrantedIOMMU, authoritativeGrantedCore] using
          hmappingMember
      have hcapability :
          findMappingCapability before.iommu.core translation.mapping =
            some
              { slot := 2
                identity := 5
                owner := 2
                object := 20
                frame := ⟨4, 1⟩
                offset := 0
                length := 64
                permission := readWrite } := by
        rw [hmapping]
        rfl
      have hafter : lifecycleWrittenIOMMU plan = after := by
        change
          writeOutcomeState
              (deviceWrite (authoritativeGrantedIOMMU plan)
                lifecycleWriteRequest [0xa5]) =
            after
        calc
          writeOutcomeState
              (deviceWrite (authoritativeGrantedIOMMU plan)
                lifecycleWriteRequest [0xa5]) =
              writeOutcomeState (.written after translation) := by
                simpa [before, authoritativeGrantedWitness] using
                  congrArg writeOutcomeState hwrite
          _ = after := rfl
      have hcoherent :
          ({ kernel := before.kernel
             iommu := after
             scrub :=
               { before.scrub with
                 bytes := after.core.memory
                 written := FrameScrub.setWritten before.scrub.written
                   20 true } } :
            AuthoritativeExtension).Coherent := by
        simpa [before, authoritativeGrantedWitness,
          authoritativeSample, lifecycleWrittenWitness,
          lifecycleWrittenScrub, hafter] using
          lifecycleWrittenWitness_coherent plan
      calc
        (lifecycleWriteOutcome plan).state =
            { kernel := before.kernel
              iommu := after
              scrub :=
                { before.scrub with
                  bytes := after.core.memory
                  written := FrameScrub.setWritten before.scrub.written
                    20 true } } := by
              exact gatedMemory_deviceWrite_state_of before
                (authoritativeGrantedWitness_invariant plan)
                lifecycleWriteRequest [0xa5] after translation _ rfl hwrite
                hcapability hcoherent
        _ = lifecycleWrittenWitness plan := by
          simp [before, authoritativeGrantedWitness,
            authoritativeSample, lifecycleWrittenWitness,
            lifecycleWrittenScrub, hafter]

private theorem lifecycle_write_accepted (plan : BootPageTablePlan.Plan) :
    (lifecycleWriteOutcome plan).isAccepted = true := by
  classical
  let before := authoritativeGrantedWitness plan
  have hwritten :
      (deviceWrite before.iommu lifecycleWriteRequest [0xa5]).isWritten =
        true := by
    change
      (deviceWrite (authoritativeGrantedIOMMU plan)
        lifecycleWriteRequest [0xa5]).isWritten = true
    rfl
  generalize hwrite :
      deviceWrite before.iommu lifecycleWriteRequest [0xa5] = outcome
  cases outcome with
  | rejected reason =>
      simp [WriteOutcome.isWritten, hwrite] at hwritten
  | written after translation =>
      have hmappingMember :
          translation.mapping ∈ before.iommu.core.mappings :=
        List.mem_of_find?_eq_some translation.mappingFound
      have hmapping :
          translation.mapping =
            { handle := ⟨0, 1⟩
              assignment := ⟨0, 1⟩
              domain := ⟨0, 1⟩
              owner := 2
              iova := 0
              length := pageSize
              frame := ⟨4, 1⟩
              frameOffset := 0
              permission := readWrite } := by
        simpa [before, authoritativeGrantedWitness,
          authoritativeGrantedIOMMU, authoritativeGrantedCore] using
          hmappingMember
      have hcapability :
          findMappingCapability before.iommu.core translation.mapping =
            some
              { slot := 2
                identity := 5
                owner := 2
                object := 20
                frame := ⟨4, 1⟩
                offset := 0
                length := 64
                permission := readWrite } := by
        rw [hmapping]
        rfl
      rcases write_integrity before.iommu lifecycleWriteRequest [0xa5]
          after translation hwrite with
        ⟨howner, hnextAssignment, hnextDomain, hnextMapping,
          hassignments, hmappings, hframes, hcapabilityAuthority,
          hframeAuthority, hcapabilities, _hotherFrame, _houtside⟩
      rcases (authoritativeGrantedWitness_invariant plan).2.2 with
        ⟨hownerBefore, hcapabilityBefore, hmemoryBefore, _hbytesBefore,
          _hscrubBefore, hassignmentsBefore, hcapabilitiesBefore,
          hmappingsBefore, hframesBefore⟩
      have hscrub :
          FrameScrub.ScrubInvariant
            { (authoritativeGrantedWitness plan).scrub with
              bytes := after.core.memory
              written := FrameScrub.setWritten
                (authoritativeGrantedWitness plan).scrub.written 20 true } := by
        intro object frame hbinding hunwritten
        have hobject : object ≠ 20 := by
          intro hequal
          subst object
          simp [FrameScrub.setWritten] at hunwritten
        change (if object = 20 then some 4 else none) = some frame at hbinding
        simp [hobject] at hbinding
      have hcoherent :
          ({ kernel := before.kernel
             iommu := after
             scrub :=
               { before.scrub with
                 bytes := after.core.memory
                 written := FrameScrub.setWritten before.scrub.written
                   20 true } } :
            AuthoritativeExtension).Coherent := by
        refine
          ⟨howner.trans hownerBefore,
            hcapabilityAuthority.trans hcapabilityBefore,
            hmemoryBefore, rfl, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [before] using hscrub
        · rw [hassignments]
          exact hassignmentsBefore
        · rw [hcapabilities]
          exact hcapabilitiesBefore
        · rw [hmappings, hcapabilities]
          simpa [before] using hmappingsBefore
        · rw [hframes]
          exact hframesBefore
      exact gatedMemory_deviceWrite_accepted_of before
        (authoritativeGrantedWitness_invariant plan)
        lifecycleWriteRequest [0xa5] after translation _ rfl hwrite
        hcapability hcoherent

set_option linter.unusedSimpArgs false

/-! The lifecycle trace below uses an unfoldable two-subject kernel seed.
Unlike the canonical mixed-dispatcher witness above, none of its authority
projections is private to `FailStop`, so every release/allocation post-state
can be reduced and checked in this module. -/

private def lifecycleSubjectOneSpace : LeanOS.Capability.Capability :=
  { object := 1, kind := .addressSpace, rights := { revoke := true },
    identity := 1 }

private def lifecycleSubjectTwoSpace : LeanOS.Capability.Capability :=
  { object := 2, kind := .addressSpace, rights := { revoke := true },
    identity := 2 }

private def lifecycleSubjectTwoMemory : LeanOS.Capability.Capability :=
  { object := 20, kind := .memory, rights := LeanOS.Capability.allRights,
    identity := 3 }

private def lifecycleCapabilities : LeanOS.Capability.State :=
  { nextIdentity := 4
    derivations := fun identity =>
      if identity = 1 then
        some (none, 1, .addressSpace, { revoke := true })
      else if identity = 2 then
        some (none, 2, .addressSpace, { revoke := true })
      else if identity = 3 then
        some (none, 20, .memory, LeanOS.Capability.allRights)
      else none
    subjects := fun subject => subject = 1 || subject = 2
    objects := fun object => object = 1 || object = 2 || object = 20
    kinds := fun object =>
      if object = 1 || object = 2 then some .addressSpace
      else if object = 20 then some .memory else none
    slots := fun subject slot =>
      if subject = 1 && slot = 0 then some lifecycleSubjectOneSpace
      else if subject = 2 && slot = 0 then some lifecycleSubjectTwoSpace
      else if subject = 2 && slot = 1 then some lifecycleSubjectTwoMemory
      else none }

@[simp] private theorem lifecycleCapabilities_wellFormed :
    LeanOS.Capability.WellFormed lifecycleCapabilities := by
  simp only [LeanOS.Capability.WellFormed]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro subject slot capability hslot
    simp only [lifecycleCapabilities, lifecycleSubjectOneSpace,
      lifecycleSubjectTwoSpace, lifecycleSubjectTwoMemory] at hslot
    repeat' split at hslot
    all_goals cases hslot <;>
      simp [lifecycleCapabilities, lifecycleSubjectOneSpace,
        lifecycleSubjectTwoSpace, lifecycleSubjectTwoMemory,
        LeanOS.Capability.rightsValid,
        LeanOS.Capability.nonemptyRights,
        LeanOS.Capability.allRights]
    all_goals grind
  · intro identity parent object kind rights hderivation
    simp only [lifecycleCapabilities] at hderivation
    repeat' split at hderivation
    all_goals rcases hderivation with ⟨rfl, rfl, rfl, rfl⟩ <;>
      simp [lifecycleCapabilities]
    all_goals grind
  · intro subject slot capability otherSubject otherSlot otherCapability
      hslot hother hidentity
    simp only [lifecycleCapabilities, lifecycleSubjectOneSpace,
      lifecycleSubjectTwoSpace, lifecycleSubjectTwoMemory] at hslot hother
    repeat' split at hslot
    all_goals repeat' split at hother
    all_goals cases hslot <;> cases hother <;> simp_all
  · intro subject slot hslot
    change 4 ≤ slot at hslot
    have hne0 : slot ≠ 0 := by omega
    have hne1 : slot ≠ 1 := by omega
    simp [lifecycleCapabilities, hne0, hne1]

private def lifecycleMemory : MemoryLifecycle.State :=
  { capabilities := lifecycleCapabilities
    allocator :=
      { frames := [4]
        status := fun frame => if frame = 4 then .owned 20 else .reserved }
    binding := fun object => if object = 20 then some 4 else none
    issued := fun object => object = 1 || object = 2 || object = 20 }

private def lifecycleVirtualMemory : VirtualMapping.State :=
  { memory := lifecycleMemory
    owner := fun space =>
      if space = 1 then some 1 else if space = 2 then some 2 else none
    mappings := fun _ _ => none
    issuedAddressSpace := fun space => space = 1 || space = 2 }

private def lifecycleSubjectState : SubjectLifecycle.State :=
  { capabilities := lifecycleCapabilities
    issuedSubjects := fun subject => subject = 1 || subject = 2
    ownedMemory := fun object => if object = 20 then some (2, 4) else none
    addressOwner := lifecycleVirtualMemory.owner
    mapping := fun _ _ => none
    endpointOwner := fun _ => none
    mailbox := fun _ => none
    frameOwner := fun frame => if frame = 4 then some 2 else none
    freeFrame := fun frame => frame != 4
    runnable := fun subject => subject = 1 || subject = 2
    current := some 2 }

private def lifecycleScheduler : Scheduler.State :=
  { lifecycle := lifecycleSubjectState, ready := [1], capacity := 2 }

private def lifecycleEndpoints : EndpointIPC.State :=
  { capabilities := lifecycleCapabilities
    allocator := lifecycleMemory.allocator
    binding := lifecycleMemory.binding
    issued := lifecycleMemory.issued
    issuedAddressSpace := lifecycleVirtualMemory.issuedAddressSpace
    mailbox := fun _ => none
    sendHistory := fun _ => [] }

private def lifecycleSavedFrame : Interrupt.HardwareFrame :=
  { vector := 32
    errorCode := 0
    savedPrivilege := .user
    instructionPointer := 0x400000
    stackPointer := 0x500000
    codeSelector := 0x23
    stackSelector := 0x1b
    flags := 0x202
    canonicalInstructionPointer := true
    canonicalStackPointer := true
    flagsAllowed := true }

private def lifecycleSavedRegisters : ResumableContext.Registers :=
  { accumulator := 0, base := 0, count := 0, data := 0
    source := 0, destination := 0, basePointer := 0
    r8 := 0, r9 := 0, r10 := 0, r11 := 0, r12 := 0, r13 := 0,
    r14 := 0, r15 := 0 }

private def lifecycleSubjectOneContext : ResumableContext.Context :=
  { owner := 1
    addressSpace := 1
    frame := lifecycleSavedFrame
    registers := lifecycleSavedRegisters
    kind := .suspended }

private def lifecycleKernel (plan : BootPageTablePlan.Plan) :
    FailStop.CompositeState :=
  let base := FailStop.bootRuntime plan
  let scheduler := lifecycleScheduler
  { base with
    execution :=
      { base.execution with
        core :=
          { lifecycle := lifecycleSubjectState
            context :=
              { base.execution.core.context with
                currentSubject := 2
                activeAddressSpace := 2 } }
        mode := .running }
    scheduler
    preemption := { base.preemption with scheduler }
    virtualMemory := lifecycleVirtualMemory
    ipc := { virtualMemory := lifecycleVirtualMemory, endpoints := lifecycleEndpoints }
    capabilities := lifecycleCapabilities
    lifecycle := lifecycleSubjectState
    resumable :=
      { scheduler
        contexts := [lifecycleSubjectOneContext]
        capacity := 2
        translations :=
          { virtual := lifecycleVirtualMemory
            active := some 2
            entries := [] } }
    transfers := { toEndpointState := lifecycleEndpoints, pending := fun _ => none }
    blockingIPC :=
      { scheduler
        mailbox := fun _ => none
        waiters := fun _ => []
        waiterEndpoint := fun _ => none
        waiterCapacity := 0
        completion := fun _ => none }
    blockingContexts := fun _ => none
    deferredCancels := BlockingIPCContext.emptyDeferred }

private theorem lifecycleAddressOwner_some_iff
    (addressSpace subject : Nat) :
    lifecycleSubjectState.addressOwner addressSpace = some subject ↔
      (addressSpace = 1 ∧ subject = 1) ∨
        (addressSpace = 2 ∧ subject = 2) := by
  constructor
  · intro howner
    by_cases hfirst : addressSpace = 1
    · subst addressSpace
      simp [lifecycleSubjectState, lifecycleVirtualMemory] at howner
      exact Or.inl ⟨rfl, howner.symm⟩
    · by_cases hsecond : addressSpace = 2
      · subst addressSpace
        simp [lifecycleSubjectState, lifecycleVirtualMemory] at howner
        exact Or.inr ⟨rfl, howner.symm⟩
      · simp [lifecycleSubjectState, lifecycleVirtualMemory,
          hfirst, hsecond] at howner
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      simp [lifecycleSubjectState, lifecycleVirtualMemory]

private theorem lifecycleAddressSpace_live (addressSpace : Nat)
    (_hobject : lifecycleCapabilities.objects addressSpace = true)
    (hkind : lifecycleCapabilities.kinds addressSpace =
      some .addressSpace) :
    addressSpace = 1 ∨ addressSpace = 2 := by
  by_cases hlive : addressSpace = 1 ∨ addressSpace = 2
  · exact hlive
  · have hne1 : addressSpace ≠ 1 := fun heq => hlive (Or.inl heq)
    have hne2 : addressSpace ≠ 2 := fun heq => hlive (Or.inr heq)
    simp [lifecycleCapabilities, hne1, hne2] at hkind

set_option maxHeartbeats 2000000 in
private theorem lifecycleKernel_invariant (plan : BootPageTablePlan.Plan) :
    FailStop.AuthoritativeRuntimeWellFormed (lifecycleKernel plan) := by
  rcases lifecycleCapabilities_wellFormed with
    ⟨hslots, hderivations, hidentities, hslotSpaces⟩
  have hspace1 :
      LeanOS.Capability.HasAuthority lifecycleCapabilities 1 1 .revoke :=
    ⟨0, lifecycleSubjectOneSpace, rfl, rfl, rfl⟩
  have hspace2 :
      LeanOS.Capability.HasAuthority lifecycleCapabilities 2 2 .revoke :=
    ⟨0, lifecycleSubjectTwoSpace, rfl, rfl, rfl⟩
  have hownerAuthorityIf :
      ∀ addressSpace subject,
        (if addressSpace = 1 then some 1
          else if addressSpace = 2 then some 2 else none) = some subject →
          LeanOS.Capability.HasAuthority lifecycleCapabilities
            subject addressSpace .revoke := by
    intro addressSpace subject howner
    rcases (lifecycleAddressOwner_some_iff addressSpace subject).1
        (by simpa [lifecycleSubjectState, lifecycleVirtualMemory] using
          howner) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hspace1
    · exact hspace2
  have haddressComplete :
      ∀ addressSpace,
        lifecycleCapabilities.objects addressSpace = true →
          lifecycleCapabilities.kinds addressSpace = some .addressSpace →
            ∃ subject,
              lifecycleSubjectState.addressOwner addressSpace =
                some subject := by
    intro addressSpace hobject hkind
    rcases lifecycleAddressSpace_live addressSpace hobject hkind with
      rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  have hsubjectOneContextValid :
      ResumablePreemption.validContext
        (lifecycleKernel plan).resumable lifecycleSubjectOneContext := by
    simp [ResumablePreemption.validContext, lifecycleKernel,
      lifecycleSubjectOneContext, lifecycleSavedFrame,
      lifecycleScheduler, lifecycleSubjectState, lifecycleVirtualMemory,
      lifecycleCapabilities,
      Scheduler.ownsAddressSpace,
      Interrupt.validSavedUserFrame]
  have htlbCoherent :
      TLB.Coherent (lifecycleKernel plan).resumable.translations := by
    simp [TLB.Coherent, lifecycleKernel]
  have hportControls :
      DirectPortIO.AcceptedControls DirectPortIO.selectedControls := rfl
  have hdmaQuarantined :
      (FailStop.bootRuntime plan).dmaObserved =
        (FailStop.bootRuntime plan).dmaAccepted.snapshot := rfl
  have hownerFacts :
      ∀ addressSpace subject,
        (if addressSpace = 1 then some 1
          else if addressSpace = 2 then some 2 else none) = some subject →
          ((addressSpace = 1 ∨ addressSpace = 2) ∨ addressSpace = 20) ∧
          (addressSpace ≠ 1 → addressSpace = 2) ∧
          (addressSpace = 1 ∨ addressSpace = 2) ∧
          ((addressSpace = 1 ∨ addressSpace = 2) ∨ addressSpace = 20) := by
    intro addressSpace subject howner
    by_cases hfirst : addressSpace = 1
    · subst addressSpace
      simp
    · by_cases hsecond : addressSpace = 2
      · subst addressSpace
        simp
      · simp [hfirst, hsecond] at howner
  have hsubjectLive :
      ∀ subject, lifecycleCapabilities.subjects subject = true →
        subject = 1 ∨ subject = 2 := by
    intro subject hlive
    simp [lifecycleCapabilities] at hlive
    exact hlive
  have hobjectLive :
      ∀ object, lifecycleCapabilities.objects object = true →
        (object = 1 ∨ object = 2) ∨ object = 20 := by
    intro object hlive
    simp [lifecycleCapabilities] at hlive
    exact hlive
  have hnoEndpointKind :
      ∀ object, lifecycleCapabilities.objects object = true →
        lifecycleCapabilities.kinds object = some .endpoint → False := by
    intro object hlive hkind
    rcases hobjectLive object hlive with (rfl | rfl) | rfl <;>
      simp [lifecycleCapabilities] at hkind
  have hconcreteCapabilities :
      lifecycleCapabilities.subjects 1 = true ∧
      lifecycleCapabilities.subjects 2 = true ∧
      lifecycleCapabilities.objects 1 = true ∧
      lifecycleCapabilities.objects 2 = true ∧
      lifecycleCapabilities.objects 20 = true ∧
      lifecycleCapabilities.kinds 1 = some .addressSpace ∧
      lifecycleCapabilities.kinds 2 = some .addressSpace ∧
      lifecycleCapabilities.kinds 20 = some .memory := by
    simp [lifecycleCapabilities]
  have hlifecycleWellFormed :
      SubjectLifecycle.WellFormed lifecycleSubjectState := by
    simp [SubjectLifecycle.WellFormed, lifecycleSubjectState,
      lifecycleCapabilities, lifecycleVirtualMemory]
    grind
  have hdeferredWellFormed :
      (lifecycleKernel plan).DeferredCancellationWellFormed := by
    simp [FailStop.CompositeState.DeferredCancellationWellFormed,
      BlockingIPCContext.DeferredWellFormed,
      FailStop.CompositeState.blockingIPCContext,
      BlockingIPCContext.WellFormed,
      BlockingIPCContext.ContextAgreement, BlockingIPC.WellFormed,
      BlockingIPC.authorizedReceive, BlockingIPCContext.emptyDeferred,
      lifecycleKernel, lifecycleScheduler, lifecycleSubjectState,
      lifecycleCapabilities, lifecycleVirtualMemory,
      Scheduler.WellFormed, Scheduler.ownsAddressSpace]
    constructor
    · exact hlifecycleWellFormed
    · simpa [lifecycleCapabilities] using lifecycleCapabilities_wellFormed
  suffices hlegacy :
      FailStop.DeferredBlockingRuntimeWellFormed
        (lifecycleKernel plan) by
    refine ⟨hlegacy.1, hlegacy.2, ?_⟩
    change InvalidationPublication.WellFormed InvalidationPublication.initial
    exact InvalidationPublication.initial_wellFormed
  refine ⟨?_, hdeferredWellFormed⟩
  simp only [FailStop.RuntimeWellFormed]
  repeat' apply And.intro
  all_goals first
    | assumption
    | exact hsubjectOneContextValid
    | exact htlbCoherent
    | exact hportControls
    | exact hdmaQuarantined
    | exact hlifecycleWellFormed
    | simp [ResumablePreemption.validContext,
        lifecycleSubjectOneContext, lifecycleSavedFrame,
        Interrupt.validSavedUserFrame]
    | simp (config := { failIfUnchanged := false })
        [lifecycleKernel, lifecycleScheduler, lifecycleSubjectState,
          lifecycleVirtualMemory, lifecycleMemory, lifecycleEndpoints,
          lifecycleSubjectOneContext, lifecycleSavedFrame,
          lifecycleSavedRegisters, FailStop.CompositeState.Coherent,
          FailStop.WellFormed, Interrupt.WellFormed,
          VirtualMapping.LifecycleWellFormed, VirtualMapping.WellFormed,
          IPCSyscall.WellFormed, EndpointIPC.WellFormed,
          Scheduler.WellFormed, Preemption.WellFormed,
          ResumablePreemption.WellFormed,
          ResumablePreemption.ReadyContextAgreement,
          ResumablePreemption.TranslationAgreement,
          ResumablePreemption.VirtualAgreement,
          ResumablePreemption.ResourceKindAgreement,
          CapabilityTransfer.WellFormed,
          FailStop.CompositeState.ReturnPlanLive,
          FailStop.CompositeState.blockingIPCContext,
          FailStop.CompositeState.BlockingIPCCoherent,
          FailStop.CompositeState.DeferredCancellationWellFormed,
          BlockingIPCContext.DeferredWellFormed,
          BlockingIPCContext.WellFormed,
          BlockingIPCContext.ContextAgreement, BlockingIPC.WellFormed,
          BlockingIPC.authorizedReceive, BlockingIPCContext.emptyDeferred,
          BlockingIPCContext.validSaved, Scheduler.ownsAddressSpace,
          ResumablePreemption.contextFor,
          ResumablePreemption.validContext,
          LeanOS.Capability.rightsValid,
          LeanOS.Capability.rightsSubset,
          LeanOS.Capability.nonemptyRights,
          Interrupt.validSavedUserFrame,
          DMAQuarantine.q35Accepted, FailStop.bootRuntime]
  all_goals simp (config := { failIfUnchanged := false })
    [lifecycleKernel, lifecycleSubjectState,
      lifecycleScheduler, lifecycleVirtualMemory, lifecycleMemory,
      lifecycleEndpoints, lifecycleSubjectOneContext,
      lifecycleSavedFrame, lifecycleSavedRegisters,
      ResumablePreemption.contextFor,
      Scheduler.ownsAddressSpace]
  all_goals grind

private def lifecycleScrub : FrameScrub.State :=
  { memory := lifecycleMemory
    bytes := scrubbedMemory
    written := fun _ => false }

private theorem lifecycleScrub_invariant :
    FrameScrub.ScrubInvariant lifecycleScrub := by
  intro object frame hbinding _hunwritten
  change (if object = 20 then some 4 else none) = some frame at hbinding
  by_cases hobject : object = 20
  · subst object
    simp at hbinding
    subst frame
    exact ⟨rfl, by intros; rfl⟩
  · simp [hobject] at hbinding

private def lifecycleInitialCore : Core :=
  { currentOwner := 2
    nextAssignmentGeneration := 2
    nextDomainGeneration := 2
    nextMappingGeneration := 2
    assignments := [⟨⟨0, 1⟩, 0, 0, ⟨0, 1⟩, 2⟩]
    mappings :=
      [⟨⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, 2, 0, pageSize,
        ⟨4, 1⟩, 0, readWrite⟩]
    frames := [⟨⟨4, 1⟩, 2, true, false, false, false, 64⟩]
    capabilityAuthority := lifecycleCapabilities
    frameAuthority := fun object =>
      if object = 20 then some ⟨4, 1⟩ else none
    capabilities := [⟨1, 3, 2, 20, ⟨4, 1⟩, 0, 64, readWrite⟩]
    memory := scrubbedMemory }

private def lifecycleInitialIOMMU : State :=
  { core := lifecycleInitialCore
    valid := by native_decide
    capabilityWellFormed := lifecycleCapabilities_wellFormed }

private def lifecycleInitial (plan : BootPageTablePlan.Plan) :
    AuthoritativeExtension :=
  { kernel := lifecycleKernel plan
    iommu := lifecycleInitialIOMMU
    scrub := lifecycleScrub }

private theorem lifecycleInitial_invariant (plan : BootPageTablePlan.Plan) :
    (lifecycleInitial plan).Invariant := by
  refine ⟨lifecycleKernel_invariant plan, lifecycleInitialIOMMU.invariant, ?_⟩
  refine ⟨rfl, rfl, rfl, rfl, lifecycleScrub_invariant, ?_⟩
  simp [lifecycleInitial, lifecycleInitialIOMMU, lifecycleInitialCore,
    lifecycleKernel, lifecycleCapabilities, lifecycleMemory,
    lifecycleSubjectState, lifecycleVirtualMemory, pageSize,
    rangeContained, Permission.attenuates]

private def publicationWriteRequest : TransferRequest :=
  ⟨0, 1, 0, 1⟩

private def lifecycleAfterWriteBytes : FrameId → Nat → UInt8 :=
  writeMemory scrubbedMemory 4 0 [0xa5]

private def lifecycleAfterWriteIOMMU : State :=
  { core := { lifecycleInitialCore with memory := lifecycleAfterWriteBytes }
    valid := by
      change validateCore lifecycleInitialCore = true
      exact lifecycleInitialIOMMU.valid
    capabilityWellFormed := lifecycleCapabilities_wellFormed }

private def lifecycleAfterWriteScrub : FrameScrub.State :=
  { lifecycleScrub with
    bytes := lifecycleAfterWriteBytes
    written := FrameScrub.setWritten lifecycleScrub.written 20 true }

private theorem lifecycleAfterWriteScrub_invariant :
    FrameScrub.ScrubInvariant lifecycleAfterWriteScrub := by
  intro object frame hbinding hunwritten
  have hobject : object ≠ 20 := by
    intro heq
    subst object
    simp [lifecycleAfterWriteScrub, FrameScrub.setWritten] at hunwritten
  change (if object = 20 then some 4 else none) = some frame at hbinding
  simp [hobject] at hbinding

private def lifecycleAfterWrite (plan : BootPageTablePlan.Plan) :
    AuthoritativeExtension :=
  { kernel := lifecycleKernel plan
    iommu := lifecycleAfterWriteIOMMU
    scrub := lifecycleAfterWriteScrub }

private theorem lifecycleAfterWrite_coherent (plan : BootPageTablePlan.Plan) :
    (lifecycleAfterWrite plan).Coherent := by
  refine ⟨rfl, rfl, rfl, rfl, lifecycleAfterWriteScrub_invariant, ?_⟩
  simp [lifecycleAfterWrite, lifecycleAfterWriteIOMMU,
    lifecycleInitialCore, lifecycleKernel, lifecycleCapabilities,
    lifecycleMemory, lifecycleSubjectState, lifecycleVirtualMemory,
    pageSize, rangeContained, Permission.attenuates]

private theorem lifecycleAfterWrite_invariant (plan : BootPageTablePlan.Plan) :
    (lifecycleAfterWrite plan).Invariant :=
  ⟨lifecycleKernel_invariant plan, lifecycleAfterWriteIOMMU.invariant,
    lifecycleAfterWrite_coherent plan⟩

/-! A concrete invariant-bearing state exercises the release guard independently
of the successful trace.  The kernel binding names frame 4, while the uncached
IOMMU object authority deliberately names a different live frame. -/
private def mismatchedReleaseCore : Core :=
  { lifecycleAfterWriteIOMMU.core with
    mappings := []
    frames := lifecycleAfterWriteIOMMU.core.frames ++
      [⟨⟨5, 1⟩, 2, true, false, false, false, 64⟩]
    frameAuthority := fun object =>
      if object = 20 then some ⟨5, 1⟩ else none
    capabilities := [] }

private def mismatchedReleaseIOMMU : State :=
  { core := mismatchedReleaseCore
    valid := by native_decide
    capabilityWellFormed := lifecycleCapabilities_wellFormed }

private def mismatchedReleaseState (plan : BootPageTablePlan.Plan) :
    AuthoritativeExtension :=
  { kernel := lifecycleKernel plan
    iommu := mismatchedReleaseIOMMU
    scrub := lifecycleAfterWriteScrub }

private theorem mismatchedReleaseState_invariant
    (plan : BootPageTablePlan.Plan) :
    (mismatchedReleaseState plan).Invariant := by
  refine ⟨lifecycleKernel_invariant plan, mismatchedReleaseIOMMU.invariant, ?_⟩
  refine ⟨rfl, rfl, rfl, rfl, lifecycleAfterWriteScrub_invariant, ?_⟩
  simp [mismatchedReleaseState, mismatchedReleaseIOMMU,
    mismatchedReleaseCore, lifecycleAfterWriteIOMMU,
    lifecycleInitialCore, lifecycleKernel, lifecycleCapabilities,
    lifecycleMemory, lifecycleSubjectState, lifecycleVirtualMemory]

theorem mismatched_live_release_authority_rejects
    (plan : BootPageTablePlan.Plan) :
    (gatedMemoryByKernel (mismatchedReleaseState plan)
      (mismatchedReleaseState_invariant plan)
      (.release 2 1)).reason = some .missingAuthority := by
  apply gatedMemory_release_rejects_mismatched_authority
    (mismatchedReleaseState plan) (mismatchedReleaseState_invariant plan)
    2 1 lifecycleSubjectTwoMemory 4 ⟨5, 1⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · decide

private noncomputable def publicationWriteOutcome
    (plan : BootPageTablePlan.Plan) :=
  gatedMemoryByKernel (lifecycleInitial plan)
    (lifecycleInitial_invariant plan)
    (.deviceWrite publicationWriteRequest [0xa5])

private def publicationWriteTranslation :
    Translation lifecycleInitialIOMMU publicationWriteRequest .write :=
  { assignment := ⟨⟨0, 1⟩, 0, 0, ⟨0, 1⟩, 2⟩
    mapping :=
      ⟨⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, 2, 0, pageSize,
        ⟨4, 1⟩, 0, readWrite⟩
    frame := ⟨⟨4, 1⟩, 2, true, false, false, false, 64⟩
    assignmentFound := by native_decide
    mappingFound := by native_decide
    frameFound := by native_decide
    sourceBound := rfl
    assignmentGenerationBound := rfl
    mappingAssignmentBound := rfl
    domainBound := rfl
    ownerBound := rfl
    frameHandleBound := rfl
    frameOwnerBound := rfl
    frameLive := rfl
    frameNotKernel := rfl
    frameNotPageTable := rfl
    frameNotAllocatorMetadata := rfl
    transferContained := by native_decide
    backingContained := by native_decide
    directionPermitted := rfl }

theorem authoritative_lifecycle_write_accepted
    (plan : BootPageTablePlan.Plan) :
    (publicationWriteOutcome plan).isAccepted = true := by
  apply gatedMemory_deviceWrite_accepted_of
      (lifecycleInitial plan) (lifecycleInitial_invariant plan)
      publicationWriteRequest [0xa5] lifecycleAfterWriteIOMMU
      publicationWriteTranslation
      { slot := 1, identity := 3, owner := 2, object := 20
        frame := ⟨4, 1⟩, offset := 0, length := 64
        permission := readWrite }
  · rfl
  · rfl
  · rfl
  · exact lifecycleAfterWrite_coherent plan

private theorem authoritative_lifecycle_write_state_exact
    (plan : BootPageTablePlan.Plan) :
    (publicationWriteOutcome plan).state = lifecycleAfterWrite plan := by
  exact gatedMemory_deviceWrite_state_of
    (lifecycleInitial plan) (lifecycleInitial_invariant plan)
    publicationWriteRequest [0xa5] lifecycleAfterWriteIOMMU
    publicationWriteTranslation
    { slot := 1, identity := 3, owner := 2, object := 20
      frame := ⟨4, 1⟩, offset := 0, length := 64
      permission := readWrite }
    rfl rfl rfl (lifecycleAfterWrite_coherent plan)

private def lifecycleReleaseScrub : FrameScrub.State :=
  (FrameScrub.release lifecycleAfterWriteScrub 2 1).state

private def lifecycleReleasedCapabilities : LeanOS.Capability.State :=
  MemoryLifecycle.retireCapabilities lifecycleCapabilities 20

@[simp] private theorem lifecycle_retired_capabilities_exact :
    MemoryLifecycle.retireCapabilities lifecycleCapabilities 20 =
      lifecycleReleasedCapabilities := rfl

@[simp] private theorem lifecycleReleaseScrub_capabilities :
    lifecycleReleaseScrub.memory.capabilities =
      lifecycleReleasedCapabilities := by
  exact lifecycle_retired_capabilities_exact

@[simp] private theorem lifecycleReleasedCapabilities_subjects :
    lifecycleReleasedCapabilities.subjects =
      lifecycleCapabilities.subjects := rfl

@[simp] private theorem lifecycleReleaseScrub_binding :
    lifecycleReleaseScrub.memory.binding =
      MemoryLifecycle.setBinding lifecycleMemory.binding 20 none := by
  rfl

@[simp] private theorem lifecycleReleaseScrub_issued :
    lifecycleReleaseScrub.memory.issued = lifecycleMemory.issued := by
  rfl

@[simp] private theorem lifecycleReleaseScrub_allocator :
    lifecycleReleaseScrub.memory.allocator =
      FrameAllocator.setStatus lifecycleMemory.allocator 4 .free := by
  rfl

@[simp] private theorem lifecycleReleaseScrub_bytes :
    lifecycleReleaseScrub.bytes = lifecycleAfterWriteBytes := by
  rfl

private def lifecycleReleaseLifecycle : SubjectLifecycle.State :=
  retireMemoryFromLifecycle lifecycleSubjectState
    lifecycleReleaseScrub.memory 20 4

private def lifecycleReleaseKernel (plan : BootPageTablePlan.Plan) :
    FailStop.CompositeState :=
  publishKernelMemory (lifecycleKernel plan)
    lifecycleReleaseScrub.memory lifecycleReleaseLifecycle

private def lifecycleReleaseCore : Core :=
  releaseMemoryCore lifecycleAfterWriteIOMMU.core lifecycleReleaseScrub
    20 ⟨4, 1⟩

private def lifecycleReleaseIOMMU : State :=
  { core := lifecycleReleaseCore
    valid := by native_decide
    capabilityWellFormed := by
      change LeanOS.Capability.WellFormed
        lifecycleReleaseScrub.memory.capabilities
      rw [lifecycleReleaseScrub_capabilities,
        ← lifecycle_retired_capabilities_exact]
      rcases lifecycleCapabilities_wellFormed with
        ⟨hslots, hderivations, hidentities, hslotSpaces⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro subject slot capability hslot
        cases hsource : lifecycleCapabilities.slots subject slot with
        | none =>
            simp [MemoryLifecycle.retireCapabilities, hsource] at hslot
        | some existing =>
            by_cases hretired : existing.object = 20
            · simp [MemoryLifecycle.retireCapabilities, hsource,
                hretired] at hslot
            · have hslot' :
                  lifecycleCapabilities.slots subject slot =
                    some capability := by
                simpa [MemoryLifecycle.retireCapabilities, hsource,
                  hretired] using hslot
              have heq : existing = capability := by
                rw [hsource] at hslot'
                injection hslot'
              subst existing
              simpa [MemoryLifecycle.retireCapabilities,
                MemoryLifecycle.setObject, hretired] using
                hslots subject slot capability hslot'
      · exact hderivations
      · intro subject slot capability otherSubject otherSlot otherCapability
          hslot hother hidentity
        cases hsource : lifecycleCapabilities.slots subject slot with
        | none =>
            simp [MemoryLifecycle.retireCapabilities, hsource] at hslot
        | some existing =>
            cases hotherSource :
                lifecycleCapabilities.slots otherSubject otherSlot with
            | none =>
                simp [MemoryLifecycle.retireCapabilities,
                  hotherSource] at hother
            | some otherExisting =>
                by_cases hretired : existing.object = 20
                · simp [MemoryLifecycle.retireCapabilities, hsource,
                    hretired] at hslot
                · by_cases hotherRetired : otherExisting.object = 20
                  · simp [MemoryLifecycle.retireCapabilities,
                      hotherSource, hotherRetired] at hother
                  · have hslot' :
                        lifecycleCapabilities.slots subject slot =
                          some capability := by
                      simpa [MemoryLifecycle.retireCapabilities, hsource,
                        hretired] using hslot
                    have hother' :
                        lifecycleCapabilities.slots otherSubject otherSlot =
                          some otherCapability := by
                      simpa [MemoryLifecycle.retireCapabilities,
                        hotherSource, hotherRetired] using hother
                    have heq : existing = capability := by
                      rw [hsource] at hslot'
                      injection hslot'
                    have hotherEq : otherExisting = otherCapability := by
                      rw [hotherSource] at hother'
                      injection hother'
                    subst existing
                    subst otherExisting
                    exact hidentities subject slot capability otherSubject
                      otherSlot otherCapability hslot' hother' hidentity
      · intro subject slot hslot
        have hnone := hslotSpaces subject slot hslot
        simp [MemoryLifecycle.retireCapabilities, hnone] }

private def lifecycleReleased (plan : BootPageTablePlan.Plan) :
    AuthoritativeExtension :=
  { kernel := lifecycleReleaseKernel plan
    iommu := lifecycleReleaseIOMMU
    scrub := lifecycleReleaseScrub }

private theorem lifecycleReleaseScrub_invariant :
    FrameScrub.ScrubInvariant lifecycleReleaseScrub := by
  intro object frame hbinding _hunwritten
  change
    (MemoryLifecycle.setBinding lifecycleMemory.binding 20 none) object =
      some frame at hbinding
  simp [MemoryLifecycle.setBinding, lifecycleMemory] at hbinding
  exact (hbinding.1 hbinding.2.1).elim

set_option maxHeartbeats 6000000 in
private theorem lifecycleReleaseKernel_invariant
    (plan : BootPageTablePlan.Plan) :
    FailStop.AuthoritativeRuntimeWellFormed (lifecycleReleaseKernel plan) := by
  have hcapabilities :
      LeanOS.Capability.WellFormed
        lifecycleReleaseScrub.memory.capabilities :=
    lifecycleReleaseIOMMU.capabilityWellFormed
  rcases hcapabilities with
    ⟨hslots, hderivations, hidentities, hslotSpaces⟩
  have hspace1 :
      LeanOS.Capability.HasAuthority
        lifecycleReleaseScrub.memory.capabilities 1 1 .revoke := by
    exact ⟨0, lifecycleSubjectOneSpace, rfl, rfl, rfl⟩
  have hspace2 :
      LeanOS.Capability.HasAuthority
        lifecycleReleaseScrub.memory.capabilities 2 2 .revoke := by
    exact ⟨0, lifecycleSubjectTwoSpace, rfl, rfl, rfl⟩
  have hownerAuthorityIf :
      ∀ addressSpace subject,
        lifecycleReleaseLifecycle.addressOwner addressSpace = some subject →
          LeanOS.Capability.HasAuthority
            lifecycleReleaseScrub.memory.capabilities
            subject addressSpace .revoke := by
    intro addressSpace subject howner
    rcases (lifecycleAddressOwner_some_iff addressSpace subject).1
        (by simpa [lifecycleReleaseLifecycle,
          retireMemoryFromLifecycle] using howner) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hspace1
    · exact hspace2
  have haddressComplete :
      ∀ addressSpace,
        lifecycleReleaseScrub.memory.capabilities.objects addressSpace = true →
          lifecycleReleaseScrub.memory.capabilities.kinds addressSpace =
            some .addressSpace →
            ∃ subject,
              lifecycleReleaseLifecycle.addressOwner addressSpace =
                some subject := by
    intro addressSpace hobject hkind
    have hkindPair :
        addressSpace ≠ 20 ∧
          lifecycleCapabilities.kinds addressSpace =
            some .addressSpace := by
      simpa [lifecycleReleasedCapabilities,
        MemoryLifecycle.retireCapabilities] using hkind
    have hkind' :
        lifecycleCapabilities.kinds addressSpace = some .addressSpace := by
      exact hkindPair.2
    have hobjectPair :
        addressSpace ≠ 20 ∧
          lifecycleCapabilities.objects addressSpace = true := by
      simpa [lifecycleReleasedCapabilities,
        MemoryLifecycle.retireCapabilities,
        MemoryLifecycle.setObject] using hobject
    rcases lifecycleAddressSpace_live addressSpace
        hobjectPair.2
        hkind' with rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  have hreleaseMailboxesEmpty :
      ∀ object,
        retainLiveEndpointMailboxes
            lifecycleReleaseScrub.memory.capabilities (fun _ => none)
            object = none := by
    intro object
    simp [retainLiveEndpointMailboxes]
  have hreleaseOwnedMemoryEmpty :
      ∀ object, lifecycleReleaseLifecycle.ownedMemory object = none := by
    intro object
    simp [lifecycleReleaseLifecycle, retireMemoryFromLifecycle,
      setOwnedMemory, lifecycleSubjectState]
  have hreleaseOwnedMemoryProjection :
      ∀ object,
        setOwnedMemory
            (fun candidate => if candidate = 20 then some (2, 4) else none)
            20 none object = none := by
    intro object
    by_cases hobject : object = 20
    · subst object
      simp [setOwnedMemory]
    · simp [setOwnedMemory, hobject]
  have hreleaseMappingsEmpty :
      ∀ addressSpace page,
        retainLiveVirtualMappings lifecycleReleaseScrub.memory
            (fun _ _ => none) addressSpace page = none := by
    intro addressSpace page
    simp [retainLiveVirtualMappings]
  have hreleaseWaitersEmpty :
      ∀ endpoint,
        (lifecycleReleaseKernel plan).blockingIPCContext.ipc.waiters
            endpoint = [] := by
    intro endpoint
    rfl
  have hreleaseWaiterEndpointEmpty :
      ∀ subject,
        (lifecycleReleaseKernel plan).blockingIPCContext.ipc.waiterEndpoint
            subject = none := by
    intro subject
    rfl
  have hreleaseBlockedEmpty :
      ∀ subject,
        (lifecycleReleaseKernel plan).blockingIPCContext.blocked subject =
          none := by
    intro subject
    rfl
  have hreleaseEndpointOwnerEmpty :
      ∀ object, lifecycleReleaseLifecycle.endpointOwner object = none := by
    intro object
    rfl
  have hreleaseAddressOwnerExact :
      ∀ addressSpace subject,
        lifecycleReleaseLifecycle.addressOwner addressSpace = some subject →
          (addressSpace = 1 ∧ subject = 1) ∨
            (addressSpace = 2 ∧ subject = 2) := by
    intro addressSpace subject howner
    change
      (if addressSpace = 1 then some 1
        else if addressSpace = 2 then some 2 else none) = some subject
      at howner
    by_cases hspaceOne : addressSpace = 1
    · subst addressSpace
      simp at howner
      exact Or.inl ⟨rfl, howner.symm⟩
    · by_cases hspaceTwo : addressSpace = 2
      · subst addressSpace
        simp at howner
        exact Or.inr ⟨rfl, howner.symm⟩
      · simp [hspaceOne, hspaceTwo] at howner
  have hreleaseAddressOwnerExists :
      ∀ addressSpace,
        addressSpace ≠ 20 →
          (addressSpace = 1 ∨ addressSpace = 2) →
            ∃ subject,
              lifecycleReleaseLifecycle.addressOwner addressSpace =
                some subject := by
    intro addressSpace _ hlive
    rcases hlive with rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  have hreleaseAddressOwnerSubjectLive :
      ∀ addressSpace subject,
        lifecycleReleaseLifecycle.addressOwner addressSpace = some subject →
          lifecycleReleaseScrub.memory.capabilities.subjects subject = true := by
    intro addressSpace subject howner
    rcases hreleaseAddressOwnerExact addressSpace subject howner with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · rfl
  have hreleaseRunnableLive :
      ∀ subject,
        lifecycleReleaseLifecycle.runnable subject = true →
          lifecycleReleaseScrub.memory.capabilities.subjects subject = true := by
    intro subject hrunnable
    rw [lifecycleReleaseScrub_capabilities,
      lifecycleReleasedCapabilities_subjects]
    simpa [lifecycleReleaseLifecycle, retireMemoryFromLifecycle,
      lifecycleSubjectState, lifecycleCapabilities] using hrunnable
  have hreleaseCurrentLive :
      ∀ subject,
        lifecycleReleaseLifecycle.current = some subject →
          lifecycleReleaseScrub.memory.capabilities.subjects subject = true := by
    intro subject hcurrent
    change some 2 = some subject at hcurrent
    injection hcurrent with hsubject
    subst subject
    rw [lifecycleReleaseScrub_capabilities,
      lifecycleReleasedCapabilities_subjects]
    rfl
  have hreleaseSubjectOneContextValid :
      ResumablePreemption.validContext
        (lifecycleReleaseKernel plan).resumable lifecycleSubjectOneContext := by
    simp [ResumablePreemption.validContext, lifecycleReleaseKernel,
      publishKernelMemory, lifecycleKernel, lifecycleReleaseLifecycle,
      retireMemoryFromLifecycle, lifecycleSubjectOneContext,
      lifecycleSavedFrame, lifecycleScheduler, lifecycleSubjectState,
      lifecycleVirtualMemory, lifecycleMemory, lifecycleCapabilities,
      lifecycleReleasedCapabilities, MemoryLifecycle.retireCapabilities,
      MemoryLifecycle.setObject, Scheduler.ownsAddressSpace,
      Interrupt.validSavedUserFrame]
  have hreleaseSubjectTwoContextMissing :
      ResumablePreemption.contextFor
          (lifecycleReleaseKernel plan).resumable.contexts 2 = none := by
    rfl
  have hreleaseTlbCoherent :
      TLB.Coherent (lifecycleReleaseKernel plan).resumable.translations := by
    simp [TLB.Coherent, lifecycleReleaseKernel, publishKernelMemory,
      lifecycleKernel]
  have hreleasePortControls :
      DirectPortIO.AcceptedControls DirectPortIO.selectedControls := rfl
  have hreleaseDmaQuarantined :
      (lifecycleReleaseKernel plan).dmaObserved =
        (lifecycleReleaseKernel plan).dmaAccepted.snapshot := rfl
  have hreleaseLifecycleWellFormed :
      SubjectLifecycle.WellFormed lifecycleReleaseLifecycle := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro subject hlive
      simpa [lifecycleReleaseLifecycle, retireMemoryFromLifecycle,
        lifecycleSubjectState, lifecycleCapabilities] using hlive
    · intro object subject frame howned
      rw [hreleaseOwnedMemoryEmpty object] at howned
      contradiction
    · exact hreleaseAddressOwnerSubjectLive
    · intro object subject howner
      rw [hreleaseEndpointOwnerEmpty object] at howner
      contradiction
    · exact hreleaseRunnableLive
    · exact hreleaseCurrentLive
  have hreleaseCapabilitiesWellFormed :
      LeanOS.Capability.WellFormed
        lifecycleReleaseScrub.memory.capabilities :=
    ⟨hslots, hderivations, hidentities, hslotSpaces⟩
  have hreleaseVirtualWellFormed :
      VirtualMapping.LifecycleWellFormed
        (lifecycleReleaseKernel plan).virtualMemory := by
    refine ⟨⟨?_, ?_⟩, hreleaseCapabilitiesWellFormed, ?_, ?_⟩
    · intro addressSpace subject howner
      change lifecycleReleaseLifecycle.addressOwner addressSpace =
        some subject at howner
      exact hreleaseAddressOwnerSubjectLive addressSpace subject howner
    · intro addressSpace page mapping hmapping
      change retainLiveVirtualMappings lifecycleReleaseScrub.memory
        (fun _ _ => none) addressSpace page = some mapping at hmapping
      rw [hreleaseMappingsEmpty addressSpace page] at hmapping
      contradiction
    · intro addressSpace subject howner
      change lifecycleReleaseLifecycle.addressOwner addressSpace =
        some subject at howner
      rcases hreleaseAddressOwnerExact addressSpace subject howner with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl, hspace1⟩
      · exact ⟨rfl, rfl, rfl, rfl, hspace2⟩
    · intro addressSpace hobject hkind
      exact haddressComplete addressSpace hobject hkind
  have hreleaseIPCWellFormed :
      IPCSyscall.WellFormed (lifecycleReleaseKernel plan).ipc := by
    refine ⟨hreleaseVirtualWellFormed, ?_⟩
    refine ⟨hreleaseCapabilitiesWellFormed, ?_, ?_, ?_, ?_⟩
    · intro object hobject hkind
      simp [lifecycleReleaseKernel, publishKernelMemory, lifecycleKernel,
        lifecycleReleaseLifecycle, retireMemoryFromLifecycle,
        lifecycleCapabilities, lifecycleReleasedCapabilities,
        MemoryLifecycle.retireCapabilities, MemoryLifecycle.setObject] at hobject hkind
      rcases hobject.2 with hspace | hmemory
      · simp [hspace] at hkind
      · exact (hobject.1 hmemory).elim
    · intro object envelope hmailbox
      change retainLiveEndpointMailboxes
        lifecycleReleaseScrub.memory.capabilities (fun _ => none) object =
          some envelope at hmailbox
      rw [hreleaseMailboxesEmpty object] at hmailbox
      contradiction
    · intro object _hdead
      exact hreleaseMailboxesEmpty object
    · intro object envelope hhistory
      simp [lifecycleReleaseKernel, publishKernelMemory, lifecycleKernel,
        lifecycleEndpoints] at hhistory
  have hreleaseSchedulerWellFormed :
      Scheduler.WellFormed (lifecycleReleaseKernel plan).scheduler := by
    refine ⟨hreleaseLifecycleWellFormed, ?_, ?_, ?_, ?_⟩
    · simp [lifecycleReleaseKernel, publishKernelMemory, lifecycleKernel,
        lifecycleScheduler]
    · simp [lifecycleReleaseKernel, publishKernelMemory, lifecycleKernel,
        lifecycleScheduler]
    · intro subject hready
      change subject ∈ [1] at hready
      simp at hready
      subst subject
      exact ⟨rfl, rfl, by
        simp [Scheduler.ownsAddressSpace, lifecycleReleaseKernel,
          publishKernelMemory, lifecycleKernel, lifecycleReleaseLifecycle,
          retireMemoryFromLifecycle, lifecycleSubjectState,
          lifecycleVirtualMemory]⟩
    · intro subject hcurrent
      change some 2 = some subject at hcurrent
      injection hcurrent with hsubject
      subst subject
      exact ⟨rfl, rfl, by
        simp [Scheduler.ownsAddressSpace, lifecycleReleaseKernel,
          publishKernelMemory, lifecycleKernel, lifecycleReleaseLifecycle,
          retireMemoryFromLifecycle, lifecycleSubjectState,
          lifecycleVirtualMemory], by
            change 2 ∉ [1]
            decide⟩
  have hreleasePreemptionWellFormed :
      Preemption.WellFormed (lifecycleReleaseKernel plan).preemption := by
    exact ⟨hreleaseSchedulerWellFormed, rfl⟩
  have hreleaseResumableWellFormed :
      ResumablePreemption.WellFormed
        (lifecycleReleaseKernel plan).resumable := by
    refine ⟨hreleaseSchedulerWellFormed, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hreleaseTlbCoherent⟩
    · change [lifecycleSubjectOneContext].length ≤ 2
      decide
    · change [lifecycleSubjectOneContext].Pairwise
        (fun first second => first.owner ≠ second.owner)
      simp
    · intro context hcontext
      change context ∈ [lifecycleSubjectOneContext] at hcontext
      simp at hcontext
      subst context
      exact hreleaseSubjectOneContextValid
    · intro subject hcurrent
      change some 2 = some subject at hcurrent
      injection hcurrent with hsubject
      subst subject
      exact hreleaseSubjectTwoContextMissing
    · constructor
      · intro subject hready
        change subject ∈ [1] at hready
        simp at hready
        subst subject
        exact ⟨lifecycleSubjectOneContext, by
          change lifecycleSubjectOneContext ∈ [lifecycleSubjectOneContext]
          simp, rfl⟩
      · intro context hcontext _hsuspended
        change context ∈ [lifecycleSubjectOneContext] at hcontext
        simp at hcontext
        subst context
        change 1 ∈ [1]
        decide
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, hreleaseVirtualWellFormed⟩
    · constructor
      · intro object owner frame howned
        change lifecycleReleaseLifecycle.ownedMemory object =
          some (owner, frame) at howned
        rw [hreleaseOwnedMemoryEmpty object] at howned
        contradiction
      · intro object owner hendpoint
        change lifecycleReleaseLifecycle.endpointOwner object =
          some owner at hendpoint
        rw [hreleaseEndpointOwnerEmpty object] at hendpoint
        contradiction
  have hreleaseTransfersWellFormed :
      CapabilityTransfer.WellFormed
        (lifecycleReleaseKernel plan).transfers := by
    refine ⟨hreleaseIPCWellFormed.2, ?_⟩
    intro endpoint transfer hpending
    change (fun _ => none) endpoint = some transfer at hpending
    contradiction
  have hreleaseHaltedWellFormed :
      (lifecycleReleaseKernel plan).resumable.halted = true ↔
        ∃ record,
          (lifecycleReleaseKernel plan).execution.mode =
            FailStop.Mode.halted record := by
    constructor
    · intro hhalted
      change false = true at hhalted
      contradiction
    · rintro ⟨record, hmode⟩
      change FailStop.Mode.running = FailStop.Mode.halted record at hmode
      contradiction
  have hreleaseReturnWellFormed :
      (lifecycleReleaseKernel plan).execution.returnAuthorityArmed = true →
        (lifecycleReleaseKernel plan).ReturnPlanLive = true := by
    intro harmed
    change false = true at harmed
    contradiction
  have hreleaseBlockingCoherent :
      (lifecycleReleaseKernel plan).BlockingIPCCoherent := by
    exact ⟨rfl, rfl⟩
  have hreleaseCoherent :
      FailStop.CompositeState.Coherent (lifecycleReleaseKernel plan) := by
    simp only [FailStop.CompositeState.Coherent]
    repeat' apply And.intro
    all_goals first
      | rfl
      | (intro subject hcurrent
         change some 2 = some subject at hcurrent
         injection hcurrent with hsubject
         subst subject
         exact ⟨rfl, rfl⟩)
      | (intro object _hdead
         exact hreleaseMailboxesEmpty object)
      | (intro object envelope hmailbox
         change retainLiveEndpointMailboxes
           lifecycleReleaseScrub.memory.capabilities (fun _ => none)
           object = some envelope at hmailbox
         rw [hreleaseMailboxesEmpty object] at hmailbox
         contradiction)
  have hreleaseExecutionWellFormed :
      FailStop.WellFormed (lifecycleReleaseKernel plan).execution := by
    simp [FailStop.WellFormed, Interrupt.WellFormed,
      lifecycleReleaseKernel, publishKernelMemory, lifecycleKernel,
      lifecycleReleaseLifecycle, retireMemoryFromLifecycle,
      lifecycleSubjectState, lifecycleCapabilities,
      lifecycleVirtualMemory, lifecycleReleasedCapabilities,
      MemoryLifecycle.retireCapabilities, MemoryLifecycle.setObject]
    constructor
    · change SubjectLifecycle.WellFormed lifecycleReleaseLifecycle
      exact hreleaseLifecycleWellFormed
    · rfl
  have hreleaseDeferredWellFormed :
      (lifecycleReleaseKernel plan).DeferredCancellationWellFormed := by
    simp [FailStop.CompositeState.DeferredCancellationWellFormed,
      BlockingIPCContext.DeferredWellFormed,
      FailStop.CompositeState.blockingIPCContext,
      BlockingIPCContext.WellFormed,
      BlockingIPCContext.ContextAgreement, BlockingIPC.WellFormed,
      BlockingIPC.authorizedReceive, BlockingIPCContext.emptyDeferred,
      lifecycleReleaseKernel, publishKernelMemory, lifecycleKernel,
      lifecycleScheduler, lifecycleSubjectState, lifecycleCapabilities,
      lifecycleReleaseLifecycle, retireMemoryFromLifecycle,
      lifecycleReleasedCapabilities, MemoryLifecycle.retireCapabilities,
      MemoryLifecycle.setObject, Scheduler.WellFormed,
      Scheduler.ownsAddressSpace]
    constructor
    · refine ⟨?_, rfl, rfl⟩
      change SubjectLifecycle.WellFormed lifecycleReleaseLifecycle
      exact hreleaseLifecycleWellFormed
    · simpa only [lifecycleReleaseScrub_capabilities,
        lifecycleReleasedCapabilities, lifecycleCapabilities,
        MemoryLifecycle.retireCapabilities, MemoryLifecycle.setObject,
        Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] using
        hreleaseCapabilitiesWellFormed
  suffices hlegacy :
      FailStop.DeferredBlockingRuntimeWellFormed
        (lifecycleReleaseKernel plan) by
    refine ⟨hlegacy.1, hlegacy.2, ?_⟩
    change InvalidationPublication.WellFormed InvalidationPublication.initial
    exact InvalidationPublication.initial_wellFormed
  refine ⟨?_, hreleaseDeferredWellFormed⟩
  simp only [FailStop.RuntimeWellFormed]
  exact ⟨hreleaseCoherent, hreleaseExecutionWellFormed,
    hreleaseLifecycleWellFormed, hreleaseCapabilitiesWellFormed,
    hreleaseVirtualWellFormed, hreleaseIPCWellFormed,
    hreleaseSchedulerWellFormed, hreleasePreemptionWellFormed,
    hreleaseResumableWellFormed, hreleaseTransfersWellFormed,
    hreleaseHaltedWellFormed, hreleaseReturnWellFormed,
    hreleaseBlockingCoherent, hreleasePortControls,
    hreleaseDmaQuarantined⟩

private theorem lifecycleReleased_coherent (plan : BootPageTablePlan.Plan) :
    (lifecycleReleased plan).Coherent := by
  refine ⟨rfl, rfl, rfl, rfl, lifecycleReleaseScrub_invariant,
    ?_, ?_, ?_, ?_⟩
  all_goals
    simp [lifecycleReleased, lifecycleReleaseIOMMU,
      lifecycleReleaseCore, releaseMemoryCore, lifecycleAfterWriteIOMMU,
      lifecycleInitialCore, lifecycleReleaseKernel, publishKernelMemory,
      lifecycleKernel, lifecycleReleaseLifecycle,
      retireMemoryFromLifecycle, lifecycleReleaseScrub,
      lifecycleAfterWriteScrub, lifecycleScrub, lifecycleMemory,
      lifecycleCapabilities, lifecycleSubjectState,
      lifecycleVirtualMemory, setFrameLive]
  all_goals simp_all (config := { failIfUnchanged := false })
    [lifecycleCapabilities]
  all_goals native_decide

private theorem lifecycleReleased_invariant (plan : BootPageTablePlan.Plan) :
    (lifecycleReleased plan).Invariant :=
  ⟨lifecycleReleaseKernel_invariant plan, lifecycleReleaseIOMMU.invariant,
    lifecycleReleased_coherent plan⟩

private noncomputable def publicationReleaseOutcome
    (plan : BootPageTablePlan.Plan) :=
  gatedMemoryByKernel (lifecycleAfterWrite plan)
    (lifecycleAfterWrite_invariant plan) (.release 2 1)

private theorem lifecycle_scrub_release_accepted :
    (FrameScrub.release lifecycleAfterWriteScrub 2 1).result =
      .accepted := by
  native_decide

theorem authoritative_lifecycle_release_accepted
    (plan : BootPageTablePlan.Plan) :
    (publicationReleaseOutcome plan).isAccepted = true := by
  classical
  unfold publicationReleaseOutcome
  simp only [gatedMemoryByKernel]
  rw [show (lifecycleAfterWrite plan).kernel.execution.mode =
    .running by rfl]
  simp only [lifecycleAfterWrite]
  rw [lifecycle_scrub_release_accepted]
  simp only [lifecycleAfterWriteScrub, lifecycleScrub, lifecycleMemory,
    lifecycleCapabilities, lifecycleSubjectTwoMemory,
    LeanOS.Capability.lookup]
  change
    (commitAuthoritativeMemory (lifecycleAfterWrite plan)
      (lifecycleReleaseKernel plan) lifecycleReleaseCore
      lifecycleReleaseScrub .released).isAccepted = true
  have hcap :
      LeanOS.Capability.WellFormed
        lifecycleReleaseCore.capabilityAuthority :=
    lifecycleReleaseIOMMU.capabilityWellFormed
  have hvalid : validateCore lifecycleReleaseCore = true :=
    lifecycleReleaseIOMMU.valid
  have hinvariant :
      ({ kernel := lifecycleReleaseKernel plan
         iommu := lifecycleReleaseIOMMU
         scrub := lifecycleReleaseScrub } :
        AuthoritativeExtension).Invariant := by
    simpa [lifecycleReleased] using lifecycleReleased_invariant plan
  simp only [commitAuthoritativeMemory, dif_pos hcap, dif_pos hvalid]
  split
  · rfl
  · next hbad =>
      exfalso
      apply hbad
      simpa [lifecycleReleaseIOMMU] using hinvariant

private theorem authoritative_lifecycle_release_state_exact
    (plan : BootPageTablePlan.Plan) :
    (publicationReleaseOutcome plan).state = lifecycleReleased plan := by
  classical
  unfold publicationReleaseOutcome
  simp only [gatedMemoryByKernel]
  rw [show (lifecycleAfterWrite plan).kernel.execution.mode =
    .running by rfl]
  simp only [lifecycleAfterWrite]
  rw [lifecycle_scrub_release_accepted]
  simp only [lifecycleAfterWriteScrub, lifecycleScrub, lifecycleMemory,
    lifecycleCapabilities, lifecycleSubjectTwoMemory,
    LeanOS.Capability.lookup]
  change
    (commitAuthoritativeMemory (lifecycleAfterWrite plan)
      (lifecycleReleaseKernel plan) lifecycleReleaseCore
      lifecycleReleaseScrub .released).state = lifecycleReleased plan
  have hcap :
      LeanOS.Capability.WellFormed
        lifecycleReleaseCore.capabilityAuthority :=
    lifecycleReleaseIOMMU.capabilityWellFormed
  have hvalid : validateCore lifecycleReleaseCore = true :=
    lifecycleReleaseIOMMU.valid
  have hinvariant :
      ({ kernel := lifecycleReleaseKernel plan
         iommu := lifecycleReleaseIOMMU
         scrub := lifecycleReleaseScrub } :
        AuthoritativeExtension).Invariant := by
    simpa [lifecycleReleased] using lifecycleReleased_invariant plan
  simp only [commitAuthoritativeMemory, dif_pos hcap, dif_pos hvalid]
  split
  · change
      ({ kernel := lifecycleReleaseKernel plan
         iommu :=
           { core := lifecycleReleaseCore
             valid := by assumption
             capabilityWellFormed := by assumption }
         scrub := lifecycleReleaseScrub } :
        AuthoritativeExtension) = lifecycleReleased plan
    unfold lifecycleReleased
    congr
  · next hbad =>
      exfalso
      apply hbad
      simpa [lifecycleReleaseIOMMU] using hinvariant

private def lifecycleScheduleKernel (plan : BootPageTablePlan.Plan) :
    FailStop.CompositeState :=
  (FailStop.authoritativeGate (lifecycleReleaseKernel plan)
    (.ordinary (.resumePreempt lifecycleSavedFrame
      lifecycleSavedRegisters))).state

private def lifecycleScheduleIOMMU : State :=
  { lifecycleReleaseIOMMU with
    core := { lifecycleReleaseCore with currentOwner := 1 }
    valid := by native_decide }

private def lifecycleScheduledCandidate (plan : BootPageTablePlan.Plan) :
    AuthoritativeExtension :=
  { kernel := lifecycleScheduleKernel plan
    iommu := lifecycleScheduleIOMMU
    scrub := lifecycleReleaseScrub }

private theorem lifecycleScheduleKernel_invariant
    (plan : BootPageTablePlan.Plan) :
    FailStop.AuthoritativeRuntimeWellFormed (lifecycleScheduleKernel plan) :=
  FailStop.authoritativeGate_preserves_authoritativeRuntimeWellFormed
    (lifecycleReleaseKernel plan)
    (.ordinary (.resumePreempt lifecycleSavedFrame lifecycleSavedRegisters))
    (lifecycleReleaseKernel_invariant plan)

private theorem lifecycleScheduledCandidate_coherent
    (plan : BootPageTablePlan.Plan) :
    (lifecycleScheduledCandidate plan).Coherent := by
  have hcapabilities :
      (lifecycleScheduleKernel plan).capabilities =
        (lifecycleReleaseKernel plan).capabilities := rfl
  have hmemory :
      (lifecycleScheduleKernel plan).virtualMemory.memory =
        (lifecycleReleaseKernel plan).virtualMemory.memory := rfl
  refine ⟨?_, rfl, rfl, rfl, lifecycleReleaseScrub_invariant,
    ?_, ?_, ?_, ?_⟩
  · have hsync :=
      FailStop.resumePreempt_synchronizes_current_context
        (lifecycleReleaseKernel plan) lifecycleSavedFrame
        lifecycleSavedRegisters (lifecycleReleaseKernel_invariant plan).1.1
    have hcurrent :
        (FailStop.applyOperation (lifecycleReleaseKernel plan)
          (.resumePreempt lifecycleSavedFrame
            lifecycleSavedRegisters)).scheduler.lifecycle.current =
          some 1 := by
      change
        (ResumablePreemption.switch
          (lifecycleReleaseKernel plan).resumable
          (lifecycleReleaseKernel plan).execution.core
          lifecycleSavedFrame lifecycleSavedRegisters).state.scheduler.lifecycle.current =
            some 1
      simp [lifecycleReleaseKernel, publishKernelMemory, lifecycleKernel,
        lifecycleScheduler, lifecycleSubjectState, lifecycleVirtualMemory,
        lifecycleReleaseLifecycle, lifecycleReleasedCapabilities,
        lifecycleCapabilities, retireMemoryFromLifecycle,
        lifecycleReleaseScrub, lifecycleAfterWriteScrub, lifecycleScrub,
        lifecycleMemory, lifecycleSubjectTwoMemory,
        FrameScrub.release, MemoryLifecycle.release,
        LeanOS.Capability.lookup, LeanOS.Capability.slotInRange,
        LeanOS.Capability.allRights, MemoryLifecycle.retireCapabilities,
        MemoryLifecycle.setObject, MemoryLifecycle.setBinding,
        FrameAllocator.release, FrameAllocator.setStatus,
        FailStop.bootRuntime,
        ResumablePreemption.switch, Scheduler.tick, Scheduler.yield,
        Scheduler.selectNext, Scheduler.ownsAddressSpace,
        ResumablePreemption.contextFor,
        ResumablePreemption.eraseContext, TLB.switch,
        Interrupt.dispatchHardware, Interrupt.validSavedUserFrame,
        Interrupt.decodeVector, lifecycleSavedFrame,
        lifecycleSavedRegisters, lifecycleSubjectOneContext]
    have hsubject := (hsync 1 hcurrent).1
    have hmode :
        (lifecycleReleaseKernel plan).execution.mode = .running := rfl
    simpa [lifecycleScheduledCandidate, lifecycleScheduleIOMMU,
      lifecycleScheduleKernel, FailStop.authoritativeGate,
      FailStop.applyAuthoritativeOperation, hmode] using hsubject.symm
  · change
      ∀ assignment ∈ lifecycleReleaseCore.assignments,
        (lifecycleScheduleKernel plan).capabilities.subjects
          assignment.owner = true
    rw [hcapabilities]
    simpa only [lifecycleScheduledCandidate, lifecycleScheduleIOMMU,
      lifecycleReleased, lifecycleReleaseIOMMU] using
      (lifecycleReleased_coherent plan).2.2.2.2.2.1
  · change
      ∀ capability ∈ lifecycleReleaseCore.capabilities,
        (lifecycleScheduleKernel plan).capabilities.subjects
              capability.owner = true ∧
          (lifecycleScheduleKernel plan).virtualMemory.memory.binding
              capability.object = some capability.frame.frame
    rw [hcapabilities, hmemory]
    simpa only [lifecycleScheduledCandidate, lifecycleScheduleIOMMU,
      lifecycleReleased, lifecycleReleaseIOMMU] using
      (lifecycleReleased_coherent plan).2.2.2.2.2.2.1
  · change
      ∀ mapping ∈ lifecycleReleaseCore.mappings,
        (lifecycleScheduleKernel plan).capabilities.subjects
              mapping.owner = true ∧
          ∃ capability ∈ lifecycleReleaseCore.capabilities,
            capability.owner = mapping.owner ∧
              capability.frame = mapping.frame ∧
              rangeContained mapping.frameOffset mapping.length
                  capability.offset capability.length = true ∧
                mapping.permission.attenuates capability.permission = true
    rw [hcapabilities]
    simpa only [lifecycleScheduledCandidate, lifecycleScheduleIOMMU,
      lifecycleReleased, lifecycleReleaseIOMMU] using
      (lifecycleReleased_coherent plan).2.2.2.2.2.2.2.1
  · change
      ∀ frame ∈ lifecycleReleaseCore.frames,
        frame.live = true → frame.kernelOwned = false →
          frame.pageTable = false → frame.allocatorMetadata = false →
            (lifecycleScheduleKernel plan).capabilities.subjects
              frame.owner = true
    rw [hcapabilities]
    simpa only [lifecycleScheduledCandidate, lifecycleScheduleIOMMU,
      lifecycleReleased, lifecycleReleaseIOMMU] using
      (lifecycleReleased_coherent plan).2.2.2.2.2.2.2.2

private theorem lifecycleScheduledCandidate_invariant
    (plan : BootPageTablePlan.Plan) :
    (lifecycleScheduledCandidate plan).Invariant :=
  ⟨lifecycleScheduleKernel_invariant plan, lifecycleScheduleIOMMU.invariant,
    lifecycleScheduledCandidate_coherent plan⟩

private noncomputable def lifecycleScheduled
    (plan : BootPageTablePlan.Plan) : AuthoritativeExtension :=
  applyKernelOperation (lifecycleReleased plan)
    (.ordinary (.resumePreempt lifecycleSavedFrame
      lifecycleSavedRegisters))

private theorem lifecycle_schedule_reconcile_exact
    (plan : BootPageTablePlan.Plan) :
    reconcileKernelAuthority (lifecycleScheduleKernel plan)
      lifecycleReleaseIOMMU = lifecycleScheduleIOMMU := by
  classical
  have hcapability :
      (lifecycleScheduleKernel plan).capabilities =
        lifecycleReleaseCore.capabilityAuthority := rfl
  have hcurrent :
      (lifecycleScheduleKernel plan).execution.core.context.currentSubject =
        1 :=
    (lifecycleScheduledCandidate_coherent plan).1.symm
  have hcore :
      { lifecycleReleaseCore with
        currentOwner :=
          (lifecycleScheduleKernel plan).execution.core.context.currentSubject
        capabilityAuthority :=
          (lifecycleScheduleKernel plan).capabilities } =
        lifecycleScheduleIOMMU.core := by
    rw [hcurrent, hcapability]
    rfl
  simp only [reconcileKernelAuthority, lifecycleReleaseIOMMU,
    hcapability, not_true_eq_false, if_false, hcore]
  split
  · next _hwell =>
      split
      · next _hvalid =>
          congr
      · next hbad =>
          exact False.elim (hbad lifecycleScheduleIOMMU.valid)
  · next hbad =>
      exact False.elim
        (hbad lifecycleScheduleIOMMU.capabilityWellFormed)

private theorem lifecycle_schedule_state_exact
    (plan : BootPageTablePlan.Plan) :
    lifecycleScheduled plan = lifecycleScheduledCandidate plan := by
  classical
  unfold lifecycleScheduled applyKernelOperation
  dsimp only
  change
    (if
        ({ kernel := lifecycleScheduleKernel plan
           iommu := reconcileKernelAuthority (lifecycleScheduleKernel plan)
             lifecycleReleaseIOMMU
           scrub := lifecycleReleaseScrub } :
          AuthoritativeExtension).Coherent then
        ({ kernel := lifecycleScheduleKernel plan
           iommu := reconcileKernelAuthority (lifecycleScheduleKernel plan)
             lifecycleReleaseIOMMU
           scrub := lifecycleReleaseScrub } :
          AuthoritativeExtension)
      else lifecycleReleased plan) =
      lifecycleScheduledCandidate plan
  rw [lifecycle_schedule_reconcile_exact]
  change
    (if (lifecycleScheduledCandidate plan).Coherent then
        lifecycleScheduledCandidate plan
      else lifecycleReleased plan) =
      lifecycleScheduledCandidate plan
  rw [if_pos (lifecycleScheduledCandidate_coherent plan)]

private theorem lifecycleScheduled_invariant
    (plan : BootPageTablePlan.Plan) :
    (lifecycleScheduled plan).Invariant := by
  rw [lifecycle_schedule_state_exact]
  exact lifecycleScheduledCandidate_invariant plan

theorem authoritative_lifecycle_switch_to_b_from_kernel_operation
    (plan : BootPageTablePlan.Plan) :
    (applyKernelOperation (lifecycleReleased plan)
        (.ordinary (.resumePreempt lifecycleSavedFrame
          lifecycleSavedRegisters))).kernel.execution.core.context.currentSubject =
        1 ∧
      (applyKernelOperation (lifecycleReleased plan)
        (.ordinary (.resumePreempt lifecycleSavedFrame
          lifecycleSavedRegisters))).iommu.core.currentOwner = 1 := by
  change
    (lifecycleScheduled plan).kernel.execution.core.context.currentSubject = 1 ∧
      (lifecycleScheduled plan).iommu.core.currentOwner = 1
  rw [lifecycle_schedule_state_exact]
  exact ⟨rfl, rfl⟩

private def lifecycleSubjectOneMemory : LeanOS.Capability.Capability :=
  { object := 21, kind := .memory, rights := LeanOS.Capability.allRights
    identity := 4 }

private def lifecycleAllocatedCapabilities : LeanOS.Capability.State :=
  { nextIdentity := 5
    derivations := fun identity =>
      if identity = 1 then
        some (none, 1, .addressSpace, { revoke := true })
      else if identity = 2 then
        some (none, 2, .addressSpace, { revoke := true })
      else if identity = 3 then
        some (none, 20, .memory, LeanOS.Capability.allRights)
      else if identity = 4 then
        some (none, 21, .memory, LeanOS.Capability.allRights)
      else none
    subjects := fun subject => subject = 1 || subject = 2
    objects := fun object => object = 1 || object = 2 || object = 21
    kinds := fun object =>
      if object = 1 || object = 2 then some .addressSpace
      else if object = 21 then some .memory else none
    slots := fun subject slot =>
      if subject = 1 && slot = 0 then some lifecycleSubjectOneSpace
      else if subject = 1 && slot = 1 then some lifecycleSubjectOneMemory
      else if subject = 2 && slot = 0 then some lifecycleSubjectTwoSpace
      else none }

private theorem lifecycleAllocatedCapabilities_wellFormed :
    LeanOS.Capability.WellFormed lifecycleAllocatedCapabilities := by
  simp only [LeanOS.Capability.WellFormed]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro subject slot capability hslot
    simp only [lifecycleAllocatedCapabilities, lifecycleSubjectOneSpace,
      lifecycleSubjectOneMemory, lifecycleSubjectTwoSpace] at hslot
    repeat' split at hslot
    all_goals cases hslot <;>
      simp [lifecycleAllocatedCapabilities, lifecycleSubjectOneSpace,
        lifecycleSubjectOneMemory, lifecycleSubjectTwoSpace,
        LeanOS.Capability.rightsValid,
        LeanOS.Capability.nonemptyRights,
        LeanOS.Capability.allRights]
    all_goals grind
  · intro identity parent object kind rights hderivation
    simp only [lifecycleAllocatedCapabilities] at hderivation
    repeat' split at hderivation
    all_goals rcases hderivation with ⟨rfl, rfl, rfl, rfl⟩ <;>
      simp [lifecycleAllocatedCapabilities]
    all_goals grind
  · intro subject slot capability otherSubject otherSlot otherCapability
      hslot hother hidentity
    simp only [lifecycleAllocatedCapabilities, lifecycleSubjectOneSpace,
      lifecycleSubjectOneMemory, lifecycleSubjectTwoSpace] at hslot hother
    repeat' split at hslot
    all_goals repeat' split at hother
    all_goals cases hslot <;> cases hother <;> simp_all
  · intro subject slot hslot
    change 4 ≤ slot at hslot
    have hne0 : slot ≠ 0 := by omega
    have hne1 : slot ≠ 1 := by omega
    simp [lifecycleAllocatedCapabilities, hne0, hne1]

private def lifecycleAllocatedScrub : FrameScrub.State :=
  { memory :=
      { capabilities := lifecycleAllocatedCapabilities
        allocator :=
          { frames := [4]
            status := fun frame => if frame = 4 then .owned 21 else .reserved }
        binding := fun object => if object = 21 then some 4 else none
        issued := fun object =>
          object = 1 || object = 2 || object = 20 || object = 21 }
    bytes := FrameScrub.scrubFrame lifecycleReleaseScrub.bytes 4
    written := FrameScrub.setWritten lifecycleReleaseScrub.written 21 false }

@[simp] private theorem lifecycle_allocate_state_exact :
    (FrameScrub.allocate lifecycleReleaseScrub 21 1 1).state =
      lifecycleAllocatedScrub := by
  simp [FrameScrub.allocate, MemoryLifecycle.allocate,
    lifecycleAllocatedScrub, lifecycleAllocatedCapabilities,
    lifecycleReleasedCapabilities, lifecycleCapabilities,
    lifecycleMemory, MemoryLifecycle.retireCapabilities,
    lifecycleSubjectOneSpace, lifecycleSubjectOneMemory,
    lifecycleSubjectTwoSpace, lifecycleSubjectTwoMemory,
    LeanOS.Capability.slotInRange,
    CapabilityHandle.slotReserved, CapabilityHandle.slotRadix,
    CapabilityHandle.generationReserved, CapabilityHandle.generationRadix,
    MemoryLifecycle.activateObject, MemoryLifecycle.setObject,
    MemoryLifecycle.setBinding, MemoryLifecycle.setIssued,
    FrameAllocator.allocate, FrameAllocator.setStatus,
    LeanOS.Capability.installRoot, LeanOS.Capability.install,
    show
      (FrameAllocator.FrameState.free ==
        FrameAllocator.FrameState.free) = true by decide]
  congr 1
  repeat' apply And.intro
  all_goals
    funext first
    try funext second
    simp (config := { failIfUnchanged := false })
      [lifecycleAllocatedCapabilities, lifecycleCapabilities,
      lifecycleMemory, lifecycleSubjectOneSpace,
      lifecycleSubjectOneMemory, lifecycleSubjectTwoSpace,
      lifecycleSubjectTwoMemory, MemoryLifecycle.setObject,
      MemoryLifecycle.setBinding, MemoryLifecycle.setIssued,
      FrameAllocator.setStatus, LeanOS.Capability.install,
      Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]
  all_goals grind

@[simp] private theorem lifecycle_allocate_result_accepted :
    (FrameScrub.allocate lifecycleReleaseScrub 21 1 1).result =
      .accepted := by
  native_decide

private def lifecycleAllocatedLifecycle (plan : BootPageTablePlan.Plan) :
    SubjectLifecycle.State :=
  allocateMemoryToLifecycle (lifecycleScheduleKernel plan).lifecycle
    lifecycleAllocatedScrub.memory 21 1 4

private def lifecycleAllocatedKernel (plan : BootPageTablePlan.Plan) :
    FailStop.CompositeState :=
  publishKernelMemory (lifecycleScheduleKernel plan)
    lifecycleAllocatedScrub.memory (lifecycleAllocatedLifecycle plan)

private def lifecycleAllocatedCore : Core :=
  allocateMemoryCore lifecycleScheduleIOMMU.core lifecycleAllocatedScrub
    21 1 1 4 lifecycleSubjectOneMemory

private def lifecycleAllocatedIOMMU : State :=
  { core := lifecycleAllocatedCore
    valid := by native_decide
    capabilityWellFormed := by
      simpa [lifecycleAllocatedCore, allocateMemoryCore,
        lifecycleAllocatedScrub] using
        lifecycleAllocatedCapabilities_wellFormed }

private def lifecycleAllocated (plan : BootPageTablePlan.Plan) :
    AuthoritativeExtension :=
  { kernel := lifecycleAllocatedKernel plan
    iommu := lifecycleAllocatedIOMMU
    scrub := lifecycleAllocatedScrub }

private theorem lifecycleScheduleKernel_addressOwner
    (plan : BootPageTablePlan.Plan) :
    (lifecycleScheduleKernel plan).lifecycle.addressOwner =
      lifecycleSubjectState.addressOwner := by
  rcases (lifecycleScheduleKernel_invariant plan).1 with
    ⟨hcoherent, _, _, _, _, _, _, _, hresumable, _⟩
  rcases hcoherent with
    ⟨_, hscheduler, _, _, _, _, _, hresumableScheduler,
      hresumableVirtual, _, _, _, _⟩
  rcases hresumable with
    ⟨_, _, _, _, _, _, htranslation, _, _, _⟩
  calc
    (lifecycleScheduleKernel plan).lifecycle.addressOwner =
        (lifecycleScheduleKernel plan).virtualMemory.owner := by
      rw [← hscheduler, ← hresumableScheduler,
        ← hresumableVirtual]
      exact htranslation.1.symm
    _ = lifecycleVirtualMemory.owner := rfl
    _ = lifecycleSubjectState.addressOwner := rfl

private theorem lifecycleAllocatedScrub_invariant :
    FrameScrub.ScrubInvariant lifecycleAllocatedScrub := by
  intro object frame hbinding hunwritten
  simp only [lifecycleAllocatedScrub] at hbinding
  simp at hbinding
  rcases hbinding with ⟨rfl, rfl⟩
  constructor
  · rfl
  · intro offset hoffset
    exact FrameScrub.scrubFrame_target lifecycleReleaseScrub.bytes 4
      offset hoffset

private theorem lifecycleAllocated_retained_mailbox_sender_live
    (plan : BootPageTablePlan.Plan) :
    ∀ object envelope,
      retainLiveEndpointMailboxes
          lifecycleAllocatedScrub.memory.capabilities
          (lifecycleScheduleKernel plan).ipc.endpoints.mailbox object =
        some envelope →
      (lifecycleAllocatedLifecycle plan).capabilities.subjects
        envelope.sender = true := by
  rcases (lifecycleScheduleKernel_invariant plan).1.1 with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, hliveSender⟩
  intro object envelope hmailbox
  simp only [retainLiveEndpointMailboxes] at hmailbox
  split at hmailbox
  · have hsubjects :
        (lifecycleScheduleKernel plan).lifecycle.capabilities.subjects =
          (lifecycleAllocatedLifecycle plan).capabilities.subjects := by
      rfl
    rw [← hsubjects]
    exact hliveSender object envelope hmailbox
  · contradiction

set_option maxHeartbeats 3000000 in
private theorem lifecycleAllocatedKernel_invariant
    (plan : BootPageTablePlan.Plan) :
    FailStop.AuthoritativeRuntimeWellFormed (lifecycleAllocatedKernel plan) := by
  have hschedule := lifecycleScheduleKernel_invariant plan
  have hcapabilities :
      LeanOS.Capability.WellFormed
        lifecycleAllocatedScrub.memory.capabilities :=
    lifecycleAllocatedIOMMU.capabilityWellFormed
  rcases hcapabilities with
    ⟨hslots, hderivations, hidentities, hslotSpaces⟩
  have hspace1 :
      LeanOS.Capability.HasAuthority
        lifecycleAllocatedScrub.memory.capabilities 1 1 .revoke := by
    exact ⟨0, lifecycleSubjectOneSpace, rfl, rfl, rfl⟩
  have hspace2 :
      LeanOS.Capability.HasAuthority
        lifecycleAllocatedScrub.memory.capabilities 2 2 .revoke := by
    exact ⟨0, lifecycleSubjectTwoSpace, rfl, rfl, rfl⟩
  have hownerAuthorityIf :
      ∀ addressSpace subject,
        (lifecycleAllocatedLifecycle plan).addressOwner addressSpace =
            some subject →
          LeanOS.Capability.HasAuthority
            lifecycleAllocatedScrub.memory.capabilities
            subject addressSpace .revoke := by
    intro addressSpace subject howner
    have howner' :
        lifecycleSubjectState.addressOwner addressSpace = some subject := by
      simpa [lifecycleAllocatedLifecycle, allocateMemoryToLifecycle,
        lifecycleScheduleKernel_addressOwner] using howner
    rcases (lifecycleAddressOwner_some_iff addressSpace subject).1
        howner' with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hspace1
    · exact hspace2
  have hownerSubjectIf :
      ∀ addressSpace subject,
        (lifecycleAllocatedLifecycle plan).addressOwner addressSpace =
            some subject →
          lifecycleAllocatedScrub.memory.capabilities.subjects subject =
            true := by
    intro addressSpace subject howner
    rcases hownerAuthorityIf addressSpace subject howner with
      ⟨slot, capability, hslot, _hobject, _hright⟩
    exact (hslots subject slot capability hslot).1
  have haddressComplete :
      ∀ addressSpace,
        lifecycleAllocatedScrub.memory.capabilities.objects addressSpace =
            true →
          lifecycleAllocatedScrub.memory.capabilities.kinds addressSpace =
            some .addressSpace →
            ∃ subject,
              (lifecycleAllocatedLifecycle plan).addressOwner addressSpace =
                some subject := by
    intro addressSpace _hobject hkind
    have hlive : addressSpace = 1 ∨ addressSpace = 2 := by
      by_cases hfirst : addressSpace = 1
      · exact Or.inl hfirst
      · by_cases hsecond : addressSpace = 2
        · exact Or.inr hsecond
        · simp [lifecycleAllocatedScrub, lifecycleAllocatedCapabilities,
            hfirst, hsecond] at hkind
    rcases hlive with rfl | rfl
    · refine ⟨1, ?_⟩
      change
        (lifecycleScheduleKernel plan).lifecycle.addressOwner 1 = some 1
      rw [lifecycleScheduleKernel_addressOwner]
      rfl
    · refine ⟨2, ?_⟩
      change
        (lifecycleScheduleKernel plan).lifecycle.addressOwner 2 = some 2
      rw [lifecycleScheduleKernel_addressOwner]
      rfl
  have hmailboxSender :=
    lifecycleAllocated_retained_mailbox_sender_live plan
  have hsubjects :
      (lifecycleScheduleKernel plan).lifecycle.capabilities.subjects =
        lifecycleAllocatedCapabilities.subjects := by
    rfl
  have hdeferredSchedule := hschedule.right
  have hpublicationSchedule := hschedule.publication
  rcases hschedule.left with
    ⟨hcoherentSchedule, hexecutionSchedule, hlifecycleSchedule,
      hcapabilitiesSchedule, hvirtualSchedule, hipcSchedule,
      hschedulerSchedule, hpreemptionSchedule, hresumableSchedule,
      htransfersSchedule, hhaltedSchedule, hreturnSchedule,
      hblockingSchedule, hportSchedule, hdmaSchedule⟩
  simp only [FailStop.CompositeState.Coherent] at hcoherentSchedule
  simp only [SubjectLifecycle.WellFormed] at hlifecycleSchedule
  have hownedFrameNeFour :
      ∀ object subject,
        (lifecycleScheduleKernel plan).lifecycle.ownedMemory object =
            some (subject, 4) → False := by
    intro object subject hownedMemory
    rcases hlifecycleSchedule.2.1 object subject 4 hownedMemory with
      ⟨_hlive, _hframeOwner, hfree⟩
    have hfree4 :
        (lifecycleScheduleKernel plan).lifecycle.freeFrame 4 = true := rfl
    rw [hfree4] at hfree
    contradiction
  have hexecutionModeSchedule := hexecutionSchedule.2.2
  have hnoScheduleMappings :
      ∀ addressSpace page,
        (lifecycleScheduleKernel plan).virtualMemory.mappings
            addressSpace page = none := by
    intro addressSpace page
    rfl
  have hscheduleMailboxKind :
      ∀ object envelope,
        (lifecycleScheduleKernel plan).ipc.endpoints.mailbox object =
            some envelope →
          (lifecycleScheduleKernel plan).ipc.endpoints.capabilities.kinds
              object = some .endpoint := by
    intro object envelope hmailbox
    exact (hipcSchedule.2.2.2.1 object envelope hmailbox).2.1
  have hscheduleIPCCapabilities :
      (lifecycleScheduleKernel plan).ipc.endpoints.capabilities =
        (lifecycleScheduleKernel plan).lifecycle.capabilities :=
    hcoherentSchedule.2.2.2.2.2.2.1
  have hscheduleLifecycleCapabilities :
      (lifecycleScheduleKernel plan).lifecycle.capabilities =
        lifecycleReleasedCapabilities := by
    calc
      (lifecycleScheduleKernel plan).lifecycle.capabilities =
          (lifecycleScheduleKernel plan).capabilities :=
        hcoherentSchedule.2.2.2.1.symm
      _ = lifecycleReleasedCapabilities := rfl
  have hnoScheduleMailbox :
      ∀ object envelope,
        (lifecycleScheduleKernel plan).ipc.endpoints.mailbox object =
            some envelope → False := by
    intro object envelope hmailbox
    have hkind := hscheduleMailboxKind object envelope hmailbox
    rw [hscheduleIPCCapabilities, hscheduleLifecycleCapabilities] at hkind
    simp [lifecycleReleasedCapabilities, lifecycleCapabilities,
      MemoryLifecycle.retireCapabilities] at hkind
    split at hkind <;> simp_all
  have hscheduleHistoryEndpoint :
      ∀ object envelope,
        envelope ∈
            (lifecycleScheduleKernel plan).ipc.endpoints.sendHistory object →
          envelope.endpoint = object := by
    exact hipcSchedule.2.2.2.2.2
  have hallocatedMailboxNone :
      ∀ object,
        (lifecycleAllocatedKernel plan).ipc.endpoints.mailbox object = none := by
    intro object
    change retainLiveEndpointMailboxes lifecycleAllocatedCapabilities
      (lifecycleScheduleKernel plan).ipc.endpoints.mailbox object = none
    cases hmailbox :
        (lifecycleScheduleKernel plan).ipc.endpoints.mailbox object with
    | none => simp [retainLiveEndpointMailboxes, hmailbox]
    | some envelope => exact False.elim (hnoScheduleMailbox object envelope hmailbox)
  have hendpointAllocated :
      EndpointIPC.WellFormed
        (lifecycleAllocatedKernel plan).ipc.endpoints := by
    refine ⟨⟨hslots, hderivations, hidentities, hslotSpaces⟩,
      ?_, ?_, ?_, ?_⟩
    · intro object _hobject hkind
      change lifecycleAllocatedCapabilities.kinds object =
        some .endpoint at hkind
      by_cases haddressSpace : object = 1 ∨ object = 2
      · simp [lifecycleAllocatedCapabilities, haddressSpace] at hkind
      · by_cases hmemory : object = 21
        · simp [lifecycleAllocatedCapabilities, haddressSpace, hmemory] at hkind
        · simp [lifecycleAllocatedCapabilities, haddressSpace, hmemory] at hkind
    · intro object envelope hmailbox
      rw [hallocatedMailboxNone object] at hmailbox
      contradiction
    · intro object _hobject
      exact hallocatedMailboxNone object
    · intro object envelope hhistory
      exact hscheduleHistoryEndpoint object envelope hhistory
  have hscheduleOwner :
      (lifecycleScheduleKernel plan).virtualMemory.owner =
        lifecycleVirtualMemory.owner := by
    rfl
  have hscheduleIssuedAddressSpace :
      (lifecycleScheduleKernel plan).virtualMemory.issuedAddressSpace =
        lifecycleVirtualMemory.issuedAddressSpace := by
    rfl
  have hscheduleOwnerAddress :
      ∀ addressSpace subject,
        (lifecycleScheduleKernel plan).virtualMemory.owner addressSpace =
            some subject →
          addressSpace = 1 ∨ addressSpace = 2 := by
    intro addressSpace subject howner
    rw [hscheduleOwner] at howner
    by_cases hfirst : addressSpace = 1
    · exact Or.inl hfirst
    · by_cases hsecond : addressSpace = 2
      · exact Or.inr hsecond
      · simp [lifecycleVirtualMemory, hfirst, hsecond] at howner
  have hscheduleOwnerIssued :
      ∀ addressSpace subject,
        (lifecycleScheduleKernel plan).virtualMemory.owner addressSpace =
            some subject →
          (lifecycleScheduleKernel plan).virtualMemory.issuedAddressSpace
              addressSpace = true := by
    intro addressSpace subject howner
    rcases hscheduleOwnerAddress addressSpace subject howner with
      hfirst | hsecond
    · subst addressSpace
      rfl
    · subst addressSpace
      rfl
  have hscheduleOwnerIdentity :
      ∀ addressSpace subject,
        (lifecycleScheduleKernel plan).virtualMemory.owner addressSpace =
            some subject →
          (addressSpace = 1 ∧ subject = 1) ∨
            (addressSpace = 2 ∧ subject = 2) := by
    intro addressSpace subject howner
    rw [hscheduleOwner] at howner
    change lifecycleSubjectState.addressOwner addressSpace = some subject at howner
    exact (lifecycleAddressOwner_some_iff addressSpace subject).1 howner
  have hscheduleOwnerAuthority :
      ∀ addressSpace subject,
        (lifecycleScheduleKernel plan).virtualMemory.owner addressSpace =
            some subject →
          Capability.HasAuthority lifecycleAllocatedScrub.memory.capabilities
            subject addressSpace Capability.Right.revoke := by
    intro addressSpace subject howner
    rcases hscheduleOwnerIdentity addressSpace subject howner with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hspace1
    · exact hspace2
  have hscheduleOwnerAllocatedAuthority :
      ∀ addressSpace subject,
        (lifecycleScheduleKernel plan).virtualMemory.owner addressSpace =
            some subject →
          Capability.HasAuthority lifecycleAllocatedCapabilities
            subject addressSpace Capability.Right.revoke := by
    intro addressSpace subject howner
    rcases hscheduleOwnerIdentity addressSpace subject howner with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨0, lifecycleSubjectOneSpace, rfl, rfl, rfl⟩
    · exact ⟨0, lifecycleSubjectTwoSpace, rfl, rfl, rfl⟩
  have hscheduleReadyNodup :
      (lifecycleScheduleKernel plan).scheduler.ready.Nodup :=
    hschedulerSchedule.2.1
  have hscheduleReadyBound :
      (lifecycleScheduleKernel plan).scheduler.ready.length ≤
        (lifecycleScheduleKernel plan).scheduler.capacity :=
    hschedulerSchedule.2.2.1
  have hscheduleReadyMembers := hschedulerSchedule.2.2.2.1
  have hscheduleCurrentReady := hschedulerSchedule.2.2.2.2
  have hscheduleAcceptedTicks :
      (lifecycleScheduleKernel plan).preemption.acceptedTicks =
        if (lifecycleScheduleKernel plan).preemption.timerArmed then 0 else 1 :=
    hpreemptionSchedule.2
  have hscheduleContextsBound := hresumableSchedule.2.1
  have hscheduleContextsPairwise := hresumableSchedule.2.2.1
  have hscheduleContextsValid := hresumableSchedule.2.2.2.1
  have hscheduleCurrentContext := hresumableSchedule.2.2.2.2.1
  have hscheduleReadyContexts := hresumableSchedule.2.2.2.2.2.1
  have hscheduleTranslations := hresumableSchedule.2.2.2.2.2.2.1
  have hscheduleVirtualAgreement := hresumableSchedule.2.2.2.2.2.2.2.1
  have hscheduleResourceKinds := hresumableSchedule.2.2.2.2.2.2.2.2.1
  have hscheduleTLB := hresumableSchedule.2.2.2.2.2.2.2.2.2
  have hlifecycleAllocated :
      SubjectLifecycle.WellFormed (lifecycleAllocatedLifecycle plan) := by
    rcases hlifecycleSchedule with
      ⟨hissued, howned, haddress, hendpoint, hrunnable, hcurrent⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro subject hlive
      change lifecycleAllocatedCapabilities.subjects subject = true at hlive
      rw [← hsubjects] at hlive
      change
        (lifecycleScheduleKernel plan).lifecycle.issuedSubjects subject = true
      exact hissued subject hlive
    · intro object subject frame hownedMemory
      simp only [lifecycleAllocatedLifecycle, allocateMemoryToLifecycle,
        setOwnedMemory] at hownedMemory
      split at hownedMemory
      · next hobject =>
          subst object
          simp only [Option.some.injEq, Prod.mk.injEq] at hownedMemory
          rcases hownedMemory with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩
      · next hobject =>
          have hold := howned object subject frame hownedMemory
          rcases hold with ⟨hlive, hframeOwner, hfree⟩
          have hframeNe : frame ≠ 4 := by
            intro hframe
            subst frame
            exact hownedFrameNeFour object subject hownedMemory
          refine ⟨?_, ?_, ?_⟩
          · change lifecycleAllocatedCapabilities.subjects subject = true
            rw [← hsubjects]
            exact hlive
          · simp [lifecycleAllocatedLifecycle, allocateMemoryToLifecycle,
              setFrameOwner, hframeNe, hframeOwner]
          · simp [lifecycleAllocatedLifecycle, allocateMemoryToLifecycle,
              setFreeFrame, hframeNe, hfree]
    · intro addressSpace subject howner
      exact hownerSubjectIf addressSpace subject howner
    · intro object subject howner
      change lifecycleAllocatedCapabilities.subjects subject = true
      rw [← hsubjects]
      exact hendpoint object subject howner
    · intro subject hruns
      change lifecycleAllocatedCapabilities.subjects subject = true
      rw [← hsubjects]
      exact hrunnable subject hruns
    · intro subject hselected
      change lifecycleAllocatedCapabilities.subjects subject = true
      rw [← hsubjects]
      exact hcurrent subject hselected
  have hschedulerAllocated :
      Scheduler.WellFormed (lifecycleAllocatedKernel plan).scheduler := by
    refine ⟨hlifecycleAllocated, ?_, ?_, ?_, ?_⟩
    · exact hscheduleReadyNodup
    · exact hscheduleReadyBound
    · intro subject hready
      rcases hscheduleReadyMembers subject hready with
        ⟨hlive, hrunnable, haddressSpace⟩
      refine ⟨?_, hrunnable, ?_⟩
      · change lifecycleAllocatedCapabilities.subjects subject = true
        rw [← hsubjects]
        exact hlive
      · change
          (if (lifecycleScheduleKernel plan).lifecycle.addressOwner subject =
              some subject then some subject else none) ≠ none
        exact haddressSpace
    · intro subject hcurrent
      have hcurrent' :
          (lifecycleScheduleKernel plan).lifecycle.current = some subject :=
        hcurrent
      rcases hscheduleCurrentReady subject hcurrent' with
        ⟨hlive, hrunnable, haddressSpace, hnotReady⟩
      refine ⟨?_, hrunnable, ?_, hnotReady⟩
      · change lifecycleAllocatedCapabilities.subjects subject = true
        rw [← hsubjects]
        exact hlive
      · change
          (if (lifecycleScheduleKernel plan).lifecycle.addressOwner subject =
              some subject then some subject else none) ≠ none
        exact haddressSpace
  have hpreemptionAllocated :
      Preemption.WellFormed (lifecycleAllocatedKernel plan).preemption := by
    exact ⟨hschedulerAllocated, hscheduleAcceptedTicks⟩
  have hvirtualAllocated :
      VirtualMapping.LifecycleWellFormed
        (lifecycleAllocatedKernel plan).virtualMemory := by
    refine ⟨⟨?_, ?_⟩, ⟨hslots, hderivations, hidentities, hslotSpaces⟩,
      ?_, ?_⟩
    · intro addressSpace subject howner
      rcases hscheduleOwnerIdentity addressSpace subject howner with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · rfl
    · intro addressSpace page mapping hmapping
      change retainLiveVirtualMappings lifecycleAllocatedScrub.memory
        (lifecycleScheduleKernel plan).virtualMemory.mappings
          addressSpace page = some mapping at hmapping
      simp [retainLiveVirtualMappings,
        hnoScheduleMappings addressSpace page] at hmapping
    · intro addressSpace subject howner
      have howner' :
          (lifecycleScheduleKernel plan).virtualMemory.owner addressSpace =
            some subject := by
        exact howner
      rcases hscheduleOwnerIdentity addressSpace subject howner' with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl, hspace1⟩
      · exact ⟨rfl, rfl, rfl, rfl, hspace2⟩
    · intro addressSpace hobject hkind
      rcases haddressComplete addressSpace hobject hkind with
        ⟨subject, howner⟩
      refine ⟨subject, ?_⟩
      change
        (lifecycleScheduleKernel plan).virtualMemory.owner addressSpace =
          some subject
      rw [hscheduleOwner]
      exact howner
  have hresumableAllocated :
      ResumablePreemption.WellFormed
        (lifecycleAllocatedKernel plan).resumable := by
    refine ⟨hschedulerAllocated, hscheduleContextsBound,
      hscheduleContextsPairwise, ?_, hscheduleCurrentContext,
      hscheduleReadyContexts, ?_, ?_, ?_, hscheduleTLB⟩
    · intro context hcontext
      rcases hscheduleContextsValid context hcontext with
        ⟨hframe, haddress, hlive, hrunnable, howner⟩
      refine ⟨hframe, haddress, ?_, hrunnable, howner⟩
      change lifecycleAllocatedCapabilities.subjects context.owner = true
      rw [← hsubjects]
      exact hlive
    · constructor
      · change
          (lifecycleScheduleKernel plan).virtualMemory.owner =
            (lifecycleAllocatedLifecycle plan).addressOwner
        rw [hscheduleOwner]
        change lifecycleVirtualMemory.owner =
          lifecycleSubjectState.addressOwner
        rfl
      · have hresumableScheduler :=
          hcoherentSchedule.2.2.2.2.2.2.2.1
        have hschedulerLifecycle := hcoherentSchedule.2.1
        have hcurrentAgreement := hscheduleTranslations.2
        rw [hresumableScheduler, hschedulerLifecycle] at hcurrentAgreement
        exact hcurrentAgreement
    · exact ⟨rfl, hvirtualAllocated⟩
    · constructor
      · intro object owner frame howned
        simp only [lifecycleAllocatedKernel, publishKernelMemory,
          lifecycleAllocatedLifecycle, allocateMemoryToLifecycle,
          setOwnedMemory] at howned
        split at howned
        · next hobject =>
          subst object
          simp only [Option.some.injEq, Prod.mk.injEq] at howned
          rcases howned with ⟨rfl, rfl⟩
          rfl
        · next hobject =>
          have hkind := hscheduleResourceKinds.1 object owner frame howned
          change lifecycleReleasedCapabilities.kinds object =
            some .memory at hkind
          exfalso
          by_cases hfirst : object = 1
          · subst object
            simp [lifecycleReleasedCapabilities, lifecycleCapabilities,
              MemoryLifecycle.retireCapabilities] at hkind
          · by_cases hsecond : object = 2
            · subst object
              simp [lifecycleReleasedCapabilities, lifecycleCapabilities,
                MemoryLifecycle.retireCapabilities] at hkind
            · by_cases hreleased : object = 20
              · subst object
                simp [lifecycleReleasedCapabilities, lifecycleCapabilities,
                  MemoryLifecycle.retireCapabilities] at hkind
              · simp [lifecycleReleasedCapabilities, lifecycleCapabilities,
                  MemoryLifecycle.retireCapabilities, hfirst, hsecond,
                  hreleased] at hkind
      · intro object owner hendpointOwner
        have hkind :=
          hscheduleResourceKinds.2 object owner hendpointOwner
        change lifecycleReleasedCapabilities.kinds object =
          some .endpoint at hkind
        simp [lifecycleReleasedCapabilities, lifecycleCapabilities,
          MemoryLifecycle.retireCapabilities] at hkind
        split at hkind <;> simp_all
  have htransfersAllocated :
      CapabilityTransfer.WellFormed
        (lifecycleAllocatedKernel plan).transfers := by
    refine ⟨hendpointAllocated, ?_⟩
    intro endpoint transfer hpending
    have hvalid := htransfersSchedule.2 endpoint transfer hpending
    rcases hvalid.1 with ⟨envelope, hmailbox, _⟩
    exact False.elim ((hnoScheduleMailbox endpoint envelope) hmailbox)
  have hhaltedAllocated :
      (lifecycleAllocatedKernel plan).resumable.halted = true ↔
        ∃ record,
          (lifecycleAllocatedKernel plan).execution.mode =
            FailStop.Mode.halted record := by
    exact hhaltedSchedule
  have hreturnAllocated :
      (lifecycleAllocatedKernel plan).execution.returnAuthorityArmed = true →
        (lifecycleAllocatedKernel plan).ReturnPlanLive = true := by
    simp [lifecycleAllocatedKernel, publishKernelMemory]
  have hblockingAllocated :
      (lifecycleAllocatedKernel plan).BlockingIPCCoherent := by
    simp [lifecycleAllocatedKernel, publishKernelMemory,
      FailStop.CompositeState.BlockingIPCCoherent]
  have hdeferredAllocated :
      (lifecycleAllocatedKernel plan).DeferredCancellationWellFormed := by
    rcases hdeferredSchedule with
      ⟨⟨⟨hblockingIPCSchedule, hcontextAgreementSchedule⟩,
        hblockedDeferredSchedule, hretainedSchedule⟩,
        hblockedResumableSchedule, hretainedResumableSchedule⟩
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨?_, hblockedDeferredSchedule, hretainedSchedule⟩
      refine ⟨?_, hcontextAgreementSchedule⟩
      rcases hblockingIPCSchedule with
        ⟨_hschedulerSchedule, hwaitersSchedule, hwaiterMembersSchedule,
          hwaiterUniqueSchedule, hwaiterIndexSchedule, _hmailboxSchedule,
          _hcapabilitiesSchedule⟩
      refine ⟨hschedulerAllocated, hwaitersSchedule, ?_,
        hwaiterUniqueSchedule, hwaiterIndexSchedule, ?_,
        hendpointAllocated.1⟩
      · intro endpoint subject hwaiter
        have hvalid := hwaiterMembersSchedule endpoint subject hwaiter
        rcases hvalid.2.1 with
          ⟨slot, capability, hslot, hobject, hkind, _hrights, _hlive⟩
        have hcapabilityKind :=
          (_hcapabilitiesSchedule.1 subject slot capability hslot).2.2.1
        rw [hobject, hkind] at hcapabilityKind
        change
          (lifecycleScheduleKernel plan).blockingIPC.scheduler.lifecycle.capabilities.kinds
              endpoint = some .endpoint at hcapabilityKind
        rw [hblockingSchedule.2, hscheduleLifecycleCapabilities] at hcapabilityKind
        simp [lifecycleReleasedCapabilities, lifecycleCapabilities,
          MemoryLifecycle.retireCapabilities] at hcapabilityKind
        split at hcapabilityKind <;> simp_all
      · intro endpoint envelope hmailbox
        have hmailbox' :
            (lifecycleScheduleKernel plan).blockingIPCContext.ipc.mailbox
                endpoint = some envelope := hmailbox
        have hvalid := _hmailboxSchedule endpoint envelope hmailbox'
        have hkind := hvalid.2.1
        change
          (lifecycleScheduleKernel plan).blockingIPC.scheduler.lifecycle.capabilities.kinds
              endpoint = some .endpoint at hkind
        rw [hblockingSchedule.2, hscheduleLifecycleCapabilities] at hkind
        simp [lifecycleReleasedCapabilities, lifecycleCapabilities,
          MemoryLifecycle.retireCapabilities] at hkind
        split at hkind <;> simp_all
    · intro subject saved hblocked
      exact hblockedResumableSchedule subject saved hblocked
    · intro subject saved hretained
      exact hretainedResumableSchedule subject saved hretained
  have hpublicationAllocated :
      InvalidationPublication.WellFormed
        (lifecycleAllocatedKernel plan).invalidationPublication := by
    simpa [lifecycleAllocatedKernel, publishKernelMemory] using
      hpublicationSchedule
  apply FailStop.DeferredBlockingRuntimeWellFormed.authoritative
  repeat' first
    | exact hendpointAllocated
    | exact hschedulerAllocated
    | exact hpreemptionAllocated
    | exact hresumableAllocated
    | exact htransfersAllocated
    | exact hhaltedAllocated
    | exact hreturnAllocated
    | exact hblockingAllocated
    | exact hdeferredAllocated
    | exact hpublicationAllocated
    | assumption
    | apply And.intro
  all_goals first
    | assumption
    | simp [lifecycleAllocatedKernel, publishKernelMemory,
    lifecycleAllocatedLifecycle, allocateMemoryToLifecycle,
    lifecycleScheduleKernel_addressOwner, lifecycleAllocatedScrub,
    lifecycleReleaseScrub, lifecycleAfterWriteScrub, lifecycleScrub,
    FrameScrub.allocate, MemoryLifecycle.allocate,
    MemoryLifecycle.activateObject, MemoryLifecycle.retireCapabilities,
    MemoryLifecycle.setObject, MemoryLifecycle.setBinding,
    MemoryLifecycle.setIssued, FrameAllocator.allocate,
    FrameAllocator.setStatus, LeanOS.Capability.installRoot,
    LeanOS.Capability.install,
    setOwnedMemory, setFrameOwner, setFreeFrame,
    retainLiveVirtualMappings, retainLiveEndpointMailboxes,
    FailStop.CompositeState.Coherent,
    FailStop.WellFormed, Interrupt.WellFormed,
    SubjectLifecycle.WellFormed,
    VirtualMapping.LifecycleWellFormed, VirtualMapping.WellFormed,
    IPCSyscall.WellFormed, EndpointIPC.WellFormed,
    Scheduler.WellFormed, Preemption.WellFormed,
    ResumablePreemption.WellFormed,
    ResumablePreemption.ReadyContextAgreement,
    ResumablePreemption.TranslationAgreement,
    ResumablePreemption.VirtualAgreement,
    ResumablePreemption.ResourceKindAgreement,
    CapabilityTransfer.WellFormed, TLB.Coherent,
    FailStop.CompositeState.ReturnPlanLive,
    FailStop.CompositeState.blockingIPCContext,
    FailStop.CompositeState.BlockingIPCCoherent,
    FailStop.CompositeState.DeferredCancellationWellFormed,
    BlockingIPCContext.DeferredWellFormed,
    BlockingIPCContext.WellFormed,
    BlockingIPCContext.ContextAgreement, BlockingIPC.WellFormed,
    BlockingIPC.authorizedReceive, BlockingIPCContext.emptyDeferred,
    BlockingIPCContext.validSaved, Scheduler.ownsAddressSpace,
    ResumablePreemption.contextFor, ResumablePreemption.validContext,
    LeanOS.Capability.rightsValid, LeanOS.Capability.rightsSubset,
    LeanOS.Capability.nonemptyRights, Interrupt.validSavedUserFrame,
    DirectPortIO.AcceptedControls, DMAQuarantine.q35Accepted,
    FailStop.bootRuntime]
  all_goals simp_all (config := { failIfUnchanged := false })
    [lifecycleCapabilities, lifecycleAllocatedCapabilities]
  all_goals grind

private theorem lifecycleAllocated_coherent
    (plan : BootPageTablePlan.Plan) :
    (lifecycleAllocated plan).Coherent := by
  refine ⟨rfl, rfl, rfl, rfl, lifecycleAllocatedScrub_invariant, ?_⟩
  simp [lifecycleAllocated, lifecycleAllocatedKernel,
    lifecycleAllocatedIOMMU, lifecycleAllocatedCore,
    allocateMemoryCore, lifecycleAllocatedLifecycle,
    allocateMemoryToLifecycle, publishKernelMemory,
    lifecycleScheduleKernel, lifecycleScheduleIOMMU,
    lifecycleReleaseIOMMU, lifecycleReleaseCore, releaseMemoryCore,
    lifecycleAfterWriteIOMMU, lifecycleInitialCore,
    lifecycleAllocatedScrub, lifecycleReleaseScrub,
    lifecycleAfterWriteScrub, lifecycleScrub, lifecycleMemory,
    lifecycleCapabilities, lifecycleSubjectOneMemory,
    lifecycleSubjectOneSpace, lifecycleSubjectTwoSpace,
    lifecycleSubjectTwoMemory, lifecycleReleaseKernel,
    lifecycleReleaseLifecycle, retireMemoryFromLifecycle,
    lifecycleKernel, lifecycleSubjectState, lifecycleVirtualMemory,
    lifecycleScheduler, FailStop.authoritativeGate,
    FailStop.applyAuthoritativeOperation, FailStop.applyOperation,
    FrameScrub.allocate, MemoryLifecycle.allocate,
    MemoryLifecycle.activateObject, MemoryLifecycle.retireCapabilities,
    MemoryLifecycle.setObject, MemoryLifecycle.setBinding,
    MemoryLifecycle.setIssued, FrameAllocator.allocate,
    FrameAllocator.setStatus, LeanOS.Capability.installRoot,
    LeanOS.Capability.install, nextFrameGeneration, setFrameAuthority,
    setFrameLive, setOwnedMemory, setFrameOwner, setFreeFrame,
    pageSize, rangeContained, Permission.attenuates]
  native_decide

private theorem lifecycleAllocated_invariant
    (plan : BootPageTablePlan.Plan) :
    (lifecycleAllocated plan).Invariant :=
  ⟨lifecycleAllocatedKernel_invariant plan,
    lifecycleAllocatedIOMMU.invariant,
    lifecycleAllocated_coherent plan⟩

private noncomputable def publicationAllocateOutcome
    (plan : BootPageTablePlan.Plan) :=
  gatedMemoryByKernel (lifecycleScheduled plan)
    (lifecycleScheduled_invariant plan) (.allocate 21 1 1)

theorem authoritative_lifecycle_allocate_accepted
    (plan : BootPageTablePlan.Plan) :
    (publicationAllocateOutcome plan).isAccepted = true := by
  classical
  have hpacked :
      (⟨lifecycleScheduled plan, lifecycleScheduled_invariant plan⟩ :
          { state : AuthoritativeExtension // state.Invariant }) =
        ⟨lifecycleScheduledCandidate plan,
          lifecycleScheduledCandidate_invariant plan⟩ := by
    apply Subtype.ext
    exact lifecycle_schedule_state_exact plan
  have hout := congrArg
    (fun packed : { state : AuthoritativeExtension // state.Invariant } =>
      (gatedMemoryByKernel packed.1 packed.2 (.allocate 21 1 1)).isAccepted)
    hpacked
  change (publicationAllocateOutcome plan).isAccepted =
    (gatedMemoryByKernel (lifecycleScheduledCandidate plan)
      (lifecycleScheduledCandidate_invariant plan)
      (.allocate 21 1 1)).isAccepted at hout
  rw [hout]
  have hmode :
      (lifecycleScheduleKernel plan).execution.mode = .running := rfl
  have hcurrent :
      (lifecycleScheduleKernel plan).execution.core.context.currentSubject =
        (1 : FrameScrub.SubjectId) :=
    (lifecycleScheduledCandidate_coherent plan).1
  simp only [gatedMemoryByKernel, lifecycleScheduledCandidate,
    hmode, hcurrent, if_pos]
  rw [lifecycle_allocate_result_accepted]
  rw [lifecycle_allocate_state_exact]
  have hbinding :
      lifecycleAllocatedScrub.memory.binding 21 = some 4 := by
    native_decide
  have hlookup :
      LeanOS.Capability.lookup
          lifecycleAllocatedScrub.memory.capabilities 1 1 =
        .found lifecycleSubjectOneMemory := by
    native_decide
  rw [hbinding, hlookup]
  change
    (commitAuthoritativeMemory (lifecycleScheduledCandidate plan)
      (lifecycleAllocatedKernel plan) lifecycleAllocatedCore
      lifecycleAllocatedScrub .allocated).isAccepted = true
  unfold commitAuthoritativeMemory
  split
  · split
    · dsimp only
      split
      · rfl
      · next hinvariant =>
        have hcandidate :
            ({ kernel := lifecycleAllocatedKernel plan
               iommu := lifecycleAllocatedIOMMU
               scrub := lifecycleAllocatedScrub } :
              AuthoritativeExtension).Invariant := by
          simpa [lifecycleAllocated] using lifecycleAllocated_invariant plan
        exact (hinvariant hcandidate).elim
    · next hvalid =>
      exact (hvalid lifecycleAllocatedIOMMU.valid).elim
  · next hcapability =>
    exact (hcapability lifecycleAllocatedIOMMU.capabilityWellFormed).elim

private theorem authoritative_lifecycle_allocate_state_exact
    (plan : BootPageTablePlan.Plan) :
    (publicationAllocateOutcome plan).state = lifecycleAllocated plan := by
  classical
  have hpacked :
      (⟨lifecycleScheduled plan, lifecycleScheduled_invariant plan⟩ :
          { state : AuthoritativeExtension // state.Invariant }) =
        ⟨lifecycleScheduledCandidate plan,
          lifecycleScheduledCandidate_invariant plan⟩ := by
    apply Subtype.ext
    exact lifecycle_schedule_state_exact plan
  have hout := congrArg
    (fun packed : { state : AuthoritativeExtension // state.Invariant } =>
      (gatedMemoryByKernel packed.1 packed.2 (.allocate 21 1 1)).state)
    hpacked
  change (publicationAllocateOutcome plan).state =
    (gatedMemoryByKernel (lifecycleScheduledCandidate plan)
      (lifecycleScheduledCandidate_invariant plan)
      (.allocate 21 1 1)).state at hout
  rw [hout]
  have hmode :
      (lifecycleScheduleKernel plan).execution.mode = .running := rfl
  have hcurrent :
      (lifecycleScheduleKernel plan).execution.core.context.currentSubject =
        (1 : FrameScrub.SubjectId) :=
    (lifecycleScheduledCandidate_coherent plan).1
  simp only [gatedMemoryByKernel, lifecycleScheduledCandidate,
    hmode, hcurrent, if_pos]
  rw [lifecycle_allocate_result_accepted]
  rw [lifecycle_allocate_state_exact]
  have hbinding :
      lifecycleAllocatedScrub.memory.binding 21 = some 4 := by
    native_decide
  have hlookup :
      LeanOS.Capability.lookup
          lifecycleAllocatedScrub.memory.capabilities 1 1 =
        .found lifecycleSubjectOneMemory := by
    native_decide
  rw [hbinding, hlookup]
  change
    (commitAuthoritativeMemory (lifecycleScheduledCandidate plan)
      (lifecycleAllocatedKernel plan) lifecycleAllocatedCore
      lifecycleAllocatedScrub .allocated).state = lifecycleAllocated plan
  unfold commitAuthoritativeMemory
  split
  · split
    · dsimp only
      split
      · rfl
      · next hinvariant =>
        have hcandidate :
            ({ kernel := lifecycleAllocatedKernel plan
               iommu := lifecycleAllocatedIOMMU
               scrub := lifecycleAllocatedScrub } :
              AuthoritativeExtension).Invariant := by
          simpa [lifecycleAllocated] using lifecycleAllocated_invariant plan
        exact (hinvariant hcandidate).elim
    · next hvalid =>
      exact (hvalid lifecycleAllocatedIOMMU.valid).elim
  · next hcapability =>
    exact (hcapability lifecycleAllocatedIOMMU.capabilityWellFormed).elim

private def lifecycleAssignedCore : Core :=
  { lifecycleAllocatedCore with
    nextAssignmentGeneration := 3
    nextDomainGeneration := 3
    assignments := lifecycleAllocatedCore.assignments ++
      [⟨⟨1, 2⟩, 1, 1, ⟨1, 2⟩, 1⟩] }

private def lifecycleAssignedIOMMU : State :=
  { core := lifecycleAssignedCore
    valid := by native_decide
    capabilityWellFormed := lifecycleAllocatedIOMMU.capabilityWellFormed }

private def lifecycleAssigned (plan : BootPageTablePlan.Plan) :
    AuthoritativeExtension :=
  { kernel := lifecycleAllocatedKernel plan
    iommu := lifecycleAssignedIOMMU
    scrub := lifecycleAllocatedScrub }

private theorem lifecycleAssigned_coherent
    (plan : BootPageTablePlan.Plan) :
    (lifecycleAssigned plan).Coherent := by
  refine ⟨rfl, rfl, rfl, rfl, lifecycleAllocatedScrub_invariant, ?_⟩
  rcases (lifecycleAllocated_coherent plan).2.2.2.2.2 with
    ⟨hassignments, hcapabilities, hmappings, hframes⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro assignment hmember
    simp only [lifecycleAssigned, lifecycleAssignedIOMMU,
      lifecycleAssignedCore, List.mem_append, List.mem_singleton] at hmember
    rcases hmember with hmember | rfl
    · exact hassignments assignment hmember
    · have hexists :
          ∃ capability ∈ lifecycleAllocatedCore.capabilities,
            capability.owner = 1 := by
        native_decide
      rcases hexists with ⟨capability, hmember, howner⟩
      simpa [howner, lifecycleAssigned, lifecycleAllocated] using
        (hcapabilities capability hmember).1
  · simpa [lifecycleAssigned, lifecycleAssignedIOMMU,
      lifecycleAssignedCore, lifecycleAllocated,
      lifecycleAllocatedIOMMU] using hcapabilities
  · simpa [lifecycleAssigned, lifecycleAssignedIOMMU,
      lifecycleAssignedCore, lifecycleAllocated,
      lifecycleAllocatedIOMMU] using hmappings
  · simpa [lifecycleAssigned, lifecycleAssignedIOMMU,
      lifecycleAssignedCore, lifecycleAllocated,
      lifecycleAllocatedIOMMU] using hframes

private theorem lifecycleAssigned_invariant
    (plan : BootPageTablePlan.Plan) :
    (lifecycleAssigned plan).Invariant :=
  ⟨lifecycleAllocatedKernel_invariant plan,
    lifecycleAssignedIOMMU.invariant,
    lifecycleAssigned_coherent plan⟩

private theorem lifecycle_assign_accepted :
    (gate lifecycleAllocatedIOMMU (.assign ⟨1⟩)).isAccepted = true := by
  native_decide

private theorem lifecycle_assign_state_exact :
    (gate lifecycleAllocatedIOMMU (.assign ⟨1⟩)).state =
      lifecycleAssignedIOMMU := by
  rfl

private noncomputable def publicationAssignOutcome
    (plan : BootPageTablePlan.Plan) :=
  gatedByKernel (lifecycleAllocated plan)
    (lifecycleAllocated_invariant plan) (.assign ⟨1⟩)

theorem authoritative_lifecycle_assign_to_b_accepted
    (plan : BootPageTablePlan.Plan) :
    (publicationAssignOutcome plan).isAccepted = true := by
  classical
  have hmode : (lifecycleAllocatedKernel plan).execution.mode = .running := rfl
  unfold publicationAssignOutcome gatedByKernel
  simp only [lifecycleAllocated, hmode]
  cases hgate : gate lifecycleAllocatedIOMMU (.assign ⟨1⟩) with
  | rejected reason =>
      have haccepted := lifecycle_assign_accepted
      rw [hgate] at haccepted
      contradiction
  | accepted after reply =>
      have hstate := lifecycle_assign_state_exact
      rw [hgate] at hstate
      change after = lifecycleAssignedIOMMU at hstate
      subst after
      have hcoherent :
          ({ kernel := lifecycleAllocatedKernel plan
             iommu := lifecycleAssignedIOMMU
             scrub := lifecycleAllocatedScrub } : AuthoritativeExtension).Coherent :=
        lifecycleAssigned_coherent plan
      simp only [AuthoritativeOutcome.isAccepted]
      simp [hcoherent]

private theorem authoritative_lifecycle_assign_state_exact
    (plan : BootPageTablePlan.Plan) :
    (publicationAssignOutcome plan).state = lifecycleAssigned plan := by
  classical
  have hmode : (lifecycleAllocatedKernel plan).execution.mode = .running := rfl
  unfold publicationAssignOutcome gatedByKernel
  simp only [lifecycleAllocated, hmode]
  cases hgate : gate lifecycleAllocatedIOMMU (.assign ⟨1⟩) with
  | rejected reason =>
      have haccepted := lifecycle_assign_accepted
      rw [hgate] at haccepted
      contradiction
  | accepted after reply =>
      have hstate := lifecycle_assign_state_exact
      rw [hgate] at hstate
      change after = lifecycleAssignedIOMMU at hstate
      subst after
      have hcoherent :
          ({ kernel := lifecycleAllocatedKernel plan
             iommu := lifecycleAssignedIOMMU
             scrub := lifecycleAllocatedScrub } : AuthoritativeExtension).Coherent :=
        lifecycleAssigned_coherent plan
      simp only [AuthoritativeOutcome.state]
      rw [dif_pos hcoherent]
      rfl

private def lifecycleGrant : GrantRequest :=
  ⟨⟨1, 2⟩, ⟨1, 4⟩, 0, 0, pageSize, readWrite⟩

private def lifecycleGrantedCore : Core :=
  { lifecycleAssignedCore with
    nextMappingGeneration := 3
    mappings := lifecycleAssignedCore.mappings ++
      [⟨⟨0, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, 1, 0, pageSize,
        ⟨4, 2⟩, 0, readWrite⟩] }

private def lifecycleGrantedIOMMU : State :=
  { core := lifecycleGrantedCore
    valid := by native_decide
    capabilityWellFormed := lifecycleAssignedIOMMU.capabilityWellFormed }

private def lifecycleGranted (plan : BootPageTablePlan.Plan) :
    AuthoritativeExtension :=
  { kernel := lifecycleAllocatedKernel plan
    iommu := lifecycleGrantedIOMMU
    scrub := lifecycleAllocatedScrub }

private theorem lifecycleGranted_coherent
    (plan : BootPageTablePlan.Plan) :
    (lifecycleGranted plan).Coherent := by
  refine ⟨rfl, rfl, rfl, rfl, lifecycleAllocatedScrub_invariant, ?_⟩
  rcases (lifecycleAssigned_coherent plan).2.2.2.2.2 with
    ⟨hassignments, hcapabilities, hmappings, hframes⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hassignments
  · exact hcapabilities
  · intro mapping hmember
    simp only [lifecycleGranted, lifecycleGrantedIOMMU,
      lifecycleGrantedCore, List.mem_append, List.mem_singleton] at hmember
    rcases hmember with hmember | rfl
    · exact hmappings mapping hmember
    · let capability : Capability :=
        ⟨1, 4, 1, 21, ⟨4, 2⟩, 0, FrameScrub.frameBytes, readWrite⟩
      have hmember : capability ∈ lifecycleAssignedCore.capabilities := by
        simp only [capability, lifecycleAssignedCore, lifecycleAllocatedCore,
          allocateMemoryCore, List.mem_append, List.mem_singleton]
        right
        congr 1
      have hcapability := hcapabilities capability hmember
      exact ⟨hcapability.1, capability, hmember, rfl, rfl,
        by native_decide, by native_decide⟩
  · exact hframes

private theorem lifecycleGranted_invariant
    (plan : BootPageTablePlan.Plan) :
    (lifecycleGranted plan).Invariant :=
  ⟨lifecycleAllocatedKernel_invariant plan,
    lifecycleGrantedIOMMU.invariant,
    lifecycleGranted_coherent plan⟩

private theorem lifecycle_grant_accepted :
    (gate lifecycleAssignedIOMMU (.grant lifecycleGrant)).isAccepted = true := by
  native_decide

private theorem lifecycle_grant_state_exact :
    (gate lifecycleAssignedIOMMU (.grant lifecycleGrant)).state =
      lifecycleGrantedIOMMU := by
  rfl

private noncomputable def publicationGrantOutcome
    (plan : BootPageTablePlan.Plan) :=
  gatedByKernel (lifecycleAssigned plan)
    (lifecycleAssigned_invariant plan) (.grant lifecycleGrant)

theorem authoritative_lifecycle_grant_to_b_accepted
    (plan : BootPageTablePlan.Plan) :
    (publicationGrantOutcome plan).isAccepted = true := by
  classical
  have hmode : (lifecycleAllocatedKernel plan).execution.mode = .running := rfl
  unfold publicationGrantOutcome gatedByKernel
  simp only [lifecycleAssigned, hmode]
  cases hgate : gate lifecycleAssignedIOMMU (.grant lifecycleGrant) with
  | rejected reason =>
      have haccepted := lifecycle_grant_accepted
      rw [hgate] at haccepted
      contradiction
  | accepted after reply =>
      have hstate := lifecycle_grant_state_exact
      rw [hgate] at hstate
      change after = lifecycleGrantedIOMMU at hstate
      subst after
      have hcoherent :
          ({ kernel := lifecycleAllocatedKernel plan
             iommu := lifecycleGrantedIOMMU
             scrub := lifecycleAllocatedScrub } : AuthoritativeExtension).Coherent :=
        lifecycleGranted_coherent plan
      simp only [AuthoritativeOutcome.isAccepted]
      simp [hcoherent]

private theorem authoritative_lifecycle_grant_state_exact
    (plan : BootPageTablePlan.Plan) :
    (publicationGrantOutcome plan).state = lifecycleGranted plan := by
  classical
  have hmode : (lifecycleAllocatedKernel plan).execution.mode = .running := rfl
  unfold publicationGrantOutcome gatedByKernel
  simp only [lifecycleAssigned, hmode]
  cases hgate : gate lifecycleAssignedIOMMU (.grant lifecycleGrant) with
  | rejected reason =>
      have haccepted := lifecycle_grant_accepted
      rw [hgate] at haccepted
      contradiction
  | accepted after reply =>
      have hstate := lifecycle_grant_state_exact
      rw [hgate] at hstate
      change after = lifecycleGrantedIOMMU at hstate
      subst after
      have hcoherent :
          ({ kernel := lifecycleAllocatedKernel plan
             iommu := lifecycleGrantedIOMMU
             scrub := lifecycleAllocatedScrub } : AuthoritativeExtension).Coherent :=
        lifecycleGranted_coherent plan
      simp only [AuthoritativeOutcome.state]
      rw [dif_pos hcoherent]
      rfl

private def lifecycleReadRequest : TransferRequest :=
  ⟨1, 2, 0, 1⟩

private def observedBytes {state request} :
    ReadOutcome state request → List UInt8
  | .observed _ bytes => bytes
  | .rejected _ => []

/-- The full public, invariant-bearing lifetime trace is nonvacuous.  A's
authorized device write stores the sentinel, release retires its exact live
frame lifetime, the kernel selects B, allocation scrubs and republishes the
same physical frame under a fresh lifetime, and B obtains fresh assignment
and mapping authority.  B's resulting device observation cannot contain A's
sentinel. -/
theorem scrubbed_reassignment_device_read_no_sentinel
    (plan : BootPageTablePlan.Plan) :
    (publicationWriteOutcome plan).isAccepted = true ∧
      (publicationWriteOutcome plan).state = lifecycleAfterWrite plan ∧
      lifecycleAfterWriteScrub.bytes 4 0 = 0xa5 ∧
      (publicationReleaseOutcome plan).isAccepted = true ∧
      (publicationReleaseOutcome plan).state = lifecycleReleased plan ∧
      lifecycleReleaseScrub.bytes 4 0 = 0xa5 ∧
      lifecycleScheduled plan = lifecycleScheduledCandidate plan ∧
      (publicationAllocateOutcome plan).isAccepted = true ∧
      (publicationAllocateOutcome plan).state = lifecycleAllocated plan ∧
      FrameScrub.Fresh lifecycleAllocatedScrub 21 ∧
      lifecycleAllocatedScrub.memory.binding 21 = some 4 ∧
      lifecycleAllocatedIOMMU.core.memory = lifecycleAllocatedScrub.bytes ∧
      (publicationAssignOutcome plan).isAccepted = true ∧
      (publicationAssignOutcome plan).state = lifecycleAssigned plan ∧
      (publicationGrantOutcome plan).isAccepted = true ∧
      (publicationGrantOutcome plan).state = lifecycleGranted plan ∧
      (deviceRead lifecycleGrantedIOMMU
        lifecycleReadRequest).isObserved = true ∧
      observedBytes (deviceRead lifecycleGrantedIOMMU
        lifecycleReadRequest) = [FrameScrub.initialByte] ∧
      0xa5 ∉ observedBytes (deviceRead lifecycleGrantedIOMMU
        lifecycleReadRequest) := by
  refine ⟨authoritative_lifecycle_write_accepted plan,
    authoritative_lifecycle_write_state_exact plan, by native_decide,
    authoritative_lifecycle_release_accepted plan,
    authoritative_lifecycle_release_state_exact plan, by native_decide,
    lifecycle_schedule_state_exact plan,
    authoritative_lifecycle_allocate_accepted plan,
    authoritative_lifecycle_allocate_state_exact plan, ?_,
    by native_decide, rfl,
    authoritative_lifecycle_assign_to_b_accepted plan,
    authoritative_lifecycle_assign_state_exact plan,
    authoritative_lifecycle_grant_to_b_accepted plan,
    authoritative_lifecycle_grant_state_exact plan,
    by native_decide, by native_decide, by native_decide⟩
  exact FrameScrub.allocation_publishes_scrubbed
    lifecycleReleaseScrub 21 1 1 (by native_decide)

end LeanOS.IOMMU
