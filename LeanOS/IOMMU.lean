import LeanOS.DMAQuarantine
import LeanOS.FailStop
import LeanOS.CapabilityHandle
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
        capability.owner capability.slot, findFrame core capability.frame with
    | .found source, some frame =>
        source.object == capability.object &&
          decide (source.kind = .memory) &&
          source.identity == capability.identity &&
          (!capability.permission.read || source.rights.read) &&
          (!capability.permission.write || source.rights.write) &&
          frame.live && !frame.kernelOwned && !frame.pageTable &&
          !frame.allocatorMetadata && frame.owner == capability.owner &&
          rangeContained capability.offset capability.length 0 frame.size
    | _, _ => false

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
    mappingsDisjoint core.mappings

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
          else if frame.kernelOwned || frame.pageTable || frame.allocatorMetadata then
            .rejected .protectedFrame
          else if state.core.mappings.any (·.frame == handle) then
            .rejected .frameStillReachable
          else
            commit state
              { state.core with
                frames := setFrameLive state.core.frames handle false
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
      let frames := state.core.frames.map fun frame =>
        if frame.owner == owner && !frame.kernelOwned && !frame.pageTable &&
            !frame.allocatorMetadata then
          { frame with live := false }
        else frame
      commit state
        { state.core with
          assignments := retainedAssignments
          mappings := retainedMappings
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

/-- Source is supplied by the trusted device/IOMMU boundary.  Assignment
generation is included so retirement followed by reuse of the same device BDF
and source cannot revive an old request.  There is deliberately no domain,
owner, or physical-frame field. -/
structure TransferRequest where
  source : SourceId
  assignmentGeneration : Generation
  iova : IOVA
  length : Nat
  deriving BEq, DecidableEq, Repr

/-- Explicit platform assumption, intentionally weaker than confinement:
hardware supplies the requester/source identity and transfer range faithfully.
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
          refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
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

/-- A source assignment cannot translate to a frame owned by a different
subject.  Combined with range-local reads/writes, this is the owner-isolation
bridge used by the one-step and finite-trace confinement claims. -/
theorem translation_owner_isolation
    (translation : Translation state request direction)
    (otherOwner : OwnerId)
    (hother : otherOwner ≠ translation.assignment.owner) :
    translation.frame.owner ≠ otherOwner := by
  rw [translation.frameOwnerBound]
  exact Ne.symm hother

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
            ⟨_, _, _, _, _, _, _, _, _, hotherFrame, _⟩
          exact hotherFrame frame hne.symm

/-- Finite-trace integrity: if no successful authorized write names a frame,
every byte of that frame is identical after the trace.  Kernel-owned,
page-table, allocator-metadata, unassigned, and unrelated-subject frames are
instances because translation can never target the first three and owner
isolation prevents the latter two from becoming an assigned mapping. -/
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
      · by_cases hprotected :
            frame.kernelOwned || frame.pageTable || frame.allocatorMetadata
        · exact ⟨.protectedFrame, by simp [howner, hprotected]⟩
        · exact ⟨.frameStillReachable, by simp [howner, hprotected, hreachable]⟩

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

/-- Cross-projection authority coherence.  The selected owner is the exact
kernel-selected subject, capability provenance is the authoritative kernel
capability state, and every retained device authority owner is live. -/
def AuthoritativeExtension.Coherent (state : AuthoritativeExtension) : Prop :=
  state.iommu.core.currentOwner =
      state.kernel.execution.core.context.currentSubject ∧
    state.iommu.core.capabilityAuthority = state.kernel.capabilities ∧
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
    { kernel, iommu := reconcileKernelAuthority kernel state.iommu }
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

/-- IOMMU authority is admitted only while the global fatal latch is running.
Busy and halted states reject definitionally without an IOMMU post-state. -/
def gatedByKernel (kernel : FailStop.CompositeState) (state : State)
    (operation : Operation) : Outcome state :=
  match kernel.execution.mode with
  | .running => gate state operation
  | .handling _ => .rejected .kernelBusy
  | .halted _ => .rejected .kernelHalted

theorem halted_iommu_absorbing (kernel : FailStop.CompositeState) (state : State)
    (operation : Operation) (record : FailStop.HaltRecord)
    (hhalted : kernel.execution.mode = .halted record) :
    gatedByKernel kernel state operation = .rejected .kernelHalted := by
  simp [gatedByKernel, hhalted]

def runGated (kernel : FailStop.CompositeState) : State → List Operation → State
  | state, [] => state
  | state, operation :: rest =>
      runGated kernel (gatedByKernel kernel state operation).state rest

theorem halted_iommu_suffix_absorbing (kernel : FailStop.CompositeState)
    (state : State) (operations : List Operation) (record : FailStop.HaltRecord)
    (hhalted : kernel.execution.mode = .halted record) :
    runGated kernel state operations = state := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation rest ih =>
      simp only [runGated]
      rw [halted_iommu_absorbing kernel state operation record hhalted]
      exact ih state

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
  native_decide
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

end LeanOS.IOMMU
