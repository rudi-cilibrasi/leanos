import LeanOS.VTdBootPlan

/-!
# Linked VT-d boot-plan generator

This host-only executable receives the final-ELF remapping-table symbol
addresses plus the CPU page-table layout, constructs the finite
`VTdBootPlan.Input` values those symbols represent (the deny-all state, the
assigned-EDU state, and, for a device-service image, the device-service state,
each with its reviewed platform binding), requires `VTdBootPlan.compile` to
accept every one, and emits the compiled root, context, and second-level table
words plus the pinned register constants consumed by the guest constructor.
Every table word in the generated header is `compile` output.  The linker,
symbol extraction, generated header, C/assembly table writes, VT-d MMIO
programming, and hardware page walk remain trusted build and integration
boundaries rather than proved refinement steps.
-/
namespace LeanOS.VTdBootPlanGenerator

open LeanOS
open LeanOS.X86PageTable (pageBytes)
open LeanOS.VTdBootPlan

structure Layout where
  rootTableStart : Nat
  contextTableStart : Nat
  secondLevelRootStart : Nat
  secondLevelDirectoryStart : Nat
  secondLevelTableStart : Nat
  remappingTableEnd : Nat
  cpuRootA : Nat
  cpuTableEnd : Nat
  assignedGuardBeforeStart : Nat
  assignedReadBufferStart : Nat
  assignedWriteBufferStart : Nat
  assignedGuardAfterStart : Nat
  /-- Device-service images only: the executor scratch whose first pages form
  the assigned controller's DMA window; `none` for every other image. -/
  serviceDmaStart : Option Nat := none
  /-- Which reviewed device-service assignment the image carries: 1 the q35
  xHCI (`deviceServiceState`), 2 the q35 AHCI (`ahciServiceState`). -/
  serviceDevice : Nat := 1
  deriving Repr

def expectedArgumentCount : Nat := 12

def parseNat (value : String) : Except String Nat :=
  match value.toNat? with
  | some parsed => .ok parsed
  | none => .error s!"invalid decimal address: {value}"

def parseLayout (args : List String) : Except String Layout := do
  if args.length != expectedArgumentCount && args.length != expectedArgumentCount + 1 &&
      args.length != expectedArgumentCount + 2 then
    throw s!"expected {expectedArgumentCount} decimal addresses (+1 for a device service, +2 with its device), got {args.length}"
  let values ← args.mapM parseNat
  let valueAt (index : Nat) := values[index]?.getD 0
  pure {
    rootTableStart := valueAt 0, contextTableStart := valueAt 1,
    secondLevelRootStart := valueAt 2, secondLevelDirectoryStart := valueAt 3,
    secondLevelTableStart := valueAt 4, remappingTableEnd := valueAt 5,
    cpuRootA := valueAt 6, cpuTableEnd := valueAt 7,
    assignedGuardBeforeStart := valueAt 8,
    assignedReadBufferStart := valueAt 9,
    assignedWriteBufferStart := valueAt 10,
    assignedGuardAfterStart := valueAt 11,
    serviceDmaStart := if args.length > expectedArgumentCount then some (valueAt 12) else none,
    serviceDevice := if args.length > expectedArgumentCount + 1 then valueAt 13 else 1 }

def frameOf (address : Nat) : Nat := address / pageBytes

/-- The linked CPU page-table frames the remapping tables must avoid.  The
range `[cpuRootA, cpuTableEnd)` is the same 22-frame block the boot page-table
plan reserves as `.pageTables`. -/
def cpuTableFrames (layout : Layout) : List Nat :=
  (List.range ((layout.cpuTableEnd - layout.cpuRootA) / pageBytes)).map
    (frameOf layout.cpuRootA + ·)

/-- The remapping-table reservation overlaid on a single usable window,
mirroring the boot page-plan generator's construction so the same authority
excludes both table families from allocation.  The seven non-`pageTables`
identities occupy the fixed low frames below the linked remapping block; the
`.pageTables` reservation covers the whole `[rootTableStart, remappingTableEnd)`
span, which contains both VT-d table frames. -/
def reservationResult (layout : Layout) : Option BootReservation.Result :=
  let imageEnd := layout.remappingTableEnd
  let handoff := BootMemoryMap.mkHandoff [{ base := 0, length := imageEnd, kind := .usable }]
  let manifest : List BootReservation.Reservation :=
    [{ identity := .lowMemory, start := 0, length := pageBytes, lifetime := .permanent },
     { identity := .loadedImage, start := pageBytes,
       length := imageEnd - pageBytes, lifetime := .permanent },
     { identity := .descriptorTables, start := pageBytes,
       length := pageBytes, lifetime := .permanent },
     { identity := .kernelStacks, start := 2 * pageBytes,
       length := pageBytes, lifetime := .permanent },
     { identity := .embeddedUsers, start := 3 * pageBytes,
       length := pageBytes, lifetime := .permanent },
     { identity := .ordinaryEntryGuard, start := 6 * pageBytes,
       length := pageBytes, lifetime := .permanent },
     { identity := .ordinaryEntryStack, start := 7 * pageBytes,
       length := pageBytes, lifetime := .permanent },
     { identity := .pageTables, start := layout.rootTableStart,
       length := imageEnd - layout.rootTableStart, lifetime := .permanent },
     { identity := .multibootInfo, start := pageBytes, length := pageBytes,
       lifetime := .bootstrap }]
  (BootReservation.initializeAllocator handoff manifest).toOption

def input (layout : Layout) : Input :=
  { state := IOMMU.emptyState
    rootTableFrame := frameOf layout.rootTableStart
    contextTableFrame := frameOf layout.contextTableStart
    cpuTableFrames := cpuTableFrames layout
    reservationResult := reservationResult layout }

/-- The linker-owned second-level table storage the assigned and
device-service plans bind: three pages directly after the context table. -/
def assignedTableLayoutValid (layout : Layout) : Bool :=
  layout.rootTableStart % pageBytes == 0 &&
    layout.contextTableStart == layout.rootTableStart + pageBytes &&
    layout.secondLevelRootStart == layout.contextTableStart + pageBytes &&
    layout.secondLevelDirectoryStart == layout.secondLevelRootStart + pageBytes &&
    layout.secondLevelTableStart == layout.secondLevelDirectoryStart + pageBytes &&
    layout.remappingTableEnd == layout.secondLevelTableStart + pageBytes

/-- Four linker-owned pages surround the two directionally mapped DMA pages.
The guards are intentionally absent from the assigned second-level leaf. -/
def assignedBufferLayoutValid (layout : Layout) : Bool :=
  layout.assignedGuardBeforeStart == layout.remappingTableEnd &&
    layout.assignedGuardBeforeStart % pageBytes == 0 &&
    layout.assignedReadBufferStart == layout.assignedGuardBeforeStart + pageBytes &&
    layout.assignedWriteBufferStart == layout.assignedReadBufferStart + pageBytes &&
    layout.assignedGuardAfterStart == layout.assignedWriteBufferStart + pageBytes

/-! The assigned image will consume one authoritative model projection rather
than accepting requester, domain, owner, IOVA, or permission words from the
device or a CPL3 caller. Keep this projection separate from `input`, which
continues to compile the production deny-all tables. -/

def assignedScenarioState : IOMMU.State :=
  LeanOS.VTdBootPlan.assignedEDUState

def assignedScenarioAuthorityValid : Bool :=
  match assignedScenarioState.core.assignments,
      assignedScenarioState.core.mappings with
  | [assignment], [readMapping, writeMapping] =>
      assignment.device == 0 && assignment.source == 0 &&
        assignment.handle == IOMMU.assignment0 &&
        assignment.domain == IOMMU.domain0 && assignment.owner == 0 &&
        readMapping.assignment == assignment.handle &&
        readMapping.domain == assignment.domain &&
        readMapping.owner == assignment.owner && readMapping.iova == 0 &&
        readMapping.length == IOMMU.pageSize && readMapping.frameOffset == 0 &&
        readMapping.permission == IOMMU.readOnly &&
        writeMapping.assignment == assignment.handle &&
        writeMapping.domain == assignment.domain &&
        writeMapping.owner == assignment.owner &&
        writeMapping.iova == IOMMU.pageSize &&
        writeMapping.length == IOMMU.pageSize &&
        writeMapping.frame == readMapping.frame &&
        writeMapping.frameOffset == IOMMU.pageSize &&
        writeMapping.permission == IOMMU.writeOnly
  | _, _ => false

example : assignedScenarioAuthorityValid = true := by native_decide

/-! The finite IOMMU model uses 16-byte pages so proofs stay executable. The
assigned image scales each model page to one hardware 4 KiB page. Model device
zero remains the authoritative assignment; this reviewed platform projection
binds it to q35 EDU at BDF 00:02.0 (requester/context index 16). -/

def assignedEduRequester : Nat := 2 * 8

def hardwareIova (modelIova : Nat) : Nat :=
  (modelIova / IOMMU.pageSize) * pageBytes

/-- The reviewed binding of the assigned scenario onto the linked layout: the
assigned function's requester, the linked second-level table frames, and the
hardware frame that holds model page 0 of the scenario's model frame. -/
def assignedBinding (layout : Layout) (modelFrame hardwareFrame : Nat) : GrantBinding :=
  { requester := assignedEduRequester
    secondLevelRootFrame := frameOf layout.secondLevelRootStart
    secondLevelDirectoryFrame := frameOf layout.secondLevelDirectoryStart
    secondLevelTableFrame := frameOf layout.secondLevelTableStart
    frameBases := [(modelFrame, hardwareFrame)] }

/-- The assigned-EDU plan input: both model pages of frame 0 land on the
linked read and write buffers, which `assignedBufferLayoutValid` places on
consecutive pages. -/
def assignedInput (layout : Layout) : Input :=
  { input layout with
    state := assignedScenarioState
    grantBinding := some (assignedBinding layout
      assignedScenarioState.core.mappings.head!.frame.frame
      (frameOf layout.assignedReadBufferStart)) }

def assignedHardwareProjectionValid (layout : Layout) (plan : Plan) : Bool :=
  assignedBufferLayoutValid layout && assignedEduRequester == 16 &&
    hardwareIova assignedScenarioState.core.mappings.head!.iova == 0 &&
    hardwareIova assignedScenarioState.core.mappings.tail.head!.iova == pageBytes &&
    (contextTableWords plan).length == 512 &&
    plan.secondLevelRootWords.length == 512 &&
    plan.secondLevelDirectoryWords.length == 512 &&
    plan.secondLevelTableWords.length == 512 &&
    validateAssignedEDUProjection assignedProjectionVersion assignedEDUTopologyVersion
      (UInt64.ofNat assignedScenarioState.core.assignments.head!.device)
      (UInt64.ofNat assignedScenarioState.core.assignments.head!.source)
      (UInt64.ofNat assignedScenarioState.core.assignments.head!.handle.generation)
      (UInt64.ofNat assignedScenarioState.core.assignments.head!.domain.slot)
      (UInt64.ofNat assignedScenarioState.core.assignments.head!.domain.generation)
      (UInt64.ofNat assignedScenarioState.core.assignments.head!.owner)
      (UInt64.ofNat assignedEduRequester)
      (UInt64.ofNat (frameOf layout.secondLevelRootStart))
      (UInt64.ofNat (frameOf layout.secondLevelDirectoryStart))
      (UInt64.ofNat (frameOf layout.secondLevelTableStart))
      (UInt64.ofNat (frameOf layout.assignedReadBufferStart))
      (UInt64.ofNat (frameOf layout.assignedWriteBufferStart))
      (UInt64.ofNat assignedScenarioState.core.mappings.head!.iova)
      (UInt64.ofNat assignedScenarioState.core.mappings.head!.length)
      (UInt64.ofNat assignedScenarioState.core.mappings.head!.frame.frame)
      (UInt64.ofNat assignedScenarioState.core.mappings.head!.frame.generation)
      (UInt64.ofNat assignedScenarioState.core.mappings.head!.frameOffset)
      (UInt64.ofNat (permissionBits assignedScenarioState.core.mappings.head!.permission))
      (UInt64.ofNat assignedScenarioState.core.mappings.tail.head!.iova)
      (UInt64.ofNat assignedScenarioState.core.mappings.tail.head!.length)
      (UInt64.ofNat assignedScenarioState.core.mappings.tail.head!.frame.frame)
      (UInt64.ofNat assignedScenarioState.core.mappings.tail.head!.frame.generation)
      (UInt64.ofNat assignedScenarioState.core.mappings.tail.head!.frameOffset)
      (UInt64.ofNat
        (permissionBits assignedScenarioState.core.mappings.tail.head!.permission)) == 0

def emitArray (name : String) (entries : List Nat) : String :=
  let body := String.intercalate ",\n" (entries.map fun entry => s!"  {entry}ULL")
  "static const unsigned long long " ++ name ++ "[" ++ toString entries.length ++ "] = {\n" ++
    body ++ "\n};"

def emitConstant (name : String) (value : Nat) : String :=
  "#define " ++ name ++ " " ++ toString value ++ "ULL"

/-! The device-service projection: the single read/write mapping of the
image's reviewed service state scaled to hardware pages, starting at the
executor scratch, bound to the assigned controller's requester. Only these
leaves are present; the rest of scratch, and every other page, stays unmapped
for the controller. -/

/-- One reviewed device-service assignment: its model state, its transfer
admission, the platform requester it binds, the number of pages it grants,
and the construction it belongs to. -/
structure Service where
  state : IOMMU.State
  transfer : Nat → Nat → Nat → Nat → Nat → Nat
  requester : Nat
  pages : Nat
  topology : UInt64

/-- The q35 xHCI at 00:02.0 (requester 16), issue #449. -/
def xhciService : Service :=
  { state := deviceServiceState, transfer := validateDeviceServiceTransfer,
    requester := 2 * 8, pages := 4, topology := deviceServiceTopologyVersion }

/-- The q35 ICH9 AHCI at 00:1f.2 (requester 250), issue #496. -/
def ahciService : Service :=
  { state := ahciServiceState, transfer := validateAhciServiceTransfer,
    requester := 31 * 8 + 2, pages := 1, topology := ahciServiceTopologyVersion }

def serviceOf : Nat → Option Service
  | 1 => some xhciService
  | 2 => some ahciService
  | _ => none

def Service.mapping (service : Service) : IOMMU.Mapping := service.state.core.mappings.head!

def Service.authorityValid (service : Service) : Bool :=
  let mapping := service.mapping
  service.state.core.mappings.length == 1 &&
    service.state.core.assignments.length == 1 &&
    mapping.iova == 4 * IOMMU.pageSize && mapping.frameOffset == 0 &&
    mapping.permission == IOMMU.readWrite &&
    mapping.length == service.pages * IOMMU.pageSize &&
    service.requester < contextEntryCount &&
    service.transfer 0 1 mapping.iova mapping.length 1 == 0 &&
    service.transfer 0 1 mapping.iova mapping.length 2 == 0 &&
    service.transfer 0 1 0 1 1 == 4 &&
    service.transfer 0 1 (mapping.iova + mapping.length) 1 1 == 4

example : xhciService.authorityValid = true := by native_decide
example : ahciService.authorityValid = true := by native_decide

/-- The device-service plan input: the window's model frame lands at the
start of the executor scratch, for the service's requester. -/
def serviceInput (layout : Layout) (service : Service) (dmaStart : Nat) : Input :=
  { input layout with
    state := service.state
    grantBinding := some { assignedBinding layout service.mapping.frame.frame
      (frameOf dmaStart) with requester := service.requester } }

def compileOrThrow (label : String) (planInput : Input) : Except String Plan :=
  match compile planInput with
  | .error error => throw s!"{label} VT-d plan rejected: {repr error}"
  | .ok plan => pure plan

/-- The window is page-aligned kernel memory clear of both table families. -/
def serviceLayoutValid (layout : Layout) (pages dmaStart : Nat) : Bool :=
  dmaStart != 0 && dmaStart % pageBytes == 0 &&
    (dmaStart + pages * pageBytes ≤ layout.rootTableStart ||
      layout.assignedGuardAfterStart + pageBytes ≤ dmaStart) &&
    (dmaStart + pages * pageBytes ≤ layout.cpuRootA ||
      layout.cpuTableEnd ≤ dmaStart)

def emitService (layout : Layout) (assigned : Plan) : Except String (List String) :=
  match layout.serviceDmaStart with
  | none => pure []
  | some dmaStart => do
    let some service := serviceOf layout.serviceDevice
      | throw s!"unknown device-service assignment {layout.serviceDevice}"
    if !service.authorityValid then
      throw "device-service model authority is not the reviewed read/write window"
    if !serviceLayoutValid layout service.pages dmaStart then
      throw "device-service DMA window is not page-aligned kernel memory clear of the tables"
    let plan ← compileOrThrow "device-service" (serviceInput layout service dmaStart)
    -- The kernel installs the assigned image's top and directory tables for
    -- every assigned image; the service plan must agree with them.
    if plan.secondLevelRootWords != assigned.secondLevelRootWords ||
        plan.secondLevelDirectoryWords != assigned.secondLevelDirectoryWords ||
        rootTableWords plan != rootTableWords assigned then
      throw "device-service plan disagrees with the assigned upper tables"
    pure
      [emitConstant "LEANOS_VTD_SERVICE_TOPOLOGY" service.topology.toNat,
       emitConstant "LEANOS_VTD_SERVICE_REQUESTER" service.requester,
       emitConstant "LEANOS_VTD_SERVICE_DMA_FRAME" (frameOf dmaStart),
       emitConstant "LEANOS_VTD_SERVICE_DMA_PAGES" service.pages,
       emitConstant "LEANOS_VTD_SERVICE_IOVA" (hardwareIova service.mapping.iova),
       emitArray "leanos_vtd_service_context_table" (contextTableWords plan),
       emitArray "leanos_vtd_service_second_level_table" plan.secondLevelTableWords]

def emit (layout : Layout) : Except String String := do
  if !assignedTableLayoutValid layout then
    throw "linked VT-d assigned-table reservation is not contiguous and page-aligned"
  if !assignedScenarioAuthorityValid then
    throw "assigned EDU model authority is not the reviewed read/write projection"
  let assigned ← compileOrThrow "assigned EDU" (assignedInput layout)
  if !assignedHardwareProjectionValid layout assigned then
    throw "assigned EDU hardware tables do not match the reviewed model projection"
  let service ← emitService layout assigned
  let plan ← compileOrThrow "canonical linked" (input layout)
  if rootTableWords assigned != rootTableWords plan then
    throw "assigned and deny-all VT-d plans disagree on the root table"
  pure <| String.intercalate "\n"
      (["/* Generated by the accepted LeanOS.VTdBootPlan; do not edit. */",
       emitConstant "LEANOS_VTD_MMIO_BASE" mmioBase,
       emitConstant "LEANOS_VTD_PLAN_VERSION" planVersion.toNat,
       emitConstant "LEANOS_VTD_EXPECTED_VERSION" expectedVersionRegister.toNat,
       emitConstant "LEANOS_VTD_EXPECTED_CAP" expectedCapabilityRegister.toNat,
       emitConstant "LEANOS_VTD_EXPECTED_ECAP" expectedExtendedCapabilityRegister.toNat,
       emitConstant "LEANOS_VTD_ENABLED_GSTS" enabledGlobalStatus.toNat,
       emitConstant "LEANOS_VTD_TOPOLOGY" DMAQuarantine.q35TopologyVersion.toNat,
       emitConstant "LEANOS_VTD_ASSIGNED_TOPOLOGY" assignedEDUTopologyVersion.toNat,
       emitConstant "LEANOS_VTD_ROOT_TABLE_FRAME" plan.rootFrame,
       emitConstant "LEANOS_VTD_CONTEXT_TABLE_FRAME" plan.contextFrame,
       emitConstant "LEANOS_VTD_SECOND_LEVEL_ROOT_FRAME"
         (frameOf layout.secondLevelRootStart),
       emitConstant "LEANOS_VTD_SECOND_LEVEL_DIRECTORY_FRAME"
         (frameOf layout.secondLevelDirectoryStart),
       emitConstant "LEANOS_VTD_SECOND_LEVEL_TABLE_FRAME"
         (frameOf layout.secondLevelTableStart),
       emitConstant "LEANOS_VTD_ASSIGNED_DEVICE"
         assignedScenarioState.core.assignments.head!.device,
       emitConstant "LEANOS_VTD_ASSIGNED_SOURCE"
         assignedScenarioState.core.assignments.head!.source,
       emitConstant "LEANOS_VTD_ASSIGNED_HANDLE"
         assignedScenarioState.core.assignments.head!.handle.slot,
       emitConstant "LEANOS_VTD_ASSIGNED_GENERATION"
         assignedScenarioState.core.assignments.head!.handle.generation,
       emitConstant "LEANOS_VTD_ASSIGNED_DOMAIN"
         assignedScenarioState.core.assignments.head!.domain.slot,
       emitConstant "LEANOS_VTD_ASSIGNED_DOMAIN_GENERATION"
         assignedScenarioState.core.assignments.head!.domain.generation,
       emitConstant "LEANOS_VTD_ASSIGNED_OWNER"
         assignedScenarioState.core.assignments.head!.owner,
       emitConstant "LEANOS_VTD_ASSIGNED_REQUESTER" assignedEduRequester,
       emitConstant "LEANOS_VTD_ASSIGNED_READ_BUFFER_FRAME"
         (frameOf layout.assignedReadBufferStart),
       emitConstant "LEANOS_VTD_ASSIGNED_WRITE_BUFFER_FRAME"
         (frameOf layout.assignedWriteBufferStart),
       emitConstant "LEANOS_VTD_MODEL_READ_IOVA"
         assignedScenarioState.core.mappings.head!.iova,
       emitConstant "LEANOS_VTD_MODEL_READ_MAPPING"
         assignedScenarioState.core.mappings.head!.handle.slot,
       emitConstant "LEANOS_VTD_MODEL_READ_MAPPING_GENERATION"
         assignedScenarioState.core.mappings.head!.handle.generation,
       emitConstant "LEANOS_VTD_HARDWARE_READ_IOVA"
         (hardwareIova assignedScenarioState.core.mappings.head!.iova),
       emitConstant "LEANOS_VTD_MODEL_READ_LENGTH"
         assignedScenarioState.core.mappings.head!.length,
       emitConstant "LEANOS_VTD_MODEL_READ_FRAME"
         assignedScenarioState.core.mappings.head!.frame.frame,
       emitConstant "LEANOS_VTD_MODEL_READ_FRAME_GENERATION"
         assignedScenarioState.core.mappings.head!.frame.generation,
       emitConstant "LEANOS_VTD_MODEL_READ_FRAME_OFFSET"
         assignedScenarioState.core.mappings.head!.frameOffset,
       emitConstant "LEANOS_VTD_MODEL_READ_PERMISSION"
         (permissionBits assignedScenarioState.core.mappings.head!.permission),
       emitConstant "LEANOS_VTD_MODEL_WRITE_IOVA"
         assignedScenarioState.core.mappings.tail.head!.iova,
       emitConstant "LEANOS_VTD_MODEL_WRITE_LENGTH"
         assignedScenarioState.core.mappings.tail.head!.length,
       emitConstant "LEANOS_VTD_MODEL_WRITE_FRAME"
         assignedScenarioState.core.mappings.tail.head!.frame.frame,
       emitConstant "LEANOS_VTD_MODEL_WRITE_FRAME_GENERATION"
         assignedScenarioState.core.mappings.tail.head!.frame.generation,
       emitConstant "LEANOS_VTD_MODEL_WRITE_FRAME_OFFSET"
         assignedScenarioState.core.mappings.tail.head!.frameOffset,
       emitConstant "LEANOS_VTD_MODEL_WRITE_PERMISSION"
         (permissionBits assignedScenarioState.core.mappings.tail.head!.permission),
       emitConstant "LEANOS_VTD_ROOT_TABLE_ADDRESS" (plan.rootFrame * pageBytes),
       emitConstant "LEANOS_VTD_CANONICAL_JOURNAL" canonicalJournalWord,
       emitArray "leanos_vtd_root_table" (rootTableWords plan),
       emitArray "leanos_vtd_context_table" (contextTableWords plan),
       emitArray "leanos_vtd_assigned_context_table" (contextTableWords assigned),
       emitArray "leanos_vtd_assigned_second_level_root" assigned.secondLevelRootWords,
       emitArray "leanos_vtd_assigned_second_level_directory"
         assigned.secondLevelDirectoryWords,
       emitArray "leanos_vtd_assigned_second_level_table"
         assigned.secondLevelTableWords] ++ service) ++ "\n"

end LeanOS.VTdBootPlanGenerator

def main (args : List String) : IO UInt32 := do
  match LeanOS.VTdBootPlanGenerator.parseLayout args >>=
      LeanOS.VTdBootPlanGenerator.emit with
  | .ok output =>
      IO.print output
      pure 0
  | .error message =>
      IO.eprintln s!"error: {message}"
      pure 1
