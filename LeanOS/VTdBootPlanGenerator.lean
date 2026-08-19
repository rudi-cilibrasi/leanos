import LeanOS.VTdBootPlan

/-!
# Linked VT-d boot-plan generator

This host-only executable receives the final-ELF remapping-table symbol
addresses plus the CPU page-table layout, constructs the same finite
`VTdBootPlan.Input` those symbols represent over the accepted deny-all
device-domain state, requires `VTdBootPlan.compile` to accept it, and emits the
canonical root/context table words and pinned register constants consumed by
the guest constructor.  The linker, symbol extraction, generated header,
C/assembly table writes, VT-d MMIO programming, and hardware page walk remain
trusted build and integration boundaries rather than proved refinement steps.
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
  deriving Repr

def expectedArgumentCount : Nat := 12

def parseNat (value : String) : Except String Nat :=
  match value.toNat? with
  | some parsed => .ok parsed
  | none => .error s!"invalid decimal address: {value}"

def parseLayout (args : List String) : Except String Layout := do
  if args.length != expectedArgumentCount then
    throw s!"expected {expectedArgumentCount} decimal addresses, got {args.length}"
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
    assignedGuardAfterStart := valueAt 11 }

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

/-- The assigned-EDU table storage is not part of the deny-all plan yet, but
its exact linker-owned frame layout is already a checked generator input. -/
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

def permissionBits (permission : IOMMU.Permission) : Nat :=
  (if permission.read then 1 else 0) + (if permission.write then 2 else 0)

/-! The finite IOMMU model uses 16-byte pages so proofs stay executable. The
assigned image scales each model page to one hardware 4 KiB page. Model device
zero remains the authoritative assignment; this reviewed platform projection
binds it to q35 EDU at BDF 00:02.0 (requester/context index 16). -/

def assignedEduRequester : Nat := 2 * 8

def hardwareIova (modelIova : Nat) : Nat :=
  (modelIova / IOMMU.pageSize) * pageBytes

def assignedContextEntries (layout : Layout) : List ContextEntry :=
  (List.range contextEntryCount).map fun requester =>
    if requester == assignedEduRequester then
      { present := true
        domain := assignedScenarioState.core.assignments.head!.domain.slot
        addressWidth := addressWidthEncoding
        secondLevelFrame := frameOf layout.secondLevelRootStart }
    else absentContextEntry

def assignedContextTableWords (layout : Layout) : List Nat :=
  (assignedContextEntries layout).flatMap fun entry =>
    [contextEntryLow entry, contextEntryHigh entry]

def singleEntryPage (index value : Nat) : List Nat :=
  (List.range 512).map fun candidate => if candidate == index then value else 0

def assignedSecondLevelRootWords (layout : Layout) : List Nat :=
  singleEntryPage 0 (layout.secondLevelDirectoryStart + 3)

def assignedSecondLevelDirectoryWords (layout : Layout) : List Nat :=
  singleEntryPage 0 (layout.secondLevelTableStart + 3)

def assignedSecondLevelTableWords (layout : Layout) : List Nat :=
  let readMapping := assignedScenarioState.core.mappings.head!
  let writeMapping := assignedScenarioState.core.mappings.tail.head!
  (List.range 512).map fun index =>
    if index == hardwareIova readMapping.iova / pageBytes then
      layout.assignedReadBufferStart + permissionBits readMapping.permission
    else if index == hardwareIova writeMapping.iova / pageBytes then
      layout.assignedWriteBufferStart + permissionBits writeMapping.permission
    else 0

def assignedHardwareProjectionValid (layout : Layout) : Bool :=
  assignedBufferLayoutValid layout && assignedEduRequester == 16 &&
    hardwareIova assignedScenarioState.core.mappings.head!.iova == 0 &&
    hardwareIova assignedScenarioState.core.mappings.tail.head!.iova == pageBytes &&
    (assignedContextTableWords layout).length == 512 &&
    (assignedSecondLevelRootWords layout).length == 512 &&
    (assignedSecondLevelDirectoryWords layout).length == 512 &&
    (assignedSecondLevelTableWords layout).length == 512 &&
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

def emit (layout : Layout) : Except String String := do
  if !assignedTableLayoutValid layout then
    throw "linked VT-d assigned-table reservation is not contiguous and page-aligned"
  if !assignedScenarioAuthorityValid then
    throw "assigned EDU model authority is not the reviewed read/write projection"
  if !assignedHardwareProjectionValid layout then
    throw "assigned EDU hardware tables do not match the reviewed model projection"
  match compile (input layout) with
  | .error error => throw s!"canonical linked VT-d plan rejected: {repr error}"
  | .ok plan =>
    pure <| String.intercalate "\n"
      ["/* Generated by the accepted LeanOS.VTdBootPlan; do not edit. */",
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
       emitArray "leanos_vtd_assigned_context_table"
         (assignedContextTableWords layout),
       emitArray "leanos_vtd_assigned_second_level_root"
         (assignedSecondLevelRootWords layout),
       emitArray "leanos_vtd_assigned_second_level_directory"
         (assignedSecondLevelDirectoryWords layout),
       emitArray "leanos_vtd_assigned_second_level_table"
         (assignedSecondLevelTableWords layout)] ++ "\n"

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
