import LeanOS.BootPageTablePlan
import LeanOS.VTdBootPlan

/-!
# Linked boot page-table plan generator

This host-only executable receives final-ELF symbol addresses, constructs the
same finite `BootPageTablePlan.Input` represented by those symbols, requires
`BootPageTablePlan.compile` to accept it, and emits the canonical expected PTE
arrays consumed by the guest walker. The linker, symbol extraction, generated
header, C/assembly constructor, and machine page walk remain trusted build and
integration boundaries rather than proved refinement steps.
-/
namespace LeanOS.BootPageTablePlanGenerator

open LeanOS
open LeanOS.X86PageTable
open LeanOS.BootReservation
open LeanOS.BootPageTablePlan

/-- The third subject's linked page-table roots, present only when the ELF
links them (issue #472). -/
structure ThirdTables where
  root : Nat
  pdpt : Nat
  pd : Nat
  pt : Nat

structure Layout where
  bootStart : Nat
  bootEnd : Nat
  kernelTextStart : Nat
  kernelTextEnd : Nat
  guardStart : Nat
  guardEnd : Nat
  dfStackStart : Nat
  dfStackEnd : Nat
  nmiGuardStart : Nat
  nmiGuardEnd : Nat
  nmiStackStart : Nat
  nmiStackEnd : Nat
  entryGuardStart : Nat
  entryGuardEnd : Nat
  entryStackStart : Nat
  entryStackEnd : Nat
  rootA : Nat
  pdptA : Nat
  pdA : Nat
  ptA : Nat
  rootB : Nat
  pdptB : Nat
  pdB : Nat
  ptB : Nat
  tableEnd : Nat
  stackStart : Nat
  stackEnd : Nat
  userATextStart : Nat
  userATextEnd : Nat
  userAStackStart : Nat
  userAStackEnd : Nat
  userBTextStart : Nat
  userBTextEnd : Nat
  userBStackStart : Nat
  userBStackEnd : Nat
  vtdWindowStart : Nat
  vtdWindowEnd : Nat
  eduWindowStart : Nat
  eduWindowEnd : Nat
  /-- 0: no assigned device; 1: q35 EDU (4 KiB BAR); 2: the device-service
  image's q35 xHCI (16 KiB BAR). The window pages map the device's BAR. -/
  assignedDevice : Nat
  vtdTableStart : Nat
  vtdTableEnd : Nat
  /-- The third subject's text and stack.  Every image links these symbols;
  a two-subject image's ranges are empty. -/
  userCTextStart : Nat
  userCTextEnd : Nat
  userCStackStart : Nat
  userCStackEnd : Nat
  /-- `some` exactly when the image links the third subject's tables. Then
  `tableEnd` is the end of C's tables, after A's and B's. -/
  third : Option ThirdTables

/-- A two-subject image passes the 42 original addresses plus C's four empty
section bounds; a three-subject image also passes C's four table roots. -/
def expectedArgumentCount : Nat := 46
def threeSubjectArgumentCount : Nat := 50

def parseNat (value : String) : Except String Nat :=
  match value.toNat? with
  | some parsed => .ok parsed
  | none => .error s!"invalid decimal address: {value}"

def parseLayout (args : List String) : Except String Layout := do
  if args.length != expectedArgumentCount && args.length != threeSubjectArgumentCount then
    throw s!"expected {expectedArgumentCount} or {threeSubjectArgumentCount} decimal addresses, got {args.length}"
  let values ← args.mapM parseNat
  let valueAt (index : Nat) := values[index]?.getD 0
  pure {
    bootStart := valueAt 0, bootEnd := valueAt 1,
    kernelTextStart := valueAt 2, kernelTextEnd := valueAt 3,
    guardStart := valueAt 4, guardEnd := valueAt 5,
    dfStackStart := valueAt 6, dfStackEnd := valueAt 7,
    nmiGuardStart := valueAt 8, nmiGuardEnd := valueAt 9,
    nmiStackStart := valueAt 10, nmiStackEnd := valueAt 11,
    entryGuardStart := valueAt 12, entryGuardEnd := valueAt 13,
    entryStackStart := valueAt 14, entryStackEnd := valueAt 15,
    rootA := valueAt 16, pdptA := valueAt 17, pdA := valueAt 18, ptA := valueAt 19,
    rootB := valueAt 20, pdptB := valueAt 21, pdB := valueAt 22, ptB := valueAt 23,
    tableEnd := valueAt 24, stackStart := valueAt 25, stackEnd := valueAt 26,
    userATextStart := valueAt 27, userATextEnd := valueAt 28,
    userAStackStart := valueAt 29, userAStackEnd := valueAt 30,
    userBTextStart := valueAt 31, userBTextEnd := valueAt 32,
    userBStackStart := valueAt 33, userBStackEnd := valueAt 34,
    vtdWindowStart := valueAt 35, vtdWindowEnd := valueAt 36,
    eduWindowStart := valueAt 37, eduWindowEnd := valueAt 38,
    assignedDevice := valueAt 39,
    vtdTableStart := valueAt 40, vtdTableEnd := valueAt 41,
    userCTextStart := valueAt 42, userCTextEnd := valueAt 43,
    userCStackStart := valueAt 44, userCStackEnd := valueAt 45,
    third := if args.length == threeSubjectArgumentCount then
        some { root := valueAt 46, pdpt := valueAt 47, pd := valueAt 48, pt := valueAt 49 }
      else none }

def firstPage (address : Nat) : Nat := address / pageBytes
def endPage (address : Nat) : Nat := (address + pageBytes - 1) / pageBytes
def pageIn (page start stop : Nat) : Bool := firstPage start ≤ page && page < endPage stop

/-- The pinned BAR each assigned device is placed at: EDU where SeaBIOS puts
it, and the xHCI at the address the device-service kernel programs into its
BAR0 before enabling memory decoding. -/
def assignedBarBase (device : Nat) : Nat :=
  if device == 2 then 0xFEBF0000 else 0xFEA00000

structure PageClass where
  policy : PolicyRegion
  owner : Owner

def pageClass (layout : Layout) (space : Space) (page : Nat) : Option PageClass :=
  if pageIn page layout.guardStart layout.guardEnd ||
      pageIn page layout.nmiGuardStart layout.nmiGuardEnd ||
      pageIn page layout.entryGuardStart layout.entryGuardEnd then none
  else if space == .subjectA && pageIn page layout.userATextStart layout.userATextEnd then
    some ⟨.userText, .subjectA⟩
  else if space == .subjectA && pageIn page layout.userAStackStart layout.userAStackEnd then
    some ⟨.userStack, .subjectA⟩
  else if space == .subjectB && pageIn page layout.userBTextStart layout.userBTextEnd then
    some ⟨.userText, .subjectB⟩
  else if space == .subjectB && pageIn page layout.userBStackStart layout.userBStackEnd then
    some ⟨.userStack, .subjectB⟩
  else if space == .subjectC && pageIn page layout.userCTextStart layout.userCTextEnd then
    some ⟨.userText, .subjectC⟩
  else if space == .subjectC && pageIn page layout.userCStackStart layout.userCStackEnd then
    some ⟨.userStack, .subjectC⟩
  else if pageIn page layout.userATextStart layout.userAStackEnd ||
      pageIn page layout.userBTextStart layout.userBStackEnd ||
      pageIn page layout.userCTextStart layout.userCStackEnd then none
  else if pageIn page layout.kernelTextStart layout.kernelTextEnd then
    some ⟨.kernelText, .supervisor⟩
  else if pageIn page layout.vtdWindowStart layout.vtdWindowEnd then
    some ⟨.mmioWindow, .supervisor⟩
  else if layout.assignedDevice != 0 && pageIn page layout.eduWindowStart layout.eduWindowEnd then
    some ⟨.mmioWindow, .supervisor⟩
  else if pageIn page layout.vtdTableStart layout.vtdTableEnd then
    some ⟨.remappingTables, .supervisor⟩
  else if pageIn page layout.rootA layout.tableEnd then
    some ⟨.pageTables, .supervisor⟩
  else if pageIn page layout.dfStackStart layout.dfStackEnd ||
      pageIn page layout.nmiStackStart layout.nmiStackEnd ||
      pageIn page layout.entryStackStart layout.entryStackEnd ||
      pageIn page layout.stackStart layout.stackEnd then
    some ⟨.kernelStack, .supervisor⟩
  else some ⟨.kernelData, .supervisor⟩

/-- Every reviewed class is identity-mapped except the `.mmioWindow` page,
whose frame comes from the pinned VT-d unit base rather than the linker. -/
def physicalStartAt (layout : Layout) (classification : PageClass)
    (page : Nat) : Nat :=
  if classification.policy == .mmioWindow then
    if pageIn page layout.vtdWindowStart layout.vtdWindowEnd then
      VTdBootPlan.mmioBase + (page * pageBytes - layout.vtdWindowStart)
    else assignedBarBase layout.assignedDevice + (page * pageBytes - layout.eduWindowStart)
  else page * pageBytes

def regionAt (layout : Layout) (space : Space) (page : Nat) : Option Region :=
  (pageClass layout space page).map fun classification =>
    { space, virtualStart := page * pageBytes, byteLength := pageBytes,
      physicalStart := physicalStartAt layout classification page,
      policy := classification.policy, owner := classification.owner }

def regionsFor (layout : Layout) (space : Space) : List Region :=
  (List.range supportedPathPages).filterMap (regionAt layout space)

def reservationResult (layout : Layout) : Option BootReservation.Result :=
  let handoff := BootMemoryMap.mkHandoff
    [{ base := 0, length := supportedPathPages * pageBytes, kind := .usable }]
  let manifest : List Reservation :=
    [{ identity := .lowMemory, start := 0, length := pageBytes, lifetime := .permanent },
     { identity := .loadedImage, start := layout.bootStart,
       length := layout.bootEnd - layout.bootStart, lifetime := .permanent },
     { identity := .pageTables, start := layout.rootA,
       length := layout.tableEnd - layout.rootA, lifetime := .permanent },
     { identity := .descriptorTables, start := layout.bootStart,
       length := pageBytes, lifetime := .permanent },
     { identity := .kernelStacks, start := layout.dfStackStart,
       length := layout.nmiStackEnd - layout.dfStackStart, lifetime := .permanent },
     { identity := .ordinaryEntryGuard, start := layout.entryGuardStart,
       length := layout.entryGuardEnd - layout.entryGuardStart, lifetime := .permanent },
     { identity := .ordinaryEntryStack, start := layout.entryStackStart,
       length := layout.entryStackEnd - layout.entryStackStart, lifetime := .permanent },
     { identity := .embeddedUsers, start := layout.userATextStart,
       length := layout.bootEnd - layout.userATextStart, lifetime := .permanent },
     { identity := .multibootInfo, start := layout.bootStart,
       length := pageBytes, lifetime := .bootstrap }]
  (initializeAllocator handoff manifest).toOption

def ancestorsAt (pdpt pd pt : Nat) : AncestorFrames :=
  AncestorFrames.mk (firstPage pdpt) (firstPage pd)
    (List.range bootPtCount |>.map (firstPage pt + ·))

def input (layout : Layout) : Input :=
  { roots := { subjectA := firstPage layout.rootA, subjectB := firstPage layout.rootB,
               subjectC := layout.third.map (firstPage ·.root) },
    ancestors :=
      { subjectA := ancestorsAt layout.pdptA layout.pdA layout.ptA,
        subjectB := ancestorsAt layout.pdptB layout.pdB layout.ptB,
        subjectC := layout.third.map fun third => ancestorsAt third.pdpt third.pd third.pt },
    nxe := true,
    regions := regionsFor layout .subjectA ++ regionsFor layout .subjectB ++
      (if layout.third.isSome then regionsFor layout .subjectC else []),
    reservationResult := reservationResult layout }

def bit (enabled : Bool) (value : Nat) : Nat := if enabled then value else 0

def encodeLeaf (leaf : Leaf) : Nat :=
  leaf.frame * pageBytes + bit leaf.present 1 + bit leaf.writable 2 +
    bit leaf.user 4 + bit leaf.noExecute (2 ^ 63)

def expectedEntry (layout : Layout) (space : Space) (page : Nat) : Nat :=
  match pageClass layout space page with
  | none => 0
  | some classification =>
    encodeLeaf (policyLeaf classification.policy
      (physicalStartAt layout classification page / pageBytes))

def emitArray (name : String) (entries : List Nat) : String :=
  let body := String.intercalate ",\n" (entries.map fun entry => s!"  {entry}ULL")
  "static const unsigned long long " ++ name ++ "[4096] = {\n" ++ body ++ "\n};"

def emit (layout : Layout) : Except String String := do
  -- A two-subject image links C's section bounds but no C text or stack.
  if layout.third.isNone && (layout.userCTextStart != layout.userCStackEnd ||
      layout.userCTextStart != layout.userCTextEnd ||
      layout.userCStackStart != layout.userCStackEnd) then
    throw "third-subject sections are linked without third-subject page tables"
  match compile (input layout) with
  | .error error => throw s!"canonical linked plan rejected: {repr error}"
  | .ok _ =>
    let pages := List.range supportedPathPages
    let third :=
      if layout.third.isSome then
        emitArray "leanos_boot_plan_c" (pages.map (expectedEntry layout .subjectC)) ++ "\n"
      else ""
    pure <| "/* Generated by the accepted LeanOS.BootPageTablePlan; do not edit. */\n" ++
      emitArray "leanos_boot_plan_a" (pages.map (expectedEntry layout .subjectA)) ++ "\n" ++
      emitArray "leanos_boot_plan_b" (pages.map (expectedEntry layout .subjectB)) ++ "\n" ++
      third

end LeanOS.BootPageTablePlanGenerator

def main (args : List String) : IO UInt32 := do
  match LeanOS.BootPageTablePlanGenerator.parseLayout args >>=
      LeanOS.BootPageTablePlanGenerator.emit with
  | .ok output =>
      IO.print output
      pure 0
  | .error message =>
      IO.eprintln s!"error: {message}"
      pure 1
