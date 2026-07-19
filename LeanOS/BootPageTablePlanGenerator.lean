import LeanOS.BootPageTablePlan

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

structure Layout where
  bootStart : Nat
  bootEnd : Nat
  kernelTextStart : Nat
  kernelTextEnd : Nat
  guardStart : Nat
  guardEnd : Nat
  dfStackStart : Nat
  dfStackEnd : Nat
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

def expectedArgumentCount : Nat := 31

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
    bootStart := valueAt 0, bootEnd := valueAt 1,
    kernelTextStart := valueAt 2, kernelTextEnd := valueAt 3,
    guardStart := valueAt 4, guardEnd := valueAt 5,
    dfStackStart := valueAt 6, dfStackEnd := valueAt 7,
    entryGuardStart := valueAt 8, entryGuardEnd := valueAt 9,
    entryStackStart := valueAt 10, entryStackEnd := valueAt 11,
    rootA := valueAt 12, pdptA := valueAt 13, pdA := valueAt 14, ptA := valueAt 15,
    rootB := valueAt 16, pdptB := valueAt 17, pdB := valueAt 18, ptB := valueAt 19,
    tableEnd := valueAt 20, stackStart := valueAt 21, stackEnd := valueAt 22,
    userATextStart := valueAt 23, userATextEnd := valueAt 24,
    userAStackStart := valueAt 25, userAStackEnd := valueAt 26,
    userBTextStart := valueAt 27, userBTextEnd := valueAt 28,
    userBStackStart := valueAt 29, userBStackEnd := valueAt 30 }

def firstPage (address : Nat) : Nat := address / pageBytes
def endPage (address : Nat) : Nat := (address + pageBytes - 1) / pageBytes
def pageIn (page start stop : Nat) : Bool := firstPage start ≤ page && page < endPage stop

structure PageClass where
  policy : PolicyRegion
  owner : Owner

def pageClass (layout : Layout) (space : Space) (page : Nat) : Option PageClass :=
  if pageIn page layout.guardStart layout.guardEnd ||
      pageIn page layout.entryGuardStart layout.entryGuardEnd then none
  else if space == .subjectA && pageIn page layout.userATextStart layout.userATextEnd then
    some ⟨.userText, .subjectA⟩
  else if space == .subjectA && pageIn page layout.userAStackStart layout.userAStackEnd then
    some ⟨.userStack, .subjectA⟩
  else if space == .subjectB && pageIn page layout.userBTextStart layout.userBTextEnd then
    some ⟨.userText, .subjectB⟩
  else if space == .subjectB && pageIn page layout.userBStackStart layout.userBStackEnd then
    some ⟨.userStack, .subjectB⟩
  else if pageIn page layout.userATextStart layout.userAStackEnd ||
      pageIn page layout.userBTextStart layout.userBStackEnd then none
  else if pageIn page layout.kernelTextStart layout.kernelTextEnd then
    some ⟨.kernelText, .supervisor⟩
  else if pageIn page layout.rootA layout.tableEnd then
    some ⟨.pageTables, .supervisor⟩
  else if pageIn page layout.dfStackStart layout.dfStackEnd ||
      pageIn page layout.entryStackStart layout.entryStackEnd ||
      pageIn page layout.stackStart layout.stackEnd then
    some ⟨.kernelStack, .supervisor⟩
  else some ⟨.kernelData, .supervisor⟩

def regionAt (layout : Layout) (space : Space) (page : Nat) : Option Region :=
  (pageClass layout space page).map fun classification =>
    { space, virtualStart := page * pageBytes, byteLength := pageBytes,
      physicalStart := page * pageBytes, policy := classification.policy,
      owner := classification.owner }

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
       length := layout.dfStackEnd - layout.dfStackStart, lifetime := .permanent },
     { identity := .ordinaryEntryGuard, start := layout.entryGuardStart,
       length := layout.entryGuardEnd - layout.entryGuardStart, lifetime := .permanent },
     { identity := .ordinaryEntryStack, start := layout.entryStackStart,
       length := layout.entryStackEnd - layout.entryStackStart, lifetime := .permanent },
     { identity := .embeddedUsers, start := layout.userATextStart,
       length := layout.bootEnd - layout.userATextStart, lifetime := .permanent },
     { identity := .multibootInfo, start := layout.bootStart,
       length := pageBytes, lifetime := .bootstrap }]
  (initializeAllocator handoff manifest).toOption

def input (layout : Layout) : Input :=
  { roots := Roots.mk (firstPage layout.rootA) (firstPage layout.rootB),
    ancestors := AncestorPaths.mk
      (AncestorFrames.mk (firstPage layout.pdptA) (firstPage layout.pdA)
        (List.range bootPtCount |>.map (firstPage layout.ptA + ·)))
      (AncestorFrames.mk (firstPage layout.pdptB) (firstPage layout.pdB)
        (List.range bootPtCount |>.map (firstPage layout.ptB + ·))),
    nxe := true,
    regions := regionsFor layout .subjectA ++ regionsFor layout .subjectB,
    reservationResult := reservationResult layout }

def bit (enabled : Bool) (value : Nat) : Nat := if enabled then value else 0

def encodeLeaf (leaf : Leaf) : Nat :=
  leaf.frame * pageBytes + bit leaf.present 1 + bit leaf.writable 2 +
    bit leaf.user 4 + bit leaf.noExecute (2 ^ 63)

def expectedEntry (layout : Layout) (space : Space) (page : Nat) : Nat :=
  match pageClass layout space page with
  | none => 0
  | some classification => encodeLeaf (policyLeaf classification.policy page)

def emitArray (name : String) (entries : List Nat) : String :=
  let body := String.intercalate ",\n" (entries.map fun entry => s!"  {entry}ULL")
  "static const unsigned long long " ++ name ++ "[4096] = {\n" ++ body ++ "\n};"

def emit (layout : Layout) : Except String String := do
  match compile (input layout) with
  | .error error => throw s!"canonical linked plan rejected: {repr error}"
  | .ok _ =>
    let pages := List.range supportedPathPages
    pure <| "/* Generated by the accepted LeanOS.BootPageTablePlan; do not edit. */\n" ++
      emitArray "leanos_boot_plan_a" (pages.map (expectedEntry layout .subjectA)) ++ "\n" ++
      emitArray "leanos_boot_plan_b" (pages.map (expectedEntry layout .subjectB)) ++ "\n"

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
