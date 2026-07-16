import LeanOS.X86PageTable
import LeanOS.BootReservation

/-!
# Finite Phase 2 boot page-table plan

This is the authoritative, bounded input to the early-boot table constructor.
It deliberately proves facts about accepted plan values, not about the linker,
assembly writes, CR3, an x86 page walk, or QEMU.  Those boundaries must compare
decoded live entries with `compile`.
-/
namespace LeanOS.BootPageTablePlan

open LeanOS.X86PageTable
open LeanOS.BootReservation

inductive Space where | subjectA | subjectB
  deriving BEq, DecidableEq, Repr

instance : Inhabited Space := ⟨.subjectA⟩

inductive Owner where | supervisor | subjectA | subjectB
  deriving BEq, DecidableEq, Repr

instance : Inhabited Owner := ⟨.supervisor⟩
instance : Inhabited PolicyRegion := ⟨.kernelData⟩

/-- All addresses are bytes and ranges are half-open. -/
structure Region where
  space : Space
  virtualStart : Nat
  byteLength : Nat
  physicalStart : Nat
  policy : PolicyRegion
  owner : Owner
  deriving BEq, DecidableEq, Inhabited, Repr

structure Roots where
  subjectA : PhysicalFrame
  subjectB : PhysicalFrame
  deriving BEq, DecidableEq, Repr

/-- The three non-root table frames reached while walking the bounded Phase 2
lower-half map.  The root frame itself is carried by `Roots`. -/
structure AncestorFrames where
  pdpt : PhysicalFrame
  pd : PhysicalFrame
  pt : PhysicalFrame
  deriving BEq, DecidableEq, Repr

structure AncestorPaths where
  subjectA : AncestorFrames
  subjectB : AncestorFrames
  deriving BEq, DecidableEq, Repr

structure Input where
  roots : Roots
  ancestors : AncestorPaths
  nxe : Bool
  regions : List Region
  tableReservations : List Interval
  deriving Repr

structure CompiledLeaf where
  space : Space
  page : Nat
  leaf : Leaf
  policy : PolicyRegion
  owner : Owner
  deriving BEq, DecidableEq, Repr

inductive Error where
  | missingNXE | equalRoots | misaligned | emptyRegion | addressOverflow
  | nonCanonical | frameOutOfRange | wrongOwner | incompatibleOverlap
  | duplicateLeaf | unreservedTableFrame | invalidTableFrame
  deriving BEq, DecidableEq, Repr

def aligned (address : Nat) : Bool := address % pageBytes == 0

def ownerMatches (region : Region) : Bool :=
  match region.policy, region.owner, region.space with
  | .kernelText, .supervisor, _ | .kernelData, .supervisor, _
  | .kernelStack, .supervisor, _ | .pageTables, .supervisor, _ => true
  | .userText, .subjectA, .subjectA | .userStack, .subjectA, .subjectA => true
  | .userText, .subjectB, .subjectB | .userStack, .subjectB, .subjectB => true
  | _, _, _ => false

def compileRegion (region : Region) : Except Error (List CompiledLeaf) := do
  if region.byteLength == 0 then throw .emptyRegion
  if !(aligned region.virtualStart && aligned region.byteLength && aligned region.physicalStart) then
    throw .misaligned
  if region.byteLength > Nat.sub (2 ^ 64) region.virtualStart ||
      region.byteLength > Nat.sub (2 ^ 64) region.physicalStart then throw .addressOverflow
  let firstPage := region.virtualStart / pageBytes
  let firstFrame := region.physicalStart / pageBytes
  let count := region.byteLength / pageBytes
  if firstPage + count > lowerCanonicalPages then throw .nonCanonical
  if firstFrame + count > physicalFrameLimit then throw .frameOutOfRange
  if !ownerMatches region then throw .wrongOwner
  pure <| (List.range count).map fun offset =>
    { space := region.space, page := firstPage + offset,
      leaf := policyLeaf region.policy (firstFrame + offset),
      policy := region.policy, owner := region.owner }

def sameLocation (a b : CompiledLeaf) : Bool := a.space == b.space && a.page == b.page

def noDuplicateLeaves (leaves : List CompiledLeaf) : Bool :=
  leaves.Pairwise fun a b => !sameLocation a b

/-- A page-table frame must be covered by the reviewed page-table reservation,
not merely by some unrelated boot artifact that happens to overlap it. -/
def reservedAsPageTable (reservations : List Interval) (frame : PhysicalFrame) : Bool :=
  reservations.any fun interval =>
    interval.identity == .pageTables && interval.contains frame

def tableFramesReserved (input : Input) : Bool :=
  reservedAsPageTable input.tableReservations input.roots.subjectA &&
    reservedAsPageTable input.tableReservations input.roots.subjectB &&
    reservedAsPageTable input.tableReservations input.ancestors.subjectA.pdpt &&
    reservedAsPageTable input.tableReservations input.ancestors.subjectA.pd &&
    reservedAsPageTable input.tableReservations input.ancestors.subjectA.pt &&
    reservedAsPageTable input.tableReservations input.ancestors.subjectB.pdpt &&
    reservedAsPageTable input.tableReservations input.ancestors.subjectB.pd &&
    reservedAsPageTable input.tableReservations input.ancestors.subjectB.pt &&
    input.regions.all fun region => region.policy != .pageTables ||
      (List.range (region.byteLength / pageBytes)).all fun offset =>
        reservedAsPageTable input.tableReservations
          (region.physicalStart / pageBytes + offset)

def tableFramesRepresentable (input : Input) : Bool :=
  representableFrame input.roots.subjectA && representableFrame input.roots.subjectB &&
    representableFrame input.ancestors.subjectA.pdpt &&
    representableFrame input.ancestors.subjectA.pd &&
    representableFrame input.ancestors.subjectA.pt &&
    representableFrame input.ancestors.subjectB.pdpt &&
    representableFrame input.ancestors.subjectB.pd &&
    representableFrame input.ancestors.subjectB.pt

def wxSafe (leaves : List CompiledLeaf) : Bool :=
  leaves.all fun entry => !entry.leaf.writable || entry.leaf.noExecute

def ownershipSafe (leaves : List CompiledLeaf) : Bool :=
  leaves.all fun entry =>
    (!entry.leaf.user && entry.owner == .supervisor) ||
    (entry.leaf.user &&
      ((entry.space == .subjectA && entry.owner == .subjectA) ||
       (entry.space == .subjectB && entry.owner == .subjectB)))

/-- User-owned frames are not shared across the two subject views.  Supervisor
frames may intentionally be identical in both roots. -/
def userViewsSeparated (leaves : List CompiledLeaf) : Bool :=
  leaves.Pairwise fun a b =>
    !a.leaf.user || !b.leaf.user || a.space == b.space || a.leaf.frame != b.leaf.frame

/-- Every emitted leaf is in the supported 4 KiB lower-half subset. -/
def structurallySafe (leaves : List CompiledLeaf) : Bool :=
  leaves.all fun entry => canonicalPage entry.page &&
    representableFrame entry.leaf.frame && entry.leaf.present &&
    entry.leaf.reservedBitsClear

/-- The compiler has not invented an encoding independently of
`X86PageTable.policyLeaf`. -/
def refinesPolicy (leaves : List CompiledLeaf) : Bool :=
  leaves.all fun entry => entry.leaf == policyLeaf entry.policy entry.leaf.frame

def supervisorConfinement (leaves : List CompiledLeaf) : Bool :=
  leaves.all fun entry =>
    match entry.policy with
    | .kernelText | .kernelData | .kernelStack | .pageTables => !entry.leaf.user
    | .userText | .userStack => true

/-- The permission profiles called out by the boot policy are checked
explicitly, in addition to the generic W^X and policy-refinement checks. -/
def policyAttributesSafe (leaves : List CompiledLeaf) : Bool :=
  leaves.all fun entry =>
    match entry.policy with
    | .kernelText => !entry.leaf.user && !entry.leaf.writable && !entry.leaf.noExecute
    | .kernelData | .kernelStack | .pageTables =>
        !entry.leaf.user && entry.leaf.writable && entry.leaf.noExecute
    | .userText => entry.leaf.user && !entry.leaf.writable && !entry.leaf.noExecute
    | .userStack => entry.leaf.user && entry.leaf.writable && entry.leaf.noExecute

structure Plan where
  roots : Roots
  leaves : List CompiledLeaf
  rootsDistinct : roots.subjectA ≠ roots.subjectB
  noDuplicates : noDuplicateLeaves leaves = true
  wx : wxSafe leaves = true
  ownership : ownershipSafe leaves = true
  userViewsSeparated : userViewsSeparated leaves = true
  structural : structurallySafe leaves = true
  policyRefinement : refinesPolicy leaves = true
  supervisorOnly : supervisorConfinement leaves = true
  policyAttributes : policyAttributesSafe leaves = true
  tableFramesReserved : Bool
  reservationsChecked : tableFramesReserved = true
  tableFramesValid : Bool
  tableFramesValidityChecked : tableFramesValid = true

/-- Total compiler/checker for the deliberately finite supported subset. -/
def compile (input : Input) : Except Error Plan := do
  if !input.nxe then throw .missingNXE
  if hroot : input.roots.subjectA == input.roots.subjectB then throw .equalRoots else
    if hvalid : !tableFramesRepresentable input then throw .invalidTableFrame else
     if hreserved : !tableFramesReserved input then throw .unreservedTableFrame else
      let leaves <- input.regions.flatMapM compileRegion
      if hduplicates : noDuplicateLeaves leaves then
        if hwx : wxSafe leaves then
          if hownership : ownershipSafe leaves then
            if hseparated : userViewsSeparated leaves then
              if hstructural : structurallySafe leaves then
                if hrefines : refinesPolicy leaves then
                  if hsupervisor : supervisorConfinement leaves then
                    if hattributes : policyAttributesSafe leaves then
                      have hroots : input.roots.subjectA ≠ input.roots.subjectB := by
                        intro heq
                        apply hroot
                        simp [heq]
                      have htables : tableFramesReserved input = true := by
                        simpa using hreserved
                      have hframes : tableFramesRepresentable input = true := by
                        simpa using hvalid
                      pure ⟨input.roots, leaves, hroots, hduplicates, hwx, hownership, hseparated,
                        hstructural, hrefines, hsupervisor, hattributes,
                        tableFramesReserved input, htables,
                        tableFramesRepresentable input, hframes⟩
                    else throw .incompatibleOverlap
                  else throw .wrongOwner
                else throw .incompatibleOverlap
              else throw .nonCanonical
            else throw .incompatibleOverlap
          else throw .incompatibleOverlap
        else throw .incompatibleOverlap
      else throw .duplicateLeaf

theorem compile_deterministic input first second
    (hfirst : compile input = first) (hsecond : compile input = second) : first = second := by
  rw [hfirst] at hsecond
  exact hsecond

theorem accepted_wx input plan (_h : compile input = .ok plan) :
    wxSafe plan.leaves = true := plan.wx

theorem accepted_ownership input plan (_h : compile input = .ok plan) :
    ownershipSafe plan.leaves = true := plan.ownership

theorem accepted_distinct_user_views input plan (_h : compile input = .ok plan) :
    userViewsSeparated plan.leaves = true := plan.userViewsSeparated

theorem accepted_structurally_valid input plan (_h : compile input = .ok plan) :
    structurallySafe plan.leaves = true := plan.structural

theorem accepted_refines_policy input plan (_h : compile input = .ok plan) :
    refinesPolicy plan.leaves = true := plan.policyRefinement

theorem accepted_supervisor_confinement input plan (_h : compile input = .ok plan) :
    supervisorConfinement plan.leaves = true := plan.supervisorOnly

theorem accepted_policy_attributes input plan (_h : compile input = .ok plan) :
    policyAttributesSafe plan.leaves = true := plan.policyAttributes

theorem accepted_distinct_views input plan (_h : compile input = .ok plan) :
    plan.roots.subjectA ≠ plan.roots.subjectB := by
  exact plan.rootsDistinct

theorem accepted_no_duplicate_leaf input plan (_h : compile input = .ok plan) :
    noDuplicateLeaves plan.leaves = true := plan.noDuplicates

theorem accepted_table_frames_reserved input plan (_h : compile input = .ok plan) :
    plan.tableFramesReserved = true := plan.reservationsChecked

theorem accepted_table_frames_representable input plan (_h : compile input = .ok plan) :
    plan.tableFramesValid = true := plan.tableFramesValidityChecked

/-! ## Bounded live-table comparison boundary -/

/-- A guest walker decodes ancestors into this flag subset. Physical pointers
are checked for representation and reservation; the pointer chase itself is
integration evidence, not a Lean theorem. -/
structure DecodedAncestor where
  present : Bool
  writable : Bool
  user : Bool
  reservedBitsClear : Bool
  nextFrame : PhysicalFrame
  deriving BEq, DecidableEq, Repr

structure DecodedLeaf where
  page : Nat
  leaf : Leaf
  deriving BEq, DecidableEq, Repr

structure DecodedRoot where
  space : Space
  selectedRoot : PhysicalFrame
  pml4 : DecodedAncestor
  pdpt : DecodedAncestor
  pd : DecodedAncestor
  leaves : List DecodedLeaf
  deriving BEq, DecidableEq, Repr

inductive ReportError where
  | wrongRoot | wrongAncestor | unreservedAncestor | duplicateActual
  | missingLeaf | unexpectedLeaf | mismatchedLeaf
  deriving BEq, DecidableEq, Repr

def expectedRoot (plan : Plan) : Space → PhysicalFrame
  | .subjectA => plan.roots.subjectA
  | .subjectB => plan.roots.subjectB

def legalDecodedAncestor (entry : DecodedAncestor) : Bool :=
  entry.present && entry.writable && entry.user && entry.reservedBitsClear &&
    representableFrame entry.nextFrame

def decodedAncestorReserved (input : Input) (entry : DecodedAncestor) : Bool :=
  reservedAsPageTable input.tableReservations entry.nextFrame

def expectedAncestorFrames (input : Input) : Space → AncestorFrames
  | .subjectA => input.ancestors.subjectA
  | .subjectB => input.ancestors.subjectB

def ancestorPointersMatch (input : Input) (report : DecodedRoot) : Bool :=
  let expected := expectedAncestorFrames input report.space
  report.pml4.nextFrame == expected.pdpt && report.pdpt.nextFrame == expected.pd &&
    report.pd.nextFrame == expected.pt

def decodedNoDuplicates (leaves : List DecodedLeaf) : Bool :=
  leaves.Pairwise fun a b => a.page != b.page

def expectedAt (plan : Plan) (space : Space) (page : Nat) : Option Leaf :=
  (plan.leaves.find? fun entry => entry.space == space && entry.page == page).map (·.leaf)

def actualAt (report : DecodedRoot) (page : Nat) : Option Leaf :=
  (report.leaves.find? fun entry => entry.page == page).map (·.leaf)

/-- Compare a decoded root with precisely the leaves emitted by `compile`.
The two directions reject both omitted and unmanifested present leaves. -/
def validateDecodedRoot (input : Input) (plan : Plan) (report : DecodedRoot) :
    Except ReportError Unit := do
  if report.selectedRoot != expectedRoot plan report.space then throw .wrongRoot
  if !(legalDecodedAncestor report.pml4 && legalDecodedAncestor report.pdpt &&
      legalDecodedAncestor report.pd) then throw .wrongAncestor
  if !ancestorPointersMatch input report then throw .wrongAncestor
  if !(decodedAncestorReserved input report.pml4 && decodedAncestorReserved input report.pdpt &&
      decodedAncestorReserved input report.pd) then throw .unreservedAncestor
  if !decodedNoDuplicates report.leaves then throw .duplicateActual
  for actual in report.leaves do
    match expectedAt plan report.space actual.page with
    | none => throw .unexpectedLeaf
    | some expected => if actual.leaf != expected then throw .mismatchedLeaf
  for expected in plan.leaves do
    if expected.space == report.space && actualAt report expected.page != some expected.leaf then
      throw .missingLeaf

theorem decoded_validation_deterministic input plan report first second
    (hfirst : validateDecodedRoot input plan report = first)
    (hsecond : validateDecodedRoot input plan report = second) : first = second := by
  rw [hfirst] at hsecond
  exact hsecond

/-- Require one report for each address space, rather than allowing an
integration harness to validate the same selected root twice. -/
def validateDecodedPair (input : Input) (plan : Plan)
    (subjectA subjectB : DecodedRoot) : Except ReportError Unit := do
  if subjectA.space != .subjectA || subjectB.space != .subjectB then throw .wrongRoot
  validateDecodedRoot input plan subjectA
  validateDecodedRoot input plan subjectB

/-! ## Executable positive and adversarial fixtures -/

def sampleReservations : List Interval :=
  [{ identity := .pageTables, firstFrame := 10, frameCount := 16,
     lifetime := .permanent }]

def sampleRegions : List Region :=
  [{ space := .subjectA, virtualStart := pageBytes, byteLength := pageBytes,
     physicalStart := pageBytes, policy := .kernelText, owner := .supervisor },
   { space := .subjectB, virtualStart := pageBytes, byteLength := pageBytes,
     physicalStart := pageBytes, policy := .kernelText, owner := .supervisor },
   { space := .subjectA, virtualStart := 100 * pageBytes, byteLength := pageBytes,
     physicalStart := 100 * pageBytes, policy := .userText, owner := .subjectA },
   { space := .subjectA, virtualStart := 101 * pageBytes, byteLength := pageBytes,
     physicalStart := 101 * pageBytes, policy := .userStack, owner := .subjectA },
   { space := .subjectB, virtualStart := 100 * pageBytes, byteLength := pageBytes,
     physicalStart := 200 * pageBytes, policy := .userText, owner := .subjectB },
   { space := .subjectB, virtualStart := 101 * pageBytes, byteLength := pageBytes,
     physicalStart := 201 * pageBytes, policy := .userStack, owner := .subjectB }]

def sampleInput : Input :=
  { roots := { subjectA := 10, subjectB := 11 }, nxe := true,
    ancestors :=
      { subjectA := { pdpt := 12, pd := 13, pt := 14 },
        subjectB := { pdpt := 15, pd := 16, pt := 17 } },
    regions := sampleRegions, tableReservations := sampleReservations }

def rejectedAs (input : Input) (wanted : Error) : Bool :=
  match compile input with
  | .error actual => actual == wanted
  | .ok _ => false

example : (match compile sampleInput with | .ok _ => true | .error _ => false) = true := by
  native_decide
example : rejectedAs { sampleInput with nxe := false } .missingNXE = true := by native_decide
example : rejectedAs { sampleInput with roots := { subjectA := 10, subjectB := 10 } }
    .equalRoots = true := by native_decide
example : rejectedAs { sampleInput with tableReservations := [] }
    .unreservedTableFrame = true := by native_decide
example : rejectedAs
    { sampleInput with tableReservations :=
        [{ identity := .loadedImage, firstFrame := 10, frameCount := 16,
           lifetime := .permanent }] }
    .unreservedTableFrame = true := by native_decide
example : rejectedAs
    { sampleInput with roots := { subjectA := physicalFrameLimit, subjectB := 11 } }
    .invalidTableFrame = true := by native_decide
example : rejectedAs { sampleInput with regions := sampleRegions ++ [sampleRegions[0]!] }
    .duplicateLeaf = true := by native_decide
example : rejectedAs { sampleInput with regions :=
    [{ sampleRegions[2]! with owner := .subjectB }] } .wrongOwner = true := by native_decide
def sampleOverflowRegion : Region :=
  { sampleRegions[0]! with
    virtualStart := 2 ^ 64 - pageBytes
    byteLength := 2 * pageBytes }

example : rejectedAs { sampleInput with regions := [sampleOverflowRegion] }
    .addressOverflow = true := by native_decide

def decodedAncestor (frame : Nat) : DecodedAncestor :=
  { present := true, writable := true, user := true, reservedBitsClear := true,
    nextFrame := frame }

def decodedReport (plan : Plan) (space : Space) : DecodedRoot :=
  let expected := expectedAncestorFrames sampleInput space
  { space, selectedRoot := expectedRoot plan space,
    pml4 := decodedAncestor expected.pdpt, pdpt := decodedAncestor expected.pd,
    pd := decodedAncestor expected.pt,
    leaves := (plan.leaves.filter (·.space == space)).map fun entry =>
      { page := entry.page, leaf := entry.leaf } }

def sampleReportCheck (mutate : DecodedRoot → DecodedRoot) : Except ReportError Unit :=
  match compile sampleInput with
  | .error _ => .error .missingLeaf
  | .ok plan => validateDecodedRoot sampleInput plan (mutate (decodedReport plan .subjectA))

def unchangedReport (report : DecodedRoot) : DecodedRoot := report
def wrongRootReport (report : DecodedRoot) : DecodedRoot := { report with selectedRoot := 11 }
def wrongAncestorReport (report : DecodedRoot) : DecodedRoot :=
  { report with pd := { report.pd with present := false } }
def wrongAncestorPointerReport (report : DecodedRoot) : DecodedRoot :=
  { report with pd := { report.pd with nextFrame := report.pd.nextFrame + 1 } }
def unexpectedLeafReport (report : DecodedRoot) : DecodedRoot :=
  { report with leaves := report.leaves ++
      [{ page := 300, leaf := policyLeaf .userStack 300 }] }
def missingLeafReport (report : DecodedRoot) : DecodedRoot :=
  { report with leaves := report.leaves.drop 1 }
def flippedWritableReport (report : DecodedRoot) : DecodedRoot :=
  { report with leaves := report.leaves.mapIdx fun index entry =>
      if index == 0 then { entry with leaf := { entry.leaf with writable := !entry.leaf.writable } }
      else entry }
def flippedPresentReport (report : DecodedRoot) : DecodedRoot :=
  { report with leaves := report.leaves.mapIdx fun index entry =>
      if index == 0 then { entry with leaf := { entry.leaf with present := false } } else entry }
def flippedUserReport (report : DecodedRoot) : DecodedRoot :=
  { report with leaves := report.leaves.mapIdx fun index entry =>
      if index == 0 then { entry with leaf := { entry.leaf with user := !entry.leaf.user } }
      else entry }
def flippedNXReport (report : DecodedRoot) : DecodedRoot :=
  { report with leaves := report.leaves.mapIdx fun index entry =>
      if index == 0 then { entry with leaf := { entry.leaf with noExecute := !entry.leaf.noExecute } }
      else entry }
def flippedFrameReport (report : DecodedRoot) : DecodedRoot :=
  { report with leaves := report.leaves.mapIdx fun index entry =>
      if index == 0 then { entry with leaf := { entry.leaf with frame := entry.leaf.frame + 1 } }
      else entry }
def flippedReservedBitsReport (report : DecodedRoot) : DecodedRoot :=
  { report with leaves := report.leaves.mapIdx fun index entry =>
      if index == 0 then { entry with leaf := { entry.leaf with reservedBitsClear := false } }
      else entry }

def reportAccepted (result : Except ReportError Unit) : Bool :=
  match result with | .ok _ => true | .error _ => false

def reportRejectedAs (result : Except ReportError Unit) (wanted : ReportError) : Bool :=
  match result with | .ok _ => false | .error actual => actual == wanted

example : reportAccepted (sampleReportCheck unchangedReport) = true := by native_decide
example : reportRejectedAs (sampleReportCheck wrongRootReport) .wrongRoot = true := by native_decide
example : reportRejectedAs (sampleReportCheck wrongAncestorReport) .wrongAncestor = true := by
  native_decide
example : reportRejectedAs (sampleReportCheck wrongAncestorPointerReport) .wrongAncestor = true := by
  native_decide
example : reportRejectedAs (sampleReportCheck unexpectedLeafReport) .unexpectedLeaf = true := by
  native_decide
example : reportRejectedAs (sampleReportCheck missingLeafReport) .missingLeaf = true := by
  native_decide
example : reportRejectedAs (sampleReportCheck flippedWritableReport) .mismatchedLeaf = true := by
  native_decide
example : reportRejectedAs (sampleReportCheck flippedPresentReport) .mismatchedLeaf = true := by
  native_decide
example : reportRejectedAs (sampleReportCheck flippedUserReport) .mismatchedLeaf = true := by
  native_decide
example : reportRejectedAs (sampleReportCheck flippedNXReport) .mismatchedLeaf = true := by
  native_decide
example : reportRejectedAs (sampleReportCheck flippedFrameReport) .mismatchedLeaf = true := by
  native_decide
example : reportRejectedAs (sampleReportCheck flippedReservedBitsReport) .mismatchedLeaf = true := by
  native_decide

def samplePairCheck (mutateA mutateB : DecodedRoot → DecodedRoot) :
    Except ReportError Unit :=
  match compile sampleInput with
  | .error _ => .error .missingLeaf
  | .ok plan => validateDecodedPair sampleInput plan
      (mutateA (decodedReport plan .subjectA)) (mutateB (decodedReport plan .subjectB))

example : reportAccepted (samplePairCheck unchangedReport unchangedReport) = true := by
  native_decide
example : reportRejectedAs
    (samplePairCheck (fun report => { report with space := .subjectB }) unchangedReport)
    .wrongRoot = true := by native_decide

def swappedUserLeavesCheck : Except ReportError Unit :=
  match compile sampleInput with
  | .error _ => .error .missingLeaf
  | .ok plan =>
      let reportA := decodedReport plan .subjectA
      let reportB := decodedReport plan .subjectB
      let userA := reportA.leaves.drop 1
      let userB := reportB.leaves.drop 1
      validateDecodedPair sampleInput plan
        { reportA with leaves := reportA.leaves.take 1 ++ userB }
        { reportB with leaves := reportB.leaves.take 1 ++ userA }

example : reportRejectedAs swappedUserLeavesCheck .mismatchedLeaf = true := by native_decide

end LeanOS.BootPageTablePlan
