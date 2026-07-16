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

/-- The non-root frames for the boot constructor's eight-PT 16 MiB map. -/
structure AncestorFrames where
  pdpt : PhysicalFrame
  pd : PhysicalFrame
  pts : List PhysicalFrame
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
  /-- The page-table reservation is accepted only as part of the allocator
  result that validated and overlaid the complete boot manifest. -/
  reservationResult : Option BootReservation.Result

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
  | duplicateLeaf | duplicateTableFrame | unreservedTableFrame | invalidTableFrame
  | missingRequiredRegion | unsafePhysicalAlias | missingValidatedReservation
  | tableManifestMismatch
  deriving BEq, DecidableEq, Repr

def aligned (address : Nat) : Bool := address % pageBytes == 0

def bootPtCount : Nat := 8
def supportedPathPages : Nat := 512 * bootPtCount

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
  if firstPage + count > lowerCanonicalPages || firstPage + count > supportedPathPages then
    throw .nonCanonical
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
  match input.reservationResult with
  | none => false
  | some reserved =>
    reservedAsPageTable reserved.intervals input.roots.subjectA &&
      reservedAsPageTable reserved.intervals input.roots.subjectB &&
      reservedAsPageTable reserved.intervals input.ancestors.subjectA.pdpt &&
      reservedAsPageTable reserved.intervals input.ancestors.subjectA.pd &&
      input.ancestors.subjectA.pts.length == bootPtCount &&
      input.ancestors.subjectA.pts.all (reservedAsPageTable reserved.intervals) &&
      reservedAsPageTable reserved.intervals input.ancestors.subjectB.pdpt &&
      reservedAsPageTable reserved.intervals input.ancestors.subjectB.pd &&
      input.ancestors.subjectB.pts.length == bootPtCount &&
      input.ancestors.subjectB.pts.all (reservedAsPageTable reserved.intervals) &&
      input.regions.all fun region => region.policy != .pageTables ||
        (List.range (region.byteLength / pageBytes)).all fun offset =>
          reservedAsPageTable reserved.intervals
            (region.physicalStart / pageBytes + offset)

def tableFramesRepresentable (input : Input) : Bool :=
  representableFrame input.roots.subjectA && representableFrame input.roots.subjectB &&
    representableFrame input.ancestors.subjectA.pdpt &&
    representableFrame input.ancestors.subjectA.pd &&
    input.ancestors.subjectA.pts.length == bootPtCount &&
    input.ancestors.subjectA.pts.all representableFrame &&
    representableFrame input.ancestors.subjectB.pdpt &&
    representableFrame input.ancestors.subjectB.pd &&
    input.ancestors.subjectB.pts.length == bootPtCount &&
    input.ancestors.subjectB.pts.all representableFrame

def tableFrames (input : Input) : List PhysicalFrame :=
  [input.roots.subjectA, input.roots.subjectB,
   input.ancestors.subjectA.pdpt, input.ancestors.subjectA.pd] ++
   input.ancestors.subjectA.pts ++
   [input.ancestors.subjectB.pdpt, input.ancestors.subjectB.pd] ++
   input.ancestors.subjectB.pts

/-- Each level has distinct storage.  Aliasing a root with one of its descendants,
or two descendants with each other, cannot describe the supported four-level tree. -/
def tableFramesDistinct (input : Input) : Bool :=
  (tableFrames input).Pairwise (· != ·)

def hasRegion (input : Input) (space : Space) (policy : PolicyRegion) (owner : Owner) : Bool :=
  input.regions.any fun region =>
    region.space == space && region.policy == policy && region.owner == owner

/-- The Phase 2 plan is not an optional list: both roots must contain the
reviewed supervisor classes and their subject-specific user text and stack. -/
def requiredCoverage (input : Input) : Bool :=
  [.subjectA, .subjectB].all fun space =>
    hasRegion input space .kernelText .supervisor &&
    hasRegion input space .kernelData .supervisor &&
    hasRegion input space .kernelStack .supervisor &&
    hasRegion input space .pageTables .supervisor &&
    match space with
    | .subjectA =>
        hasRegion input space .userText .subjectA && hasRegion input space .userStack .subjectA
    | .subjectB =>
        hasRegion input space .userText .subjectB && hasRegion input space .userStack .subjectB

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

/-- Physical aliases are permitted only for the same reviewed supervisor
policy in the two roots.  In particular, user leaves can never alias a live
root/ancestor frame or any other supervisor-owned frame. -/
def physicalAliasesSafe (leaves : List CompiledLeaf) : Bool :=
  leaves.Pairwise fun a b =>
    a.leaf.frame != b.leaf.frame ||
      (!a.leaf.user && !b.leaf.user && a.policy == b.policy)

/-- The live roots and ancestor frames are authoritative constructor inputs,
not inferred from whichever `.pageTables` regions the manifest happens to
contain.  No user mapping may therefore alias any one of those frames. -/
def userAvoidsTableFrames (frames : List PhysicalFrame) (leaves : List CompiledLeaf) : Bool :=
  leaves.all fun entry => !entry.leaf.user || !frames.contains entry.leaf.frame

def userAvoidsLiveTableFrames (input : Input) (leaves : List CompiledLeaf) : Bool :=
  userAvoidsTableFrames (tableFrames input) leaves

/-- The manifest names exactly the constructor-owned table frames in both
address spaces, at their identity-mapped boot addresses.  This prevents an
otherwise valid reservation from being paired with unrelated `.pageTables`
regions. -/
def tableManifestMatches (input : Input) (leaves : List CompiledLeaf) : Bool :=
  let frames := tableFrames input
  [.subjectA, .subjectB].all fun space =>
    let declared := leaves.filter fun entry =>
      entry.space == space && entry.policy == .pageTables
    declared.all (fun entry => entry.page == entry.leaf.frame && frames.contains entry.leaf.frame) &&
      frames.all fun frame => declared.any fun entry => entry.leaf.frame == frame

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
  liveTableFrames : List PhysicalFrame
  liveTablesChecked : userAvoidsTableFrames liveTableFrames leaves = true
  structural : structurallySafe leaves = true
  policyRefinement : refinesPolicy leaves = true
  supervisorOnly : supervisorConfinement leaves = true
  policyAttributes : policyAttributesSafe leaves = true
  tableFramesReserved : Bool
  reservationsChecked : tableFramesReserved = true
  tableFramesValid : Bool
  tableFramesValidityChecked : tableFramesValid = true
  tableFramesUnique : Bool
  tableFramesUniquenessChecked : tableFramesUnique = true

/-- Total compiler/checker for the deliberately finite supported subset. -/
def compile (input : Input) : Except Error Plan := do
  if !input.nxe then throw .missingNXE
  if input.reservationResult.isNone then throw .missingValidatedReservation
  if hroot : input.roots.subjectA == input.roots.subjectB then throw .equalRoots else
    if hvalid : !tableFramesRepresentable input then throw .invalidTableFrame else
     if hunique : !tableFramesDistinct input then throw .duplicateTableFrame else
      if hreserved : !tableFramesReserved input then throw .unreservedTableFrame else
      let leaves <- input.regions.flatMapM compileRegion
      if !requiredCoverage input then throw .missingRequiredRegion
      if !tableManifestMatches input leaves then throw .tableManifestMismatch
      if hduplicates : noDuplicateLeaves leaves then
        if hwx : wxSafe leaves then
          if !physicalAliasesSafe leaves then throw .unsafePhysicalAlias else
          if hliveTables : userAvoidsLiveTableFrames input leaves then
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
                        have hframesUnique : tableFramesDistinct input = true := by
                          simpa using hunique
                        pure ⟨input.roots, leaves, hroots, hduplicates, hwx, hownership, hseparated,
                          tableFrames input, hliveTables,
                          hstructural, hrefines, hsupervisor, hattributes,
                          tableFramesReserved input, htables,
                          tableFramesRepresentable input, hframes,
                          tableFramesDistinct input, hframesUnique⟩
                      else throw .incompatibleOverlap
                    else throw .wrongOwner
                  else throw .incompatibleOverlap
                else throw .nonCanonical
              else throw .incompatibleOverlap
            else throw .incompatibleOverlap
          else throw .unsafePhysicalAlias
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

theorem accepted_user_avoids_live_table_frames input plan
    (_h : compile input = .ok plan) :
    userAvoidsTableFrames plan.liveTableFrames plan.leaves = true :=
  plan.liveTablesChecked

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

theorem accepted_table_frames_distinct input plan (_h : compile input = .ok plan) :
    plan.tableFramesUnique = true := plan.tableFramesUniquenessChecked

/-! ## Bounded live-table comparison boundary -/

/-- A guest walker decodes ancestors into this flag subset. Physical pointers
are checked for representation and reservation; the pointer chase itself is
integration evidence, not a Lean theorem. -/
structure DecodedAncestor where
  present : Bool
  writable : Bool
  user : Bool
  noExecute : Bool
  hugePage : Bool
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
  ptPointers : List DecodedAncestor
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
  entry.present && entry.writable && entry.user && !entry.noExecute && !entry.hugePage &&
    entry.reservedBitsClear &&
    representableFrame entry.nextFrame

def decodedAncestorReserved (input : Input) (entry : DecodedAncestor) : Bool :=
  match input.reservationResult with
  | none => false
  | some reserved => reservedAsPageTable reserved.intervals entry.nextFrame

def expectedAncestorFrames (input : Input) : Space → AncestorFrames
  | .subjectA => input.ancestors.subjectA
  | .subjectB => input.ancestors.subjectB

def ancestorPointersMatch (input : Input) (report : DecodedRoot) : Bool :=
  let expected := expectedAncestorFrames input report.space
  report.pml4.nextFrame == expected.pdpt && report.pdpt.nextFrame == expected.pd &&
    report.ptPointers.map (·.nextFrame) == expected.pts

def decodedNoDuplicates (leaves : List DecodedLeaf) : Bool :=
  leaves.Pairwise fun a b => a.page != b.page

def expectedAt (plan : Plan) (space : Space) (page : Nat) : Option Leaf :=
  (plan.leaves.find? fun entry => entry.space == space && entry.page == page).map (·.leaf)

def actualAt (report : DecodedRoot) (page : Nat) : Option Leaf :=
  (report.leaves.find? fun entry => entry.page == page).map (·.leaf)

def absentLeaf : Leaf :=
  { frame := 0, present := false, writable := false, user := false,
    noExecute := false, reservedBitsClear := true }

def expectedDecodedAt (plan : Plan) (space : Space) (page : Nat) : Leaf :=
  (expectedAt plan space page).getD absentLeaf

/-- Compare all 4,096 decoded PTEs reached through the eight PT pointers.
Manifest omissions are deliberately absent zero entries, so neither an extra
present mapping nor corruption in a later PT can hide outside the report. -/
def validateDecodedRoot (input : Input) (plan : Plan) (report : DecodedRoot) :
    Except ReportError Unit := do
  if report.selectedRoot != expectedRoot plan report.space then throw .wrongRoot
  if !(legalDecodedAncestor report.pml4 && legalDecodedAncestor report.pdpt &&
      report.ptPointers.length == bootPtCount &&
      report.ptPointers.all legalDecodedAncestor) then throw .wrongAncestor
  if !ancestorPointersMatch input report then throw .wrongAncestor
  if !(decodedAncestorReserved input report.pml4 && decodedAncestorReserved input report.pdpt &&
      report.ptPointers.all (decodedAncestorReserved input)) then throw .unreservedAncestor
  if !decodedNoDuplicates report.leaves then throw .duplicateActual
  for actual in report.leaves do
    if actual.page >= supportedPathPages then throw .unexpectedLeaf
    if actual.leaf != expectedDecodedAt plan report.space actual.page then
      throw .mismatchedLeaf
  if report.leaves.length != supportedPathPages then throw .missingLeaf

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
  [{ identity := .pageTables, firstFrame := 10, frameCount := 22,
     lifetime := .permanent }]

def sampleReservationManifest : List Reservation :=
  [{ identity := .lowMemory, start := 0, length := pageBytes, lifetime := .permanent },
   { identity := .loadedImage, start := 2 * pageBytes, length := 30 * pageBytes,
     lifetime := .permanent },
   { identity := .pageTables, start := 10 * pageBytes, length := 22 * pageBytes,
     lifetime := .permanent },
   { identity := .descriptorTables, start := 3 * pageBytes, length := pageBytes,
     lifetime := .permanent },
   { identity := .kernelStacks, start := 4 * pageBytes, length := pageBytes,
     lifetime := .permanent },
   { identity := .embeddedUsers, start := 5 * pageBytes, length := pageBytes,
     lifetime := .permanent },
   { identity := .multibootInfo, start := pageBytes, length := pageBytes,
     lifetime := .bootstrap }]

def sampleReservationHandoff : BootMemoryMap.Handoff :=
  BootMemoryMap.mkHandoff [{ base := 0, length := 40 * pageBytes, kind := .usable }]

def sampleReservationResult : Option BootReservation.Result :=
  (initializeAllocator sampleReservationHandoff sampleReservationManifest).toOption

def sampleRegions : List Region :=
  [{ space := .subjectA, virtualStart := pageBytes, byteLength := pageBytes,
     physicalStart := pageBytes, policy := .kernelText, owner := .supervisor },
   { space := .subjectB, virtualStart := pageBytes, byteLength := pageBytes,
     physicalStart := pageBytes, policy := .kernelText, owner := .supervisor },
   { space := .subjectA, virtualStart := 2 * pageBytes, byteLength := pageBytes,
     physicalStart := 2 * pageBytes, policy := .kernelData, owner := .supervisor },
   { space := .subjectB, virtualStart := 2 * pageBytes, byteLength := pageBytes,
     physicalStart := 2 * pageBytes, policy := .kernelData, owner := .supervisor },
   { space := .subjectA, virtualStart := 3 * pageBytes, byteLength := pageBytes,
     physicalStart := 3 * pageBytes, policy := .kernelStack, owner := .supervisor },
   { space := .subjectB, virtualStart := 3 * pageBytes, byteLength := pageBytes,
     physicalStart := 3 * pageBytes, policy := .kernelStack, owner := .supervisor },
   { space := .subjectA, virtualStart := 10 * pageBytes, byteLength := 22 * pageBytes,
     physicalStart := 10 * pageBytes, policy := .pageTables, owner := .supervisor },
   { space := .subjectB, virtualStart := 10 * pageBytes, byteLength := 22 * pageBytes,
     physicalStart := 10 * pageBytes, policy := .pageTables, owner := .supervisor },
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
      { subjectA := { pdpt := 12, pd := 13, pts := List.range 8 |>.map (14 + ·) },
        subjectB := { pdpt := 22, pd := 23, pts := List.range 8 |>.map (24 + ·) } },
    regions := sampleRegions, reservationResult := sampleReservationResult }

def rejectedAs (input : Input) (wanted : Error) : Bool :=
  match compile input with
  | .error actual => actual == wanted
  | .ok _ => false

example : (match compile sampleInput with | .ok _ => true | .error _ => false) = true := by
  native_decide
example : rejectedAs { sampleInput with regions := [] } .missingRequiredRegion = true := by
  native_decide
example : rejectedAs { sampleInput with regions := sampleRegions.tail }
    .missingRequiredRegion = true := by native_decide
example : rejectedAs
    { sampleInput with regions := sampleRegions.map fun region =>
        if region.space == .subjectA && region.policy == .userText then
          { region with physicalStart := sampleInput.roots.subjectA * pageBytes }
        else region }
    .unsafePhysicalAlias = true := by native_decide
/-- Moving the declared page-table regions cannot hide a user alias of the
actual root supplied to the table constructor. -/
example : rejectedAs
    { sampleInput with regions := sampleRegions.map fun region =>
        if region.policy == .pageTables then
          { region with virtualStart := region.virtualStart + pageBytes }
        else if region.space == .subjectA && region.policy == .userText then
          { region with physicalStart := sampleInput.roots.subjectA * pageBytes }
        else region }
    .tableManifestMismatch = true := by native_decide
example : rejectedAs { sampleInput with nxe := false } .missingNXE = true := by native_decide
example : rejectedAs { sampleInput with roots := { subjectA := 10, subjectB := 10 } }
    .equalRoots = true := by native_decide
example : rejectedAs { sampleInput with reservationResult := none }
    .missingValidatedReservation = true := by native_decide
example : rejectedAs
    { sampleInput with regions := sampleRegions ++
        [{ space := .subjectA, virtualStart := 35 * pageBytes, byteLength := pageBytes,
           physicalStart := 35 * pageBytes, policy := .pageTables, owner := .supervisor }] }
    .unreservedTableFrame = true := by native_decide
example : rejectedAs
    { sampleInput with roots := { subjectA := physicalFrameLimit, subjectB := 11 } }
    .invalidTableFrame = true := by native_decide
example : rejectedAs
    { sampleInput with ancestors :=
        { sampleInput.ancestors with
          subjectA := { sampleInput.ancestors.subjectA with pdpt := sampleInput.roots.subjectA } } }
    .duplicateTableFrame = true := by native_decide
example : rejectedAs
    { sampleInput with ancestors :=
        { sampleInput.ancestors with
          subjectB := { sampleInput.ancestors.subjectB with
            pd := sampleInput.ancestors.subjectB.pts[0]! } } }
    .duplicateTableFrame = true := by native_decide
example : rejectedAs { sampleInput with regions := sampleRegions ++ [sampleRegions[0]!] }
    .duplicateLeaf = true := by native_decide
example : rejectedAs
    { sampleInput with regions := sampleRegions ++
        [{ { { sampleRegions[0]! with virtualStart := 0 } with
             byteLength := 2 * pageBytes } with physicalStart := 0 }] }
    .duplicateLeaf = true := by native_decide
example : rejectedAs { sampleInput with regions := [{ sampleRegions[0]! with byteLength := 0 }] }
    .emptyRegion = true := by native_decide
example : rejectedAs
    { sampleInput with regions := [{ sampleRegions[0]! with virtualStart := pageBytes + 1 }] }
    .misaligned = true := by native_decide
example : rejectedAs
    { sampleInput with regions := [{ sampleRegions[0]! with physicalStart := pageBytes + 1 }] }
    .misaligned = true := by native_decide
example : rejectedAs
    { sampleInput with regions := [{ sampleRegions[0]! with byteLength := pageBytes + 1 }] }
    .misaligned = true := by native_decide
example : rejectedAs
    { sampleInput with regions :=
        [{ sampleRegions[0]! with virtualStart := lowerCanonicalPages * pageBytes }] }
    .nonCanonical = true := by native_decide
/-- A lower-canonical leaf that crosses into a second PT is outside the single
ancestor path supplied by `Input`. -/
example : rejectedAs
    { sampleInput with regions := sampleRegions.map fun region =>
        if region.space == .subjectA && region.policy == .userText then
          { region with virtualStart := supportedPathPages * pageBytes }
        else region }
    .nonCanonical = true := by native_decide
example : rejectedAs
    { sampleInput with regions :=
        [{ sampleRegions[0]! with physicalStart := physicalFrameLimit * pageBytes }] }
    .frameOutOfRange = true := by native_decide
example : rejectedAs { sampleInput with regions :=
    [{ sampleRegions[8]! with owner := .subjectB }] } .wrongOwner = true := by native_decide
example : rejectedAs { sampleInput with regions :=
    [{ sampleRegions[8]! with space := .subjectB }] } .wrongOwner = true := by native_decide
def sampleOverflowRegion : Region :=
  { sampleRegions[0]! with
    virtualStart := 2 ^ 64 - pageBytes
    byteLength := 2 * pageBytes }

example : rejectedAs { sampleInput with regions := [sampleOverflowRegion] }
    .addressOverflow = true := by native_decide
example : rejectedAs
    { sampleInput with regions :=
        [{ { sampleRegions[0]! with physicalStart := 2 ^ 64 - pageBytes } with
           byteLength := 2 * pageBytes }] }
    .addressOverflow = true := by native_decide

def decodedAncestor (frame : Nat) : DecodedAncestor :=
  { present := true, writable := true, user := true, noExecute := false,
    hugePage := false, reservedBitsClear := true, nextFrame := frame }

def decodedReport (plan : Plan) (space : Space) : DecodedRoot :=
  let expected := expectedAncestorFrames sampleInput space
  { space, selectedRoot := expectedRoot plan space,
    pml4 := decodedAncestor expected.pdpt, pdpt := decodedAncestor expected.pd,
    ptPointers := expected.pts.map decodedAncestor,
    leaves := (List.range supportedPathPages).map fun page =>
      { page, leaf := expectedDecodedAt plan space page } }

def sampleReportCheck (mutate : DecodedRoot → DecodedRoot) : Except ReportError Unit :=
  match compile sampleInput with
  | .error _ => .error .missingLeaf
  | .ok plan => validateDecodedRoot sampleInput plan (mutate (decodedReport plan .subjectA))

def unchangedReport (report : DecodedRoot) : DecodedRoot := report
def wrongRootReport (report : DecodedRoot) : DecodedRoot := { report with selectedRoot := 11 }
def wrongAncestorReport (report : DecodedRoot) : DecodedRoot :=
  { report with ptPointers := report.ptPointers.modify 0 fun e => { e with present := false } }
def wrongAncestorWritableReport (report : DecodedRoot) : DecodedRoot :=
  { report with ptPointers := report.ptPointers.modify 0 fun e => { e with writable := false } }
def wrongAncestorUserReport (report : DecodedRoot) : DecodedRoot :=
  { report with ptPointers := report.ptPointers.modify 0 fun e => { e with user := false } }
def wrongAncestorReservedBitsReport (report : DecodedRoot) : DecodedRoot :=
  { report with ptPointers := report.ptPointers.modify 0 fun e => { e with reservedBitsClear := false } }
def wrongAncestorNXReport (report : DecodedRoot) : DecodedRoot :=
  { report with ptPointers := report.ptPointers.modify 7 fun e => { e with noExecute := true } }
def wrongAncestorHugePageReport (report : DecodedRoot) : DecodedRoot :=
  { report with ptPointers := report.ptPointers.modify 7 fun e => { e with hugePage := true } }
def wrongAncestorPointerReport (report : DecodedRoot) : DecodedRoot :=
  { report with ptPointers := report.ptPointers.modify 7 fun e => { e with nextFrame := e.nextFrame + 1 } }
def duplicateLeafReport (report : DecodedRoot) : DecodedRoot :=
  { report with leaves := report.leaves ++ report.leaves.take 1 }
def unexpectedLeafReport (report : DecodedRoot) : DecodedRoot :=
  { report with leaves := report.leaves ++
      [{ page := supportedPathPages, leaf := policyLeaf .userStack supportedPathPages }] }
def missingLeafReport (report : DecodedRoot) : DecodedRoot :=
  { report with leaves := report.leaves.drop 1 }
def flippedWritableReport (report : DecodedRoot) : DecodedRoot :=
  { report with leaves := report.leaves.mapIdx fun index entry =>
      if index == 0 then { entry with leaf := { entry.leaf with writable := !entry.leaf.writable } }
      else entry }
def flippedPresentReport (report : DecodedRoot) : DecodedRoot :=
  { report with leaves := report.leaves.mapIdx fun index entry =>
      if index == 0 then { entry with leaf := { entry.leaf with present := !entry.leaf.present } }
      else entry }
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
example : reportRejectedAs (sampleReportCheck wrongAncestorWritableReport) .wrongAncestor = true := by
  native_decide
example : reportRejectedAs (sampleReportCheck wrongAncestorUserReport) .wrongAncestor = true := by
  native_decide
example : reportRejectedAs (sampleReportCheck wrongAncestorReservedBitsReport) .wrongAncestor = true := by
  native_decide
example : reportRejectedAs (sampleReportCheck wrongAncestorNXReport) .wrongAncestor = true := by
  native_decide
example : reportRejectedAs (sampleReportCheck wrongAncestorHugePageReport) .wrongAncestor = true := by
  native_decide
example : reportRejectedAs (sampleReportCheck wrongAncestorPointerReport) .wrongAncestor = true := by
  native_decide
example : reportRejectedAs (sampleReportCheck duplicateLeafReport) .duplicateActual = true := by
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
      let userA := reportA.leaves.filter fun entry => entry.leaf.user
      let userB := reportB.leaves.filter fun entry => entry.leaf.user
      validateDecodedPair sampleInput plan
        { reportA with leaves := reportA.leaves.filter (fun entry => !entry.leaf.user) ++ userB }
        { reportB with leaves := reportB.leaves.filter (fun entry => !entry.leaf.user) ++ userA }

example : reportRejectedAs swappedUserLeavesCheck .mismatchedLeaf = true := by native_decide

end LeanOS.BootPageTablePlan
