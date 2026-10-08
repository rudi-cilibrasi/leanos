import LeanOS.X86PageTable
import LeanOS.BootReservation

/-!
# Finite Phase 2 boot page-table plan

This is the authoritative, bounded input to the early-boot table constructor.
It deliberately proves facts about accepted plan values, not about the linker,
assembly writes, CR3, an x86 page walk, or QEMU.  Those boundaries must compare
decoded live entries with `compile`.

The image has a fixed set of subjects, not a dynamic count. Subjects A and B
are always present. A third subject C (issue #472) is optional: its root and
ancestor frames are `none` in every two-subject image and `some` only in an
image that links C's tables. A two-subject input therefore compiles exactly as
before, and an input that maps a leaf into an unconfigured space is rejected.
-/
namespace LeanOS.BootPageTablePlan

open LeanOS.X86PageTable
open LeanOS.BootReservation

inductive Space where | subjectA | subjectB | subjectC
  deriving BEq, DecidableEq, Repr

instance : Inhabited Space := ⟨.subjectA⟩

inductive Owner where | supervisor | subjectA | subjectB | subjectC
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
  /-- The third subject's root; `none` in a two-subject image. -/
  subjectC : Option PhysicalFrame := none
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
  /-- The third subject's ancestors; `none` in a two-subject image. -/
  subjectC : Option AncestorFrames := none
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
  | tableManifestMismatch | mmioAliasesRam | unreservedRemappingFrame
  | unconfiguredSpace
  deriving BEq, DecidableEq, Repr

def aligned (address : Nat) : Bool := address % pageBytes == 0

def bootPtCount : Nat := 8
def supportedPathPages : Nat := 512 * bootPtCount

def ownerMatches (region : Region) : Bool :=
  match region.policy, region.owner, region.space with
  | .kernelText, .supervisor, _ | .kernelData, .supervisor, _
  | .kernelStack, .supervisor, _ | .pageTables, .supervisor, _
  | .mmioWindow, .supervisor, _ | .remappingTables, .supervisor, _ => true
  | .userText, .subjectA, .subjectA | .userStack, .subjectA, .subjectA => true
  | .userText, .subjectB, .subjectB | .userStack, .subjectB, .subjectB => true
  | .userText, .subjectC, .subjectC | .userStack, .subjectC, .subjectC => true
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

/-- The optional third subject's root and ancestors satisfy `check`, with the
same eight-PT shape as A and B; an absent third subject is vacuous. -/
def thirdFramesSatisfy (input : Input) (check : PhysicalFrame → Bool) : Bool :=
  (match input.roots.subjectC with
   | none => true
   | some root => check root) &&
  (match input.ancestors.subjectC with
   | none => true
   | some frames =>
       check frames.pdpt && check frames.pd &&
         frames.pts.length == bootPtCount && frames.pts.all check)

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
      thirdFramesSatisfy input (reservedAsPageTable reserved.intervals) &&
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
    input.ancestors.subjectB.pts.all representableFrame &&
    thirdFramesSatisfy input representableFrame

/-- The third subject's frames, appended after A and B's so a two-subject
layout is exactly the two-subject list. -/
def thirdLayoutFrames (roots : Roots) (ancestors : AncestorPaths) : List PhysicalFrame :=
  roots.subjectC.toList ++
    match ancestors.subjectC with
    | none => []
    | some frames => [frames.pdpt, frames.pd] ++ frames.pts

def layoutFrames (roots : Roots) (ancestors : AncestorPaths) : List PhysicalFrame :=
  [roots.subjectA, roots.subjectB,
   ancestors.subjectA.pdpt, ancestors.subjectA.pd] ++
   ancestors.subjectA.pts ++
   [ancestors.subjectB.pdpt, ancestors.subjectB.pd] ++
   ancestors.subjectB.pts ++
   thirdLayoutFrames roots ancestors

def tableFrames (input : Input) : List PhysicalFrame :=
  layoutFrames input.roots input.ancestors

/-- Each level has distinct storage.  Aliasing a root with one of its descendants,
or two descendants with each other, cannot describe the supported four-level tree. -/
def tableFramesDistinct (input : Input) : Bool :=
  (tableFrames input).Pairwise (· != ·)

/-- The third subject is configured when its root is present.  Its root and
ancestors must be present together (`thirdSubjectConsistent`). -/
def Roots.hasThird (roots : Roots) : Bool := roots.subjectC.isSome

def thirdSubjectConsistent (input : Input) : Bool :=
  input.roots.subjectC.isSome == input.ancestors.subjectC.isSome

/-- The address spaces this input configures: always A and B, plus C when the
third subject's tables are present. -/
def configuredSpaces (roots : Roots) : List Space :=
  if roots.hasThird then [.subjectA, .subjectB, .subjectC] else [.subjectA, .subjectB]

def spaceConfigured (roots : Roots) (space : Space) : Bool :=
  (configuredSpaces roots).contains space

/-- The third root differs from both A and B.  `tableFramesDistinct` implies
this too; checking it first keeps the `equalRoots` diagnostic for roots. -/
def thirdRootDistinct (roots : Roots) : Bool :=
  match roots.subjectC with
  | none => true
  | some root => root != roots.subjectA && root != roots.subjectB

def hasRegion (input : Input) (space : Space) (policy : PolicyRegion) (owner : Owner) : Bool :=
  input.regions.any fun region =>
    region.space == space && region.policy == policy && region.owner == owner

/-- The Phase 2 plan is not an optional list: every configured root must
contain the reviewed supervisor classes and its subject-specific user text
and stack. -/
def requiredCoverage (input : Input) : Bool :=
  (configuredSpaces input.roots).all fun space =>
    hasRegion input space .kernelText .supervisor &&
    hasRegion input space .kernelData .supervisor &&
    hasRegion input space .kernelStack .supervisor &&
    hasRegion input space .pageTables .supervisor &&
    match space with
    | .subjectA =>
        hasRegion input space .userText .subjectA && hasRegion input space .userStack .subjectA
    | .subjectB =>
        hasRegion input space .userText .subjectB && hasRegion input space .userStack .subjectB
    | .subjectC =>
        hasRegion input space .userText .subjectC && hasRegion input space .userStack .subjectC

def wxSafe (leaves : List CompiledLeaf) : Bool :=
  leaves.all fun entry => !entry.leaf.writable || entry.leaf.noExecute

def ownershipSafe (leaves : List CompiledLeaf) : Bool :=
  leaves.all fun entry =>
    (!entry.leaf.user && entry.owner == .supervisor) ||
    (entry.leaf.user &&
      ((entry.space == .subjectA && entry.owner == .subjectA) ||
       (entry.space == .subjectB && entry.owner == .subjectB) ||
       (entry.space == .subjectC && entry.owner == .subjectC)))

/-- User-owned frames are not shared across the subject views.  Supervisor
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
      (!a.leaf.user && !b.leaf.user && a.space != b.space &&
        a.page == b.page && a.policy == b.policy)

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
  (configuredSpaces input.roots).all fun space =>
    let declared := leaves.filter fun entry =>
      entry.space == space && entry.policy == .pageTables
    declared.all (fun entry => entry.page == entry.leaf.frame && frames.contains entry.leaf.frame) &&
      frames.all fun frame => declared.any fun entry => entry.leaf.frame == frame

/-- Device windows and RAM never alias: every `.mmioWindow` leaf targets a
frame at or beyond the identity-mapped boot window, and every other class stays
inside it.  Identity classes already satisfy the bound by construction; this
makes the confinement explicit for the one reviewed non-identity class. -/
def mmioFramesOutsideRam (leaves : List CompiledLeaf) : Bool :=
  leaves.all fun entry =>
    if entry.policy == .mmioWindow then decide (entry.leaf.frame ≥ supportedPathPages)
    else decide (entry.leaf.frame < supportedPathPages)

/-- DMA-remapping (VT-d root/context) table frames are identity-mapped and
covered by the validated boot reservation overlay, so the same authority that
excludes CPU page tables from allocation also excludes the remapping tables. -/
def remappingFramesReserved (input : Input) (leaves : List CompiledLeaf) : Bool :=
  match input.reservationResult with
  | none => leaves.all fun entry => entry.policy != .remappingTables
  | some reserved => leaves.all fun entry =>
      entry.policy != .remappingTables ||
        (entry.page == entry.leaf.frame &&
          BootReservation.reservedBy reserved.intervals entry.leaf.frame)

/-- Every leaf belongs to an address space whose root the input supplies, so a
two-subject image cannot carry third-subject leaves with no root behind them. -/
def leavesConfigured (roots : Roots) (leaves : List CompiledLeaf) : Bool :=
  leaves.all fun entry => spaceConfigured roots entry.space

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
    | .kernelText | .kernelData | .kernelStack | .pageTables
    | .mmioWindow | .remappingTables => !entry.leaf.user
    | .userText | .userStack => true

/-- The permission profiles called out by the boot policy are checked
explicitly, in addition to the generic W^X and policy-refinement checks. -/
def policyAttributesSafe (leaves : List CompiledLeaf) : Bool :=
  leaves.all fun entry =>
    match entry.policy with
    | .kernelText => !entry.leaf.user && !entry.leaf.writable && !entry.leaf.noExecute
    | .kernelData | .kernelStack | .pageTables | .mmioWindow | .remappingTables =>
        !entry.leaf.user && entry.leaf.writable && entry.leaf.noExecute
    | .userText => entry.leaf.user && !entry.leaf.writable && !entry.leaf.noExecute
    | .userStack => entry.leaf.user && entry.leaf.writable && entry.leaf.noExecute

structure Plan where
  private mk ::
  private roots : Roots
  private leaves : List CompiledLeaf
  private rootsDistinct : roots.subjectA ≠ roots.subjectB
  private thirdRootFresh : thirdRootDistinct roots = true
  private configured : leavesConfigured roots leaves = true
  private noDuplicates : noDuplicateLeaves leaves = true
  private wx : wxSafe leaves = true
  private ownership : ownershipSafe leaves = true
  private userViewsSeparated : userViewsSeparated leaves = true
  private liveTableFrames : List PhysicalFrame
  private liveTablesChecked : userAvoidsTableFrames liveTableFrames leaves = true
  private structural : structurallySafe leaves = true
  private policyRefinement : refinesPolicy leaves = true
  private supervisorOnly : supervisorConfinement leaves = true
  private policyAttributes : policyAttributesSafe leaves = true
  private tableFramesReserved : Bool
  private reservationsChecked : tableFramesReserved = true
  private tableFramesValid : Bool
  private tableFramesValidityChecked : tableFramesValid = true
  private tableFramesUnique : Bool
  private tableFramesUniquenessChecked : tableFramesUnique = true
  /-- Exact ancestor layout and validated reservation result accepted by
  `compile`. Live-table validation must not take either from a second input. -/
  private compiledAncestors : AncestorPaths
  private compiledReservationResult : Option BootReservation.Result
  /-- Proof-carrying commitment to the exact ancestor layout accepted by
  `compile`. Updating `compiledAncestors` alone cannot produce another `Plan`. -/
  private compiledLayoutBound : layoutFrames roots compiledAncestors = liveTableFrames
  private mmioConfined : mmioFramesOutsideRam leaves = true
  private remappingReservedFlag : Bool
  private remappingReservationChecked : remappingReservedFlag = true

/-- Public, read-only projections used by return-policy consumers.  A `Plan`
can only be constructed by `compile`, so these values retain its checks. -/
def Plan.configuredRoot (plan : Plan) : Space → Option PhysicalFrame
  | .subjectA => some plan.roots.subjectA
  | .subjectB => some plan.roots.subjectB
  | .subjectC => plan.roots.subjectC

/-- Total root projection.  An unconfigured third space has no root; it
projects to `physicalFrameLimit`, the first frame no live root can occupy
(`tableFramesRepresentable`).  Consumers that may name the third space use
`configuredRoot`; the decoded-root validator rejects an unconfigured space. -/
def Plan.rootFrame (plan : Plan) (space : Space) : PhysicalFrame :=
  (plan.configuredRoot space).getD physicalFrameLimit

/-- Whether the accepted plan configures the third subject's address space. -/
def Plan.hasThirdSubject (plan : Plan) : Bool := plan.roots.hasThird

def Plan.hasPolicyLeaf (plan : Plan) (space : Space) (page : Nat)
    (policy : PolicyRegion) (owner : Owner) : Bool :=
  plan.leaves.any fun leaf =>
    leaf.space == space && leaf.page == page && leaf.policy == policy && leaf.owner == owner

/-- Query the physical frame as well as the reviewed policy.  This projection
lets a consumer compare a compiled leaf with a separately modeled live map
without exposing `Plan`'s constructor or unchecked leaf list. -/
def Plan.hasPolicyLeafAtFrame (plan : Plan) (space : Space) (page : Nat)
    (frame : X86PageTable.PhysicalFrame) (policy : PolicyRegion) (owner : Owner) : Bool :=
  plan.leaves.any fun leaf =>
    leaf.space == space && leaf.page == page && leaf.leaf.frame == frame &&
      leaf.policy == policy && leaf.owner == owner

/-- Total compiler/checker for the deliberately finite supported subset. -/
def compile (input : Input) : Except Error Plan := do
  if !input.nxe then throw .missingNXE
  if input.reservationResult.isNone then throw .missingValidatedReservation
  if !thirdSubjectConsistent input then throw .unconfiguredSpace
  if !input.regions.all (fun region => spaceConfigured input.roots region.space) then
    throw .unconfiguredSpace
  if hroot : input.roots.subjectA == input.roots.subjectB then throw .equalRoots else
   if hthird : !thirdRootDistinct input.roots then throw .equalRoots else
    if hvalid : !tableFramesRepresentable input then throw .invalidTableFrame else
     if hunique : !tableFramesDistinct input then throw .duplicateTableFrame else
      if hreserved : !tableFramesReserved input then throw .unreservedTableFrame else
      let leaves <- input.regions.flatMapM compileRegion
      if !requiredCoverage input then throw .missingRequiredRegion
      if !tableManifestMatches input leaves then throw .tableManifestMismatch
      if hconfigured : !leavesConfigured input.roots leaves then throw .unconfiguredSpace else
      if hduplicates : noDuplicateLeaves leaves then
        if hwx : wxSafe leaves then
          if !physicalAliasesSafe leaves then throw .unsafePhysicalAlias else
          if hmmio : mmioFramesOutsideRam leaves then
           if hremapping : remappingFramesReserved input leaves then
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
                        have hthirdFresh : thirdRootDistinct input.roots = true := by
                          simpa using hthird
                        have hleavesConfigured : leavesConfigured input.roots leaves = true := by
                          simpa using hconfigured
                        pure ⟨input.roots, leaves, hroots, hthirdFresh, hleavesConfigured,
                          hduplicates, hwx, hownership, hseparated,
                          tableFrames input, hliveTables,
                          hstructural, hrefines, hsupervisor, hattributes,
                          tableFramesReserved input, htables,
                          tableFramesRepresentable input, hframes,
                          tableFramesDistinct input, hframesUnique,
                          input.ancestors, input.reservationResult, rfl,
                          hmmio, remappingFramesReserved input leaves, hremapping⟩
                      else throw .incompatibleOverlap
                    else throw .wrongOwner
                  else throw .incompatibleOverlap
                else throw .nonCanonical
              else throw .incompatibleOverlap
             else throw .incompatibleOverlap
            else throw .incompatibleOverlap
           else throw .unreservedRemappingFrame
          else throw .mmioAliasesRam
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

/-- A configured third root is a separate map from both A and B. -/
theorem accepted_third_root_distinct input plan (_h : compile input = .ok plan)
    root (hroot : plan.roots.subjectC = some root) :
    root ≠ plan.roots.subjectA ∧ root ≠ plan.roots.subjectB := by
  have hfresh := plan.thirdRootFresh
  simp only [thirdRootDistinct, hroot, Bool.and_eq_true, bne_iff_ne, ne_eq] at hfresh
  exact hfresh

/-- Every leaf of an accepted plan lies in an address space the input
configured. -/
theorem accepted_leaves_configured input plan (_h : compile input = .ok plan) :
    leavesConfigured plan.roots plan.leaves = true := plan.configured

/-- A plan accepted without a third root has no third-subject leaf. -/
theorem accepted_two_subject_has_no_third_leaf input plan
    (_h : compile input = .ok plan) (htwo : plan.roots.subjectC = none) :
    plan.leaves.all (fun entry => entry.space != .subjectC) = true := by
  have hconfigured := plan.configured
  simp only [leavesConfigured, List.all_eq_true] at hconfigured ⊢
  intro entry hmem
  have hentry := hconfigured entry hmem
  simp only [spaceConfigured, configuredSpaces, Roots.hasThird, htwo, Option.isSome_none,
    Bool.false_eq_true, ↓reduceIte] at hentry
  cases hspace : entry.space <;> rw [hspace] at hentry <;> revert hentry <;> decide

theorem accepted_no_duplicate_leaf input plan (_h : compile input = .ok plan) :
    noDuplicateLeaves plan.leaves = true := plan.noDuplicates

theorem accepted_table_frames_reserved input plan (_h : compile input = .ok plan) :
    plan.tableFramesReserved = true := plan.reservationsChecked

theorem accepted_table_frames_representable input plan (_h : compile input = .ok plan) :
    plan.tableFramesValid = true := plan.tableFramesValidityChecked

theorem accepted_table_frames_distinct input plan (_h : compile input = .ok plan) :
    plan.tableFramesUnique = true := plan.tableFramesUniquenessChecked

theorem accepted_compiled_layout_bound input plan (_h : compile input = .ok plan) :
    layoutFrames plan.roots plan.compiledAncestors = plan.liveTableFrames :=
  plan.compiledLayoutBound

theorem accepted_mmio_confined input plan (_h : compile input = .ok plan) :
    mmioFramesOutsideRam plan.leaves = true := plan.mmioConfined

theorem accepted_remapping_frames_reserved input plan (_h : compile input = .ok plan) :
    plan.remappingReservedFlag = true := plan.remappingReservationChecked

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
  /-- Complete decoded ancestor tables. Keeping all 512 slots makes both an
  extra present pointer and a pointer emitted at the wrong index observable. -/
  pml4Entries : List DecodedAncestor
  pdptEntries : List DecodedAncestor
  pdEntries : List DecodedAncestor
  leaves : List DecodedLeaf
  deriving BEq, DecidableEq, Repr

inductive ReportError where
  | wrongRoot | wrongAncestor | unreservedAncestor | duplicateActual
  | missingLeaf | unexpectedLeaf | mismatchedLeaf
  deriving BEq, DecidableEq, Repr

/-- The root a report for `space` must name; `none` for an unconfigured third
space, which no report can match. -/
def expectedRoot (plan : Plan) (space : Space) : Option PhysicalFrame :=
  plan.configuredRoot space

def legalDecodedAncestor (entry : DecodedAncestor) : Bool :=
  entry.present && entry.writable && entry.user && !entry.noExecute && !entry.hugePage &&
    entry.reservedBitsClear &&
    representableFrame entry.nextFrame

def decodedAncestorReserved (plan : Plan) (entry : DecodedAncestor) : Bool :=
  match plan.compiledReservationResult with
  | none => false
  | some reserved => reservedAsPageTable reserved.intervals entry.nextFrame

def expectedAncestorFrames (plan : Plan) : Space → Option AncestorFrames
  | .subjectA => some plan.compiledAncestors.subjectA
  | .subjectB => some plan.compiledAncestors.subjectB
  | .subjectC => plan.compiledAncestors.subjectC

def absentDecodedAncestor : DecodedAncestor :=
  { present := false, writable := false, user := false, noExecute := false,
    hugePage := false, reservedBitsClear := true, nextFrame := 0 }

def expectedDecodedAncestor (frame : PhysicalFrame) : DecodedAncestor :=
  { present := true, writable := true, user := true, noExecute := false,
    hugePage := false, reservedBitsClear := true, nextFrame := frame }

def singletonAncestorTable (frame : PhysicalFrame) : List DecodedAncestor :=
  (List.range 512).map fun index =>
    if index == 0 then expectedDecodedAncestor frame else absentDecodedAncestor

def pdAncestorTable (frames : List PhysicalFrame) : List DecodedAncestor :=
  (List.range 512).map fun index =>
    match frames[index]? with
    | some frame => expectedDecodedAncestor frame
    | none => absentDecodedAncestor

/-- Match every ancestor-table slot, not only the selected pointers. This binds
the decoded pointer to its paging index and proves absence for all other slots. -/
def ancestorTablesMatch (plan : Plan) (report : DecodedRoot) : Bool :=
  match expectedAncestorFrames plan report.space with
  | none => false
  | some expected =>
    report.pml4Entries == singletonAncestorTable expected.pdpt &&
      report.pdptEntries == singletonAncestorTable expected.pd &&
      report.pdEntries == pdAncestorTable expected.pts

def decodedAncestorTableReserved (plan : Plan) (entries : List DecodedAncestor) : Bool :=
  entries.all fun entry => !entry.present || decodedAncestorReserved plan entry

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
def validateDecodedRoot (plan : Plan) (report : DecodedRoot) :
    Except ReportError Unit := do
  if expectedRoot plan report.space != some report.selectedRoot then throw .wrongRoot
  if !ancestorTablesMatch plan report then throw .wrongAncestor
  if !(decodedAncestorTableReserved plan report.pml4Entries &&
      decodedAncestorTableReserved plan report.pdptEntries &&
      decodedAncestorTableReserved plan report.pdEntries) then throw .unreservedAncestor
  if !decodedNoDuplicates report.leaves then throw .duplicateActual
  for actual in report.leaves do
    if actual.page >= supportedPathPages then throw .unexpectedLeaf
    if actual.leaf != expectedDecodedAt plan report.space actual.page then
      throw .mismatchedLeaf
  if report.leaves.length != supportedPathPages then throw .missingLeaf

theorem decoded_validation_deterministic plan report first second
    (hfirst : validateDecodedRoot plan report = first)
    (hsecond : validateDecodedRoot plan report = second) : first = second := by
  rw [hfirst] at hsecond
  exact hsecond

/-- Require one report for each address space, rather than allowing an
integration harness to validate the same selected root twice. -/
def validateDecodedPair (plan : Plan)
    (subjectA subjectB : DecodedRoot) : Except ReportError Unit := do
  if subjectA.space != .subjectA || subjectB.space != .subjectB then throw .wrongRoot
  validateDecodedRoot plan subjectA
  validateDecodedRoot plan subjectB

/-- The three-subject form: one report per configured space.  A plan without
a third root rejects every third report, so this cannot pass on a
two-subject plan. -/
def validateDecodedTriple (plan : Plan)
    (subjectA subjectB subjectC : DecodedRoot) : Except ReportError Unit := do
  if subjectC.space != .subjectC then throw .wrongRoot
  validateDecodedPair plan subjectA subjectB
  validateDecodedRoot plan subjectC

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
   { identity := .ordinaryEntryGuard, start := 6 * pageBytes, length := pageBytes,
     lifetime := .permanent },
   { identity := .ordinaryEntryStack, start := 7 * pageBytes, length := pageBytes,
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
/-- Supervisor sharing is limited to the same reviewed virtual mapping across
the two roots; an extra same-root alias is not part of the canonical plan. -/
example : rejectedAs
    { sampleInput with regions := sampleRegions ++
        [{ space := .subjectA, virtualStart := 300 * pageBytes,
           byteLength := pageBytes, physicalStart := 2 * pageBytes,
           policy := .kernelData, owner := .supervisor }] }
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

/-- The reviewed device-window and remapping-table classes: a shared supervisor
window onto an out-of-RAM device frame plus identity-mapped reserved VT-d table
frames inside the validated image reservation. -/
def deviceWindowRegions : List Region :=
  [{ space := .subjectA, virtualStart := 40 * pageBytes, byteLength := pageBytes,
     physicalStart := 0xFED90000, policy := .mmioWindow, owner := .supervisor },
   { space := .subjectB, virtualStart := 40 * pageBytes, byteLength := pageBytes,
     physicalStart := 0xFED90000, policy := .mmioWindow, owner := .supervisor },
   { space := .subjectA, virtualStart := 8 * pageBytes, byteLength := 2 * pageBytes,
     physicalStart := 8 * pageBytes, policy := .remappingTables, owner := .supervisor },
   { space := .subjectB, virtualStart := 8 * pageBytes, byteLength := 2 * pageBytes,
     physicalStart := 8 * pageBytes, policy := .remappingTables, owner := .supervisor }]

def deviceWindowInput : Input :=
  { sampleInput with regions := sampleRegions ++ deviceWindowRegions }

example : (match compile deviceWindowInput with | .ok _ => true | .error _ => false) = true := by
  native_decide
/-- A device window pointed back into boot RAM is rejected. -/
example : rejectedAs
    { deviceWindowInput with regions := sampleRegions ++ deviceWindowRegions.map fun region =>
        if region.policy == .mmioWindow then { region with physicalStart := 50 * pageBytes }
        else region }
    .mmioAliasesRam = true := by native_decide
/-- A RAM policy class pointed at a device frame is rejected. -/
example : rejectedAs
    { sampleInput with regions := sampleRegions ++
        [{ space := .subjectA, virtualStart := 41 * pageBytes, byteLength := pageBytes,
           physicalStart := 0xFEE00000, policy := .kernelData, owner := .supervisor }] }
    .mmioAliasesRam = true := by native_decide
/-- Remapping-table frames outside every validated reservation are rejected. -/
example : rejectedAs
    { sampleInput with regions := sampleRegions ++
        [{ space := .subjectA, virtualStart := 35 * pageBytes, byteLength := pageBytes,
           physicalStart := 35 * pageBytes, policy := .remappingTables, owner := .supervisor }] }
    .unreservedRemappingFrame = true := by native_decide
/-- Remapping-table frames must be identity-mapped at their boot addresses. -/
example : rejectedAs
    { sampleInput with regions := sampleRegions ++
        [{ space := .subjectA, virtualStart := 8 * pageBytes, byteLength := pageBytes,
           physicalStart := 9 * pageBytes, policy := .remappingTables, owner := .supervisor }] }
    .unreservedRemappingFrame = true := by native_decide
/-- Neither reviewed device class can be user-owned. -/
example : rejectedAs
    { sampleInput with regions := sampleRegions ++
        [{ space := .subjectA, virtualStart := 40 * pageBytes, byteLength := pageBytes,
           physicalStart := 0xFED90000, policy := .mmioWindow, owner := .subjectA }] }
    .wrongOwner = true := by native_decide
example : rejectedAs
    { sampleInput with regions := sampleRegions ++
        [{ space := .subjectA, virtualStart := 8 * pageBytes, byteLength := pageBytes,
           physicalStart := 8 * pageBytes, policy := .remappingTables, owner := .subjectA }] }
    .wrongOwner = true := by native_decide

def decodedAncestor (frame : Nat) : DecodedAncestor :=
  expectedDecodedAncestor frame

def decodedReportWithAncestors (plan : Plan) (ancestors : AncestorPaths)
    (space : Space) : DecodedRoot :=
  let expected := match space with
    | .subjectA => ancestors.subjectA
    | .subjectB => ancestors.subjectB
    | .subjectC => ancestors.subjectC.getD ancestors.subjectA
  { space, selectedRoot := plan.rootFrame space,
    pml4Entries := singletonAncestorTable expected.pdpt,
    pdptEntries := singletonAncestorTable expected.pd,
    pdEntries := pdAncestorTable expected.pts,
    leaves := (List.range supportedPathPages).map fun page =>
      { page, leaf := expectedDecodedAt plan space page } }

def decodedReport (plan : Plan) (space : Space) : DecodedRoot :=
  decodedReportWithAncestors plan plan.compiledAncestors space

def sampleReportCheck (mutate : DecodedRoot → DecodedRoot) : Except ReportError Unit :=
  match compile sampleInput with
  | .error _ => .error .missingLeaf
  | .ok plan => validateDecodedRoot plan (mutate (decodedReport plan .subjectA))

def unchangedReport (report : DecodedRoot) : DecodedRoot := report
def wrongRootReport (report : DecodedRoot) : DecodedRoot := { report with selectedRoot := 11 }
def wrongAncestorReport (report : DecodedRoot) : DecodedRoot :=
  { report with pdEntries := report.pdEntries.modify 0 fun e => { e with present := false } }
def wrongAncestorWritableReport (report : DecodedRoot) : DecodedRoot :=
  { report with pdEntries := report.pdEntries.modify 0 fun e => { e with writable := false } }
def wrongAncestorUserReport (report : DecodedRoot) : DecodedRoot :=
  { report with pdEntries := report.pdEntries.modify 0 fun e => { e with user := false } }
def wrongAncestorReservedBitsReport (report : DecodedRoot) : DecodedRoot :=
  { report with pdEntries := report.pdEntries.modify 0 fun e => { e with reservedBitsClear := false } }
def wrongAncestorNXReport (report : DecodedRoot) : DecodedRoot :=
  { report with pdEntries := report.pdEntries.modify 7 fun e => { e with noExecute := true } }
def wrongAncestorHugePageReport (report : DecodedRoot) : DecodedRoot :=
  { report with pdEntries := report.pdEntries.modify 7 fun e => { e with hugePage := true } }
def wrongAncestorPointerReport (report : DecodedRoot) : DecodedRoot :=
  { report with pdEntries := report.pdEntries.modify 7 fun e => { e with nextFrame := e.nextFrame + 1 } }
def extraPml4AncestorReport (report : DecodedRoot) : DecodedRoot :=
  { report with pml4Entries := report.pml4Entries.modify 1 fun _ => decodedAncestor 31 }
def misplacedPml4AncestorReport (report : DecodedRoot) : DecodedRoot :=
  { report with pml4Entries :=
      (report.pml4Entries.modify 0 fun _ => absentDecodedAncestor).modify 1 fun _ =>
        decodedAncestor 12 }
def extraPdptAncestorReport (report : DecodedRoot) : DecodedRoot :=
  { report with pdptEntries := report.pdptEntries.modify 1 fun _ => decodedAncestor 31 }
def misplacedPdptAncestorReport (report : DecodedRoot) : DecodedRoot :=
  { report with pdptEntries :=
      (report.pdptEntries.modify 0 fun _ => absentDecodedAncestor).modify 1 fun _ =>
        decodedAncestor 13 }
def extraPdAncestorReport (report : DecodedRoot) : DecodedRoot :=
  { report with pdEntries := report.pdEntries.modify bootPtCount fun _ => decodedAncestor 31 }
def misplacedPdAncestorReport (report : DecodedRoot) : DecodedRoot :=
  { report with pdEntries :=
      (report.pdEntries.modify 0 fun _ => absentDecodedAncestor).modify bootPtCount fun _ =>
        decodedAncestor 14 }
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
example : reportRejectedAs (sampleReportCheck extraPml4AncestorReport) .wrongAncestor = true := by
  native_decide
example : reportRejectedAs (sampleReportCheck misplacedPml4AncestorReport) .wrongAncestor = true := by
  native_decide
example : reportRejectedAs (sampleReportCheck extraPdptAncestorReport) .wrongAncestor = true := by
  native_decide
example : reportRejectedAs (sampleReportCheck misplacedPdptAncestorReport) .wrongAncestor = true := by
  native_decide
example : reportRejectedAs (sampleReportCheck extraPdAncestorReport) .wrongAncestor = true := by
  native_decide
example : reportRejectedAs (sampleReportCheck misplacedPdAncestorReport) .wrongAncestor = true := by
  native_decide
/-- A report produced from a different reserved input cannot substitute an
ancestor that aliases one of the compiled plan's PT frames. -/
def crossInputAliasedAncestorCheck : Except ReportError Unit :=
  match compile sampleInput with
  | .error _ => .error .missingLeaf
  | .ok plan =>
      let substituted :=
        { sampleInput.ancestors with
          subjectA :=
            { sampleInput.ancestors.subjectA with
              pdpt := sampleInput.ancestors.subjectA.pts[7]! } }
      validateDecodedRoot plan (decodedReportWithAncestors plan substituted .subjectA)

example : reportRejectedAs crossInputAliasedAncestorCheck .wrongAncestor = true := by
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
  | .ok plan => validateDecodedPair plan
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
      validateDecodedPair plan
        { reportA with leaves := reportA.leaves.filter (fun entry => !entry.leaf.user) ++ userB }
        { reportB with leaves := reportB.leaves.filter (fun entry => !entry.leaf.user) ++ userA }

example : reportRejectedAs swappedUserLeavesCheck .mismatchedLeaf = true := by native_decide

/-! ## Three-subject fixtures (issue #472)

The same sample with a third subject C: eleven more table frames (32 to 42)
inside an enlarged page-table reservation, C's own supervisor view, and C's
user text and stack on frames no other subject maps. -/

def threeSubjectReservationManifest : List Reservation :=
  sampleReservationManifest.map fun reservation =>
    if reservation.identity == .loadedImage then
      { reservation with length := 41 * pageBytes }
    else if reservation.identity == .pageTables then
      { reservation with length := 33 * pageBytes }
    else reservation

def threeSubjectReservationResult : Option BootReservation.Result :=
  (initializeAllocator
    (BootMemoryMap.mkHandoff [{ base := 0, length := 50 * pageBytes, kind := .usable }])
    threeSubjectReservationManifest).toOption

def threeSubjectRegions : List Region :=
  (sampleRegions.map fun region =>
    if region.policy == .pageTables then { region with byteLength := 33 * pageBytes }
    else region) ++
  [{ space := .subjectC, virtualStart := pageBytes, byteLength := pageBytes,
     physicalStart := pageBytes, policy := .kernelText, owner := .supervisor },
   { space := .subjectC, virtualStart := 2 * pageBytes, byteLength := pageBytes,
     physicalStart := 2 * pageBytes, policy := .kernelData, owner := .supervisor },
   { space := .subjectC, virtualStart := 3 * pageBytes, byteLength := pageBytes,
     physicalStart := 3 * pageBytes, policy := .kernelStack, owner := .supervisor },
   { space := .subjectC, virtualStart := 10 * pageBytes, byteLength := 33 * pageBytes,
     physicalStart := 10 * pageBytes, policy := .pageTables, owner := .supervisor },
   { space := .subjectC, virtualStart := 100 * pageBytes, byteLength := pageBytes,
     physicalStart := 300 * pageBytes, policy := .userText, owner := .subjectC },
   { space := .subjectC, virtualStart := 101 * pageBytes, byteLength := pageBytes,
     physicalStart := 301 * pageBytes, policy := .userStack, owner := .subjectC }]

def threeSubjectInput : Input :=
  { roots := { subjectA := 10, subjectB := 11, subjectC := some 32 }, nxe := true,
    ancestors :=
      { subjectA := { pdpt := 12, pd := 13, pts := List.range 8 |>.map (14 + ·) },
        subjectB := { pdpt := 22, pd := 23, pts := List.range 8 |>.map (24 + ·) },
        subjectC := some { pdpt := 33, pd := 34, pts := List.range 8 |>.map (35 + ·) } },
    regions := threeSubjectRegions, reservationResult := threeSubjectReservationResult }

/-- Replace C's user leaves (text, stack) with `textFrame`/`stackFrame`. -/
def threeSubjectWithUserFrames (textFrame stackFrame : Nat) : Input :=
  { threeSubjectInput with regions := threeSubjectRegions.map fun region =>
      if region.space == .subjectC && region.policy == .userText then
        { region with physicalStart := textFrame * pageBytes }
      else if region.space == .subjectC && region.policy == .userStack then
        { region with physicalStart := stackFrame * pageBytes }
      else region }

example : (match compile threeSubjectInput with | .ok _ => true | .error _ => false) = true := by
  native_decide
/-- The accepted three-subject plan configures C and keeps its root apart. -/
example : (match compile threeSubjectInput with
    | .ok plan => plan.hasThirdSubject && plan.configuredRoot .subjectC == some 32
    | .error _ => false) = true := by native_decide
/-- A two-subject plan configures no third space. -/
example : (match compile sampleInput with
    | .ok plan => !plan.hasThirdSubject && plan.configuredRoot .subjectC == none
    | .error _ => false) = true := by native_decide
/-- A third root without third ancestors (or the reverse) is not a layout. -/
example : rejectedAs { threeSubjectInput with
    ancestors := { threeSubjectInput.ancestors with subjectC := none } }
    .unconfiguredSpace = true := by native_decide
example : rejectedAs { threeSubjectInput with
    roots := { threeSubjectInput.roots with subjectC := none } }
    .unconfiguredSpace = true := by native_decide
/-- Third-subject leaves cannot ride along in a two-subject input. -/
example : rejectedAs
    { sampleInput with
      regions := sampleRegions ++ threeSubjectRegions.filter fun region =>
        region.space == .subjectC }
    .unconfiguredSpace = true := by native_decide
/-- The third root must differ from A's and B's. -/
example : rejectedAs { threeSubjectInput with
    roots := { threeSubjectInput.roots with subjectC := some 10 } }
    .equalRoots = true := by native_decide
example : rejectedAs { threeSubjectInput with
    roots := { threeSubjectInput.roots with subjectC := some 11 } }
    .equalRoots = true := by native_decide
/-- A third ancestor may not reuse another subject's table frame. -/
example : rejectedAs { threeSubjectInput with
    ancestors := { threeSubjectInput.ancestors with
      subjectC := some { pdpt := 33, pd := 24, pts := List.range 8 |>.map (35 + ·) } } }
    .duplicateTableFrame = true := by native_decide
/-- Third table frames outside the page-table reservation are rejected. -/
example : rejectedAs { threeSubjectInput with reservationResult := sampleReservationResult }
    .unreservedTableFrame = true := by native_decide
/-- C must have its own user text and stack. -/
example : rejectedAs { threeSubjectInput with regions := threeSubjectRegions.filter fun region =>
    !(region.space == .subjectC && region.policy == .userStack) }
    .missingRequiredRegion = true := by native_decide
/-- A user page in C's space must be owned by C. -/
example : rejectedAs { threeSubjectInput with regions := threeSubjectRegions.map fun region =>
    if region.space == .subjectC && region.policy == .userText then
      { region with owner := .subjectA }
    else region }
    .wrongOwner = true := by native_decide
/-- C's user leaves cannot alias A's user frame, B's user frame, or a live
table frame (here C's own root). -/
example : rejectedAs (threeSubjectWithUserFrames 100 301) .unsafePhysicalAlias = true := by
  native_decide
example : rejectedAs (threeSubjectWithUserFrames 300 201) .unsafePhysicalAlias = true := by
  native_decide
example : rejectedAs (threeSubjectWithUserFrames 32 301) .unsafePhysicalAlias = true := by
  native_decide
/-- C's view must declare every live table frame, including A's and B's. -/
example : rejectedAs { threeSubjectInput with regions := threeSubjectRegions.map fun region =>
    if region.space == .subjectC && region.policy == .pageTables then
      { region with byteLength := 22 * pageBytes }
    else region }
    .tableManifestMismatch = true := by native_decide

def threeSubjectTripleCheck (mutateC : DecodedRoot → DecodedRoot) :
    Except ReportError Unit :=
  match compile threeSubjectInput with
  | .error _ => .error .missingLeaf
  | .ok plan => validateDecodedTriple plan (decodedReport plan .subjectA)
      (decodedReport plan .subjectB) (mutateC (decodedReport plan .subjectC))

example : reportAccepted (threeSubjectTripleCheck unchangedReport) = true := by native_decide
example : reportRejectedAs (threeSubjectTripleCheck wrongRootReport) .wrongRoot = true := by
  native_decide
example : reportRejectedAs (threeSubjectTripleCheck wrongAncestorPointerReport)
    .wrongAncestor = true := by native_decide
example : reportRejectedAs (threeSubjectTripleCheck flippedUserReport)
    .mismatchedLeaf = true := by native_decide
example : reportRejectedAs
    (threeSubjectTripleCheck fun report => { report with space := .subjectB })
    .wrongRoot = true := by native_decide

/-- A two-subject plan has no third root, so no third report validates. -/
def twoSubjectThirdReportCheck : Except ReportError Unit :=
  match compile sampleInput with
  | .error _ => .error .missingLeaf
  | .ok plan => validateDecodedRoot plan (decodedReport plan .subjectC)

example : reportRejectedAs twoSubjectThirdReportCheck .wrongRoot = true := by native_decide

/-- C's user leaves are absent from A's view: moving them there is caught. -/
def threeSubjectLeakedUserLeavesCheck : Except ReportError Unit :=
  match compile threeSubjectInput with
  | .error _ => .error .missingLeaf
  | .ok plan =>
      let reportA := decodedReport plan .subjectA
      let reportC := decodedReport plan .subjectC
      let userC := reportC.leaves.filter fun entry => entry.leaf.user
      validateDecodedTriple plan
        { reportA with leaves := reportA.leaves.filter (fun entry => !entry.leaf.user) ++ userC }
        (decodedReport plan .subjectB) reportC

example : reportRejectedAs threeSubjectLeakedUserLeavesCheck .mismatchedLeaf = true := by
  native_decide

end LeanOS.BootPageTablePlan
