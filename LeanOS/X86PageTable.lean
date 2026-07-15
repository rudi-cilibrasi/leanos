import LeanOS.VirtualMapping

/-!
# Executable x86-64 page-table refinement

This model deliberately supports only 4 KiB leaves in the lower canonical
half, with four present ancestors.  It models the effective U/S, R/W and NX
checks independently from `VirtualMapping.translate`.
-/
namespace LeanOS.X86PageTable

set_option linter.unusedSimpArgs false

open LeanOS
open LeanOS.VirtualMapping

abbrev PhysicalFrame := FrameAllocator.FrameId

def entriesPerTable : Nat := 512
def pageBytes : Nat := 4096
def lowerCanonicalPages : Nat := 2 ^ 35
def physicalFrameLimit : Nat := 2 ^ 40

def canonicalPage (page : VirtualPage) : Bool := page < lowerCanonicalPages
def representableFrame (frame : PhysicalFrame) : Bool := frame < physicalFrameLimit

structure Ancestor where
  present : Bool
  writable : Bool
  user : Bool
  deriving BEq, DecidableEq, Repr

structure Leaf where
  frame : PhysicalFrame
  present : Bool
  writable : Bool
  user : Bool
  noExecute : Bool
  reservedBitsClear : Bool
  deriving BEq, DecidableEq, Repr

structure PageTable where
  pml4 : Ancestor
  pdpt : Ancestor
  pd : Ancestor
  leaf : VirtualPage → Option Leaf

inductive UserAccess where | read | write | execute
  deriving BEq, DecidableEq, Repr

inductive WalkError where
  | nonCanonical | notPresent | supervisor | notWritable | noExecute
  | smep | smap | reservedBits | frameOutOfRange
  deriving BEq, DecidableEq, Repr

inductive Privilege where | supervisor | user
  deriving BEq, DecidableEq, Repr

inductive AccessKind where | read | write | execute
  deriving BEq, DecidableEq, Repr

/-- Exactly the control state used by the LeanOS paging policy. `ac` is only
an SMAP override; it has no effect on user accesses or instruction fetches. -/
structure AccessContext where
  privilege : Privilege
  kind : AccessKind
  writeProtect : Bool
  nxEnable : Bool
  smep : Bool
  smap : Bool
  ac : Bool
  deriving BEq, DecidableEq, Repr

def legalAncestor (entry : Ancestor) : Prop :=
  entry.present = true ∧ entry.user = true

def legalLeaf (leaf : Leaf) : Prop :=
  leaf.present = true ∧ leaf.user = true ∧ leaf.reservedBitsClear = true ∧
    representableFrame leaf.frame = true

def StructurallyValid (table : PageTable) : Prop :=
  legalAncestor table.pml4 ∧ legalAncestor table.pdpt ∧ legalAncestor table.pd ∧
    ∀ page leaf, table.leaf page = some leaf → canonicalPage page = true ∧ legalLeaf leaf

def ancestorsWritable (table : PageTable) : Bool :=
  table.pml4.writable && table.pdpt.writable && table.pd.writable

def ancestorsUser (table : PageTable) : Bool :=
  table.pml4.user && table.pdpt.user && table.pd.user

/-- Executable classification for CPL, CR0.WP, EFER.NXE, CR4.SMEP/SMAP and
the EFLAGS.AC copy-window override. Permission bits are conjoined at all four
levels. The table is assumed not to mutate during a classification. -/
def classify (table : PageTable) (page : VirtualPage) (context : AccessContext) :
    Except WalkError PhysicalFrame :=
  if !canonicalPage page then .error .nonCanonical
  else if !(table.pml4.present && table.pdpt.present && table.pd.present) then
    .error .notPresent
  else match table.leaf page with
    | none => .error .notPresent
    | some leaf =>
      if !leaf.present then .error .notPresent
      else if !leaf.reservedBitsClear then .error .reservedBits
      else if !representableFrame leaf.frame then .error .frameOutOfRange
      else
        let userPage := ancestorsUser table && leaf.user
        match context.privilege with
        | .user =>
          if !userPage then .error .supervisor
          else match context.kind with
            | .read => .ok leaf.frame
            | .write => if ancestorsWritable table && leaf.writable then .ok leaf.frame
              else .error .notWritable
            | .execute => if context.nxEnable && leaf.noExecute then .error .noExecute
              else .ok leaf.frame
        | .supervisor =>
          match context.kind with
          | .execute =>
            if context.smep && userPage then .error .smep
            else if context.nxEnable && leaf.noExecute then .error .noExecute
            else .ok leaf.frame
          | .read =>
            if context.smap && userPage && !context.ac then .error .smap else .ok leaf.frame
          | .write =>
            if context.smap && userPage && !context.ac then .error .smap
            else if context.writeProtect && !(ancestorsWritable table && leaf.writable) then
              .error .notWritable
            else .ok leaf.frame

theorem classify_deterministic table page access first second
    (hfirst : classify table page access = first)
    (hsecond : classify table page access = second) : first = second := by
  rw [hfirst] at hsecond
  exact hsecond

/-- A software model of the relevant x86 permission conjunction. -/
def walk (table : PageTable) (page : VirtualPage) (access : UserAccess) :
    Except WalkError PhysicalFrame :=
  if !canonicalPage page then .error .nonCanonical
  else if !(table.pml4.present && table.pdpt.present && table.pd.present) then
    .error .notPresent
  else if !(table.pml4.user && table.pdpt.user && table.pd.user) then .error .supervisor
  else match table.leaf page with
    | none => .error .notPresent
    | some leaf =>
      if !leaf.present then .error .notPresent
      else if !leaf.user then .error .supervisor
      else if !leaf.reservedBitsClear then .error .reservedBits
      else if !representableFrame leaf.frame then .error .frameOutOfRange
      else match access with
        | .read => .ok leaf.frame
        | .write => if ancestorsWritable table && leaf.writable then .ok leaf.frame
          else .error .notWritable
        | .execute => if leaf.noExecute then .error .noExecute else .ok leaf.frame

def userAncestor : Ancestor := { present := true, writable := true, user := true }

def encodedLeaf (state : VirtualMapping.State) (addressSpace : AddressSpaceId)
    (page : VirtualPage) : Option Leaf :=
  if !canonicalPage page then none else
  match state.mappings addressSpace page with
  | none => none
  | some mapping => match state.memory.binding mapping.object with
    | none => none
    | some frame =>
      if !representableFrame frame then none
      else if state.memory.allocator.status frame = .owned mapping.object then
        some (Leaf.mk frame true mapping.permissions.write true true true)
      else none

/-- The construction is separate from the abstract translator: it materializes
the x86 permission bits after independently rechecking lifetime and ownership. -/
def encode (state : VirtualMapping.State) (addressSpace : AddressSpaceId) : PageTable :=
  { pml4 := userAncestor, pdpt := userAncestor, pd := userAncestor,
    leaf := encodedLeaf state addressSpace }

theorem encoded_structurally_valid (state : VirtualMapping.State) addressSpace :
    StructurallyValid (encode state addressSpace) := by
  refine ⟨by simp [encode, userAncestor, legalAncestor],
    by simp [encode, userAncestor, legalAncestor],
    by simp [encode, userAncestor, legalAncestor], ?_⟩
  intro page leaf h
  simp only [encode] at h
  simp only [encodedLeaf] at h
  split at h <;> try contradiction
  next hcanonical =>
    split at h <;> try contradiction
    next mapping =>
      split at h <;> try contradiction
      next frame =>
        split at h <;> try contradiction
        next hrange =>
          split at h <;> try contradiction
          simp at h
          subst leaf
          simp_all [legalLeaf]

theorem encoded_unmapped_denied (state : VirtualMapping.State) addressSpace page
    (hcanonical : canonicalPage page = true)
    (hunmapped : state.mappings addressSpace page = none) :
    walk (encode state addressSpace) page .read = .error .notPresent := by
  simp [walk, encode, userAncestor, encodedLeaf, hcanonical, hunmapped]

theorem encoded_supervisor_impossible (state : VirtualMapping.State) addressSpace page leaf
    (h : (encode state addressSpace).leaf page = some leaf) : leaf.user = true := by
  have valid := (encoded_structurally_valid state addressSpace).2.2.2 page leaf h
  exact valid.2.2.1

theorem encoded_owned (state : VirtualMapping.State) addressSpace page leaf
    (h : (encode state addressSpace).leaf page = some leaf) :
    ∃ mapping, state.mappings addressSpace page = some mapping ∧
      state.memory.binding mapping.object = some leaf.frame ∧
      FrameAllocator.IsOwnedBy state.memory.allocator leaf.frame mapping.object := by
  simp only [encode, encodedLeaf] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  next mapping =>
    split at h <;> try contradiction
    next frame =>
      split at h <;> try contradiction
      split at h <;> try contradiction
      simp at h
      subst leaf
      simp_all [FrameAllocator.IsOwnedBy]

/-- A successful encoded read agrees with the abstract current-frame result
when the caller owns the address space and the abstract mapping permits read. -/
theorem read_refines_translate (state : VirtualMapping.State) actor addressSpace page mapping frame
    (hcanonical : canonicalPage page = true)
    (howner : state.owner addressSpace = some actor)
    (hmapping : state.mappings addressSpace page = some mapping)
    (hread : mapping.permissions.read = true)
    (hkind : state.memory.capabilities.kinds mapping.object = some .memory)
    (hbinding : state.memory.binding mapping.object = some frame)
    (hrange : representableFrame frame = true)
    (howned : state.memory.allocator.status frame = .owned mapping.object) :
    walk (encode state addressSpace) page .read = .ok frame ∧
      VirtualMapping.translate state actor addressSpace page .read = .ok frame := by
  constructor
  · simp [walk, encode, userAncestor, encodedLeaf, hcanonical, hmapping, hbinding,
      hrange, howned]
  · simp [VirtualMapping.translate, Permissions.permits, howner, hmapping, hread,
      hkind, hbinding, howned]

theorem write_not_amplified (state : VirtualMapping.State) addressSpace page mapping frame
    (hcanonical : canonicalPage page = true)
    (hmapping : state.mappings addressSpace page = some mapping)
    (hbinding : state.memory.binding mapping.object = some frame)
    (hrange : representableFrame frame = true)
    (howned : state.memory.allocator.status frame = .owned mapping.object)
    (hdeny : mapping.permissions.write = false) :
    walk (encode state addressSpace) page .write = .error .notWritable := by
  simp [walk, encode, userAncestor, encodedLeaf, hcanonical, hmapping, hbinding, hrange,
    howned, hdeny]

theorem encoded_nx (state : VirtualMapping.State) addressSpace page leaf
    (h : (encode state addressSpace).leaf page = some leaf) :
    walk (encode state addressSpace) page .execute = .error .noExecute := by
  have hencoded : encodedLeaf state addressSpace page = some leaf := by exact h
  have hv := (encoded_structurally_valid state addressSpace).2.2.2 page leaf h
  have hnx : leaf.noExecute = true := by
    simp only [encode, encodedLeaf] at h
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    simp at h
    subst leaf
    rfl
  simp [walk, encode, userAncestor, hv.1, hencoded, hv.2.1, hv.2.2.1,
    hv.2.2.2.1, hv.2.2.2.2, hnx]

theorem encoded_read_result (state : VirtualMapping.State) addressSpace page leaf
    (h : (encode state addressSpace).leaf page = some leaf) :
    walk (encode state addressSpace) page .read = .ok leaf.frame := by
  have hv := (encoded_structurally_valid state addressSpace).2.2.2 page leaf h
  have hencoded : encodedLeaf state addressSpace page = some leaf := by exact h
  simp [walk, encode, userAncestor, hv.1, hencoded, hv.2.1, hv.2.2.1,
    hv.2.2.2.1, hv.2.2.2.2]

theorem distinct_spaces_separated (state : VirtualMapping.State) first second page
    firstLeaf secondLeaf
    (hfirst : (encode state first).leaf page = some firstLeaf)
    (hsecond : (encode state second).leaf page = some secondLeaf)
    (hne : firstLeaf.frame ≠ secondLeaf.frame) :
    walk (encode state first) page .read ≠ walk (encode state second) page .read := by
  rw [encoded_read_result state first page firstLeaf hfirst,
    encoded_read_result state second page secondLeaf hsecond]
  simp [hne]

private def demoLeaf (frame : Nat) (write user nx : Bool) : Leaf :=
  { frame, present := true, writable := write, user, noExecute := nx,
    reservedBitsClear := true }
private def demo (entry : Option Leaf) : PageTable :=
  { pml4 := userAncestor, pdpt := userAncestor, pd := userAncestor,
    leaf := fun page => if page = 7 then entry else none }

/-- Reviewed mixed-map regions. Frames and pages remain explicit inputs rather
than deriving authority from linker symbols or boot globals. -/
inductive PolicyRegion where
  | kernelText | kernelData | kernelStack | pageTables | userText | userStack
  deriving BEq, DecidableEq, Repr

def policyLeaf (region : PolicyRegion) (frame : PhysicalFrame) : Leaf :=
  match region with
  | .kernelText => demoLeaf frame false false false
  | .kernelData | .kernelStack | .pageTables => demoLeaf frame true false true
  | .userText => demoLeaf frame false true false
  | .userStack => demoLeaf frame true true true

def PolicyLeaf (region : PolicyRegion) (leaf : Leaf) : Prop :=
  leaf = policyLeaf region leaf.frame

def MixedStructurallyValid (table : PageTable) : Prop :=
  table.pml4.present = true ∧ table.pdpt.present = true ∧ table.pd.present = true ∧
    ∀ page leaf, table.leaf page = some leaf → canonicalPage page = true ∧
      leaf.present = true ∧ leaf.reservedBitsClear = true ∧
        representableFrame leaf.frame = true

/-- A one-leaf executable instance of the reviewed policy. Larger maps are
formed by selecting the appropriate `policyLeaf` at each owned virtual page. -/
def policyTable (region : PolicyRegion) (page : VirtualPage)
    (frame : PhysicalFrame) : PageTable :=
  { pml4 := userAncestor, pdpt := userAncestor, pd := userAncestor,
    leaf := fun candidate => if candidate = page then some (policyLeaf region frame) else none }

theorem policy_table_structurally_valid region page frame
    (hpage : canonicalPage page = true) (hframe : representableFrame frame = true) :
    MixedStructurallyValid (policyTable region page frame) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro candidate leaf hleaf
  simp only [policyTable] at hleaf
  split at hleaf <;> try contradiction
  next heq =>
    simp at hleaf
    subst candidate
    subst leaf
    cases region <;> simp_all [policyLeaf, demoLeaf]

theorem policy_wx_exclusive region frame :
    (policyLeaf region frame).writable = false ∨
      (policyLeaf region frame).noExecute = true := by
  cases region <;> simp [policyLeaf, demoLeaf]

theorem kernel_text_policy frame : PolicyLeaf .kernelText (policyLeaf .kernelText frame) := by
  rfl
theorem kernel_data_policy frame : PolicyLeaf .kernelData (policyLeaf .kernelData frame) := by
  rfl
theorem user_text_policy frame : PolicyLeaf .userText (policyLeaf .userText frame) := by
  rfl
theorem user_stack_policy frame : PolicyLeaf .userStack (policyLeaf .userStack frame) := by
  rfl

theorem kernel_text_attributes frame :
    (policyLeaf .kernelText frame).user = false ∧
      (policyLeaf .kernelText frame).writable = false ∧
        (policyLeaf .kernelText frame).noExecute = false := by
  simp [policyLeaf, demoLeaf]
theorem kernel_writable_region_attributes
    (region : PolicyRegion) (h : region = .kernelData ∨ region = .kernelStack ∨
      region = .pageTables) :
    (policyLeaf region frame).user = false ∧ (policyLeaf region frame).writable = true ∧
      (policyLeaf region frame).noExecute = true := by
  rcases h with rfl | rfl | rfl <;> simp [policyLeaf, demoLeaf]
theorem user_text_attributes frame :
    (policyLeaf .userText frame).user = true ∧
      (policyLeaf .userText frame).writable = false ∧
        (policyLeaf .userText frame).noExecute = false := by
  simp [policyLeaf, demoLeaf]
theorem user_stack_attributes frame :
    (policyLeaf .userStack frame).user = true ∧
      (policyLeaf .userStack frame).writable = true ∧
        (policyLeaf .userStack frame).noExecute = true := by
  simp [policyLeaf, demoLeaf]

private def context (privilege : Privilege) (kind : AccessKind)
    (wp nxe smep smap ac : Bool := true) : AccessContext :=
  { privilege, kind, writeProtect := wp, nxEnable := nxe, smep, smap, ac }

private def policyDemo (region : PolicyRegion) : PageTable :=
  demo (some (policyLeaf region 4))

theorem cpl3_kernel_text_denied kind :
    classify (policyDemo .kernelText) 7 (context .user kind) = .error .supervisor := by
  cases kind <;> rfl

theorem cpl3_kernel_data_denied kind :
    classify (policyDemo .kernelData) 7 (context .user kind) = .error .supervisor := by
  cases kind <;> rfl

theorem cpl3_kernel_stack_denied kind :
    classify (policyDemo .kernelStack) 7 (context .user kind) = .error .supervisor := by
  cases kind <;> rfl

theorem cpl3_page_tables_denied kind :
    classify (policyDemo .pageTables) 7 (context .user kind) = .error .supervisor := by
  cases kind <;> rfl

theorem wp_protects_kernel_text :
    classify (policyDemo .kernelText) 7 (context .supervisor .write) =
      .error .notWritable := by rfl

theorem smep_protects_user_text :
    classify (policyDemo .userText) 7 (context .supervisor .execute) = .error .smep := by
  rfl

theorem smap_requires_override :
    classify (policyDemo .userStack) 7
      (context .supervisor .read true true true true false) = .error .smap := by
  rfl

-- User mode is confined from every supervisor region.
example : classify (policyDemo .kernelText) 7 (context .user .read) =
    .error .supervisor := by rfl
example : classify (policyDemo .kernelData) 7 (context .user .write) =
    .error .supervisor := by rfl
example : classify (policyDemo .kernelText) 7 (context .user .execute) =
    .error .supervisor := by rfl
-- CR0.WP, SMEP, SMAP, AC, and NXE have distinct observable boundaries.
example : classify (policyDemo .kernelText) 7 (context .supervisor .write) =
    .error .notWritable := by rfl
example : classify (policyDemo .kernelText) 7
    (context .supervisor .write false) = .ok 4 := by rfl
example : classify (policyDemo .userText) 7 (context .supervisor .execute) =
    .error .smep := by rfl
example : classify (policyDemo .userText) 7
    (context .supervisor .execute true true false) = .ok 4 := by rfl
example : classify (policyDemo .userStack) 7 (context .supervisor .read) =
    .ok 4 := by rfl
example : classify (policyDemo .userStack) 7
    (context .supervisor .read true true true true false) = .error .smap := by rfl
example : classify (policyDemo .userStack) 7
    (context .supervisor .read true true true true true) = .ok 4 := by rfl
example : classify (policyDemo .userStack) 7
    (context .supervisor .read true true true false false) = .ok 4 := by rfl
example : classify (policyDemo .userStack) 7
    (context .user .execute true true) = .error .noExecute := by rfl
example : classify (policyDemo .userStack) 7
    (context .user .execute true false) = .ok 4 := by rfl
-- Ancestor conjunction and malformed entries are classified before leaf access.
example : classify { policyDemo .userStack with pml4 := { userAncestor with writable := false } }
    7 (context .user .write) = .error .notWritable := by rfl
example : classify { policyDemo .userStack with pdpt := { userAncestor with user := false } }
    7 (context .user .read) = .error .supervisor := by rfl
example : classify (demo (some { policyLeaf .userStack 4 with writable := false }))
    7 (context .user .write) = .error .notWritable := by rfl
example : classify { policyDemo .userStack with pd := { userAncestor with present := false } }
    7 (context .user .read) = .error .notPresent := by rfl
example : classify (demo (some { policyLeaf .userStack 4 with present := false }))
    7 (context .user .read) = .error .notPresent := by rfl
example : classify (demo (some { policyLeaf .userStack 4 with reservedBitsClear := false }))
    7 (context .user .read) = .error .reservedBits := by rfl
-- The same reviewed policy behaves independently in two address-space values.
example : classify (demo (some (policyLeaf .userText 4))) 7 (context .user .read) = .ok 4 := by rfl
example : classify (demo (some (policyLeaf .userText 5))) 7 (context .user .read) = .ok 5 := by rfl

example : walk (demo (some (demoLeaf 4 false true true))) 7 .read = .ok 4 := by rfl
example : walk (demo (some (demoLeaf 4 false true true))) 7 .write =
    .error .notWritable := by rfl
example : walk (demo (some (demoLeaf 4 true false true))) 7 .read =
    .error .supervisor := by rfl
example : walk (demo (some (demoLeaf 4 true true true))) 7 .execute =
    .error .noExecute := by rfl
example : walk (demo none) lowerCanonicalPages .read = .error .nonCanonical := by
  simp [walk, canonicalPage]
example : (demo (some (demoLeaf 4 true true true))).leaf 7 ≠
    (demo (some (demoLeaf 5 true true true))).leaf 7 := by native_decide

end LeanOS.X86PageTable
