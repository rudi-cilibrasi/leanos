import LeanOS.UserCopy
import LeanOS.KernelUserRoot

/-!
Bounded temporary mappings for the proposed no-SMAP copy root. This is a
fresh-page-walk model, not root installation or TLB invalidation. The caller
supplies a closed kernel table and two reserved, unused virtual pages. The
frame inventory and mapping authority must remain stable through the transfer.
-/
namespace LeanOS.UserCopyAliases

open LeanOS.UserCopy LeanOS.VirtualMapping LeanOS.X86PageTable

inductive Error where
  | validation (reason : CopyError)
  | tooManyFrames | invalidSlots | occupiedSlots | unprotectedFrame | unrepresentableFrame
  deriving DecidableEq, Repr

/-- No temporary mapping is executable or accessible to user mode. Writes are
allowed only for a request that was validated with write permission. -/
def aliasLeaf (frame : PhysicalFrame) (access : Access) : Leaf :=
  { frame, present := true, writable := access == .write, user := false,
    noExecute := true, reservedBitsClear := true }

def frameLeaf (frames : List PhysicalFrame) (index : Nat) (access : Access) : Option Leaf :=
  (frames[index]?).map (fun frame => aliasLeaf frame access)

/-- The only added aliases occupy the two dedicated virtual slots. -/
def project (closed : PageTable) (base : VirtualPage) (frames : List PhysicalFrame)
    (access : Access) : PageTable :=
  { closed with leaf := fun page =>
      if page = base then frameLeaf frames 0 access
      else if page = base + 1 then frameLeaf frames 1 access
      else closed.leaf page }

structure Plan where
  locations : List Location
  frames : List PhysicalFrame
  table : PageTable

/-- Validate every byte before deriving aliases. Reject occupied slots instead
of hiding a trusted kernel mapping. The frame inventory is checked explicitly;
its completeness remains a separate obligation of the closed-root builder. -/
def prepare (state : UserCopy.State) (context : TrustedContext) (start : UInt64)
    (length : Nat) (access : Access) (closed : PageTable) (base : VirtualPage)
    (protectedFrames : List PhysicalFrame) : Except Error Plan :=
  match validate state context start length access with
  | .error reason => .error (.validation reason)
  | .ok locations =>
      let frames := (locations.map Location.frame).eraseDups
      if frames.length > 2 then .error .tooManyFrames
      else if !(canonicalPage base && canonicalPage (base + 1)) then .error .invalidSlots
      else if (closed.leaf base).isSome || (closed.leaf (base + 1)).isSome then .error .occupiedSlots
      else if !(frames.all fun frame => frame ∈ protectedFrames) then .error .unprotectedFrame
      else if !(frames.all representableFrame) then .error .unrepresentableFrame
      else .ok { locations, frames, table := project closed base frames access }

theorem alias_permissions frame access :
    (aliasLeaf frame access).user = false ∧
    (aliasLeaf frame access).noExecute = true ∧
    (aliasLeaf frame access).writable = (access == .write) := by
  exact ⟨rfl, rfl, rfl⟩

theorem outside_slots_preserved closed base frames access page
    (h0 : page ≠ base) (h1 : page ≠ base + 1) :
    (project closed base frames access).leaf page = closed.leaf page := by
  simp [project, h0, h1]

theorem ancestors_preserved closed base frames access :
    (project closed base frames access).pml4 = closed.pml4 ∧
    (project closed base frames access).pdpt = closed.pdpt ∧
    (project closed base frames access).pd = closed.pd := by
  exact ⟨rfl, rfl, rfl⟩

/-- A projected alias can only name a frame supplied in the bounded plan. -/
theorem frameLeaf_member frames index access leaf
    (h : frameLeaf frames index access = some leaf) :
    leaf.frame ∈ frames ∧ leaf.user = false ∧ leaf.noExecute = true ∧
      leaf.writable = (access == .write) := by
  simp only [frameLeaf, Option.map_eq_some_iff] at h
  obtain ⟨frame, hf, rfl⟩ := h
  exact ⟨List.mem_of_getElem? hf, rfl, rfl, rfl⟩

/-- All metadata and mappings in an accepted plan are derived from successful
whole-request validation, and at most two distinct frames can be exposed. -/
theorem prepared_validated state context start length access closed base protectedFrames plan
    (h : prepare state context start length access closed base protectedFrames = .ok plan) :
    validate state context start length access = .ok plan.locations ∧
      plan.frames = (plan.locations.map Location.frame).eraseDups ∧
      plan.frames.length ≤ 2 ∧
      plan.table = project closed base plan.frames access := by
  simp only [prepare] at h
  split at h <;> try contradiction
  next locations hv =>
    split at h <;> try contradiction
    next hcount =>
      split at h <;> try contradiction
      split at h <;> try contradiction
      split at h <;> try contradiction
      split at h <;> try contradiction
      simp only [Except.ok.injEq] at h
      subst plan
      exact ⟨hv, rfl, Nat.le_of_not_gt hcount, rfl⟩

theorem prepared_frame_authorized state context start length access closed base protectedFrames plan frame
    (h : prepare state context start length access closed base protectedFrames = .ok plan)
    (hf : frame ∈ plan.frames) :
    ∃ location, location ∈ plan.locations ∧ location.frame = frame := by
  have hp := prepared_validated _ _ _ _ _ _ _ _ _ h
  rw [hp.2.1] at hf
  simpa using hf

/-- The supplied slots are canonical and unused, and every derived frame is
both in the protected inventory and representable by this page-table model. -/
theorem prepared_checks state context start length access closed base protectedFrames plan
    (h : prepare state context start length access closed base protectedFrames = .ok plan) :
    canonicalPage base = true ∧ canonicalPage (base + 1) = true ∧
      closed.leaf base = none ∧ closed.leaf (base + 1) = none ∧
      (∀ frame, frame ∈ plan.frames → frame ∈ protectedFrames) ∧
      (∀ frame, frame ∈ plan.frames → representableFrame frame = true) := by
  simp only [prepare] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Except.ok.injEq] at h
  subst plan
  simp_all

/-- Every present alias in a reserved slot belongs to the supplied frame list
and has exactly the selected supervisor/NX permissions. -/
theorem projected_alias closed base frames access page leaf
    (hs : page = base ∨ page = base + 1)
    (hl : (project closed base frames access).leaf page = some leaf) :
    leaf.frame ∈ frames ∧ leaf.user = false ∧ leaf.noExecute = true ∧
      leaf.writable = (access == .write) := by
  rcases hs with rfl | rfl
  · exact frameLeaf_member _ 0 _ _ (by simpa [project] using hl)
  · exact frameLeaf_member _ 1 _ _ (by simpa [project] using hl)

/-- Combine the alias projection with successful validation: no exposed frame
is obtained from outside the validated byte-location list. -/
theorem prepared_alias_authorized state context start length access closed base protectedFrames plan page leaf
    (h : prepare state context start length access closed base protectedFrames = .ok plan)
    (hs : page = base ∨ page = base + 1)
    (hl : plan.table.leaf page = some leaf) :
    (∃ location, location ∈ plan.locations ∧ location.frame = leaf.frame) ∧
      leaf.user = false ∧ leaf.noExecute = true ∧ leaf.writable = (access == .write) := by
  have hp := prepared_validated _ _ _ _ _ _ _ _ _ h
  rw [hp.2.2.2] at hl
  have ha := projected_alias _ _ _ _ _ _ hs hl
  exact ⟨prepared_frame_authorized _ _ _ _ _ _ _ _ _ _ h ha.1, ha.2⟩

/-- NX prevents supervisor instruction fetch through a copy alias even without
SMAP. Earlier structural failures also reject rather than grant execution. -/
theorem alias_execution_denied closed base frames access page leaf frame
    (hs : page = base ∨ page = base + 1)
    (hl : (project closed base frames access).leaf page = some leaf) :
    classify (project closed base frames access) page
      { privilege := .supervisor, kind := .execute, writeProtect := true,
        nxEnable := true, smep := true, smap := false, ac := false } ≠ .ok frame := by
  have hp := projected_alias _ _ _ _ _ _ hs hl
  simp [classify, hl, hp.2.1, hp.2.2.1]
  repeat' split <;> simp_all

/-- No CPL3 data read can use a supervisor copy alias. -/
theorem alias_user_read_denied closed base frames access page leaf frame
    (hs : page = base ∨ page = base + 1)
    (hl : (project closed base frames access).leaf page = some leaf) :
    classify (project closed base frames access) page
      { privilege := .user, kind := .read, writeProtect := true,
        nxEnable := true, smep := true, smap := false, ac := false } ≠ .ok frame := by
  have hp := projected_alias _ _ _ _ _ _ hs hl
  simp [classify, hl, hp.2.1]
  repeat' split <;> simp_all

end LeanOS.UserCopyAliases
