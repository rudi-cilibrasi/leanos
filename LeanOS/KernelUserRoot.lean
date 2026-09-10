import LeanOS.X86PageTable

/-!
A closed-kernel projection for the proposed no-SMAP copy strategy. The protected
frame inventory must contain every user-owned frame. Filtering only user PTE
bits would leave supervisor aliases accessible, so this projection filters by
physical frame at every virtual page. It does not implement CR3 publication,
TLB invalidation, or a copy window, and does not authorize CPL3.
-/
namespace LeanOS.KernelUserRoot

open VirtualMapping X86PageTable

/-- Remove every virtual alias of the listed physical frames, preserving all
other page-table fields and leaves. Inventory completeness is a separate
platform/allocator obligation. -/
def close (table : PageTable) (protectedFrames : List PhysicalFrame) : PageTable :=
  { table with leaf := fun page =>
      match table.leaf page with
      | none => none
      | some leaf => if leaf.frame ∈ protectedFrames then none else some leaf }

theorem protected_leaf_absent table frames page leaf
    (h : table.leaf page = some leaf) (hp : leaf.frame ∈ frames) :
    (close table frames).leaf page = none := by
  simp [close, h, hp]

theorem unprotected_leaf_preserved table frames page leaf
    (h : table.leaf page = some leaf) (hp : leaf.frame ∉ frames) :
    (close table frames).leaf page = some leaf := by
  simp [close, h, hp]

theorem retained_leaf_original table frames page leaf
    (h : (close table frames).leaf page = some leaf) :
    table.leaf page = some leaf ∧ leaf.frame ∉ frames := by
  cases ht : table.leaf page with
  | none => simp [close, ht] at h
  | some original =>
      by_cases hp : original.frame ∈ frames
      · simp [close, ht, hp] at h
      · simp [close, ht, hp] at h
        subst leaf
        exact ⟨rfl, hp⟩

theorem protected_access_denied table frames page leaf context frame
    (h : table.leaf page = some leaf) (hp : leaf.frame ∈ frames) :
    classify (close table frames) page context ≠ .ok frame := by
  have absent := protected_leaf_absent table frames page leaf h hp
  simp only [classify, absent]
  split <;> simp_all

/-- Two different virtual aliases disappear together, even when one or both
were supervisor mappings. There is no U/S-bit precondition. -/
theorem protected_aliases_absent table frames page1 page2 leaf1 leaf2
    (h1 : table.leaf page1 = some leaf1) (h2 : table.leaf page2 = some leaf2)
    (same : leaf1.frame = leaf2.frame) (hp : leaf1.frame ∈ frames) :
    (close table frames).leaf page1 = none ∧ (close table frames).leaf page2 = none := by
  exact ⟨protected_leaf_absent _ _ _ _ h1 hp,
    protected_leaf_absent _ _ _ _ h2 (same ▸ hp)⟩

theorem close_preserves_ancestors table frames :
    (close table frames).pml4 = table.pml4 ∧
    (close table frames).pdpt = table.pdpt ∧
    (close table frames).pd = table.pd := by
  exact ⟨rfl, rfl, rfl⟩

theorem close_idempotent_leaf table frames page :
    (close (close table frames) frames).leaf page = (close table frames).leaf page := by
  cases h : table.leaf page with
  | none => simp [close, h]
  | some leaf =>
      by_cases hp : leaf.frame ∈ frames <;> simp [close, h, hp]

end LeanOS.KernelUserRoot
