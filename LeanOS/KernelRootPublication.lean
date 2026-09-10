import LeanOS.KernelUserRoot

/-!
Single-core root-publication contract for the proposed no-SMAP strategy.
Unlike the ordinary TLB model, a cached hit is not revalidated against the new
page table: a table update alone must not be mistaken for invalidation.
The reload effect models the architectural primitive under disabled PCID and
PGE. It does not prove execution of CR3, readback, or hardware invalidation.
-/
namespace LeanOS.KernelRootPublication

open LeanOS.VirtualMapping LeanOS.X86PageTable

structure Entry where
  page : VirtualPage
  context : AccessContext
  frame : PhysicalFrame
  deriving DecidableEq, Repr

structure State where
  table : PageTable
  cache : List Entry

structure Controls where
  pcid : Bool
  globalPages : Bool
  deriving DecidableEq, Repr

inductive Effect where
  | none | reloadRoot
  deriving DecidableEq, Repr

structure Step where
  state : State
  accepted : Bool
  effect : Effect

/-- Cached hits retain their prior authorization until an actual invalidation
is modeled. Cache misses use a fresh walk; this query does not add entries. -/
def access (state : State) (page : VirtualPage) (context : AccessContext) :
    Except WalkError PhysicalFrame :=
  match state.cache.find? (fun entry => decide (entry.page = page ∧ entry.context = context)) with
  | some entry => .ok entry.frame
  | none => classify state.table page context

/-- Table replacement alone leaves cached authority intact. This operation is
intentionally unsafe and exposed for negative evidence, not as a publication API. -/
def replaceOnly (state : State) (target : PageTable) : State :=
  { state with table := target }

/-- The machine must execute the returned reload effect before publishing the
returned state. Unsupported PCID/PGE controls reject without any mutation.
The target must already have been constructed and authorized by the caller. -/
def publish (state : State) (target : PageTable) (controls : Controls) : Step :=
  if controls.pcid || controls.globalPages then
    { state, accepted := false, effect := .none }
  else
    { state := { table := target, cache := [] }, accepted := true, effect := .reloadRoot }

theorem accepted_requires_controls state target controls
    (h : (publish state target controls).accepted = true) :
    controls.pcid = false ∧ controls.globalPages = false := by
  simp only [publish] at h
  split at h <;> simp_all

theorem unsupported_unchanged state target controls
    (h : controls.pcid = true ∨ controls.globalPages = true) :
    (publish state target controls).state = state ∧
      (publish state target controls).accepted = false ∧
      (publish state target controls).effect = .none := by
  rcases h with h | h <;> simp [publish, h]

/-- Acceptance always requires a reload, even if the root address would be
unchanged. The logical state alone cannot stand in for this machine effect. -/
theorem accepted_requires_reload state target controls
    (h : (publish state target controls).accepted = true) :
    (publish state target controls).effect = .reloadRoot ∧
      (publish state target controls).state.table = target ∧
      (publish state target controls).state.cache = [] := by
  have hc := accepted_requires_controls _ _ _ h
  simp [publish, hc.1, hc.2]

theorem published_access_fresh state target controls page context
    (h : (publish state target controls).accepted = true) :
    access (publish state target controls).state page context = classify target page context := by
  have hc := accepted_requires_controls _ _ _ h
  simp [publish, hc.1, hc.2, access]

/-- Applying the required reload and closed-root projection denies every
protected mapping despite arbitrary prior cached authority. -/
theorem published_protected_denied state table frames controls page leaf context frame
    (h : (publish state (KernelUserRoot.close table frames) controls).accepted = true)
    (hl : table.leaf page = some leaf) (hf : leaf.frame ∈ frames) :
    access (publish state (KernelUserRoot.close table frames) controls).state page context ≠ .ok frame := by
  rw [published_access_fresh _ _ _ _ _ h]
  exact KernelUserRoot.protected_access_denied _ _ _ _ _ _ hl hf

/-- Replacing a root leaves a matching cached hit usable: no fresh-walk check
silently rescues a missing invalidation. -/
theorem replacement_retains_hit state target page context entry
    (h : state.cache.find? (fun candidate => decide (candidate.page = page ∧ candidate.context = context)) = some entry) :
    access (replaceOnly state target) page context = .ok entry.frame := by
  simp only [access, replaceOnly, h]

end LeanOS.KernelRootPublication
