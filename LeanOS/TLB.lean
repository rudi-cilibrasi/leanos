import LeanOS.X86PageTable

/-! # Finite, single-core translation cache

The model uses eager invalidation for kernel mutations and also revalidates a
hit against the current encoded page table.  The latter makes stale cache data
unusable even in deliberately malformed states used by the negative examples.
-/
namespace LeanOS.TLB

set_option linter.unusedSimpArgs false

open LeanOS
open LeanOS.VirtualMapping
open LeanOS.X86PageTable

structure Key where
  addressSpace : AddressSpaceId
  page : VirtualPage
  deriving BEq, DecidableEq, Repr

structure Entry where
  key : Key
  frame : PhysicalFrame
  context : AccessContext
  deriving BEq, DecidableEq, Repr

def capacity : Nat := 16

structure State where
  virtual : VirtualMapping.State
  active : Option AddressSpaceId
  entries : List Entry

def lookup (entries : List Entry) (key : Key) (context : AccessContext) : Option Entry :=
  entries.find? fun entry => decide (entry.key = key ∧ entry.context = context)

def eraseKey (entries : List Entry) (key : Key) : List Entry :=
  entries.filter fun entry => decide (entry.key ≠ key)

def eraseSpace (entries : List Entry) (addressSpace : AddressSpaceId) : List Entry :=
  entries.filter fun entry => decide (entry.key.addressSpace ≠ addressSpace)

def insert (entries : List Entry) (entry : Entry) : List Entry :=
  (entry :: eraseKey entries entry.key).take capacity

/-- Every usable entry agrees with the current page-table classifier.  Stored
stale data is permitted, but `usable` rejects it before it can authorize access. -/
def usable (state : State) (entry : Entry) : Prop :=
  entry ∈ state.entries ∧
    classify (encode state.virtual entry.key.addressSpace) entry.key.page entry.context =
      .ok entry.frame

def Coherent (state : State) : Prop := state.entries.length ≤ capacity

inductive AccessError where
  | noActiveSpace
  | denied (cause : WalkError)
  deriving BEq, DecidableEq, Repr

/-- A hit is accepted only after a fresh walk agrees. A miss or stale hit fills
from that same walk, so every successful return is currently authorized. -/
def access (state : State) (page : VirtualPage) (context : AccessContext) :
    Except AccessError (PhysicalFrame × State) :=
  match state.active with
  | none => .error .noActiveSpace
  | some addressSpace =>
    let key := { addressSpace, page }
    match classify (encode state.virtual addressSpace) page context with
    | .error cause => .error (.denied cause)
    | .ok frame =>
      match lookup state.entries key context with
      | some entry =>
        if entry.frame = frame then .ok (frame, state)
        else .ok (frame, { state with entries := insert state.entries { key, frame, context } })
      | none => .ok (frame, { state with entries := insert state.entries { key, frame, context } })

def invalidatePage (state : State) (addressSpace : AddressSpaceId)
    (page : VirtualPage) : State :=
  { state with entries := eraseKey state.entries { addressSpace, page } }

def invalidateSpace (state : State) (addressSpace : AddressSpaceId) : State :=
  { state with entries := eraseSpace state.entries addressSpace }

/-- Without PCID/global mappings, this model conservatively treats CR3 reload
as a complete flush. -/
def switch (state : State) (addressSpace : AddressSpaceId) : State :=
  { state with active := some addressSpace, entries := [] }

structure Outcome (ε : Type) where
  state : State
  result : VirtualMapping.Result ε

/-- Page-table clearing and INVLPG are one caller-visible operation. -/
def unmap (state : State) (actor : SubjectId) (addressSpace : AddressSpaceId)
    (page : VirtualPage) : Outcome UnmapError :=
  let outcome := VirtualMapping.unmap state.virtual actor addressSpace page
  match outcome.result with
  | .rejected reason => { state, result := .rejected reason }
  | .accepted =>
    { state := invalidatePage { state with virtual := outcome.state } addressSpace page
      result := .accepted }

/-- Object retirement and cache invalidation are published atomically. A full
flush is intentionally chosen because release may affect several spaces/pages. -/
def release (state : State) (subject : SubjectId) (slot : SlotId) :
    Outcome MemoryLifecycle.ReleaseError :=
  let outcome := VirtualMapping.release state.virtual subject slot
  match outcome.result with
  | .rejected reason => { state, result := .rejected reason }
  | .accepted =>
    let next := { state with virtual := outcome.state, entries := [] }
    { state := next, result := .accepted }

def destroy (state : State) (subject : SubjectId) (slot : SlotId) :
    Outcome DestroyError :=
  let outcome := VirtualMapping.destroyAddressSpace state.virtual subject slot
  match outcome.result with
  | .rejected reason => { state, result := .rejected reason }
  | .accepted =>
    match Capability.lookup state.virtual.memory.capabilities subject slot with
    | .found cap =>
      { state := invalidateSpace { state with
          virtual := outcome.state
          active := if state.active = some cap.object then none else state.active }
          cap.object
        result := .accepted }
    | _ => { state := { state with virtual := outcome.state }, result := .accepted }

theorem erase_key_length entries key : (eraseKey entries key).length ≤ entries.length := by
  simp only [eraseKey]
  exact List.length_filter_le _ _

theorem erase_space_length entries addressSpace :
    (eraseSpace entries addressSpace).length ≤ entries.length := by
  simp only [eraseSpace]
  exact List.length_filter_le _ _

theorem insert_bounded entries entry : (insert entries entry).length ≤ capacity := by
  simp [insert, Nat.min_le_left]

theorem invalidate_page_absent entries key context :
    lookup (eraseKey entries key) key context = none := by
  simp only [lookup, List.find?_eq_none, eraseKey, List.mem_filter]
  intro entry hentry hfound
  exact (of_decide_eq_true hentry.2) (of_decide_eq_true hfound).1

theorem invalidate_space_absent entries addressSpace key context
    (hkey : key.addressSpace = addressSpace) :
    lookup (eraseSpace entries addressSpace) key context = none := by
  simp only [lookup, List.find?_eq_none, eraseSpace, List.mem_filter]
  intro entry hentry hfound
  have hne := of_decide_eq_true hentry.2
  have heq := (of_decide_eq_true hfound).1
  exact hne (heq ▸ hkey)

theorem access_success_current state page context frame next
    (h : access state page context = .ok (frame, next)) :
    ∃ addressSpace, state.active = some addressSpace ∧
      classify (encode state.virtual addressSpace) page context = .ok frame := by
  simp only [access] at h
  split at h <;> try contradiction
  next addressSpace hactive =>
    split at h <;> try contradiction
    next frame' hwalk =>
      split at h <;> simp_all
      next entry => split at h <;> simp_all

theorem successful_access_owned state page context frame next
    (h : access state page context = .ok (frame, next)) :
    ∃ addressSpace mapping,
      state.active = some addressSpace ∧
      state.virtual.mappings addressSpace page = some mapping ∧
      state.virtual.memory.binding mapping.object = some frame ∧
      FrameAllocator.IsOwnedBy state.virtual.memory.allocator frame mapping.object := by
  obtain ⟨addressSpace, hactive, hwalk⟩ := access_success_current state page context frame next h
  simp only [classify, encode] at hwalk
  split at hwalk <;> try contradiction
  split at hwalk <;> try contradiction
  split at hwalk <;> try contradiction
  next leaf hleaf =>
    split at hwalk <;> try contradiction
    split at hwalk <;> try contradiction
    split at hwalk <;> try contradiction
    split at hwalk <;> try contradiction
    all_goals
      repeat' first | split at hwalk
      all_goals try contradiction
      all_goals
      have howned := encoded_owned state.virtual addressSpace page leaf hleaf
      obtain ⟨mapping, hm, hb, ho⟩ := howned
      simp_all

theorem access_preserves_coherent state page context frame next
    (hc : Coherent state) (h : access state page context = .ok (frame, next)) : Coherent next := by
  simp only [access] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  next frame' =>
    split at h
    next entry =>
      split at h
      · simp_all [Coherent]
      · obtain ⟨rfl, rfl⟩ := h
        exact insert_bounded _ _
    next =>
      obtain ⟨rfl, rfl⟩ := h
      exact insert_bounded _ _

theorem invalidate_page_preserves_coherent state addressSpace page
    (h : Coherent state) : Coherent (invalidatePage state addressSpace page) := by
  exact Nat.le_trans (erase_key_length _ _) h

theorem invalidate_space_preserves_coherent state addressSpace
    (h : Coherent state) : Coherent (invalidateSpace state addressSpace) := by
  exact Nat.le_trans (erase_space_length _ _) h

theorem switch_coherent state addressSpace : Coherent (switch state addressSpace) := by simp [Coherent, switch]
theorem release_accepted_coherent state subject slot
    (h : (release state subject slot).result = .accepted) :
    Coherent (release state subject slot).state := by
  simp only [release] at h ⊢
  split <;> simp_all [Coherent]
theorem unmap_rejected_unchanged state actor addressSpace page reason
    (h : (unmap state actor addressSpace page).result = .rejected reason) :
    (unmap state actor addressSpace page).state = state := by
  simp only [unmap] at h ⊢
  split <;> simp_all
theorem release_rejected_unchanged state subject slot reason
    (h : (release state subject slot).result = .rejected reason) :
    (release state subject slot).state = state := by
  simp only [release] at h ⊢
  split <;> simp_all
theorem destroy_rejected_unchanged state subject slot reason
    (h : (destroy state subject slot).result = .rejected reason) :
    (destroy state subject slot).state = state := by
  simp only [destroy] at h ⊢
  split <;> simp_all
  split <;> simp_all

theorem unmap_revokes_before_return state actor addressSpace page
    (h : (unmap state actor addressSpace page).result = .accepted) context :
    lookup (unmap state actor addressSpace page).state.entries { addressSpace, page } context = none := by
  simp only [unmap] at h ⊢
  split <;> simp_all [invalidatePage, invalidate_page_absent]

theorem release_revokes_before_return state subject slot
    (h : (release state subject slot).result = .accepted) key context :
    lookup (release state subject slot).state.entries key context = none := by
  simp only [release] at h ⊢
  split <;> simp_all [lookup]

private def ancestor : Ancestor := { present := true, writable := true, user := true }
private def testLeaf (frame : Nat) (write : Bool) : Leaf :=
  { frame, present := true, writable := write, user := true, noExecute := true,
    reservedBitsClear := true }
private def table (frame : Nat) (write : Bool := true) : PageTable :=
  { pml4 := ancestor, pdpt := ancestor, pd := ancestor,
    leaf := fun page => if page = 7 then some (testLeaf frame write) else none }
private def ctx (kind : AccessKind := .read) : AccessContext :=
  { privilege := .user, kind, writeProtect := true, nxEnable := true,
    smep := true, smap := true, ac := false }
private def key1 : Key := { addressSpace := 1, page := 7 }
private def stale : Entry := { key := key1, frame := 4, context := ctx }

example : lookup (eraseKey [stale] key1) key1 (ctx) = none := by native_decide
example : lookup (eraseSpace [stale] 1) key1 (ctx) = none := by native_decide
example (virtual : VirtualMapping.State) :
    (switch (switch { virtual, active := some 1, entries := [stale] } 2) 1).entries = [] := rfl
example : eraseKey (eraseKey [stale] key1) key1 = eraseKey [stale] key1 := by native_decide

/-- Clearing a PTE without invalidation leaves the old datum present. `access`
still rejects it because it revalidates; this witnesses why invalidation is required. -/
example (virtual : VirtualMapping.State) :
    let broken : State := { virtual, active := some 1, entries := [stale] }
    lookup broken.entries key1 (ctx) = some stale := by simp [lookup, key1, stale, ctx]

/-- Omitting address-space identity aliases equal virtual pages. -/
def brokenLookup (entries : List Entry) (page : VirtualPage) : Option Entry :=
  entries.find? fun entry => decide (entry.key.page = page)
example : brokenLookup [stale] 7 = some stale := by native_decide

end LeanOS.TLB
