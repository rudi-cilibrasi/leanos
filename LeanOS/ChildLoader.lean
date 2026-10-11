import LeanOS.ElfAdmission

/-!
# Loading an admitted ELF into a spawned child (#492)

The run-time half of #492.  A ring-3 loader holds a spawn capability and the
read authority over the reserved range `[start, stop)` that holds the admitted
subject ELF (ADR 0024).  It spawns a child (`LeanOS.SpawnSyscall`), gives it
frames, and then asks the kernel to load the admitted segments into the
child's fresh address space and to start the child.  This module is the model
of that loading: the child's user pages as the kernel builds them.

## Copy or map

Decision (recorded in ADR 0024's run-time amendment):

* a **read-only** segment (not writable) is **mapped in place**: each of its
  pages is the reserved page holding its file bytes, with the segment's
  permissions.  The bytes cannot change, so sharing them is safe, and the child
  is charged no frame.  Because a mapped page cannot provide a zero fill, such
  a segment is accepted only when its memory image is its file image
  (`memBytes = fileBytes`);
* a **writable** segment is **copied**: each page is a frame given to the child
  (one of the frames the parent granted it), holding the segment's file bytes
  and zeros after them.  A child that writes its data never changes the
  admitted bytes, and the zero fill (bss) is exact.

## Requests

`load control index source` names the child by its control word, a segment of
the admitted plan by its index, and the physical address the loader claims for
the segment's first file byte.  The kernel accepts exactly the admitted
layout: the source must lie inside the loader's read authority and must be
the admitted placement of that segment (`start + fileOffset`).  The loader
cannot choose an address, a size, or a permission.  `start control` starts the
child once every segment is loaded.

## Failure rolls back the spawn

Every rejection of a request for the live child being loaded discards that
child: the model state returns to "no child", with no pages and nothing
loaded (`rollback`), and the kernel terminates the child in the composite
model (`childGate (.terminateChild control)`), which releases everything the
spawn and the grants gave it (`terminateChild_releases_everything`).  A
request that does not name the live child (a stale or forged control word) is
refused without effect: there is nothing of it to roll back.
-/
namespace LeanOS.ChildLoader

open LeanOS
open LeanOS.ElfAdmission (Segment pageBytes)

set_option linter.unusedSimpArgs false

/-! ## State -/

structure Perm where
  read : Bool
  write : Bool
  execute : Bool
  deriving DecidableEq, Repr

def segmentPerm (segment : Segment) : Perm :=
  ⟨segment.readable, segment.writable, segment.executable⟩

/-- Where a child page's bytes come from. -/
inductive Backing where
  /-- The reserved page at this physical address, mapped in place. -/
  | reserved (address : Nat)
  /-- The `slot`-th frame given to the child, holding a copy. -/
  | copy (slot : Nat)
  deriving DecidableEq, Repr

structure Leaf where
  backing : Backing
  perm : Perm
  deriving DecidableEq, Repr

/-- The child being loaded: its control word and how many frames its parent
gave it. -/
structure Child where
  control : UInt64
  frames : Nat
  deriving DecidableEq, Repr

structure State where
  /-- The loader's read authority, the reserved range `[start, stop)`. -/
  start : Nat
  stop : Nat
  /-- The admitted plan's segments. -/
  plan : List Segment
  child : Option Child
  loaded : Nat → Bool
  /-- The child's user pages, by virtual page number. -/
  leaves : Nat → Option Leaf
  /-- Frames already used for copies. -/
  used : Nat
  started : Bool

/-! ## Segment pages -/

def firstPage (segment : Segment) : Nat := segment.vaddr / pageBytes

def pageCount (segment : Segment) : Nat :=
  (segment.pageEnd - segment.vaddr) / pageBytes

/-- A virtual page lies in a segment's memory image. -/
def inSegment (segment : Segment) (page : Nat) : Bool :=
  decide (firstPage segment ≤ page) && decide (page < firstPage segment + pageCount segment)

/-- The leaf a page of a segment gets, for a source and the frames used
before the segment. -/
def leafOf (segment : Segment) (source used page : Nat) : Leaf :=
  { backing := if segment.writable then .copy (used + (page - firstPage segment))
      else .reserved (source + (page - firstPage segment) * pageBytes)
    perm := segmentPerm segment }

/-! ## Requests and replies -/

inductive Request where
  | load (control : UInt64) (index source : Nat)
  | start (control : UInt64)
  deriving DecidableEq, Repr

inductive Rejection where
  /-- The control word names no child being loaded. -/
  | noChild
  /-- The child was already started. -/
  | started
  /-- No segment of the admitted plan has this index. -/
  | badIndex
  /-- The segment is already loaded. -/
  | alreadyLoaded
  /-- The claimed source is not inside the loader's read authority. -/
  | outsideAuthority
  /-- The claimed source is not the segment's admitted placement. -/
  | wrongSource
  /-- A read-only segment with a zero fill cannot be mapped in place. -/
  | inPlaceZeroFill
  /-- The child has too few frames for the copy. -/
  | noFrames
  /-- Not every segment is loaded. -/
  | incomplete
  deriving DecidableEq, Repr

inductive Reply where
  | loaded
  | started
  /-- A refusal without effect: the request named no child being loaded. -/
  | refused (reason : Rejection)
  /-- A rejection that rolled the spawn back. -/
  | rolledBack (reason : Rejection)
  deriving DecidableEq, Repr

/-- Discard the child being loaded: no child, no pages, nothing loaded. -/
def rollback (state : State) : State :=
  { state with
    child := none
    loaded := fun _ => false
    leaves := fun _ => none
    used := 0
    started := false }

/-- Install one segment's pages. -/
def install (state : State) (index : Nat) (segment : Segment) (source : Nat) : State :=
  { state with
    loaded := fun candidate => if candidate = index then true else state.loaded candidate
    leaves := fun page =>
      if inSegment segment page then some (leafOf segment source state.used page)
      else state.leaves page
    used := if segment.writable then state.used + pageCount segment else state.used }

/-- The first failing check of a load for the live, unstarted child. -/
def loadCheck (state : State) (child : Child) (index source : Nat) : Option Rejection :=
  match state.plan[index]? with
  | none => some .badIndex
  | some segment =>
      if state.loaded index then some .alreadyLoaded
      else if !(decide (state.start ≤ source) &&
          decide (source + pageCount segment * pageBytes ≤ state.stop)) then
        some .outsideAuthority
      else if source ≠ state.start + segment.fileOffset then some .wrongSource
      else if !segment.writable && segment.memBytes ≠ segment.fileBytes then
        some .inPlaceZeroFill
      else if segment.writable && child.frames < state.used + pageCount segment then
        some .noFrames
      else none

/-- Every segment of the plan is loaded. -/
def allLoaded (state : State) : Bool :=
  (List.range state.plan.length).all state.loaded

/-- The live, unstarted child a control word names, if any. -/
def liveChild (state : State) (control : UInt64) : Option Child :=
  match state.child with
  | some child => if child.control = control && !state.started then some child else none
  | none => none

/-- One request. -/
def step (state : State) : Request → State × Reply
  | .load control index source =>
      match liveChild state control with
      | none => (state, .refused (if state.child.isSome && state.started then .started else .noChild))
      | some child =>
          match loadCheck state child index source with
          | some reason => (rollback state, .rolledBack reason)
          | none =>
              match state.plan[index]? with
              | some segment => (install state index segment source, .loaded)
              | none => (rollback state, .rolledBack .badIndex)
  | .start control =>
      match liveChild state control with
      | none => (state, .refused (if state.child.isSome && state.started then .started else .noChild))
      | some _ =>
          if allLoaded state then ({ state with started := true }, .started)
          else (rollback state, .rolledBack .incomplete)

def Reply.isRejection : Reply → Bool
  | .refused _ | .rolledBack _ => true
  | _ => false

/-! ## Failure rolls back the spawn -/

/-- **Rollback.**  Every rejection of a request naming the live, unstarted
child discards it: no child, no pages, nothing loaded, no frame used. -/
theorem rejection_rolls_back (state : State) (request : Request) (reason : Rejection)
    (rejected : (step state request).2 = .rolledBack reason) :
    (step state request).1 = rollback state := by
  cases request with
  | load control index source =>
      simp only [step] at rejected ⊢
      cases live : liveChild state control with
      | none => simp [live] at rejected
      | some child =>
          simp only [live] at rejected ⊢
          cases check : loadCheck state child index source with
          | some found => simp [check]
          | none =>
              simp only [check] at rejected ⊢
              cases segment : state.plan[index]? with
              | none => simp
              | some segment => simp [segment] at rejected
  | start control =>
      simp only [step] at rejected ⊢
      cases live : liveChild state control with
      | none => simp [live] at rejected
      | some child =>
          simp only [live] at rejected ⊢
          by_cases all : allLoaded state = true
          · simp [all] at rejected
          · simp [all]

theorem rollback_empty (state : State) :
    (rollback state).child = none ∧ (∀ page, (rollback state).leaves page = none) ∧
      (∀ index, (rollback state).loaded index = false) ∧ (rollback state).used = 0 := by
  simp [rollback]

/-- A request that does not name the live, unstarted child changes nothing. -/
theorem refused_unchanged (state : State) (request : Request) (reason : Rejection)
    (refused : (step state request).2 = .refused reason) :
    (step state request).1 = state := by
  cases request with
  | load control index source =>
      simp only [step] at refused ⊢
      cases live : liveChild state control with
      | none => simp
      | some child =>
          simp only [live] at refused
          cases check : loadCheck state child index source with
          | some found => simp [check] at refused
          | none =>
              simp only [check] at refused
              cases segment : state.plan[index]? with
              | none => simp [segment] at refused
              | some segment => simp [segment] at refused
  | start control =>
      simp only [step] at refused ⊢
      cases live : liveChild state control with
      | none => simp
      | some child =>
          simp only [live] at refused
          by_cases all : allLoaded state = true
          · simp [all] at refused
          · simp [all] at refused

/-! ## The loader cannot map outside the reserved range -/

/-- A load whose claimed source does not lie in the read authority is
rejected, and the spawn is rolled back. -/
theorem load_outside_authority_rejected (state : State) (child : Child) (control : UInt64)
    (index source : Nat) (segment : Segment)
    (live : liveChild state control = some child) (named : state.plan[index]? = some segment)
    (fresh : state.loaded index = false)
    (outside : source < state.start ∨ state.stop < source + pageCount segment * pageBytes) :
    step state (.load control index source) =
      (rollback state, .rolledBack .outsideAuthority) := by
  have bad : (decide (state.start ≤ source) &&
      decide (source + pageCount segment * pageBytes ≤ state.stop)) = false := by
    rcases outside with low | high
    · simp; omega
    · simp; omega
  simp [step, live, loadCheck, named, fresh, bad]

/-- Every in-place page lies inside the read authority, and every copy uses a
frame the child was given. -/
def Inside (state : State) : Prop :=
  ∀ page leaf, state.leaves page = some leaf →
    (∀ address, leaf.backing = .reserved address →
      state.start ≤ address ∧ address + pageBytes ≤ state.stop) ∧
    (∀ slot, leaf.backing = .copy slot → slot < state.used)

theorem inside_rollback (state : State) : Inside (rollback state) := by
  intro page leaf found
  simp [rollback] at found

theorem pageCount_pos {segment : Segment} (page : Nat) (member : inSegment segment page = true) :
    page - firstPage segment < pageCount segment := by
  simp only [inSegment, Bool.and_eq_true, decide_eq_true_eq] at member
  omega

/-- The model keeps every in-place page inside the reserved range and every
copy inside the child's frames, whatever the loader asks. -/
theorem step_preserves_inside (state : State) (request : Request) (inside : Inside state) :
    Inside (step state request).1 := by
  cases request with
  | start control =>
      simp only [step]
      cases live : liveChild state control with
      | none => exact inside
      | some child =>
          simp only
          by_cases all : allLoaded state = true
          · simp only [all, ↓reduceIte]
            intro page leaf found
            exact inside page leaf found
          · simp only [all, Bool.false_eq_true, ↓reduceIte]
            exact inside_rollback state
  | load control index source =>
      simp only [step]
      cases live : liveChild state control with
      | none => exact inside
      | some child =>
          simp only
          cases check : loadCheck state child index source with
          | some reason => exact inside_rollback state
          | none =>
              cases named : state.plan[index]? with
              | none => exact inside_rollback state
              | some segment =>
                  simp only
                  have passed := check
                  simp only [loadCheck, named] at passed
                  split at passed
                  · cases passed
                  rename_i fresh
                  split at passed
                  · cases passed
                  rename_i within
                  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
                    Nat.not_le, not_or] at within
                  have within' : state.start ≤ source ∧
                      source + pageCount segment * pageBytes ≤ state.stop := by
                    rcases within with ⟨a, b⟩
                    omega
                  intro page leaf found
                  simp only [install] at found ⊢
                  by_cases member : inSegment segment page = true
                  · simp only [member, ↓reduceIte, Option.some.injEq] at found
                    subst found
                    have offset := pageCount_pos page member
                    refine ⟨fun address backing => ?_, fun slot backing => ?_⟩
                    · simp only [leafOf] at backing
                      split at backing
                      · cases backing
                      · cases backing
                        refine ⟨by omega, ?_⟩
                        have : (page - firstPage segment) * pageBytes + pageBytes ≤
                            pageCount segment * pageBytes := by
                          rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ offset
                        omega
                    · simp only [leafOf] at backing
                      split at backing
                      · rename_i writable
                        cases backing
                        simp only [writable, ↓reduceIte]
                        omega
                      · cases backing
                  · simp only [member, Bool.false_eq_true, ↓reduceIte] at found
                    obtain ⟨reserved, copied⟩ := inside page leaf found
                    refine ⟨reserved, fun slot backing => ?_⟩
                    have := copied slot backing
                    split <;> omega

/-! ## After loading, the child holds exactly the admitted segments -/

/-- The admitted plan's layout facts the loader relies on: every segment
starts on a page, and no two segments share a page
(`ElfAdmission.admitted_segments_aligned`, `admitted_segments_disjoint`). -/
structure PlanLayout (plan : List Segment) : Prop where
  aligned : ∀ segment ∈ plan, segment.vaddr % pageBytes = 0
  disjoint : plan.Pairwise Segment.Disjoint

/-- The page a leaf of a loaded segment must be: the segment's permissions,
and a copy exactly when the segment is writable. -/
def Matches (segment : Segment) (leaf : Leaf) : Prop :=
  leaf.perm = segmentPerm segment ∧
    (segment.writable = true ↔ ∃ slot, leaf.backing = .copy slot)

/-- **Exactness.**  A page is mapped exactly when it lies in a loaded segment
of the plan, and then it carries that segment's permissions, copied when the
segment is writable and in place otherwise. -/
def Exact (state : State) : Prop :=
  ∀ page, (∀ leaf, state.leaves page = some leaf →
      ∃ index segment, state.plan[index]? = some segment ∧ state.loaded index = true ∧
        inSegment segment page = true ∧ Matches segment leaf) ∧
    (∀ index segment, state.plan[index]? = some segment → state.loaded index = true →
      inSegment segment page = true → ∃ leaf, state.leaves page = some leaf)

theorem exact_rollback (state : State) : Exact (rollback state) := by
  intro page
  refine ⟨fun leaf found => ?_, fun index segment _ loaded _ => ?_⟩
  · simp [rollback] at found
  · simp [rollback] at loaded

theorem leafOf_matches (segment : Segment) (source used page : Nat) :
    Matches segment (leafOf segment source used page) := by
  refine ⟨rfl, ?_⟩
  cases writable : segment.writable <;> simp [leafOf, writable]

theorem pageEnd_aligned (segment : Segment) : segment.pageEnd % pageBytes = 0 := by
  simp only [Segment.pageEnd, ElfAdmission.pageBytes]
  exact Nat.mul_mod_left _ _

/-- With page-aligned starts, two disjoint segments share no page. -/
theorem inSegment_disjoint {left right : Segment} (leftAligned : left.vaddr % pageBytes = 0)
    (rightAligned : right.vaddr % pageBytes = 0) (disjoint : Segment.Disjoint left right)
    (page : Nat) (inLeft : inSegment left page = true) : inSegment right page = false := by
  cases inRight : inSegment right page
  · rfl
  · exfalso
    simp only [ElfAdmission.pageBytes] at leftAligned rightAligned
    unfold Segment.Disjoint Segment.pageEnd at disjoint
    simp only [ElfAdmission.pageBytes] at disjoint
    simp only [inSegment, firstPage, pageCount, Segment.pageEnd, ElfAdmission.pageBytes,
      Bool.and_eq_true] at inLeft inRight
    obtain ⟨l1, l2⟩ := inLeft
    obtain ⟨r1, r2⟩ := inRight
    have l1' := of_decide_eq_true l1
    have l2' := of_decide_eq_true l2
    have r1' := of_decide_eq_true r1
    have r2' := of_decide_eq_true r2
    omega

theorem plan_disjoint {plan : List Segment} (layout : PlanLayout plan) {i j : Nat}
    {left right : Segment} (hi : plan[i]? = some left) (hj : plan[j]? = some right)
    (different : i ≠ j) : Segment.Disjoint left right := by
  have hiLt : i < plan.length := by
    rcases List.getElem?_eq_some_iff.1 hi with ⟨h, _⟩; exact h
  have hjLt : j < plan.length := by
    rcases List.getElem?_eq_some_iff.1 hj with ⟨h, _⟩; exact h
  have leftEq : plan[i] = left := by
    rcases List.getElem?_eq_some_iff.1 hi with ⟨_, h⟩; exact h
  have rightEq : plan[j] = right := by
    rcases List.getElem?_eq_some_iff.1 hj with ⟨_, h⟩; exact h
  have pairwise := List.pairwise_iff_getElem.1 layout.disjoint
  rcases Nat.lt_or_gt_of_ne different with lt | gt
  · have := pairwise i j hiLt hjLt lt
    rw [leftEq, rightEq] at this
    exact this
  · have := pairwise j i hjLt hiLt gt
    rw [leftEq, rightEq] at this
    rcases this with a | b
    · exact Or.inr a
    · exact Or.inl b

theorem plan_aligned {plan : List Segment} (layout : PlanLayout plan) {i : Nat} {segment : Segment}
    (hi : plan[i]? = some segment) : segment.vaddr % pageBytes = 0 :=
  layout.aligned segment (List.mem_of_getElem? hi)

/-- Every request keeps exactness, for an admitted layout. -/
theorem step_preserves_exact (state : State) (request : Request) (exact : Exact state) : Exact (step state request).1 := by
  cases request with
  | start control =>
      simp only [step]
      cases live : liveChild state control with
      | none => exact exact
      | some child =>
          simp only
          by_cases all : allLoaded state = true
          · simp only [all, ↓reduceIte]
            exact exact
          · simp only [all, Bool.false_eq_true, ↓reduceIte]
            exact exact_rollback state
  | load control index source =>
      simp only [step]
      cases live : liveChild state control with
      | none => exact exact
      | some child =>
          simp only
          cases check : loadCheck state child index source with
          | some reason => exact exact_rollback state
          | none =>
              cases named : state.plan[index]? with
              | none => exact exact_rollback state
              | some segment =>
                  simp only
                  have fresh : state.loaded index = false := by
                    have passed := check
                    simp only [loadCheck, named] at passed
                    split at passed
                    · cases passed
                    · rename_i h; simpa using h
                  intro page
                  refine ⟨fun leaf found => ?_, fun other otherSegment otherNamed otherLoaded
                    otherIn => ?_⟩
                  · simp only [install] at found
                    by_cases member : inSegment segment page = true
                    · simp only [member, ↓reduceIte, Option.some.injEq] at found
                      subst found
                      exact ⟨index, segment, named, by simp [install], member,
                        leafOf_matches segment source state.used page⟩
                    · simp only [member, Bool.false_eq_true, ↓reduceIte] at found
                      obtain ⟨i, s, hi, loaded, inS, fits⟩ := (exact page).1 leaf found
                      refine ⟨i, s, hi, ?_, inS, fits⟩
                      simp only [install]
                      split <;> simp_all
                  · simp only [install] at otherNamed otherLoaded ⊢
                    by_cases member : inSegment segment page = true
                    · simp [member]
                    · simp only [member, Bool.false_eq_true, ↓reduceIte]
                      by_cases same : other = index
                      · subst same
                        rw [named] at otherNamed
                        cases otherNamed
                        exact absurd otherIn (by simp [member])
                      · simp only [same, ↓reduceIte] at otherLoaded
                        exact (exact page).2 other otherSegment otherNamed otherLoaded otherIn

/-- **The child holds exactly the admitted segments.**  When `start` succeeds
on an exact state, every segment of the admitted plan is loaded, and the
child's pages are exactly the pages of the plan's segments: each with its
segment's permissions, copied when writable and in place otherwise. -/
theorem started_exact (state : State) (control : UInt64) (exact : Exact state)
    (started : (step state (.start control)).2 = .started) :
    let after := (step state (.start control)).1
    after.started = true ∧
      ∀ page, (∀ leaf, after.leaves page = some leaf →
          ∃ segment ∈ state.plan, inSegment segment page = true ∧ Matches segment leaf) ∧
        (∀ segment ∈ state.plan, inSegment segment page = true →
          ∃ leaf, after.leaves page = some leaf) := by
  intro after
  have shape : ∃ child, liveChild state control = some child ∧ allLoaded state = true := by
    simp only [step] at started
    cases live : liveChild state control with
    | none => simp [live] at started
    | some child =>
        simp only [live] at started
        by_cases all : allLoaded state = true
        · exact ⟨child, rfl, all⟩
        · simp [all] at started
  obtain ⟨child, live, all⟩ := shape
  have afterEq : after = { state with started := true } := by
    simp [after, step, live, all]
  rw [afterEq]
  refine ⟨rfl, fun page => ⟨fun leaf found => ?_, fun segment member inS => ?_⟩⟩
  · obtain ⟨index, segment, named, _, inS, fits⟩ := (exact page).1 leaf found
    exact ⟨segment, List.mem_of_getElem? named, inS, fits⟩
  · obtain ⟨index, indexLt, eq⟩ := List.getElem_of_mem member
    have named : state.plan[index]? = some segment := by
      rw [List.getElem?_eq_getElem indexLt, eq]
    have loaded : state.loaded index = true := by
      simp only [allLoaded, List.all_eq_true, List.mem_range] at all
      exact all index indexLt
    exact (exact page).2 index segment named loaded inS

/-- With the admitted layout, the leaf of a page matches every segment that
contains the page: segments share no page, so there is exactly one. -/
theorem started_exact_unique (state : State) (control : UInt64) (layout : PlanLayout state.plan)
    (exact : Exact state) (started : (step state (.start control)).2 = .started)
    (page : Nat) (segment : Segment) (member : segment ∈ state.plan)
    (inside : inSegment segment page = true) :
    ∃ leaf, (step state (.start control)).1.leaves page = some leaf ∧ Matches segment leaf := by
  obtain ⟨_, both⟩ := started_exact state control exact started
  obtain ⟨found, cover⟩ := both page
  obtain ⟨leaf, hleaf⟩ := cover segment member inside
  obtain ⟨other, otherMember, otherIn, fits⟩ := found leaf hleaf
  refine ⟨leaf, hleaf, ?_⟩
  by_cases same : other = segment
  · subst same; exact fits
  · exfalso
    obtain ⟨i, iLt, iEq⟩ := List.getElem_of_mem otherMember
    obtain ⟨j, jLt, jEq⟩ := List.getElem_of_mem member
    have hi : state.plan[i]? = some other := by rw [List.getElem?_eq_getElem iLt, iEq]
    have hj : state.plan[j]? = some segment := by rw [List.getElem?_eq_getElem jLt, jEq]
    have different : i ≠ j := by
      intro eq; subst eq; rw [hi] at hj; cases hj; exact same rfl
    have disjoint := plan_disjoint layout hi hj different
    have := inSegment_disjoint (plan_aligned layout hi) (plan_aligned layout hj) disjoint page otherIn
    rw [this] at inside
    cases inside

/-! ## The generated witness

The kernel computes words from its load state and asks two allocation-free
witnesses.  `loaderSource` checks the claimed source against the read
authority and the admitted placement; `loaderDecide` takes the request kind,
a word of flags, the source check's answer, and the frame counts, and returns
the model's reply (`encodeReply`).  `loader_witness_agrees` proves the pair
answers exactly the model's step whenever the kernel's words are the model
state's encoding. -/

def rejectionCode : Rejection → UInt64
  | .noChild => 1 | .started => 2 | .badIndex => 3 | .alreadyLoaded => 4
  | .outsideAuthority => 5 | .wrongSource => 6 | .inPlaceZeroFill => 7 | .noFrames => 8
  | .incomplete => 9

/-- The reply word: `1` loaded in place, `2` loaded by copy, `3` started,
`0x100 + code` refused without effect, `0x200 + code` rolled back. -/
def encodeReply (writable : Bool) : Reply → UInt64
  | .loaded => if writable then 2 else 1
  | .started => 3
  | .refused reason => 0x100 + rejectionCode reason
  | .rolledBack reason => 0x200 + rejectionCode reason

/-- **Source witness.**  `0` when `[source, source + span)` lies inside
`[start, stop)` and `source` is `start + fileOffset`; `5` when it is outside
the read authority; `6` when it is inside but not the admitted placement.  The
range test is written without overflow. -/
@[export leanos_loader_source]
def loaderSource (source start stop fileOffset span : UInt64) : UInt64 :=
  if source < start || stop < span || stop - span < source then 5
  else if source != start + fileOffset then 6
  else 0

/-- **Decision witness.**  Flag bits: 0 the control word names the live,
unstarted child; 1 the named child was already started; 2 the index names a
segment; 3 that segment is loaded; 4 it is writable; 5 its memory image is
larger than its file image; 6 every segment is loaded. -/
@[export leanos_loader_decide]
def loaderDecide (op flags sourceCode pages frames used : UInt64) : UInt64 :=
  if op == 1 then
    if flags &&& 1 == 0 then (if flags &&& 2 == 0 then 0x101 else 0x102)
    else if flags &&& 4 == 0 then 0x203
    else if flags &&& 8 != 0 then 0x204
    else if sourceCode == 5 then 0x205
    else if sourceCode != 0 then 0x206
    else if flags &&& 16 == 0 && flags &&& 32 != 0 then 0x207
    else if flags &&& 16 != 0 && (frames < used || frames - used < pages) then 0x208
    else if flags &&& 16 != 0 then 2
    else 1
  else if op == 2 then
    if flags &&& 1 == 0 then (if flags &&& 2 == 0 then 0x101 else 0x102)
    else if flags &&& 64 == 0 then 0x209
    else 3
  else 0x1ff

def bit (condition : Bool) (value : UInt64) : UInt64 := if condition then value else 0

/-- The flags word of seven conditions. -/
def flagsOf (live started named loaded writable zeroFill all : Bool) : UInt64 :=
  bit live 1 ||| bit started 2 ||| bit named 4 ||| bit loaded 8 ||| bit writable 16 |||
    bit zeroFill 32 ||| bit all 64

/-- The flags word of a request in a model state. -/
def flagsWord (state : State) : Request → UInt64
  | .load control index _ =>
      flagsOf (liveChild state control).isSome (state.child.isSome && state.started)
        (state.plan[index]?).isSome (state.loaded index)
        ((state.plan[index]?.map (·.writable)).getD false)
        ((state.plan[index]?.map (fun s => s.memBytes != s.fileBytes)).getD false)
        (allLoaded state)
  | .start control =>
      flagsOf (liveChild state control).isSome (state.child.isSome && state.started) false false
        false false (allLoaded state)

def opWord : Request → UInt64
  | .load .. => 1
  | .start _ => 2

/-- The writability the reply word reports for a load. -/
def requestWritable (state : State) : Request → Bool
  | .load _ index _ => (state.plan[index]?.map (·.writable)).getD false
  | .start _ => false

/-! ## The witnesses agree with the model -/

theorem toNat_ofNat_small {value : Nat} (small : value < 2 ^ 64) :
    (UInt64.ofNat value).toNat = value := UInt64.toNat_ofNat_of_lt' small

theorem ofNat_lt_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (UInt64.ofNat a < UInt64.ofNat b) ↔ a < b := by
  rw [UInt64.lt_iff_toNat_lt, toNat_ofNat_small ha, toNat_ofNat_small hb]

/-- The source witness is the model's range and placement test, for words
below `2^62`. -/
theorem loaderSource_agrees (source start stop fileOffset span : Nat)
    (sourceSmall : source < 2 ^ 62) (startSmall : start < 2 ^ 62) (stopSmall : stop < 2 ^ 62)
    (offsetSmall : fileOffset < 2 ^ 62) (spanSmall : span < 2 ^ 62) :
    loaderSource (UInt64.ofNat source) (UInt64.ofNat start) (UInt64.ofNat stop)
        (UInt64.ofNat fileOffset) (UInt64.ofNat span) =
      (if !(decide (start ≤ source) && decide (source + span ≤ stop)) then 5
        else if source ≠ start + fileOffset then 6 else 0) := by
  have big : (2 : Nat) ^ 62 < 2 ^ 64 := by decide
  have lowCheck := ofNat_lt_ofNat (a := source) (b := start) (by omega) (by omega)
  have spanCheck := ofNat_lt_ofNat (a := stop) (b := span) (by omega) (by omega)
  unfold loaderSource
  by_cases low : source < start
  · have : (UInt64.ofNat source < UInt64.ofNat start) := lowCheck.2 low
    have notLe : ¬ start ≤ source := by omega
    simp [this, notLe]
  · have notLow : ¬ (UInt64.ofNat source < UInt64.ofNat start) := fun h => low (lowCheck.1 h)
    by_cases short : stop < span
    · have : (UInt64.ofNat stop < UInt64.ofNat span) := spanCheck.2 short
      have notFit : ¬ source + span ≤ stop := by omega
      simp [notLow, this, notFit]
    · have notShort : ¬ (UInt64.ofNat stop < UInt64.ofNat span) := fun h => short (spanCheck.1 h)
      have subEq : (UInt64.ofNat stop - UInt64.ofNat span).toNat = stop - span := by
        rw [UInt64.toNat_sub_of_le]
        · rw [toNat_ofNat_small (by omega), toNat_ofNat_small (by omega)]
        · rw [UInt64.le_iff_toNat_le, toNat_ofNat_small (by omega), toNat_ofNat_small (by omega)]
          omega
      have fitCheck : (UInt64.ofNat stop - UInt64.ofNat span < UInt64.ofNat source) ↔
          stop - span < source := by
        rw [UInt64.lt_iff_toNat_lt, subEq, toNat_ofNat_small (by omega)]
      have sumEq : (UInt64.ofNat start + UInt64.ofNat fileOffset).toNat = start + fileOffset := by
        rw [UInt64.toNat_add, toNat_ofNat_small (by omega), toNat_ofNat_small (by omega)]
        exact Nat.mod_eq_of_lt (by omega)
      have placed : (UInt64.ofNat source != UInt64.ofNat start + UInt64.ofNat fileOffset) =
          decide (source ≠ start + fileOffset) := by
        by_cases same : source = start + fileOffset
        · have : UInt64.ofNat source = UInt64.ofNat start + UInt64.ofNat fileOffset := by
            apply UInt64.toNat_inj.1
            rw [sumEq, toNat_ofNat_small (by omega), same]
          simp [this, same]
        · have : UInt64.ofNat source ≠ UInt64.ofNat start + UInt64.ofNat fileOffset := by
            intro eq
            have := congrArg UInt64.toNat eq
            rw [sumEq, toNat_ofNat_small (by omega)] at this
            exact same this
          simp [this, same]
      by_cases fits : stop - span < source
      · have notFit : ¬ source + span ≤ stop := by omega
        simp [notLow, notShort, fitCheck.2 fits, notFit]
      · have notFitCheck : ¬ (UInt64.ofNat stop - UInt64.ofNat span < UInt64.ofNat source) :=
          fun h => fits (fitCheck.1 h)
        have fit : source + span ≤ stop := by omega
        have le : start ≤ source := by omega
        simp only [notLow, notShort, notFitCheck, decide_false, Bool.or_false, Bool.false_or,
          Bool.false_eq_true, ↓reduceIte, placed, le, fit, decide_true, Bool.and_self,
          Bool.not_true]
        by_cases same : source = start + fileOffset <;> simp [same]

/-- The frame test: the child lacks frames exactly when its frames are fewer
than the used ones plus the segment's pages. -/
theorem frames_short_agrees (frames used pages : Nat) (framesSmall : frames < 2 ^ 62)
    (usedSmall : used < 2 ^ 62) (pagesSmall : pages < 2 ^ 62) :
    (decide (UInt64.ofNat frames < UInt64.ofNat used) ||
        decide (UInt64.ofNat frames - UInt64.ofNat used < UInt64.ofNat pages)) =
      decide (frames < used + pages) := by
  have big : (2 : Nat) ^ 62 < 2 ^ 64 := by decide
  by_cases under : frames < used
  · have : UInt64.ofNat frames < UInt64.ofNat used := (ofNat_lt_ofNat (by omega) (by omega)).2 under
    have : frames < used + pages := by omega
    simp [*]
  · have notUnder : ¬ UInt64.ofNat frames < UInt64.ofNat used :=
      fun h => under ((ofNat_lt_ofNat (by omega) (by omega)).1 h)
    have subEq : (UInt64.ofNat frames - UInt64.ofNat used).toNat = frames - used := by
      rw [UInt64.toNat_sub_of_le]
      · rw [toNat_ofNat_small (by omega), toNat_ofNat_small (by omega)]
      · rw [UInt64.le_iff_toNat_le, toNat_ofNat_small (by omega), toNat_ofNat_small (by omega)]
        omega
    have short : (UInt64.ofNat frames - UInt64.ofNat used < UInt64.ofNat pages) ↔
        frames - used < pages := by
      rw [UInt64.lt_iff_toNat_lt, subEq, toNat_ofNat_small (by omega)]
    by_cases lacking : frames - used < pages
    · have : frames < used + pages := by omega
      simp [notUnder, short.2 lacking, this]
    · have : ¬ frames < used + pages := by omega
      have notShort : ¬ (UInt64.ofNat frames - UInt64.ofNat used < UInt64.ofNat pages) :=
        fun h => lacking (short.1 h)
      simp [notUnder, notShort, this]

/-- Reading back the flag bits. -/
theorem flags_bits (a b c d e f g : Bool) :
    let word := flagsOf a b c d e f g
    (word &&& 1 == 0) = !a ∧ (word &&& 2 == 0) = !b ∧ (word &&& 4 == 0) = !c ∧
      (word &&& 8 != 0) = d ∧ (word &&& 16 == 0) = !e ∧ (word &&& 16 != 0) = e ∧
      (word &&& 32 != 0) = f ∧ (word &&& 64 == 0) = !g := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> decide

theorem start_flags_bits (a b g : Bool) :
    let word := flagsOf a b false false false false g
    (word &&& 1 == 0) = !a ∧ (word &&& 2 == 0) = !b ∧ (word &&& 64 == 0) = !g := by
  cases a <;> cases b <;> cases g <;> decide

/-- Every number the kernel hands the witnesses is below `2^62`. -/
structure Small (state : State) : Prop where
  start : state.start < 2 ^ 62
  stop : state.stop < 2 ^ 62
  used : state.used < 2 ^ 62
  frames : ∀ child, state.child = some child → child.frames < 2 ^ 62
  segments : ∀ segment ∈ state.plan, segment.fileOffset < 2 ^ 62 ∧
    pageCount segment * pageBytes < 2 ^ 62

/-- The decision witness for a load, read through its flag bits. -/
theorem loaderDecide_load (sourceCode pages frames used : UInt64) (live started named loaded
    writable zeroFill all : Bool) :
    loaderDecide 1 (flagsOf live started named loaded writable zeroFill all) sourceCode pages
      frames used =
      if !live then (if !started then 0x101 else 0x102)
      else if !named then 0x203
      else if loaded then 0x204
      else if sourceCode == 5 then 0x205
      else if sourceCode != 0 then 0x206
      else if !writable && zeroFill then 0x207
      else if writable && (decide (frames < used) || decide (frames - used < pages)) then 0x208
      else if writable then 2
      else 1 := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, _⟩ := flags_bits live started named loaded writable zeroFill all
  simp only [loaderDecide, beq_self_eq_true, ↓reduceIte, b1, b2, b3, b4, b5, b6, b7]

/-- The decision witness for a start, read through its flag bits. -/
theorem loaderDecide_start (sourceCode pages frames used : UInt64) (live started all : Bool) :
    loaderDecide 2 (flagsOf live started false false false false all) sourceCode pages frames
      used =
      if !live then (if !started then 0x101 else 0x102)
      else if !all then 0x209 else 3 := by
  obtain ⟨b1, b2, b3⟩ := start_flags_bits live started all
  simp only [loaderDecide, show ((2 : UInt64) == 1) = false by decide, Bool.false_eq_true,
    ↓reduceIte, beq_self_eq_true, b1, b2, b3]

/-- **The start witness is the model.** -/
theorem loader_witness_agrees_start (state : State) (control : UInt64)
    (sourceCode pages frames used : UInt64) :
    loaderDecide 2 (flagsWord state (.start control)) sourceCode pages frames used =
      encodeReply false (step state (.start control)).2 := by
  simp only [flagsWord, loaderDecide_start, step]
  cases live : liveChild state control with
  | none =>
      cases started : (state.child.isSome && state.started) <;>
        simp [encodeReply, rejectionCode]
  | some child =>
      cases all : allLoaded state <;> simp [encodeReply, rejectionCode]

/-- **The load witnesses are the model.**  For a state whose words are small
and a load whose claimed source is small, the decision witness over the
kernel's words (the flags, the source witness's answer for the named segment,
its pages, the child's frames, the used frames) returns exactly the encoded
reply of the model's step. -/
theorem loader_witness_agrees_load (state : State) (control : UInt64) (index source : Nat)
    (small : Small state) (sourceSmall : source < 2 ^ 62) :
    let segment := state.plan[index]?
    let sourceCode := match segment with
      | some s => loaderSource (UInt64.ofNat source) (UInt64.ofNat state.start)
          (UInt64.ofNat state.stop) (UInt64.ofNat s.fileOffset)
          (UInt64.ofNat (pageCount s * pageBytes))
      | none => 0
    let pages := UInt64.ofNat ((segment.map pageCount).getD 0)
    let frames := UInt64.ofNat ((state.child.map (·.frames)).getD 0)
    loaderDecide 1 (flagsWord state (.load control index source)) sourceCode pages frames
        (UInt64.ofNat state.used) =
      encodeReply (requestWritable state (.load control index source))
        (step state (.load control index source)).2 := by
  intro segment sourceCode pages frames
  simp only [flagsWord, loaderDecide_load, step, requestWritable]
  cases live : liveChild state control with
  | none =>
      cases started : (state.child.isSome && state.started) <;>
        simp [encodeReply, rejectionCode]
  | some child =>
      have childFrames : (state.child.map (·.frames)).getD 0 = child.frames := by
        simp only [liveChild] at live
        cases found : state.child with
        | none => simp [found] at live
        | some actual =>
            simp only [found] at live
            split at live
            · cases live; rfl
            · cases live
      have framesSmall : child.frames < 2 ^ 62 := by
        simp only [liveChild] at live
        cases found : state.child with
        | none => simp [found] at live
        | some actual =>
            simp only [found] at live
            split at live
            · cases live; exact small.frames _ found
            · cases live
      simp only [Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases named : state.plan[index]? with
      | none =>
          simp [segment, named, loadCheck, encodeReply, rejectionCode]
      | some found =>
          have member : found ∈ state.plan := List.mem_of_getElem? named
          obtain ⟨offsetSmall, spanSmall⟩ := small.segments found member
          have pagesSmall : pageCount found < 2 ^ 62 := by
            have : pageCount found ≤ pageCount found * pageBytes := by
              simp only [ElfAdmission.pageBytes]; omega
            omega
          have sourceEq : sourceCode = (if !(decide (state.start ≤ source) &&
              decide (source + pageCount found * pageBytes ≤ state.stop)) then 5
              else if source ≠ state.start + found.fileOffset then 6 else 0) := by
            simp only [sourceCode, segment, named]
            exact loaderSource_agrees source state.start state.stop found.fileOffset
              (pageCount found * pageBytes) sourceSmall small.start small.stop offsetSmall spanSmall
          have framesShort := frames_short_agrees child.frames state.used (pageCount found)
            framesSmall small.used pagesSmall
          simp only [segment, named, Option.isSome_some, Option.map_some, Option.getD_some,
            Bool.not_true, Bool.false_eq_true, ↓reduceIte, sourceEq, pages, frames, childFrames,
            framesShort, loadCheck]
          cases loaded : state.loaded index
          · simp only [Bool.false_eq_true, ↓reduceIte]
            by_cases inside : state.start ≤ source ∧
                source + pageCount found * pageBytes ≤ state.stop
            · have insideB : (decide (state.start ≤ source) &&
                  decide (source + pageCount found * pageBytes ≤ state.stop)) = true := by
                simp [inside.1, inside.2]
              simp only [insideB, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              by_cases placed : source = state.start + found.fileOffset
              · simp only [placed, ne_eq, not_true_eq_false, ↓reduceIte,
                  show ((0 : UInt64) == 5) = false by decide,
                  show ((0 : UInt64) != 0) = false by decide, Bool.false_eq_true]
                by_cases writable : found.writable = true
                · by_cases short : child.frames < state.used + pageCount found
                  · simp [writable, short, encodeReply, rejectionCode]
                  · simp [writable, short, encodeReply]
                · have notWritable : found.writable = false := by simpa using writable
                  by_cases same : found.memBytes = found.fileBytes
                  · simp [notWritable, same, encodeReply]
                  · simp [notWritable, same, encodeReply, rejectionCode]
              · simp [placed, encodeReply, rejectionCode]
            · have outsideB : (decide (state.start ≤ source) &&
                  decide (source + pageCount found * pageBytes ≤ state.stop)) = false := by
                simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
                omega
              simp [outsideB, encodeReply, rejectionCode]
          · simp [encodeReply, rejectionCode]

end LeanOS.ChildLoader
