import LeanOS.FrameCopyWindow

/-!
# Frame-window roots in word form (issue #599)

`LeanOS.FrameCopyWindow` proves its isolation theorems about a window root
`windowRoot closed g w` built over a root that is `Closed` for the protected
frames. The kernel builds those roots in C, with `frame_window_build`
(`include/frame_copy_window.h`) over the copy-root builder
(`include/qotom_copy_root_builder.h`).

The QuickProof law `window_roots_isolated`
(`experiments/quickproof/copy-roots`, ADR 0030) proves under CompCert's C
semantics what an accepted build leaves in memory, for every source root,
inventory, window and physical placement:

* the geometry is the reviewed one (`FrameCopyWindow.geometryOk`);
* each root's only non-leaf entries name its own eight page tables, so only
  the 4096 arena pages are mapped;
* every closed leaf is `closedWord frames s` of its source leaf `s`;
* every fetch and send leaf is `windowWord` of the closed leaves.

This module states those leaf equations in Lean and proves that they are
exactly the model's hypotheses: decoded as the processor reads a 4 KiB leaf,
the closed leaves form a `Closed` root for the inventory
(`closedWord_closed`), and the fetch and send leaves form `windowRoot` of it,
writable and read-only (`windowWord_decode`). So every isolation theorem of
`FrameCopyWindow` applies to the roots the C builds (`window_roots_of_words`,
`window_roots_protected`, `window_roots_other_absent`).

The two definitions transcribe the C law's expressions. Reading the two as
the same is the one step between the tools that stays trusted, as for the
early text console (#597). `windowWord` writes the slot test in natural
numbers, where the C law adds `slot + pages` in `uint64_t`. Under the
reviewed geometry `slot + pages ≤ 4096`, so the sum does not wrap and the
two tests agree.
-/

namespace LeanOS.FrameWindowWords

open FrameCopyWindow

/-- Bits 12..51 of a leaf, `QOTOM_ROOT_ADDRESS_MASK`. -/
def addressMask : UInt64 := 0x000ffffffffff000

/-- The no-execute bit, `QOTOM_ROOT_NX`. -/
def nxBit : UInt64 := 0x8000000000000000

/-- The frame a leaf word names: `(word & QOTOM_ROOT_ADDRESS_MASK) >> 12`. -/
def frameWord (word : UInt64) : UInt64 := (word &&& addressMask) >>> 12

/-- The present leaf a page-table word encodes, as the processor reads a
4 KiB leaf: present is bit 0, the frame bits 12..51, writable bit 1, user
bit 2 and no-execute bit 63. -/
def decodeLeaf (word : UInt64) : Option Leaf :=
  if word &&& 1 = 0 then none
  else some { frame := (frameWord word).toNat, writable := word &&& 2 != 0,
              user := word &&& 4 != 0, nx := word &&& nxBit != 0 }

/-- A root over the arena from its 4096 leaf words. The law proves that a
built root's only non-leaf entries name its own page tables, so no other
virtual page is mapped. -/
def decodeRoot (leaves : Nat → UInt64) : Root := fun p =>
  if p < arenaPages then decodeLeaf (leaves p) else none

/-- The inventory as the model's protected-frame predicate. -/
def Protected (frames : List UInt64) (f : Nat) : Prop := ∃ x ∈ frames, x.toNat = f

/-- The closed leaf the law states for source leaf `s`: `gone ? 0 : s`, where
`gone` is `(s & QOTOM_ROOT_PRESENT) != 0 &&
member((s & QOTOM_ROOT_ADDRESS_MASK) >> 12, frames, n)`. -/
def closedWord (frames : List UInt64) (s : UInt64) : UInt64 :=
  if s &&& 1 ≠ 0 ∧ frameWord s ∈ frames then 0 else s

/-- The window-root leaf the law states at page `p`. At an alias slot it is
`(((base >> 12) + (p - slot)) << 12) | QOTOM_ROOT_PRESENT | QOTOM_ROOT_NX`,
plus `QOTOM_ROOT_WRITABLE` in the fetch root. Elsewhere it is the closed
leaf. -/
def windowWord (closed : Nat → UInt64) (base limit slot : UInt64) (writable : Bool)
    (p : Nat) : UInt64 :=
  if slot.toNat ≤ p ∧ p < slot.toNat + ((limit - base) / 4096).toNat then
    ((((base >>> 12) + (UInt64.ofNat p - slot)) <<< 12) ||| 1 ||| nxBit) |||
      (if writable then 2 else 0)
  else closed p

/-! ## Bits of an alias leaf -/

private theorem high_bits_clear (f : UInt64) (hf : f.toNat < 2 ^ 40) :
    ∀ j, 40 ≤ j → f.toBitVec.getLsbD j = false := by
  intro j hj
  rw [BitVec.getLsbD, Nat.testBit_lt_two_pow]
  exact Nat.lt_of_lt_of_le hf (Nat.pow_le_pow_right (by decide) hj)

/-- The alias leaf of frame `f`, as `windowWord` writes it. -/
private def aliasWord (f : UInt64) (w : Bool) : UInt64 :=
  (((f <<< 12) ||| 1 ||| nxBit) ||| (if w then 2 else 0))

private theorem aliasWord_frame (f : UInt64) (w : Bool) (hf : f.toNat < 2 ^ 40) :
    frameWord (aliasWord f w) = f := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hbit := high_bits_clear f hf
  have hm1 : ∀ i < 40, Nat.testBit 4503599627366400 (12 + i) = true := by decide
  have hm2 : ∀ i < 64, 40 ≤ i → Nat.testBit 4503599627366400 (12 + i) = false := by decide
  have h1 : ∀ i < 64, Nat.testBit 1 (12 + i) = false := by decide
  have h2 : ∀ i < 64, Nat.testBit 2 (12 + i) = false := by decide
  have hnx : ∀ i < 40, Nat.testBit 9223372036854775808 (12 + i) = false := by decide
  cases w <;>
  · simp [frameWord, aliasWord, addressMask, nxBit, BitVec.getLsbD_ofNat,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, h1 i hi, h2 i hi]
    by_cases h40 : i < 40
    · have ha : 12 + i < 64 := by omega
      have hb : ¬ 12 + i < 12 := by omega
      simp [hm1 i h40, hnx i h40, ha, hb]
    · simp [hm2 i hi (by omega), hbit i (by omega)]

/-- The low and no-execute bits of an alias leaf: present, writable exactly
when `w`, never user, always no-execute. -/
private theorem aliasWord_flags (f : UInt64) (w : Bool) (hf : f.toNat < 2 ^ 40) :
    aliasWord f w &&& 1 = 1 ∧ (aliasWord f w &&& 2 != 0) = w ∧
      aliasWord f w &&& 4 = 0 ∧ aliasWord f w &&& nxBit = nxBit := by
  have hbit := high_bits_clear f hf
  have e : ∀ (m : UInt64) (r : UInt64),
      (∀ i < 64, (aliasWord f w &&& m).toBitVec.getLsbD i = r.toBitVec.getLsbD i) →
        aliasWord f w &&& m = r := fun m r h =>
    UInt64.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun i hi => h i hi)
  have bits : ∀ i < 64, i < 12 → Nat.testBit 9223372036854775808 i = false := by decide
  have one : ∀ i < 64, Nat.testBit 1 i = decide (i = 0) := by decide
  have two : ∀ i < 64, Nat.testBit 2 i = decide (i = 1) := by decide
  have four : ∀ i < 64, Nat.testBit 4 i = decide (i = 2) := by decide
  have top : ∀ i < 64, Nat.testBit 9223372036854775808 i = decide (i = 63) := by decide
  refine ⟨e 1 1 ?_, ?_, e 4 0 ?_, e nxBit nxBit ?_⟩
  · intro i hi
    cases w <;> simp [aliasWord, nxBit, BitVec.getLsbD_ofNat, BitVec.getLsbD_shiftLeft,
      one i hi, two i hi, top i hi] <;> omega
  · have h2 : aliasWord f w &&& 2 = (if w then 2 else 0) := by
      apply e
      intro i hi
      cases w <;> simp [aliasWord, nxBit, BitVec.getLsbD_ofNat, BitVec.getLsbD_shiftLeft,
        one i hi, two i hi, top i hi] <;> omega
    rw [h2]; cases w <;> decide
  · intro i hi
    cases w <;> simp [aliasWord, nxBit, BitVec.getLsbD_ofNat, BitVec.getLsbD_shiftLeft,
      one i hi, two i hi, four i hi, top i hi] <;> omega
  · intro i hi
    by_cases h63 : i = 63
    · subst h63
      cases w <;> simp [aliasWord, nxBit]
    · cases w <;> simp [aliasWord, nxBit, BitVec.getLsbD_ofNat, BitVec.getLsbD_shiftLeft,
        one i hi, two i hi, top i hi, h63] <;>
        (intro _; exact hbit (i - 12) (by omega))

private theorem decode_aliasWord (f : UInt64) (w : Bool) (hf : f.toNat < 2 ^ 40) :
    decodeLeaf (aliasWord f w) =
      some { frame := f.toNat, writable := w, user := false, nx := true } := by
  obtain ⟨h1, h2, h4, hnx⟩ := aliasWord_flags f w hf
  unfold decodeLeaf
  rw [h1, h2, h4, hnx, aliasWord_frame f w hf]
  simp [nxBit]

/-! ## The closed root and the window roots -/

/-- The closed leaves the law states form a root that is closed for the
inventory: no present leaf names a frame of it. -/
theorem closedWord_closed (frames : List UInt64) (source : Nat → UInt64) :
    Closed (decodeRoot fun p => closedWord frames (source p)) (Protected frames) := by
  intro p l h ⟨x, hx, hxf⟩
  simp only [decodeRoot] at h
  split at h
  · simp only [closedWord] at h
    split at h
    · simp [decodeLeaf] at h
    · rename_i hgone
      simp only [decodeLeaf] at h
      split at h
      · exact absurd h (by simp)
      · rename_i hp
        simp only [Option.some.injEq] at h
        subst h
        have : x = frameWord (source p) := UInt64.toNat_inj.mp hxf
        exact hgone ⟨hp, this ▸ hx⟩
  · exact absurd h (by simp)

/-- Under the reviewed geometry, the window-root leaves the law states decode
to the model's `windowRoot` of the decoded closed root. -/
theorem windowWord_decode (closed : Nat → UInt64) (base limit slot : UInt64) (w : Bool)
    (h : geometryOk base limit slot = true) :
    decodeRoot (windowWord closed base limit slot w) =
      windowRoot (decodeRoot closed) (geometryOf base limit slot) w := by
  obtain ⟨hal, hlt, harena, hpages, hslot, hsum⟩ := geometryOk_nat base limit slot h
  have hsub : (limit - base).toNat = limit.toNat - base.toNat :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))
  have hpg : ((limit - base) / 4096).toNat = (limit.toNat - base.toNat) / 4096 := by
    rw [UInt64.toNat_div, hsub]; rfl
  funext p
  simp only [decodeRoot, windowRoot, windowWord, geometryOf, hpg]
  by_cases hs : slot.toNat ≤ p ∧ p < slot.toNat + (limit.toNat - base.toNat) / 4096
  · have hp : p < arenaPages := by simp only [arenaPages]; omega
    simp only [hp, hs, and_self, ite_true]
    have hslotp : slot ≤ UInt64.ofNat p := by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]; exact hs.1
    have hdiff : (UInt64.ofNat p - slot).toNat = p - slot.toNat := by
      rw [UInt64.toNat_sub_of_le _ _ hslotp, UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]
    have hshift : (base >>> 12).toNat = base.toNat / 4096 := by
      rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
    have hf : ((base >>> 12) + (UInt64.ofNat p - slot)).toNat =
        base.toNat / 4096 + (p - slot.toNat) := by
      rw [UInt64.toNat_add, hshift, hdiff, Nat.mod_eq_of_lt (by omega)]
    have hfb : ((base >>> 12) + (UInt64.ofNat p - slot)).toNat < 2 ^ 40 := by
      rw [hf]; omega
    have := decode_aliasWord ((base >>> 12) + (UInt64.ofNat p - slot)) w hfb
    simp only [aliasWord] at this
    rw [this, hf]
    simp [pageBytes]
  · simp only [hs, ite_false]

/-- The roots the C builds satisfy the model's hypotheses. When the leaves
of the closed, fetch and send roots are what the QuickProof law
`window_roots_isolated` states, the closed root is `Closed` for the
inventory, and the fetch and send roots are its `windowRoot`, writable and
read-only. -/
theorem window_roots_of_words (frames : List UInt64) (source closed fetch send : Nat → UInt64)
    (base limit slot : UInt64) (hgeom : geometryOk base limit slot = true)
    (hclosed : ∀ p < arenaPages, closed p = closedWord frames (source p))
    (hfetch : ∀ p < arenaPages, fetch p = windowWord closed base limit slot true p)
    (hsend : ∀ p < arenaPages, send p = windowWord closed base limit slot false p) :
    Closed (decodeRoot closed) (Protected frames) ∧
      decodeRoot fetch = windowRoot (decodeRoot closed) (geometryOf base limit slot) true ∧
      decodeRoot send = windowRoot (decodeRoot closed) (geometryOf base limit slot) false := by
  have hroot : ∀ a b : Nat → UInt64, (∀ p < arenaPages, a p = b p) →
      decodeRoot a = decodeRoot b := fun a b hab => by
    funext p; simp only [decodeRoot]; split
    · rename_i hp; rw [hab p hp]
    · rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hroot closed (fun p => closedWord frames (source p)) hclosed]
    exact closedWord_closed frames source
  · rw [hroot fetch _ hfetch]; exact windowWord_decode closed base limit slot true hgeom
  · rw [hroot send _ hsend]; exact windowWord_decode closed base limit slot false hgeom

/-- So, under the law's leaf equations, a window root the kernel builds maps
a frame of the inventory only at an alias slot, as a supervisor no-execute
alias of one of the window's own frames, writable exactly in the fetch root
(`FrameCopyWindow.windowRoot_protected`). -/
theorem window_roots_protected (frames : List UInt64) (source closed fetch send : Nat → UInt64)
    (base limit slot : UInt64) (hgeom : geometryOk base limit slot = true)
    (hclosed : ∀ p < arenaPages, closed p = closedWord frames (source p))
    (hfetch : ∀ p < arenaPages, fetch p = windowWord closed base limit slot true p)
    (hsend : ∀ p < arenaPages, send p = windowWord closed base limit slot false p)
    (w : Bool) (p : Nat) (l : Leaf)
    (h : decodeRoot (if w then fetch else send) p = some l) (hp : Protected frames l.frame) :
    let g := geometryOf base limit slot
    (g.slot ≤ p ∧ p < g.slot + g.pages) ∧ g.owns l.frame ∧ l.user = false ∧ l.nx = true ∧
      l.writable = w := by
  obtain ⟨hc, hf, hs⟩ :=
    window_roots_of_words frames source closed fetch send base limit slot hgeom hclosed hfetch hsend
  cases w
  · simp only [Bool.false_eq_true, ite_false] at h
    rw [hs] at h
    exact windowRoot_protected _ _ hc _ false p l h hp
  · simp only [ite_true] at h
    rw [hf] at h
    exact windowRoot_protected _ _ hc _ true p l h hp

/-- In particular such a root maps no frame of another subject: no frame of
the inventory outside the window's own (`FrameCopyWindow.windowRoot_other_absent`). -/
theorem window_roots_other_absent (frames : List UInt64) (source closed fetch send : Nat → UInt64)
    (base limit slot : UInt64) (hgeom : geometryOk base limit slot = true)
    (hclosed : ∀ p < arenaPages, closed p = closedWord frames (source p))
    (hfetch : ∀ p < arenaPages, fetch p = windowWord closed base limit slot true p)
    (hsend : ∀ p < arenaPages, send p = windowWord closed base limit slot false p)
    (other : Nat → Prop) (hother : ∀ f, other f → Protected frames f)
    (hdisj : ∀ f, other f → ¬ (geometryOf base limit slot).owns f)
    (w : Bool) (p : Nat) (l : Leaf) (h : decodeRoot (if w then fetch else send) p = some l) :
    ¬ other l.frame := fun ho =>
  hdisj _ ho (window_roots_protected frames source closed fetch send base limit slot hgeom
    hclosed hfetch hsend w p l h (hother _ ho)).2.1

end LeanOS.FrameWindowWords
