import LeanOS.DhcpSubject

/-!
# Frame copy windows (issue #569)

The frame endpoint copies whole Ethernet frames between the kernel's
endpoint slots and a port holder's own window (`LeanOS.NetworkSubject`,
`LeanOS.DhcpSubject`). On q35 the copy runs through the SMAP user-copy
window. The Qotom's J1900 has no SMAP, so its lab image copied frames
through the audited bounded copy roots instead: sixteen bytes per transfer,
aliasing only subject A's stack pages (ADR 0017). That forced the DHCP
subject and the echo subject to take turns in subject A, and a ping took
about 125 ms.

A **copy window** replaces those roots for frame transport. For each port
holder the kernel builds, before any subject runs, two *window roots* from
one closed source root, which maps no user frame of any subject:

* the **fetch root** adds supervisor, no-execute, *writable* aliases of the
  holder's window frames at reserved alias slots;
* the **send root** adds the same aliases *read-only*.

A copy selects the caller's window root, moves the whole frame (at most
1514 bytes) with one string move through the aliases, and reselects the
root it came from. No other subject's frame is mapped while the window is
open, and the window root never grants user access or execution.

This module models the window roots over 4 KiB leaves and the string move
as a sequence of byte stores or loads through the selected root, and
proves:

* **Only the holder's own frames**: a window root maps a protected (user)
  frame only at an alias slot, only as a supervisor no-execute alias of one
  of the holder's own window frames, writable exactly in the fetch root
  (`windowRoot_protected`); in particular it maps no frame of any other
  subject (`windowRoot_other_absent`).
* **Exact translation**: the alias of every window byte translates to that
  byte's own physical address (`translate_alias`).
* **Exact footprint**: through the fetch root, storing a frame at the alias
  of an address whose range the window covers stores exactly the model's
  `writeBytes` at that address (`storeAll_alias`); through either root,
  loading reads exactly the model's `readBytes` (`loadAll_alias`); the send
  root cannot store at all (`storeAll_readonly`).
* **The confinement carries over**: when physical memory agrees with the
  model's per-subject memory on every owned frame (`Rel`), an accepted
  fetch through the fetch root yields exactly the memory of
  `DhcpSubject.step`'s fetch and changes no byte outside the caller's
  window (`fetch_refines`, `fetch_footprint`), and an accepted send through
  the send root reads exactly the frame `DhcpSubject.step`'s send puts in
  the transmit slot (`send_refines`). The same holds for the one-port
  network-subject endpoint (`network_fetch_refines`,
  `network_send_refines`). So every confinement theorem of
  `DhcpSubject` and `NetworkSubject` (claims SC-DHCP-SUBJECT-SEPARATION and
  SC-NETWORK-SUBJECT-CONFINEMENT) describes the copies the window performs.
* **The kernel's operand**: the allocation-free export
  `leanos_frame_window_operand`, which the kernel calls on every copy
  request, returns a nonzero alias address exactly when the frame port
  witness `leanos_frame_port_check` accepts and the window geometry is the
  reviewed one (`frameWindowOperand_ne_zero_iff`), and that address is the
  alias of the requested buffer (`frameWindowOperand_alias`), so the string
  move touches exactly the bytes the model's step does
  (`frameWindowOperand_fetch`, `frameWindowOperand_send`).

Not modelled: the construction of the roots from the boot page tables
(`include/qotom_copy_root_builder.h`, checked by the kernel's exact scans),
CR3 loads and TLB invalidation (the transfer reloads CR3 and reads it back,
with PCID and global pages disabled), interrupts during the move (the
kernel keeps IF clear), the string move instruction itself and the
compiler. The booted kernel is tested, not proved, against this model.
-/

namespace LeanOS.FrameCopyWindow

open NetworkSubject (Window writeBytes readBytes update minFrame maxFrame)

/-- Bytes in a page, and the pages of the 16 MiB arena both platforms map
with 4 KiB leaves. -/
def pageBytes : Nat := 4096
def arenaPages : Nat := 4096

/-- A present leaf: its physical frame and its permissions. -/
structure Leaf where
  frame : Nat
  writable : Bool
  user : Bool
  nx : Bool
  deriving DecidableEq, Repr

/-- A root over the arena: each virtual page's present leaf, if any. -/
abbrev Root := Nat → Option Leaf

/-- The physical address virtual address `va` translates to under `r`, with
the leaf that maps it. -/
def translate (r : Root) (va : Nat) : Option (Nat × Leaf) :=
  (r (va / pageBytes)).map fun l => (l.frame * pageBytes + va % pageBytes, l)

/-- A port holder's copy window: `pages` pages at the page-aligned address
`base`, which the holder's own root maps to the identical physical frames
(both platforms identity-map the arena), and the first of the `pages`
virtual pages, `slot`, where a window root places its aliases. -/
structure Geometry where
  base : Nat
  pages : Nat
  slot : Nat
  deriving DecidableEq, Repr

/-- One past the window's last byte. -/
def Geometry.limit (g : Geometry) : Nat := g.base + g.pages * pageBytes

/-- The window as the endpoint models see it. -/
def Geometry.window (g : Geometry) : Window := ⟨g.base, g.limit⟩

/-- Frame `f` is one of the window's frames. -/
def Geometry.owns (g : Geometry) (f : Nat) : Prop :=
  g.base / pageBytes ≤ f ∧ f < g.base / pageBytes + g.pages

/-- The reviewed geometry: page aligned, one or two pages inside the arena,
and an alias slot range inside the arena above page 0. -/
def Geometry.ok (g : Geometry) : Prop :=
  g.base % pageBytes = 0 ∧ (g.pages = 1 ∨ g.pages = 2) ∧
    g.base / pageBytes + g.pages ≤ arenaPages ∧ 0 < g.slot ∧ g.slot + g.pages ≤ arenaPages

/-- The window root the kernel builds from the closed root `closed`: the
closed root with supervisor no-execute aliases of the window's frames at the
alias slots, writable for the fetch root and read-only for the send root. -/
def windowRoot (closed : Root) (g : Geometry) (writable : Bool) : Root := fun p =>
  if g.slot ≤ p ∧ p < g.slot + g.pages then
    some { frame := g.base / pageBytes + (p - g.slot), writable, user := false, nx := true }
  else closed p

/-- A root is closed for the protected frames when no present leaf maps
one. -/
def Closed (r : Root) (protectedFrame : Nat → Prop) : Prop :=
  ∀ p l, r p = some l → ¬ protectedFrame l.frame

/-! ## Only the holder's own frames -/

/-- Outside its alias slots a window root is the closed root. -/
theorem windowRoot_outside (closed : Root) (g : Geometry) (w : Bool) (p : Nat)
    (h : ¬ (g.slot ≤ p ∧ p < g.slot + g.pages)) : windowRoot closed g w p = closed p := by
  simp [windowRoot, h]

/-- Every alias a window root adds maps one of the window's own frames, as a
supervisor no-execute leaf whose write permission is the root's. -/
theorem windowRoot_alias (closed : Root) (g : Geometry) (w : Bool) (p : Nat) (l : Leaf)
    (hs : g.slot ≤ p ∧ p < g.slot + g.pages) (h : windowRoot closed g w p = some l) :
    g.owns l.frame ∧ l.user = false ∧ l.nx = true ∧ l.writable = w := by
  simp only [windowRoot, hs, and_self, ite_true, Option.some.injEq] at h
  subst h
  exact ⟨⟨by simp, by simp; omega⟩, rfl, rfl, rfl⟩

/-- A window root built from a closed root maps a protected frame only at an
alias slot, and only as a supervisor no-execute alias of one of the holder's
own window frames, writable exactly in the fetch root. -/
theorem windowRoot_protected (closed : Root) (prot : Nat → Prop) (hc : Closed closed prot)
    (g : Geometry) (w : Bool) (p : Nat) (l : Leaf) (h : windowRoot closed g w p = some l)
    (hp : prot l.frame) :
    (g.slot ≤ p ∧ p < g.slot + g.pages) ∧ g.owns l.frame ∧ l.user = false ∧ l.nx = true ∧
      l.writable = w := by
  by_cases hs : g.slot ≤ p ∧ p < g.slot + g.pages
  · exact ⟨hs, windowRoot_alias closed g w p l hs h⟩
  · rw [windowRoot_outside closed g w p hs] at h
    exact absurd hp (hc p l h)

/-- In particular a window root maps no frame of another subject: no frame
that is protected and not one of the holder's own window frames. -/
theorem windowRoot_other_absent (closed : Root) (prot : Nat → Prop) (hc : Closed closed prot)
    (g : Geometry) (w : Bool) (other : Nat → Prop) (hprot : ∀ f, other f → prot f)
    (hdisj : ∀ f, other f → ¬ g.owns f) (p : Nat) (l : Leaf)
    (h : windowRoot closed g w p = some l) : ¬ other l.frame := fun ho =>
  hdisj _ ho (windowRoot_protected closed prot hc g w p l h (hprot _ ho)).2.1

/-- No leaf of a window root grants user access to a protected frame. -/
theorem windowRoot_no_user (closed : Root) (prot : Nat → Prop) (hc : Closed closed prot)
    (g : Geometry) (w : Bool) (p : Nat) (l : Leaf) (h : windowRoot closed g w p = some l)
    (hp : prot l.frame) : l.user = false ∧ l.nx = true :=
  let r := windowRoot_protected closed prot hc g w p l h hp
  ⟨r.2.2.1, r.2.2.2.1⟩

/-! ## Exact translation -/

/-- The alias of window address `addr`: the same offset from the first alias
slot as `addr` from the window's base. -/
def alias (g : Geometry) (addr : Nat) : Nat := g.slot * pageBytes + (addr - g.base)

theorem covers_iff (w : Window) (addr len : Nat) :
    w.covers addr len = true ↔ w.base ≤ addr ∧ addr + len ≤ w.limit := by
  simp [Window.covers]

theorem window_covers_iff (g : Geometry) (addr len : Nat) :
    g.window.covers addr len = true ↔ g.base ≤ addr ∧ addr + len ≤ g.limit :=
  covers_iff _ _ _

theorem alias_succ (g : Geometry) (addr : Nat) (h : g.base ≤ addr) :
    alias g addr + 1 = alias g (addr + 1) := by
  unfold alias; omega

/-- The alias of every window byte translates, under either window root, to
that byte's own physical address, through a supervisor no-execute leaf of
the root's write permission. -/
theorem translate_alias (closed : Root) (g : Geometry) (w : Bool) (addr : Nat)
    (hb : g.base % pageBytes = 0) (h1 : g.base ≤ addr) (h2 : addr < g.limit) :
    translate (windowRoot closed g w) (alias g addr) =
      some (addr, { frame := addr / pageBytes, writable := w, user := false, nx := true }) := by
  have hd := Nat.div_add_mod (addr - g.base) pageBytes
  have hm := Nat.mod_lt (addr - g.base) (show 0 < pageBytes by decide)
  have hbase := Nat.div_add_mod g.base pageBytes
  generalize hq : (addr - g.base) / pageBytes = q at hd
  generalize hr : (addr - g.base) % pageBytes = r at hd hm
  have hlim : addr - g.base < g.pages * pageBytes := by unfold Geometry.limit at h2; omega
  have hqp : q < g.pages := by
    refine Nat.lt_of_not_le fun hn => ?_
    have : g.pages * pageBytes ≤ q * pageBytes := Nat.mul_le_mul_right _ hn
    have : pageBytes * q = q * pageBytes := Nat.mul_comm _ _
    omega
  have hva : alias g addr = (g.slot + q) * pageBytes + r := by
    unfold alias; rw [Nat.add_mul]; rw [Nat.mul_comm pageBytes q] at hd; omega
  have hdiv : alias g addr / pageBytes = g.slot + q := by
    rw [hva, Nat.add_comm, Nat.add_mul_div_right _ _ (by decide : 0 < pageBytes),
      Nat.div_eq_of_lt hm, Nat.zero_add]
  have hmod : alias g addr % pageBytes = r := by
    rw [hva, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hm]
  have haddr : addr = (g.base / pageBytes + q) * pageBytes + r := by
    rw [Nat.add_mul, Nat.mul_comm (g.base / pageBytes)]
    rw [hb, Nat.add_zero] at hbase
    rw [Nat.mul_comm pageBytes q] at hd
    omega
  have hframe : addr / pageBytes = g.base / pageBytes + q := by
    rw [haddr, Nat.add_comm, Nat.add_mul_div_right _ _ (by decide : 0 < pageBytes),
      Nat.div_eq_of_lt hm, Nat.zero_add]
  have hs : g.slot ≤ g.slot + q ∧ g.slot + q < g.slot + g.pages := ⟨by omega, by omega⟩
  simp only [translate, hdiv, windowRoot, hs, and_self, ite_true, Option.map_some,
    Nat.add_sub_cancel_left, hmod, hframe, Option.some.injEq, Prod.mk.injEq, and_true]
  omega

/-! ## Exact footprint of the string move -/

/-- The string move's stores: `bytes`, stored in order at consecutive
virtual addresses from `dst` under `r`, each through a present writable
leaf; `none` (a fault) at the first byte whose address does not translate
to one. -/
def storeAll (r : Root) (phys : Nat → UInt8) (dst : Nat) : List UInt8 → Option (Nat → UInt8)
  | [] => some phys
  | b :: bs =>
    match translate r dst with
    | some (pa, l) =>
      if l.writable then storeAll r (fun x => if x = pa then b else phys x) (dst + 1) bs
      else none
    | none => none

/-- The string move's loads: `len` bytes read in order from consecutive
virtual addresses from `src` under `r`; `none` (a fault) if one does not
translate. -/
def loadAll (r : Root) (phys : Nat → UInt8) (src : Nat) : Nat → Option (List UInt8)
  | 0 => some []
  | n + 1 =>
    match translate r src with
    | some (pa, _) => (loadAll r phys (src + 1) n).map (phys pa :: ·)
    | none => none

theorem writeBytes_cons (m : Nat → UInt8) (addr : Nat) (b : UInt8) (bs : List UInt8) :
    writeBytes m addr (b :: bs) =
      writeBytes (fun x => if x = addr then b else m x) (addr + 1) bs := by
  funext a
  simp only [writeBytes, List.length_cons]
  by_cases h1 : addr + 1 ≤ a ∧ a < addr + 1 + bs.length
  · have h2 : addr ≤ a ∧ a < addr + (bs.length + 1) := ⟨by omega, by omega⟩
    simp only [h1, h2, and_self, ↓reduceIte]
    have : a - addr = (a - (addr + 1)) + 1 := by omega
    rw [this]; rfl
  · simp only [h1, ↓reduceIte]
    by_cases ha : a = addr
    · subst ha; simp
    · have h2 : ¬ (addr ≤ a ∧ a < addr + (bs.length + 1)) := by omega
      simp only [h2, ha, ↓reduceIte]

/-- Through the fetch root, storing a frame at the alias of an address whose
range the window covers stores exactly the model's `writeBytes` at that
address, without a fault. -/
theorem storeAll_alias (closed : Root) (g : Geometry) (hb : g.base % pageBytes = 0) :
    ∀ (bytes : List UInt8) (phys : Nat → UInt8) (addr : Nat),
      g.window.covers addr bytes.length = true →
      storeAll (windowRoot closed g true) phys (alias g addr) bytes =
        some (writeBytes phys addr bytes)
  | [], phys, addr, _ => by
    simp only [storeAll, Option.some.injEq]
    funext a
    simp only [writeBytes, List.length_nil, Nat.add_zero]
    have : ¬ (addr ≤ a ∧ a < addr) := by omega
    simp only [this, ↓reduceIte]
  | b :: bs, phys, addr, hcov => by
    obtain ⟨h1, h2⟩ := (window_covers_iff g addr _).mp hcov
    simp only [List.length_cons] at h2
    have hlt : addr < g.limit := by omega
    simp only [storeAll, translate_alias closed g true addr hb h1 hlt, ↓reduceIte]
    rw [alias_succ g addr h1, writeBytes_cons]
    exact storeAll_alias closed g hb bs _ (addr + 1)
      ((window_covers_iff g _ _).mpr ⟨by omega, by omega⟩)

/-- Through the send root nothing can be stored: its aliases are
read-only, so the first store faults. -/
theorem storeAll_readonly (closed : Root) (g : Geometry) (hb : g.base % pageBytes = 0)
    (phys : Nat → UInt8) (addr : Nat) (b : UInt8) (bs : List UInt8)
    (hcov : g.window.covers addr (b :: bs).length = true) :
    storeAll (windowRoot closed g false) phys (alias g addr) (b :: bs) = none := by
  obtain ⟨h1, h2⟩ := (window_covers_iff g addr _).mp hcov
  simp only [List.length_cons] at h2
  simp only [storeAll, translate_alias closed g false addr hb h1 (by omega)]
  rfl

theorem readBytes_succ (m : Nat → UInt8) (addr n : Nat) :
    readBytes m addr (n + 1) = m addr :: readBytes m (addr + 1) n := by
  simp only [readBytes, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply]
  congr 1; omega

/-- Through either window root, loading `len` bytes from the alias of an
address whose range the window covers reads exactly the model's
`readBytes` at that address, without a fault. -/
theorem loadAll_alias (closed : Root) (g : Geometry) (w : Bool) (hb : g.base % pageBytes = 0)
    (phys : Nat → UInt8) :
    ∀ (len addr : Nat), g.window.covers addr len = true →
      loadAll (windowRoot closed g w) phys (alias g addr) len = some (readBytes phys addr len)
  | 0, addr, _ => by simp [loadAll, readBytes]
  | n + 1, addr, hcov => by
    obtain ⟨h1, h2⟩ := (window_covers_iff g addr _).mp hcov
    have hlt : addr < g.limit := by omega
    simp only [loadAll, translate_alias closed g w addr hb h1 hlt]
    rw [alias_succ g addr h1, loadAll_alias closed g w hb phys n (addr + 1)
      ((window_covers_iff g _ _).mpr ⟨by omega, by omega⟩), readBytes_succ]
    rfl

/-! ## The confinement carries over -/

/-- Physical memory agrees with the model's per-subject memory: every byte of
a frame that `owner` assigns to subject `x` is `x`'s memory at the same
address (both platforms identity-map the arena). -/
def Rel (owner : Nat → Option Nat) (phys : Nat → UInt8) (mem : Nat → Nat → UInt8) : Prop :=
  ∀ x a, owner (a / pageBytes) = some x → mem x a = phys a

/-- Each port holder's window: its geometry, whose window is the one the
endpoint model gives it, and whose frames the inventory assigns to it. -/
structure Windows (owner : Nat → Option Nat) (p : DhcpSubject.Ports) where
  geometry : Nat → Option Geometry
  window_eq : ∀ who g, geometry who = some g → p.window who = some g.window
  aligned : ∀ who g, geometry who = some g → g.base % pageBytes = 0
  owned : ∀ who g, geometry who = some g → ∀ a, g.window.contains a → owner (a / pageBytes) = some who
  holders : ∀ who, p.window who ≠ none → geometry who ≠ none

theorem covers_contains (w : Window) (addr len a : Nat) (h : w.covers addr len = true)
    (ha : addr ≤ a ∧ a < addr + len) : w.contains a := by
  simp only [Window.covers, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨by omega, by omega⟩

/-- An accepted fetch through the caller's fetch root does not fault, and
the physical memory it leaves agrees with the memory of the model's fetch:
the window performs exactly `DhcpSubject.step`'s copy. -/
theorem fetch_refines (owner : Nat → Option Nat) (p : DhcpSubject.Ports) (ws : Windows owner p)
    (closed : Root) (phys : Nat → UInt8) (s : DhcpSubject.State) (who addr : Nat) (g : Geometry)
    (hrel : Rel owner phys s.mem) (hok : DhcpSubject.fetchOk p s who addr = true)
    (hg : ws.geometry who = some g) :
    storeAll (windowRoot closed g true) phys (alias g addr) s.rx =
        some (writeBytes phys addr s.rx) ∧
      Rel owner (writeBytes phys addr s.rx) (DhcpSubject.step p s (.fetch who addr)).1.mem := by
  obtain ⟨-, w, hw, hcov⟩ := DhcpSubject.fetchOk_route hok
  have hwin := ws.window_eq who g hg
  rw [hwin, Option.some.injEq] at hw
  subst hw
  refine ⟨storeAll_alias closed g (ws.aligned who g hg) s.rx phys addr hcov, ?_⟩
  intro x a hx
  simp only [DhcpSubject.step, hok, ite_true, update]
  by_cases hin : addr ≤ a ∧ a < addr + s.rx.length
  · have hown := ws.owned who g hg a (covers_contains _ _ _ _ hcov hin)
    rw [hx] at hown
    cases hown
    simp [writeBytes, hin]
  · rw [NetworkSubject.writeBytes_outside _ _ _ _ hin]
    by_cases hxw : x = who
    · subst hxw; simp only [↓reduceIte]; rw [NetworkSubject.writeBytes_outside _ _ _ _ hin]
      exact hrel _ _ hx
    · simp only [hxw, ↓reduceIte]; exact hrel _ _ hx

/-- The fetch's physical footprint: a byte it changes lies in the requested
range, inside the caller's own window, on a frame the inventory assigns to
the caller. -/
theorem fetch_footprint (owner : Nat → Option Nat) (p : DhcpSubject.Ports) (ws : Windows owner p)
    (phys : Nat → UInt8) (s : DhcpSubject.State) (who addr : Nat) (g : Geometry)
    (hok : DhcpSubject.fetchOk p s who addr = true) (hg : ws.geometry who = some g) (a : Nat)
    (h : writeBytes phys addr s.rx a ≠ phys a) :
    addr ≤ a ∧ a < addr + s.rx.length ∧ g.window.contains a ∧ owner (a / pageBytes) = some who := by
  obtain ⟨-, w, hw, hcov⟩ := DhcpSubject.fetchOk_route hok
  rw [ws.window_eq who g hg, Option.some.injEq] at hw
  subst hw
  by_cases hin : addr ≤ a ∧ a < addr + s.rx.length
  · have hc := covers_contains _ _ _ _ hcov hin
    exact ⟨hin.1, hin.2, hc, ws.owned who g hg a hc⟩
  · exact absurd (NetworkSubject.writeBytes_outside _ _ _ _ hin) h

/-- An accepted send through the caller's send root does not fault and reads
exactly the frame the model's send puts in the transmit slot; it stores
nothing. -/
theorem send_refines (owner : Nat → Option Nat) (p : DhcpSubject.Ports) (ws : Windows owner p)
    (closed : Root) (phys : Nat → UInt8) (s : DhcpSubject.State) (who addr len : Nat)
    (g : Geometry) (hrel : Rel owner phys s.mem)
    (hok : DhcpSubject.sendOk p s who addr len = true) (hg : ws.geometry who = some g) :
    loadAll (windowRoot closed g false) phys (alias g addr) len =
      some (DhcpSubject.step p s (.send who addr len)).1.tx := by
  obtain ⟨-, w, hw, hcov⟩ := DhcpSubject.sendOk_route hok
  rw [ws.window_eq who g hg, Option.some.injEq] at hw
  subst hw
  rw [loadAll_alias closed g false (ws.aligned who g hg) phys len addr hcov]
  simp only [DhcpSubject.step, hok, ite_true, Option.some.injEq, readBytes]
  apply List.map_congr_left
  intro i hi
  have hi' : i < len := List.mem_range.mp hi
  exact (hrel who (addr + i)
    (ws.owned who g hg _ (covers_contains _ _ _ _ hcov ⟨by omega, by omega⟩))).symm

/-- For the one-port network-subject endpoint (`NetworkSubject`, issue
#450): with the network subject's window as the geometry's, an accepted
fetch through its fetch root performs exactly the model's fetch. -/
theorem network_fetch_refines (owner : Nat → Option Nat) (closed : Root) (g : Geometry)
    (hb : g.base % pageBytes = 0)
    (howned : ∀ a, g.window.contains a → owner (a / pageBytes) = some NetworkSubject.network)
    (phys : Nat → UInt8) (s : NetworkSubject.State) (who addr : Nat)
    (hrel : Rel owner phys s.mem) (hok : NetworkSubject.fetchOk g.window s who addr = true) :
    storeAll (windowRoot closed g true) phys (alias g addr) s.rx =
        some (writeBytes phys addr s.rx) ∧
      Rel owner (writeBytes phys addr s.rx) (NetworkSubject.step g.window s (.fetch who addr)).1.mem := by
  have hcov : g.window.covers addr s.rx.length = true := by
    simp only [NetworkSubject.fetchOk, Bool.and_eq_true] at hok; exact hok.2
  refine ⟨storeAll_alias closed g hb s.rx phys addr hcov, ?_⟩
  intro x a hx
  simp only [NetworkSubject.step, hok, ite_true, update]
  by_cases hin : addr ≤ a ∧ a < addr + s.rx.length
  · have hown := howned a (covers_contains _ _ _ _ hcov hin)
    rw [hx] at hown
    cases hown
    simp [writeBytes, hin]
  · rw [NetworkSubject.writeBytes_outside _ _ _ _ hin]
    by_cases hxw : x = NetworkSubject.network
    · subst hxw; simp only [↓reduceIte]; rw [NetworkSubject.writeBytes_outside _ _ _ _ hin]
      exact hrel _ _ hx
    · simp only [hxw, ↓reduceIte]; exact hrel _ _ hx

/-- With the network subject's window as the geometry's, an accepted send
through its send root reads exactly the model's reply. -/
theorem network_send_refines (owner : Nat → Option Nat) (closed : Root) (g : Geometry)
    (hb : g.base % pageBytes = 0)
    (howned : ∀ a, g.window.contains a → owner (a / pageBytes) = some NetworkSubject.network)
    (phys : Nat → UInt8) (s : NetworkSubject.State) (who addr len : Nat)
    (hrel : Rel owner phys s.mem) (hok : NetworkSubject.sendOk g.window s who addr len = true) :
    loadAll (windowRoot closed g false) phys (alias g addr) len =
      some (NetworkSubject.step g.window s (.send who addr len)).1.tx := by
  have hcov : g.window.covers addr len = true := by
    simp only [NetworkSubject.sendOk, Bool.and_eq_true] at hok; exact hok.2
  rw [loadAll_alias closed g false hb phys len addr hcov]
  simp only [NetworkSubject.step, hok, ite_true, Option.some.injEq, readBytes]
  apply List.map_congr_left
  intro i hi
  have hi' : i < len := List.mem_range.mp hi
  exact (hrel _ (addr + i) (howned _ (covers_contains _ _ _ _ hcov ⟨by omega, by omega⟩))).symm

/-! ## The kernel's operand

The export takes the first alias slot's page number, the frame port
witness's request word, the buffer, its length and the window, the six
fixed-width arguments every boot export may take. The caller is the window
owner the request word names: the kernel names the caller there, and checks
the port witness with the caller separately. -/

/-- The reviewed geometry on the kernel's words: `[base, limit)` is one or
two whole pages inside the arena, and the alias slots from `slot` (one per
window page) lie inside the arena above page 0. -/
def geometryOk (base limit slot : UInt64) : Bool :=
  base % 4096 == 0 && base < limit && limit ≤ 0x1000000 &&
    (limit - base == 4096 || limit - base == 8192) &&
    slot != 0 && slot ≤ 4096 && slot + (limit - base) / 4096 ≤ 4096

/-- The window owner a request word names. -/
def ownerOf (req : UInt64) : UInt64 := (req >>> 24) &&& 0xff

/-- Allocation-free operand of a frame copy, exported as
`leanos_frame_window_operand`: for a request that the frame port witness
accepts (`DhcpSubject.framePortCheck`, with the request's window owner as
the caller) over a window of the reviewed geometry, the alias address of the
buffer, from which the window root's string move starts; 0 for every other
request. -/
@[export leanos_frame_window_operand]
def frameWindowOperand (slot req addr len base limit : UInt64) : UInt64 :=
  if DhcpSubject.framePortCheck (ownerOf req) req addr len base limit == 0 &&
      geometryOk base limit slot then
    slot * 4096 + (addr - base)
  else 0

/-- The geometry the kernel's words describe. -/
def geometryOf (base limit slot : UInt64) : Geometry :=
  { base := base.toNat, pages := (limit.toNat - base.toNat) / 4096, slot := slot.toNat }

/-- The facts the reviewed geometry gives, on natural numbers. -/
theorem geometryOk_nat (base limit slot : UInt64) (h : geometryOk base limit slot = true) :
    base.toNat % 4096 = 0 ∧ base.toNat < limit.toNat ∧ limit.toNat ≤ 16777216 ∧
      (limit.toNat - base.toNat = 4096 ∨ limit.toNat - base.toNat = 8192) ∧
      0 < slot.toNat ∧ slot.toNat + (limit.toNat - base.toNat) / 4096 ≤ 4096 := by
  simp only [geometryOk, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.or_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hal, hlt⟩, harena⟩, hpages⟩, hslot⟩, hsmax⟩, hsum⟩ := h
  rw [UInt64.lt_iff_toNat_lt] at hlt
  rw [UInt64.le_iff_toNat_le] at harena hsum hsmax
  have hsub : (limit - base).toNat = limit.toNat - base.toNat :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))
  have hal' : base.toNat % 4096 = 0 := by
    have := congrArg UInt64.toNat hal; simpa [UInt64.toNat_mod] using this
  have hpages' : limit.toNat - base.toNat = 4096 ∨ limit.toNat - base.toNat = 8192 := by
    rcases hpages with h | h
    · left; have := congrArg UInt64.toNat h; rw [hsub] at this; simpa using this
    · right; have := congrArg UInt64.toNat h; rw [hsub] at this; simpa using this
  have hslot' : 0 < slot.toNat := by
    rcases Nat.eq_zero_or_pos slot.toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by simp [h0])) hslot
    · exact h0
  have harena' : limit.toNat ≤ 16777216 := by simpa using harena
  have hsmax' : slot.toNat ≤ 4096 := by simpa using hsmax
  have hdivw : ((limit - base) / 4096).toNat = (limit.toNat - base.toNat) / 4096 := by
    rw [UInt64.toNat_div, hsub]; rfl
  have hsum' : slot.toNat + (limit.toNat - base.toNat) / 4096 ≤ 4096 := by
    have hs := hsum
    rw [UInt64.toNat_add, hdivw] at hs
    have hd : (limit.toNat - base.toNat) / 4096 ≤ 2 := by omega
    rw [Nat.mod_eq_of_lt (by omega)] at hs
    simpa using hs
  exact ⟨hal', hlt, harena', hpages', hslot', hsum'⟩

theorem geometryOk_spec (base limit slot : UInt64) (h : geometryOk base limit slot = true) :
    (geometryOf base limit slot).ok ∧ (geometryOf base limit slot).limit = limit.toNat := by
  obtain ⟨hal, hlt, harena, hpages, hslot, hsum⟩ := geometryOk_nat base limit slot h
  have hb := Nat.div_add_mod base.toNat 4096
  simp only [Geometry.ok, geometryOf, Geometry.limit, pageBytes, arenaPages]
  rcases hpages with hp | hp <;> rw [hp] at hsum ⊢ <;>
    exact ⟨⟨hal, by decide, by omega, hslot, by omega⟩, by omega⟩

/-- The operand is nonzero exactly when the frame port witness accepts the
request (with its window owner as the caller) and the geometry is the
reviewed one. -/
theorem frameWindowOperand_ne_zero_iff (slot req addr len base limit : UInt64) :
    frameWindowOperand slot req addr len base limit ≠ 0 ↔
      DhcpSubject.framePortCheck (ownerOf req) req addr len base limit = 0 ∧
        geometryOk base limit slot = true := by
  unfold frameWindowOperand
  by_cases hc : (DhcpSubject.framePortCheck (ownerOf req) req addr len base limit == 0 &&
      geometryOk base limit slot) = true
  · simp only [hc, ↓reduceIte]
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    refine ⟨fun _ => hc, fun _ => ?_⟩
    obtain ⟨hw, hg⟩ := hc
    obtain ⟨-, -, -, hcov⟩ := DhcpSubject.framePortCheck_own_window _ _ _ _ _ _ hw
    obtain ⟨-, -, harena, -, hslot, hsum⟩ := geometryOk_nat base limit slot hg
    simp only [NetworkSubject.Window.covers, Bool.and_eq_true, decide_eq_true_eq] at hcov
    have hsub : (addr - base).toNat = addr.toNat - base.toNat :=
      UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hcov.1)
    have hmul : (slot * 4096).toNat = slot.toNat * 4096 := by
      rw [UInt64.toNat_mul]; exact Nat.mod_eq_of_lt (by simp; omega)
    intro h0
    have := congrArg UInt64.toNat h0
    rw [UInt64.toNat_add, hmul, hsub] at this
    rw [Nat.mod_eq_of_lt (by omega)] at this
    simp at this
    omega
  · simp only [hc, ↓reduceIte, Bool.false_eq_true]
    simp only [Bool.and_eq_true, beq_iff_eq, not_and] at hc
    exact ⟨fun h => absurd rfl h, fun ⟨h1, h2⟩ => absurd h2 (hc h1)⟩

/-- A nonzero operand is the alias, under the geometry the kernel's words
describe, of the requested buffer, whose whole range that window covers. -/
theorem frameWindowOperand_alias (slot req addr len base limit : UInt64)
    (h : frameWindowOperand slot req addr len base limit ≠ 0) :
    (geometryOf base limit slot).ok ∧
      (geometryOf base limit slot).window.covers addr.toNat len.toNat = true ∧
      (frameWindowOperand slot req addr len base limit).toNat =
        alias (geometryOf base limit slot) addr.toNat := by
  obtain ⟨hw, hg⟩ := (frameWindowOperand_ne_zero_iff _ _ _ _ _ _).mp h
  obtain ⟨hok, hlim⟩ := geometryOk_spec _ _ _ hg
  obtain ⟨-, -, harena, -, -, hsum⟩ := geometryOk_nat base limit slot hg
  obtain ⟨-, -, -, hcov⟩ := DhcpSubject.framePortCheck_own_window _ _ _ _ _ _ hw
  refine ⟨hok, ?_, ?_⟩
  · simp only [Geometry.window, hlim]; exact hcov
  · simp only [NetworkSubject.Window.covers, Bool.and_eq_true, decide_eq_true_eq] at hcov
    have hsub : (addr - base).toNat = addr.toNat - base.toNat :=
      UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hcov.1)
    have hmul : (slot * 4096).toNat = slot.toNat * 4096 := by
      rw [UInt64.toNat_mul]; exact Nat.mod_eq_of_lt (by simp; omega)
    have hc : (DhcpSubject.framePortCheck (ownerOf req) req addr len base limit == 0 &&
        geometryOk base limit slot) = true := by simp [hw, hg]
    simp only [frameWindowOperand, hc, ite_true, alias, geometryOf, pageBytes]
    rw [UInt64.toNat_add, hmul, hsub]
    exact Nat.mod_eq_of_lt (by omega)

/-- The request word the kernel builds for a port holder names that holder
as the window's owner. -/
theorem ownerOf_request (op route owner : UInt64) (p : Bool) (hop : op = 1 ∨ op = 2)
    (hr : route = 2 ∨ route = 3) (ho : owner = 2 ∨ owner = 3) :
    ownerOf (DhcpSubject.request op p route owner) = owner :=
  (DhcpSubject.request_fields op route owner p hop hr ho).2.2.2

/-- For a port holder whose window is `[base, limit)`, in a reachable state,
the operand of its fetch is nonzero exactly when the model's `fetchOk`
accepts (given the reviewed geometry), and then the string move through the
caller's fetch root, starting at the operand, stores exactly the model's
`writeBytes` of the pending record into the caller's buffer. -/
theorem frameWindowOperand_fetch (p : DhcpSubject.Ports) (s : DhcpSubject.State) (who : Nat)
    (addr base limit slot : UInt64) (closed : Root) (phys : Nat → UInt8)
    (hwho : who = DhcpSubject.dhcp ∨ who = DhcpSubject.echo)
    (hw : p.window who = some ⟨base.toNat, limit.toNat⟩) (hlen : s.rx.length < 2 ^ 64)
    (hroute : DhcpSubject.Routed s) (hgeo : geometryOk base limit slot = true) :
    (frameWindowOperand slot
        (DhcpSubject.request DhcpSubject.opFetch s.rxPending s.route.toUInt64 who.toUInt64)
        addr s.rx.length.toUInt64 base limit ≠ 0 ↔
      DhcpSubject.fetchOk p s who addr.toNat = true) ∧
    (DhcpSubject.fetchOk p s who addr.toNat = true →
      storeAll (windowRoot closed (geometryOf base limit slot) true) phys
        (frameWindowOperand slot
          (DhcpSubject.request DhcpSubject.opFetch s.rxPending s.route.toUInt64 who.toUInt64)
          addr s.rx.length.toUInt64 base limit).toNat s.rx =
          some (writeBytes phys addr.toNat s.rx)) := by
  have hown := ownerOf_request DhcpSubject.opFetch s.route.toUInt64 who.toUInt64 s.rxPending
    (Or.inl rfl) (DhcpSubject.port_toUInt64 hroute.port) (DhcpSubject.port_toUInt64 hwho)
  have hiff : frameWindowOperand slot
        (DhcpSubject.request DhcpSubject.opFetch s.rxPending s.route.toUInt64 who.toUInt64)
        addr s.rx.length.toUInt64 base limit ≠ 0 ↔
      DhcpSubject.fetchOk p s who addr.toNat = true := by
    rw [frameWindowOperand_ne_zero_iff, hown,
      DhcpSubject.framePortCheck_fetch p s who addr base limit hwho hw hlen hroute]
    simp [hgeo]
  refine ⟨hiff, fun hok => ?_⟩
  obtain ⟨hg, hcov, heq⟩ := frameWindowOperand_alias _ _ _ _ _ _ (hiff.mpr hok)
  rw [heq]
  have hl : (s.rx.length.toUInt64).toNat = s.rx.length := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hlen
  rw [hl] at hcov
  exact storeAll_alias closed _ hg.1 s.rx phys addr.toNat hcov

/-- For a port holder whose window is `[base, limit)`, in a reachable state,
the operand of its send is nonzero exactly when the model's `sendOk`
accepts (given the reviewed geometry), and then the string move through the
caller's send root, starting at the operand, reads exactly the model's
`readBytes` of the caller's buffer. -/
theorem frameWindowOperand_send (p : DhcpSubject.Ports) (s : DhcpSubject.State) (who : Nat)
    (addr len base limit slot : UInt64) (closed : Root) (phys : Nat → UInt8)
    (hwho : who = DhcpSubject.dhcp ∨ who = DhcpSubject.echo)
    (hw : p.window who = some ⟨base.toNat, limit.toNat⟩)
    (hroute : DhcpSubject.Routed s) (hgeo : geometryOk base limit slot = true) :
    (frameWindowOperand slot
        (DhcpSubject.request DhcpSubject.opSend s.txPending s.route.toUInt64 who.toUInt64)
        addr len base limit ≠ 0 ↔
      DhcpSubject.sendOk p s who addr.toNat len.toNat = true) ∧
    (DhcpSubject.sendOk p s who addr.toNat len.toNat = true →
      loadAll (windowRoot closed (geometryOf base limit slot) false) phys
        (frameWindowOperand slot
          (DhcpSubject.request DhcpSubject.opSend s.txPending s.route.toUInt64 who.toUInt64)
          addr len base limit).toNat len.toNat =
          some (readBytes phys addr.toNat len.toNat)) := by
  have hown := ownerOf_request DhcpSubject.opSend s.route.toUInt64 who.toUInt64 s.txPending
    (Or.inr rfl) (DhcpSubject.port_toUInt64 hroute.port) (DhcpSubject.port_toUInt64 hwho)
  have hiff : frameWindowOperand slot
        (DhcpSubject.request DhcpSubject.opSend s.txPending s.route.toUInt64 who.toUInt64)
        addr len base limit ≠ 0 ↔
      DhcpSubject.sendOk p s who addr.toNat len.toNat = true := by
    rw [frameWindowOperand_ne_zero_iff, hown,
      DhcpSubject.framePortCheck_send p s who addr len base limit hwho hw hroute]
    simp [hgeo]
  refine ⟨hiff, fun hok => ?_⟩
  obtain ⟨hg, hcov, heq⟩ := frameWindowOperand_alias _ _ _ _ _ _ (hiff.mpr hok)
  rw [heq]
  exact loadAll_alias closed _ false hg.1 phys len.toNat addr.toNat hcov

/-- A request naming a window owner that holds no port gets operand 0. -/
theorem frameWindowOperand_nonholder (slot req addr len base limit : UInt64)
    (h2 : ownerOf req ≠ 2) (h3 : ownerOf req ≠ 3) :
    frameWindowOperand slot req addr len base limit = 0 := by
  have := DhcpSubject.framePortCheck_nonholder (ownerOf req) req addr len base limit h2 h3
  simp [frameWindowOperand, this]

end LeanOS.FrameCopyWindow
