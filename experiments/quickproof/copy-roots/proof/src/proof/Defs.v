(* Pure definitions shared by every proof of leanos_roots (include/qotom_copy_root_builder.h and
   include/frame_copy_window.h): the checks the code makes and what it builds, as functions of its inputs.
   No program here.  A 64-bit word is a Z in [0, 2^64); every definition below follows the C expression it
   names in uint64_t arithmetic. *)
Require Import VST.floyd.proofauto.
Local Open Scope Z_scope.
Local Open Scope bool_scope.   (* && and || are andb and orb here, not VST's andp and orp *)

Definition W : Z := Int64.modulus.
Definition word_ok (x: Z) : Prop := 0 <= x <= Int64.max_unsigned.
Definition words_ok (l: list Z) : Prop := Forall word_ok l.

Definition ROOT_BYTES : Z := 45056.
Definition LEAVES : Z := 4096.
Definition ACCESSED : Z := 32.
Definition ADDRESS_MASK : Z := 4503599627366400.   (* 0x000ffffffffff000 *)
Definition NX : Z := 9223372036854775808.          (* 1 << 63 *)

(* The indices 0 .. n - 1. *)
Definition idx (n: Z) : list Z := map Z.of_nat (seq 0 (Z.to_nat n)).

(* x & ~QOTOM_ROOT_ACCESSED, for a word x. *)
Definition clear_accessed (x: Z) : Z := Z.land x (Z.lnot ACCESSED).

(* qotom_root_table_entry(phys, k) = (phys + k * 4096u) | 7. *)
Definition table_entry (phys k: Z) : Z := Z.lor ((phys + k * 4096) mod W) 7.

(* The words of a struct qotom_root_pages. *)
Record root := mkroot { pml4: list Z; pdpt: list Z; pd: list Z; pt: list Z }.

Definition root_ok (r: root) : Prop :=
  Zlength (pml4 r) = 512 /\ Zlength (pdpt r) = 512 /\ Zlength (pd r) = 512 /\ Zlength (pt r) = LEAVES /\
  words_ok (pml4 r) /\ words_ok (pdpt r) /\ words_ok (pd r) /\ words_ok (pt r).

(* Directory entry i of the root at phys: its i-th page table for i < 8, else 0. *)
Definition pd_entry (phys i: Z) : Z := if i <? 8 then table_entry phys (3 + i) else 0.

(* qotom_root_source_ancestors(r, phys) != 0. *)
Definition ancestors_ok (r: root) (phys: Z) : bool :=
  (clear_accessed (Znth 0 (pml4 r)) =? table_entry phys 1) &&
  (clear_accessed (Znth 0 (pdpt r)) =? table_entry phys 2) &&
  forallb (fun i => (Znth i (pml4 r) =? 0) && (Znth i (pdpt r) =? 0)) (map (Z.add 1) (idx 511)) &&
  forallb (fun i => clear_accessed (Znth i (pd r)) =? pd_entry phys i) (idx 512).

(* qotom_root_phys_ok and qotom_root_phys_disjoint. *)
Definition phys_ok (a: Z) : bool :=
  negb (a =? 0) && (a mod 4096 =? 0) && (a <=? 2 ^ 52 - ROOT_BYTES).
Definition disjoint (a b: Z) : bool :=
  if a <=? b then ROOT_BYTES <=? b - a else ROOT_BYTES <=? a - b.

Definition member (f: Z) (fs: list Z) : bool := existsb (Z.eqb f) fs.

Fixpoint distinct (l: list Z) : bool :=
  match l with
  | nil => true
  | x :: t => negb (member x t) && distinct t
  end.

(* The inventory test of qotom_build_copy_roots on its first n frames. *)
Definition inventory_ok (fs: list Z) (n: Z) : bool :=
  (1 <=? n) && (n <=? 16) && forallb (fun f => f <? 2 ^ 40) (sublist 0 n fs) && distinct (sublist 0 n fs).

(* A struct qotom_copy_alias. *)
Record alias := mkalias { a_page: Z; a_frame: Z; a_writable: Z }.

Definition alias_ok (src: root) (inv: list Z) (a: alias) : bool :=
  (a_page a <? LEAVES) && (a_writable a <=? 1) && (Znth (a_page a) (pt src) =? 0) && member (a_frame a) inv.

Definition aliases_ok (src: root) (inv: list Z) (al: list alias) (m: Z) : bool :=
  (1 <=? m) && (m <=? 2) && forallb (alias_ok src inv) (sublist 0 m al) &&
  distinct (map a_page (sublist 0 m al)) && distinct (map a_frame (sublist 0 m al)).

(* Every test qotom_build_copy_roots makes after its NULL checks. *)
Definition build_ok (src: root) (sp kp cp: Z) (fs: list Z) (n: Z) (al: list alias) (m: Z) : bool :=
  phys_ok sp && phys_ok kp && phys_ok cp && disjoint sp kp && disjoint sp cp && disjoint kp cp &&
  ancestors_ok src sp && inventory_ok fs n && aliases_ok src (sublist 0 n fs) al m.

(* (leaf & QOTOM_ROOT_ADDRESS_MASK) >> 12, and the closed root's test of a source leaf. *)
Definition frame_of (x: Z) : Z := Z.shiftr (Z.land x ADDRESS_MASK) 12.
Definition removes (inv: list Z) (s: Z) : bool := Z.odd s && member (frame_of s) inv.
Definition closed_leaf (inv: list Z) (s: Z) : Z := if removes inv s then 0 else s.

(* (frame << 12) | QOTOM_ROOT_PRESENT | QOTOM_ROOT_NX | (writable ? QOTOM_ROOT_WRITABLE : 0). *)
Definition alias_leaf (a: alias) : Z :=
  Z.lor (Z.lor (Z.lor ((a_frame a * 4096) mod W) 1) NX) (if a_writable a =? 0 then 0 else 2).

Fixpoint install (al: list alias) (leaves: list Z) : list Z :=
  match al with
  | nil => leaves
  | a :: t => install t (upd_Znth (a_page a) leaves (alias_leaf a))
  end.

(* A root the builder writes at phys: PML4[0], PDPT[0] and PD[0..7] name its own tables, every other
   non-leaf entry is 0, and its leaves are `leaves`. *)
Definition built_root (phys: Z) (leaves: list Z) : root :=
  mkroot (upd_Znth 0 (Zrepeat 0 512) (table_entry phys 1)) (upd_Znth 0 (Zrepeat 0 512) (table_entry phys 2))
         (map (pd_entry phys) (idx 512)) leaves.

Definition closed_out (src: root) (inv: list Z) (kp: Z) : root := built_root kp (map (closed_leaf inv) (pt src)).
Definition copy_out (src: root) (inv: list Z) (al: list alias) (cp: Z) : root :=
  built_root cp (install al (map (closed_leaf inv) (pt src))).

(* The counts of struct qotom_root_build_result. *)
Definition removed_count (inv: list Z) (leaves: list Z) : Z := Zlength (filter (removes inv) leaves).
Definition retained_count (inv: list Z) (leaves: list Z) : Z :=
  Zlength (filter (fun s => Z.odd s && negb (member (frame_of s) inv)) leaves).

(* A struct frame_window's integer fields. *)
Record window := mkwindow { w_fetch_phys: Z; w_send_phys: Z; w_base: Z; w_limit: Z; w_slot: Z }.

(* frame_window_pages: (limit - base) / 4096u. *)
Definition pages_of (w: window) : Z := ((w_limit w - w_base w) mod W) / 4096.

(* frame_window_geometry_ok (LeanOS.FrameCopyWindow.geometryOk). *)
Definition geometry_ok (w: window) : bool :=
  (Z.land (w_base w) 4095 =? 0) && (w_base w <? w_limit w) && (w_limit w <=? 16777216) &&
  (((w_limit w - w_base w) mod W =? 4096) || ((w_limit w - w_base w) mod W =? 8192)) &&
  negb (w_slot w =? 0) && (w_slot w <=? LEAVES) && ((w_slot w + pages_of w) mod W <=? LEAVES).

(* The aliases frame_window_build passes to the builder, writable or not. *)
Definition window_alias (w: window) (writable: Z) (i: Z) : alias :=
  mkalias ((w_slot w + i) mod W) ((Z.shiftr (w_base w) 12 + i) mod W) writable.
Definition window_aliases (w: window) (writable: Z) : list alias :=
  map (window_alias w writable) (idx (pages_of w)).

(* frame_window_root_exact's expected leaf at page p, writable or not, over the closed leaf c. *)
Definition in_slots (w: window) (p: Z) : bool := (w_slot w <=? p) && (p <? (w_slot w + pages_of w) mod W).
Definition scan_leaf (w: window) (writable: bool) (p c: Z) : Z :=
  if in_slots w p then
    Z.lor (Z.lor (Z.lor (((Z.shiftr (w_base w) 12 + (p - w_slot w) mod W) mod W * 4096) mod W) 1) NX)
          (if writable then 2 else 0)
  else c.

(* frame_window_root_exact(root, rp, closed, kp, fs, n, w, writable) != 0. *)
Definition scan_ok (r k: root) (rp kp: Z) (inv: list Z) (w: window) (writable: bool) : bool :=
  ancestors_ok r rp && ancestors_ok k kp &&
  forallb (fun p => negb (removes inv (Znth p (pt k))) &&
                    (Znth p (pt r) =? scan_leaf w writable p (Znth p (pt k)))) (idx LEAVES).
