(* Law window_scan_exact: pure facts about the definitions of Defs.v and the uint64_t arithmetic of the
   harness harness/window_scan_exact.c (no separation logic here). *)
Require Import VST.floyd.proofauto.
Require Import LeanosRoots.proof.Defs.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* ---------------------------------------------------------------------- *)
(* Indices                                                                 *)
(* ---------------------------------------------------------------------- *)

Lemma idx_succ: forall p, 0 <= p -> idx (p + 1) = idx p ++ [p].
Proof.
  intros p Hp. unfold idx. rewrite Z2Nat.inj_add by lia. rewrite seq_app, map_app.
  simpl. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma idx_0: idx 0 = [].
Proof. reflexivity. Qed.

Lemma forallb_idx_succ: forall (f: Z -> bool) p, 0 <= p ->
  forallb f (idx (p + 1)) = forallb f (idx p) && f p.
Proof.
  intros f p Hp. rewrite idx_succ by lia. rewrite forallb_app. simpl. rewrite andb_true_r. reflexivity.
Qed.

Lemma forallb_map_succ: forall (f: Z -> bool) p, 1 <= p ->
  forallb f (map (Z.add 1) (idx (p + 1 - 1))) = forallb f (map (Z.add 1) (idx (p - 1))) && f p.
Proof.
  intros f p Hp. replace (p + 1 - 1) with ((p - 1) + 1) by lia.
  rewrite idx_succ by lia. rewrite map_app, forallb_app. simpl. rewrite andb_true_r.
  replace (1 + (p - 1)) with p by lia. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* Ranges of bitwise results                                               *)
(* ---------------------------------------------------------------------- *)

Lemma modulus_eq: Int64.modulus = 2 ^ 64.
Proof. reflexivity. Qed.

Lemma land_range: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= Z.land a b <= Int64.max_unsigned.
Proof.
  intros a b Ha.
  assert (E: a = Z.land a (Z.ones 64)).
  { rewrite Z.land_ones by lia. rewrite Z.mod_small; [ reflexivity | ]. unfold Int64.max_unsigned in Ha.
    rewrite modulus_eq in Ha. lia. }
  rewrite E, <- Z.land_assoc, (Z.land_comm (Z.ones 64) b), Z.land_assoc, Z.land_ones by lia.
  unfold Int64.max_unsigned. rewrite modulus_eq.
  pose proof (Z.mod_pos_bound (Z.land a b) (2 ^ 64) ltac:(lia)). lia.
Qed.

Lemma log2_word: forall x, 0 <= x <= Int64.max_unsigned -> Z.log2 x < 64.
Proof.
  intros x Hx. unfold Int64.max_unsigned in Hx. rewrite modulus_eq in Hx.
  destruct (Z.eq_dec x 0) as [-> | N]; [ simpl; lia | ].
  apply Z.log2_lt_pow2; lia.
Qed.

Lemma lor_range: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  0 <= Z.lor a b <= Int64.max_unsigned.
Proof.
  intros a b Ha Hb. split; [ apply Z.lor_nonneg; lia | ].
  destruct (Z.eq_dec (Z.lor a b) 0) as [E | N]; [ rewrite E; rep_lia | ].
  assert (P: 0 < Z.lor a b) by (pose proof (Z.lor_nonneg a b); lia).
  assert (L: Z.lor a b < 2 ^ 64).
  { apply Z.log2_lt_pow2; [ exact P | ]. rewrite Z.log2_lor by lia.
    apply Z.max_lub_lt; apply log2_word; auto. }
  unfold Int64.max_unsigned. rewrite modulus_eq. lia.
Qed.

Lemma or_repr: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.or (Int64.repr a) (Int64.repr b) = Int64.repr (Z.lor a b).
Proof. intros. unfold Int64.or. rewrite !Int64.unsigned_repr by lia. reflexivity. Qed.

Lemma and_repr: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.and (Int64.repr a) (Int64.repr b) = Int64.repr (Z.land a b).
Proof. intros. unfold Int64.and. rewrite !Int64.unsigned_repr by lia. reflexivity. Qed.

Lemma mod_range: forall x, 0 <= x mod W <= Int64.max_unsigned.
Proof.
  intros x. unfold W, Int64.max_unsigned. pose proof (Z.mod_pos_bound x Int64.modulus ltac:(rep_lia)). lia.
Qed.

Lemma neq_repr: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.repr a <> Int64.repr b -> (a =? b) = false.
Proof. intros a b Ha Hb N. apply Z.eqb_neq. intro E. apply N. rewrite E. reflexivity. Qed.

Lemma eq_repr_inj: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.repr a = Int64.repr b -> (a =? b) = true.
Proof.
  intros a b Ha Hb E. apply Z.eqb_eq. rewrite <- (Int64.unsigned_repr a), <- (Int64.unsigned_repr b) by lia.
  rewrite E. reflexivity.
Qed.

Definition root_ranges_prop (r: root) : Prop :=
  forall i, (0 <= i < 512 -> 0 <= Znth i (pml4 r) <= Int64.max_unsigned /\
                             0 <= Znth i (pdpt r) <= Int64.max_unsigned /\
                             0 <= Znth i (pd r) <= Int64.max_unsigned) /\
            (0 <= i < 4096 -> 0 <= Znth i (pt r) <= Int64.max_unsigned).

Lemma root_ranges: forall r, root_ok r -> root_ranges_prop r.
Proof.
  intros r (L1 & L2 & L3 & L4 & W1 & W2 & W3 & W4) i. unfold LEAVES in L4.
  split; [ intros Hi; split3 | intros Hi ]; apply (Forall_Znth _ word_ok); auto; lia.
Qed.

Lemma in_idx: forall x n, 0 <= x < n -> In x (idx n).
Proof.
  intros x n H. unfold idx. apply in_map_iff. exists (Z.to_nat x). split; [ apply Z2Nat.id; lia | ].
  apply in_seq. lia.
Qed.

Lemma forallb_false: forall (f: Z -> bool) l x, In x l -> f x = false -> forallb f l = false.
Proof.
  intros f l x I F. destruct (forallb f l) eqn:E; auto. rewrite forallb_forall in E.
  rewrite (E x I) in F. discriminate.
Qed.

Lemma b2z_bool2val: forall b: bool, Vint (Int.repr (if b then 1 else 0)) = bool2val b.
Proof. destruct b; reflexivity. Qed.

Lemma repr_mod: forall x, Int64.repr (x mod W) = Int64.repr x.
Proof.
  intros x. rewrite <- (Int64.repr_unsigned (Int64.repr x)). rewrite Int64.unsigned_repr_eq. reflexivity.
Qed.

Lemma repr_lor_mod: forall a b, Int64.repr (Z.lor a b) = Int64.repr (Z.lor (a mod W) b).
Proof.
  intros a b. apply Int64.same_bits_eq. intros i Hi.
  rewrite !Int64.testbit_repr by lia. rewrite !Z.lor_spec. f_equal.
  unfold W. rewrite modulus_eq. rewrite Z.mod_pow2_bits_low by (change Int64.zwordsize with 64 in Hi; lia).
  reflexivity.
Qed.

Lemma eq_repr: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.eq (Int64.repr a) (Int64.repr b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold Int64.eq. rewrite !Int64.unsigned_repr by lia.
  destruct (zeq a b); destruct (Z.eqb_spec a b); congruence.
Qed.

(* ---------------------------------------------------------------------- *)
(* The expressions of the harness                                          *)
(* ---------------------------------------------------------------------- *)

(* x & ~QOTOM_ROOT_ACCESSED *)
Lemma clear_accessed_repr: forall x, 0 <= x <= Int64.max_unsigned ->
  Int64.and (Int64.repr x) (Int64.not (Int64.repr 32)) = Int64.repr (clear_accessed x).
Proof.
  intros x Hx. apply Int64.same_bits_eq. intros i Hi.
  rewrite Int64.bits_and by lia. rewrite Int64.bits_not by lia.
  rewrite !Int64.testbit_repr by lia. unfold clear_accessed, ACCESSED.
  rewrite Z.land_spec, Z.lnot_spec by lia. reflexivity.
Qed.

Lemma clear_accessed_range: forall x, 0 <= x <= Int64.max_unsigned ->
  0 <= clear_accessed x <= Int64.max_unsigned.
Proof. intros. apply land_range; auto. Qed.

Lemma table_entry_range: forall phys k, 0 <= table_entry phys k <= Int64.max_unsigned.
Proof.
  intros. unfold table_entry. apply lor_range; [ apply mod_range | rep_lia ].
Qed.

Lemma pd_entry_range: forall phys i, 0 <= pd_entry phys i <= Int64.max_unsigned.
Proof. intros. unfold pd_entry. destruct (i <? 8); [ apply table_entry_range | rep_lia ]. Qed.

(* table(phys, k) = (phys + 4096u * k) | 7u *)
Lemma table_repr: forall phys k, 0 <= phys <= Int64.max_unsigned -> 0 <= k <= 10 ->
  Int64.or (Int64.add (Int64.repr phys) (Int64.mul (Int64.repr 4096) (Int64.repr k))) (Int64.repr 7) =
  Int64.repr (table_entry phys k).
Proof.
  intros phys k Hp Hk. unfold Int64.mul, Int64.add, Int64.or.
  rewrite (Int64.unsigned_repr 4096), (Int64.unsigned_repr k), (Int64.unsigned_repr phys),
    (Int64.unsigned_repr 7) by rep_lia.
  rewrite (Int64.unsigned_repr (4096 * k)) by rep_lia. rewrite Int64.unsigned_repr_eq.
  unfold table_entry, W. rewrite (Z.mul_comm 4096 k). reflexivity.
Qed.

(* (c & QOTOM_ROOT_PRESENT) != 0 *)
Lemma present_repr: forall c, 0 <= c <= Int64.max_unsigned ->
  Int64.eq (Int64.and (Int64.repr c) (Int64.repr 1)) (Int64.repr 0) = negb (Z.odd c).
Proof.
  intros c Hc. rewrite and_repr by rep_lia.
  change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
  rewrite Zmod_odd. destruct (Z.odd c); reflexivity.
Qed.

(* (c & QOTOM_ROOT_ADDRESS_MASK) >> 12 *)
Lemma frame_range: forall c, 0 <= c <= Int64.max_unsigned -> 0 <= frame_of c <= Int64.max_unsigned.
Proof.
  intros c Hc. unfold frame_of. pose proof (land_range c ADDRESS_MASK Hc).
  rewrite Z.shiftr_div_pow2 by lia. split; [ apply Z.div_pos; lia | ].
  apply Z.le_trans with (Z.land c ADDRESS_MASK); [ | lia ].
  apply Z.div_le_upper_bound; [ lia | ]. lia.
Qed.

Lemma frame_repr: forall c, 0 <= c <= Int64.max_unsigned ->
  Int64.shru (Int64.and (Int64.repr c) (Int64.repr ADDRESS_MASK)) (Int64.repr 12) = Int64.repr (frame_of c).
Proof.
  intros c Hc. rewrite and_repr by (unfold ADDRESS_MASK; rep_lia).
  unfold Int64.shru. rewrite !Int64.unsigned_repr by (try apply land_range; rep_lia). reflexivity.
Qed.

(* The leaf of the window at page p:
   (((base >> 12) + (p - slot)) << 12) | PRESENT | NX | (writable ? WRITABLE : 0). *)
Lemma want_repr: forall base p slot (wr: bool),
  0 <= base <= Int64.max_unsigned -> 0 <= p <= Int64.max_unsigned -> 0 <= slot <= Int64.max_unsigned ->
  Int64.or (Int64.or (Int64.or
     (Int64.shl (Int64.add (Int64.shru (Int64.repr base) (Int64.repr 12)) (Int64.sub (Int64.repr p) (Int64.repr slot)))
                (Int64.repr 12))
     (Int64.repr 1)) (Int64.shl (Int64.repr 1) (Int64.repr 63))) (Int64.repr (if wr then 2 else 0)) =
  Int64.repr (Z.lor (Z.lor (Z.lor (((Z.shiftr base 12 + (p - slot) mod W) mod W * 4096) mod W) 1) NX)
                    (if wr then 2 else 0)).
Proof.
  intros base p slot wr Hb Hp Hs.
  assert (Sh: Int64.shru (Int64.repr base) (Int64.repr 12) = Int64.repr (Z.shiftr base 12)).
  { unfold Int64.shru. rewrite !Int64.unsigned_repr by rep_lia. reflexivity. }
  assert (Shr: 0 <= Z.shiftr base 12 <= Int64.max_unsigned).
  { rewrite Z.shiftr_div_pow2 by lia. split; [ apply Z.div_pos; lia | ].
    apply Z.le_trans with base; [ apply Z.div_le_upper_bound; lia | lia ]. }
  assert (Sub: Int64.sub (Int64.repr p) (Int64.repr slot) = Int64.repr ((p - slot) mod W)).
  { unfold Int64.sub. rewrite !Int64.unsigned_repr by rep_lia. rewrite repr_mod. reflexivity. }
  rewrite Sh, Sub.
  assert (Add: Int64.add (Int64.repr (Z.shiftr base 12)) (Int64.repr ((p - slot) mod W)) =
               Int64.repr ((Z.shiftr base 12 + (p - slot) mod W) mod W)).
  { unfold Int64.add. rewrite !Int64.unsigned_repr by (try apply mod_range; lia).
    rewrite repr_mod. reflexivity. }
  rewrite Add.
  assert (Shl: Int64.shl (Int64.repr ((Z.shiftr base 12 + (p - slot) mod W) mod W)) (Int64.repr 12) =
               Int64.repr (((Z.shiftr base 12 + (p - slot) mod W) mod W * 4096) mod W)).
  { unfold Int64.shl. rewrite !Int64.unsigned_repr by (try apply mod_range; rep_lia).
    rewrite Z.shiftl_mul_pow2 by lia. rewrite repr_mod. reflexivity. }
  rewrite Shl.
  assert (Nx: Int64.shl (Int64.repr 1) (Int64.repr 63) = Int64.repr NX) by reflexivity.
  rewrite Nx.
  pose proof (mod_range (((Z.shiftr base 12 + (p - slot) mod W) mod W * 4096))) as R.
  rewrite or_repr by (auto; rep_lia).
  rewrite or_repr by (try apply lor_range; auto; unfold NX; rep_lia).
  rewrite or_repr by (try (destruct wr; rep_lia); repeat apply lor_range; auto; unfold NX; rep_lia).
  reflexivity.
Qed.

Lemma scan_leaf_range: forall w wr p c, 0 <= c <= Int64.max_unsigned ->
  0 <= scan_leaf w wr p c <= Int64.max_unsigned.
Proof.
  intros w wr p c Hc. unfold scan_leaf. destruct (in_slots w p); [ | exact Hc ].
  repeat apply lor_range; try apply mod_range; try (destruct wr); unfold NX; rep_lia.
Qed.

(* (limit - base) / 4096u *)
Lemma pages_repr: forall limit base, 0 <= limit <= Int64.max_unsigned -> 0 <= base <= Int64.max_unsigned ->
  Int64.divu (Int64.sub (Int64.repr limit) (Int64.repr base)) (Int64.repr 4096) =
  Int64.repr (((limit - base) mod W) / 4096).
Proof.
  intros limit base Hl Hb. unfold Int64.divu, Int64.sub.
  rewrite (Int64.unsigned_repr limit), (Int64.unsigned_repr base), (Int64.unsigned_repr 4096) by rep_lia.
  rewrite Int64.unsigned_repr_eq. reflexivity.
Qed.

Lemma pages_range: forall w, 0 <= pages_of w <= Int64.max_unsigned.
Proof.
  intros w. unfold pages_of. pose proof (mod_range (w_limit w - w_base w)).
  split; [ apply Z.div_pos; lia | ]. apply Z.le_trans with ((w_limit w - w_base w) mod W); [ | lia ].
  apply Z.div_le_upper_bound; lia.
Qed.

Lemma member_sublist_succ: forall f fs i, 0 <= i < Zlength fs ->
  member f (sublist 0 (i + 1) fs) = member f (sublist 0 i fs) || (f =? Znth i fs).
Proof.
  intros f fs i Hi. rewrite (sublist_split 0 i (i + 1)) by lia. rewrite sublist_len_1 by lia.
  unfold member. rewrite existsb_app. simpl. rewrite orb_false_r. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* ancestors_ok, test by test                                              *)
(* ---------------------------------------------------------------------- *)

Definition anc_head (r: root) (phys: Z) : bool :=
  (clear_accessed (Znth 0 (pml4 r)) =? table_entry phys 1) && (clear_accessed (Znth 0 (pdpt r)) =? table_entry phys 2).
Definition anc_top (r: root) (i: Z) : bool := (Znth i (pml4 r) =? 0) && (Znth i (pdpt r) =? 0).
Definition anc_pd (r: root) (phys i: Z) : bool := clear_accessed (Znth i (pd r)) =? pd_entry phys i.

Lemma ancestors_ok_eq: forall r phys,
  ancestors_ok r phys =
  anc_head r phys && forallb (anc_top r) (map (Z.add 1) (idx 511)) && forallb (anc_pd r phys) (idx 512).
Proof. reflexivity. Qed.

Lemma in_top: forall i, 1 <= i < 512 -> In i (map (Z.add 1) (idx 511)).
Proof.
  intros i Hi. apply in_map_iff. exists (i - 1). split; [ lia | apply in_idx; lia ].
Qed.

(* ---------------------------------------------------------------------- *)
(* scan_ok, page by page                                                   *)
(* ---------------------------------------------------------------------- *)

Definition page_ok (r k: root) (inv: list Z) (w: window) (writable: bool) (p: Z) : bool :=
  negb (removes inv (Znth p (pt k))) && (Znth p (pt r) =? scan_leaf w writable p (Znth p (pt k))).

Lemma scan_ok_pages: forall r k rp kp inv w writable,
  scan_ok r k rp kp inv w writable =
  ancestors_ok r rp && ancestors_ok k kp && forallb (page_ok r k inv w writable) (idx LEAVES).
Proof. reflexivity. Qed.
