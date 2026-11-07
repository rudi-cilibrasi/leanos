(* Law table_copy_exact: facts of lists, words and the model's mem that the proofs of the harness's functions
   share; no program here. *)
Require Import VST.floyd.proofauto.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawDefs.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* ---------------------------------------------------------------------- *)
(* Lists                                                                   *)
(* ---------------------------------------------------------------------- *)

Lemma Forall_upd: forall {A} {d: Inhabitant A} (P: A -> Prop) l i x, Forall P l -> P x -> Forall P (upd_Znth i l x).
Proof.
  intros A d P l i x F Px. destruct (Z_lt_le_dec i 0) as [Hi | Hi]; [ rewrite upd_Znth_out_of_range by lia; auto | ].
  destruct (Z_lt_le_dec i (Zlength l)) as [Hl | Hl]; [ | rewrite upd_Znth_out_of_range by lia; auto ].
  rewrite upd_Znth_unfold by lia. apply Forall_app; split; [ apply Forall_sublist; auto | ].
  constructor; auto. apply Forall_sublist; auto.
Qed.

Lemma Forall_Znth': forall {A} {d: Inhabitant A} (P: A -> Prop) l i, Forall P l -> 0 <= i < Zlength l -> P (Znth i l).
Proof. intros. exact (proj1 (Forall_Znth _ _) H i H0). Qed.

Lemma Zlength_bytes_val: forall bs, Zlength (bytes_val bs) = Zlength bs.
Proof. intros. unfold bytes_val. apply Zlength_map. Qed.

Lemma Znth_bytes_val: forall bs i, 0 <= i < Zlength bs -> Znth i (bytes_val bs) = Vint (Int.repr (Znth i bs)).
Proof. intros. unfold bytes_val. rewrite Znth_map by auto. reflexivity. Qed.

Lemma sublist_bytes_val: forall bs i j, sublist i j (bytes_val bs) = bytes_val (sublist i j bs).
Proof. intros. unfold bytes_val. rewrite sublist_map. reflexivity. Qed.

Lemma bytes_val_app: forall a b, bytes_val (a ++ b) = bytes_val a ++ bytes_val b.
Proof. intros. unfold bytes_val. apply map_app. Qed.

Lemma upd_bytes_val: forall bs i b, upd_Znth i (bytes_val bs) (Vint (Int.repr b)) = bytes_val (upd_Znth i bs b).
Proof. intros. unfold bytes_val. apply (upd_Znth_map (fun z => Vint (Int.repr z))). Qed.

Lemma byte_at: forall bs i, Forall byte_ok bs -> 0 <= i < Zlength bs -> 0 <= Znth i bs <= 255.
Proof. intros. pose proof (Forall_Znth' _ _ i H H0). unfold byte_ok in H1. rep_lia. Qed.

Lemma Forall_byte_sublist: forall bs i j, Forall byte_ok bs -> Forall byte_ok (sublist i j bs).
Proof. intros. apply Forall_sublist; auto. Qed.

Lemma Znth_map_vl: forall l i, 0 <= i < Zlength l -> Znth i (map vl l) = vl (Znth i l).
Proof. intros. rewrite Znth_map by auto. reflexivity. Qed.

Lemma Znth_map_vi: forall l i, 0 <= i < Zlength l -> Znth i (map vi l) = vi (Znth i l).
Proof. intros. rewrite Znth_map by auto. reflexivity. Qed.

Lemma upd_Znth_map_vl: forall l i v, upd_Znth i (map vl l) (vl v) = map vl (upd_Znth i l v).
Proof. intros. rewrite upd_Znth_map. reflexivity. Qed.

Lemma upd_Znth_map_vi: forall l i v, upd_Znth i (map vi l) (vi v) = map vi (upd_Znth i l v).
Proof. intros. rewrite upd_Znth_map. reflexivity. Qed.

(* A prefix of answers extended by one more. *)
Lemma prefix_snoc: forall (cur l: list Z) v k, Zlength l = k -> Zlength cur < k ->
  sublist 0 (Zlength cur) l = cur ->
  sublist 0 (Zlength cur + 1) (upd_Znth (Zlength cur) l v) = cur ++ [v].
Proof. intros. pose proof (Zlength_nonneg cur). subst k. rewrite <- H1. list_solve. Qed.

Lemma prefix_full: forall (cur l: list Z) v k, Zlength l = k + 1 -> Zlength cur = k -> 0 <= k ->
  sublist 0 (Zlength cur) l = cur -> upd_Znth (Zlength cur) l v = cur ++ [v].
Proof. intros. rewrite <- H2. list_solve. Qed.

(* ---------------------------------------------------------------------- *)
(* 0, 1, .., n - 1                                                         *)
(* ---------------------------------------------------------------------- *)

Lemma range_succ: forall n, 0 <= n -> range (n + 1) = range n ++ [n].
Proof.
  intros. unfold range. rewrite Z2Nat.inj_add by lia. rewrite Nat.add_1_r, seq_S, map_app.
  simpl. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma In_range: forall n i, In i (range n) -> 0 <= i < n.
Proof.
  unfold range. intros n i H. apply in_map_iff in H as [k [E I]]. apply in_seq in I. subst.
  destruct (Z_lt_le_dec n 0).
  - rewrite Z_to_nat_neg in I by lia. lia.
  - lia.
Qed.

Lemma Zlength_range: forall n, 0 <= n -> Zlength (range n) = n.
Proof. intros. unfold range. rewrite Zlength_map, Zlength_correct, length_seq. lia. Qed.

Lemma fold_left_ext_in: forall {A B: Type} (f g: A -> B -> A) (l: list B) (a: A),
  (forall x y, In y l -> f x y = g x y) -> fold_left f l a = fold_left g l a.
Proof.
  intros A B f g l. induction l as [ | y l IH]; intros a H; simpl; [ reflexivity | ].
  rewrite H by (left; reflexivity). apply IH. intros. apply H. right; auto.
Qed.

(* i, i + 1, .., n - 1 *)
Definition range_from (i n: Z) : list Z := map Z.of_nat (seq (Z.to_nat i) (Z.to_nat (n - i))).

Lemma range_from_0: forall n, range_from 0 n = range n.
Proof. intros. unfold range_from, range. rewrite Z.sub_0_r. reflexivity. Qed.

Lemma range_from_cons: forall i n, 0 <= i < n -> range_from i n = i :: range_from (i + 1) n.
Proof.
  intros. unfold range_from.
  replace (Z.to_nat (n - i)) with (S (Z.to_nat (n - (i + 1)))) by lia.
  simpl. rewrite Z2Nat.id by lia. f_equal. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. reflexivity.
Qed.

Lemma range_from_nil: forall n, range_from n n = nil.
Proof. intros. unfold range_from. replace (n - n) with 0 by lia. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* Little-endian values                                                    *)
(* ---------------------------------------------------------------------- *)

Fixpoint le (l: list Z) : Z := match l with nil => 0 | b :: t => b + 256 * le t end.

Lemma le_app1: forall l b, le (l ++ [b]) = le l + b * 256 ^ Zlength l.
Proof.
  induction l as [ | a l IH]; intros b; simpl.
  - rewrite ?Zlength_nil. simpl. lia.
  - rewrite IH, Zlength_cons. rewrite Z.pow_succ_r by (apply Zlength_nonneg). lia.
Qed.

Lemma le_bound: forall l, Forall byte_ok l -> 0 <= le l < 256 ^ Zlength l.
Proof.
  induction l as [ | a l IH]; intros F; simpl.
  - rewrite ?Zlength_nil. simpl. lia.
  - inversion F; subst. unfold byte_ok in H1. change Byte.max_unsigned with 255 in H1. specialize (IH H2).
    rewrite Zlength_cons, Z.pow_succ_r by (apply Zlength_nonneg). nia.
Qed.

Lemma little_snoc: forall l b, little (l ++ [b]) = Z.lor (little l) (Z.shiftl b (8 * Zlength l)).
Proof.
  intros. unfold little. rewrite Zlength_app, Zlength_cons, Zlength_nil.
  rewrite range_succ by (apply Zlength_nonneg). rewrite fold_left_app. simpl.
  rewrite Znth_app2 by lia. replace (Zlength l - Zlength l) with 0 by lia. rewrite Znth_0_cons.
  f_equal. apply fold_left_ext_in. intros x y I. apply In_range in I.
  rewrite Znth_app1 by lia. reflexivity.
Qed.

Lemma land_shiftl_low: forall a b n, 0 <= n -> 0 <= a < 2 ^ n -> Z.land a (Z.shiftl b n) = 0.
Proof.
  intros. apply Z.bits_inj'. intros m Hm. rewrite Z.land_spec, Z.bits_0.
  destruct (Z_lt_le_dec m n).
  - rewrite Z.shiftl_spec by lia. rewrite (Z.testbit_neg_r b (m - n)) by lia. apply andb_false_r.
  - replace a with (a mod 2 ^ n) by (apply Z.mod_small; lia).
    rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma lor_shiftl_add: forall a b n, 0 <= n -> 0 <= a < 2 ^ n -> Z.lor a (Z.shiftl b n) = a + b * 2 ^ n.
Proof.
  intros. rewrite <- Z.lxor_lor by (apply land_shiftl_low; auto).
  rewrite <- Z.add_nocarry_lxor by (apply land_shiftl_low; auto).
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma pow256: forall n, 0 <= n -> 256 ^ n = 2 ^ (8 * n).
Proof. intros. rewrite Z.pow_mul_r by lia. reflexivity. Qed.

Lemma little_le: forall l, Forall byte_ok l -> little l = le l.
Proof.
  intros l. induction l as [ | b l IH] using rev_ind; intros F; [ reflexivity | ].
  apply Forall_app in F as [F1 F2]. inversion F2; subst. unfold byte_ok in H1. change Byte.max_unsigned with 255 in H1.
  rewrite little_snoc, IH by auto. rewrite le_app1.
  pose proof (le_bound l F1). pose proof (Zlength_nonneg l).
  rewrite pow256 in * by lia. apply lor_shiftl_add; lia.
Qed.

Lemma little_bound: forall l, Forall byte_ok l -> 0 <= little l < 256 ^ Zlength l.
Proof. intros. rewrite little_le by auto. apply le_bound; auto. Qed.

Lemma little_u64: forall l, Forall byte_ok l -> Zlength l <= 8 -> u64_ok (little l).
Proof.
  intros. pose proof (little_bound l H). unfold u64_ok.
  assert (256 ^ Zlength l <= 256 ^ 8) by (apply Z.pow_le_mono_r; lia).
  change (256 ^ 8) with (Int64.max_unsigned + 1) in H2. lia.
Qed.

(* One more byte of a little-endian value, as the C composes it in 64 bits. *)
Lemma little_step64: forall l b, Forall byte_ok l -> 0 <= b <= 255 -> Zlength l < 8 ->
  Int64.or (Int64.repr (little l)) (Int64.repr (Z.shiftl b (8 * Zlength l))) = Int64.repr (little (l ++ [b])).
Proof.
  intros l b F B L. pose proof (little_bound l F) as LB. pose proof (Zlength_nonneg l) as L0.
  rewrite little_snoc. unfold Int64.or.
  assert (Hs: 0 <= Z.shiftl b (8 * Zlength l) <= Int64.max_unsigned).
  { rewrite Z.shiftl_mul_pow2 by lia.
    assert (2 ^ (8 * Zlength l) <= 2 ^ 56) by (apply Z.pow_le_mono_r; lia).
    change (2 ^ 56) with 72057594037927936 in H. split; [ apply Z.mul_nonneg_nonneg; lia | ].
    unfold Int64.max_unsigned; simpl; nia. }
  assert (Hl: 0 <= little l <= Int64.max_unsigned).
  { assert (256 ^ Zlength l <= 256 ^ 8) by (apply Z.pow_le_mono_r; lia).
    change (256 ^ 8) with (Int64.max_unsigned + 1) in H. lia. }
  rewrite !Int64.unsigned_repr by auto. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* Sums and checksums                                                      *)
(* ---------------------------------------------------------------------- *)

Lemma checksum_gen: forall l c, fold_left (fun c b => (c + b) mod 256) l (c mod 256) = (fold_left Z.add l c) mod 256.
Proof.
  induction l as [ | b l IH]; intros c; simpl; [ reflexivity | ].
  rewrite Zplus_mod_idemp_l. apply IH.
Qed.

Lemma checksum_sum: forall l, checksum l = (fold_left Z.add l 0) mod 256.
Proof. intros. unfold checksum. rewrite <- checksum_gen. reflexivity. Qed.

Lemma sum_snoc: forall l b, fold_left Z.add (l ++ [b]) 0 = fold_left Z.add l 0 + b.
Proof. intros. rewrite fold_left_app. reflexivity. Qed.

Lemma sum_bound: forall l, Forall byte_ok l -> 0 <= fold_left Z.add l 0 <= 255 * Zlength l.
Proof.
  intros l. induction l as [ | b l IH] using rev_ind; intros F; [ simpl; rewrite ?Zlength_nil; lia | ].
  apply Forall_app in F as [F1 F2]. inversion F2; subst. unfold byte_ok in H1. change Byte.max_unsigned with 255 in H1.
  rewrite sum_snoc, Zlength_app, Zlength_cons, Zlength_nil. specialize (IH F1). lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* The model's mem                                                         *)
(* ---------------------------------------------------------------------- *)

(* The bytes of the arena the SDT g is copied into, and its capacity. *)
Definition base_mem (m: mem) (g: target) : list Z := match g with TRoot => m_root m | TTable _ => m_tables m end.
Definition base_cap (x: inputs) (g: target) : Z :=
  match g with TRoot => root_capacity x | TTable _ => table_capacity x end.

Lemma region_base: forall m g len,
  region m (dest_of g) len = sublist (cursor_of g) (cursor_of g + len) (base_mem m g).
Proof. intros. destruct g; simpl; [ rewrite Z.add_0_l | ]; reflexivity. Qed.

Lemma base_write: forall m g bs, base_mem (write m (dest_of g) bs) g = overlay (cursor_of g) bs (base_mem m g).
Proof. intros. destruct g; reflexivity. Qed.

Lemma capacity_base: forall x g, capacity_of x g = base_cap x g - cursor_of g.
Proof. intros. destruct g; simpl; [ lia | reflexivity ]. Qed.

Lemma overlay_region: forall off len l, 0 <= off -> 0 <= len -> off + len <= Zlength l ->
  overlay off (sublist off (off + len) l) l = l.
Proof. intros. unfold overlay. list_solve. Qed.

Lemma Zlength_overlay: forall off bs l, 0 <= off -> off + Zlength bs <= Zlength l ->
  Zlength (overlay off bs l) = Zlength l.
Proof. intros. unfold overlay. pose proof (Zlength_nonneg bs). list_solve. Qed.

Lemma sublist_overlay: forall off bs l, 0 <= off -> off + Zlength bs <= Zlength l ->
  sublist off (off + Zlength bs) (overlay off bs l) = bs.
Proof. intros. unfold overlay. pose proof (Zlength_nonneg bs). list_solve. Qed.

Lemma Forall_overlay: forall (P: Z -> Prop) off bs l, Forall P bs -> Forall P l -> Forall P (overlay off bs l).
Proof.
  intros. unfold overlay. apply Forall_app; split; [ apply Forall_sublist; auto | ].
  apply Forall_app; split; auto. apply Forall_sublist; auto.
Qed.

Lemma overlay_split: forall off bs l, 0 <= off -> off + Zlength bs <= Zlength l ->
  overlay off bs l = sublist 0 off l ++ bs ++ sublist (off + Zlength bs) (Zlength l) l.
Proof. reflexivity. Qed.

(* A failed copy leaves what was there: the reply's bytes are the region's. *)
Lemma write_region: forall m g len, 0 <= len -> cursor_of g + len <= Zlength (base_mem m g) ->
  0 <= cursor_of g -> write m (dest_of g) (region m (dest_of g) len) = m.
Proof.
  intros m g len L1 L2 L3. destruct m as [H R T rc en ss]. destruct g as [ | l]; simpl in *.
  - f_equal. replace (sublist 0 len R) with (sublist 0 (0 + len) R) by (f_equal; lia).
    apply overlay_region; lia.
  - f_equal. apply overlay_region; lia.
Qed.

Lemma write_header_same: forall m, Zlength (m_header m) = HEADER_BYTES ->
  write m DHeader (region m DHeader HEADER_BYTES) = m.
Proof.
  intros [H R T rc en ss] L. simpl in *. f_equal. rewrite sublist_same by auto. reflexivity.
Qed.

(* The copy records' fields after a write: only the byte objects change. *)
Lemma write_meta: forall m d bs,
  m_root_copy (write m d bs) = m_root_copy m /\ m_entries (write m d bs) = m_entries m /\
  m_slots (write m d bs) = m_slots m.
Proof. intros. destruct d; simpl; auto. Qed.
