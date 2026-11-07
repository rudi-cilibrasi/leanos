(* Pure lemmas for the body proofs of include/acpi_table_copy.h (Pipe*.v): C booleans as ints, bytes and their
   literals, 32- and 64-bit words, the little-endian composition `little` (its value, its bounds, its bytes), the
   checksum, the padding, `range`, and list facts about the byte objects. *)
Require Import VST.floyd.proofauto.
Require Import LeanosAcpi.acpi.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
#[local] Existing Instance AcpiSpecs.CS.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* ---------- C booleans ---------- *)

Definition bint (b: bool) : int := if b then Int.one else Int.zero.

Lemma bint_true: forall b, bint b <> Int.zero -> b = true.
Proof. intros [ | ] H; [ reflexivity | exfalso; apply H; reflexivity ]. Qed.
Lemma bint_false: forall b, bint b = Int.zero -> b = false.
Proof. intros [ | ] H; [ exfalso; apply Int.one_not_zero; exact H | reflexivity ]. Qed.

Ltac bfix :=
  repeat match goal with
  | H: bint _ <> Int.zero |- _ => apply bint_true in H
  | H: bint _ = Int.zero |- _ => apply bint_false in H
  end.

Lemma bool2val_bint: forall b, bool2val b = Vint (bint b).
Proof. intros [ | ]; reflexivity. Qed.

Lemma bint_one: bint true = Int.one.
Proof. reflexivity. Qed.

(* ---------- bytes ---------- *)

Lemma Zlength_bytes_val: forall bs, Zlength (bytes_val bs) = Zlength bs.
Proof. intros. unfold bytes_val. apply Zlength_map. Qed.

Lemma Znth_bytes_val: forall bs i, 0 <= i < Zlength bs -> Znth i (bytes_val bs) = Vint (Int.repr (Znth i bs)).
Proof. intros. unfold bytes_val. rewrite Znth_map by lia. reflexivity. Qed.

Lemma sublist_bytes_val: forall bs i j, sublist i j (bytes_val bs) = bytes_val (sublist i j bs).
Proof. intros. unfold bytes_val. rewrite sublist_map. reflexivity. Qed.

Lemma bytes_val_app: forall a b, bytes_val (a ++ b) = bytes_val a ++ bytes_val b.
Proof. intros. unfold bytes_val. apply map_app. Qed.

Lemma tc_byte: forall b, 0 <= b <= 255 -> tc_val tuchar (Vint (Int.repr b)).
Proof. intros. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. Qed.

Lemma byte_at: forall bs i, Forall byte_ok bs -> 0 <= i < Zlength bs -> 0 <= Znth i bs <= 255.
Proof. intros. apply (proj1 (Forall_Znth bs byte_ok) H i H0). Qed.

Lemma tc_schar: forall c, 0 <= c < 128 -> tc_val tschar (Vint (Int.repr c)).
Proof. intros. simpl. rewrite Int.signed_repr by rep_lia. rep_lia. Qed.

Lemma zext8_small: forall c, 0 <= c <= 255 -> Int.zero_ext 8 (Int.repr c) = Int.repr c.
Proof. intros. apply zero_ext_inrange. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. Qed.

Lemma Znth5_0: forall (a b c d e: val), Znth 0 [a; b; c; d; e] = a. Proof. reflexivity. Qed.
Lemma Znth5_1: forall (a b c d e: val), Znth 1 [a; b; c; d; e] = b. Proof. reflexivity. Qed.
Lemma Znth5_2: forall (a b c d e: val), Znth 2 [a; b; c; d; e] = c. Proof. reflexivity. Qed.
Lemma Znth5_3: forall (a b c d e: val), Znth 3 [a; b; c; d; e] = d. Proof. reflexivity. Qed.

Lemma eq_byte_char: forall a c, 0 <= a <= 255 -> 0 <= c < 128 ->
  bool2val (Int.eq (Int.repr a) (Int.zero_ext 8 (Int.repr c))) = Vint (bint (a =? c)).
Proof.
  intros. rewrite zext8_small by lia. unfold Int.eq. rewrite !Int.unsigned_repr by rep_lia.
  unfold bint. destruct (zeq a c); destruct (Z.eqb_spec a c); try lia; reflexivity.
Qed.

Lemma Forall_byte_sublist: forall bs i j, Forall byte_ok bs -> Forall byte_ok (sublist i j bs).
Proof. intros. apply Forall_sublist. auto. Qed.

(* ---------- words ---------- *)

Lemma eq64_repr: forall a b, u64_ok a -> u64_ok b -> Int64.eq (Int64.repr a) (Int64.repr b) = (a =? b).
Proof.
  intros. unfold u64_ok in *. unfold Int64.eq. rewrite !Int64.unsigned_repr by auto.
  destruct (zeq a b); destruct (Z.eqb_spec a b); auto; lia.
Qed.

Lemma ltu64_repr: forall a b, u64_ok a -> u64_ok b -> Int64.ltu (Int64.repr a) (Int64.repr b) = (a <? b).
Proof.
  intros. unfold u64_ok in *. unfold Int64.ltu. rewrite !Int64.unsigned_repr by auto.
  destruct (zlt a b); destruct (Z.ltb_spec a b); auto; lia.
Qed.

Lemma eq32_repr: forall a b, u32_ok a -> u32_ok b -> Int.eq (Int.repr a) (Int.repr b) = (a =? b).
Proof.
  intros. unfold u32_ok in *. unfold Int.eq. rewrite !Int.unsigned_repr by auto.
  destruct (zeq a b); destruct (Z.eqb_spec a b); auto; lia.
Qed.

Lemma ltu32_repr: forall a b, u32_ok a -> u32_ok b -> Int.ltu (Int.repr a) (Int.repr b) = (a <? b).
Proof.
  intros. unfold u32_ok in *. unfold Int.ltu. rewrite !Int.unsigned_repr by auto.
  destruct (zlt a b); destruct (Z.ltb_spec a b); auto; lia.
Qed.

Lemma repr64_inj: forall a b, u64_ok a -> u64_ok b -> Int64.repr a = Int64.repr b -> a = b.
Proof. intros. unfold u64_ok in *. apply repr_inj_unsigned64; auto. Qed.

Lemma repr32_inj: forall a b, u32_ok a -> u32_ok b -> Int.repr a = Int.repr b -> a = b.
Proof. intros. unfold u32_ok in *. apply repr_inj_unsigned; auto. Qed.

Lemma repr64_neq: forall a b, Int64.repr a <> Int64.repr b -> a <> b.
Proof. intros a b H E. subst. contradiction. Qed.

Lemma repr32_neq: forall a b, Int.repr a <> Int.repr b -> a <> b.
Proof. intros a b H E. subst. contradiction. Qed.

Lemma repr_mod32: forall z, Int.repr (z mod 2 ^ 32) = Int.repr z.
Proof.
  intros. rewrite <- (Int.repr_unsigned (Int.repr z)), Int.unsigned_repr_eq. reflexivity.
Qed.

Lemma u32_u64: forall a, u32_ok a -> u64_ok a.
Proof. unfold u32_ok, u64_ok. intros. rep_lia. Qed.

Lemma byte_u32: forall a, 0 <= a <= 255 -> u32_ok a.
Proof. unfold u32_ok. intros. rep_lia. Qed.

(* ---------- little-endian values ---------- *)

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

Lemma Znth_range: forall n i, 0 <= i < n -> Znth i (range n) = i.
Proof.
  intros. unfold range. rewrite Znth_map by (rewrite Zlength_correct, length_seq; lia).
  rewrite <- nth_Znth by (rewrite Zlength_correct, length_seq; lia).
  rewrite seq_nth by lia. simpl. lia.
Qed.

Lemma fold_left_ext_in: forall {A B: Type} (f g: A -> B -> A) (l: list B) (a: A),
  (forall x y, In y l -> f x y = g x y) -> fold_left f l a = fold_left g l a.
Proof.
  intros A B f g l. induction l as [ | y l IH]; intros a H; simpl; [ reflexivity | ].
  rewrite H by (left; reflexivity). apply IH. intros. apply H. right; auto.
Qed.

Lemma little_snoc: forall l b, little (l ++ [b]) = Z.lor (little l) (Z.shiftl b (8 * Zlength l)).
Proof.
  intros. unfold little. rewrite Zlength_app, Zlength_cons, Zlength_nil.
  rewrite range_succ by (apply Zlength_nonneg). rewrite fold_left_app. simpl.
  rewrite Znth_app2 by lia. replace (Zlength l - Zlength l) with 0 by lia. rewrite Znth_0_cons.
  f_equal. apply fold_left_ext_in. intros x y I. apply In_range in I.
  rewrite Znth_app1 by lia. reflexivity.
Qed.

Lemma little_nil: little [] = 0.
Proof. reflexivity. Qed.

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

Lemma little_u32: forall l, Forall byte_ok l -> Zlength l <= 4 -> u32_ok (little l).
Proof.
  intros. pose proof (little_bound l H). unfold u32_ok.
  assert (256 ^ Zlength l <= 256 ^ 4) by (apply Z.pow_le_mono_r; lia).
  change (256 ^ 4) with (Int.max_unsigned + 1) in H2. lia.
Qed.

Lemma le_byte: forall l k, Forall byte_ok l -> 0 <= k < Zlength l -> (le l / 256 ^ k) mod 256 = Znth k l.
Proof.
  induction l as [ | b l IH]; intros k F K; [ rewrite Zlength_nil in K; lia | ].
  inversion F; subst. unfold byte_ok in H1. change Byte.max_unsigned with 255 in H1. rewrite Zlength_cons in K. cbn [le].
  destruct (Z.eq_dec k 0).
  - subst. rewrite Znth_0_cons. rewrite Z.pow_0_r, Z.div_1_r.
    rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_small; lia.
  - rewrite Znth_pos_cons by lia.
    replace (256 ^ k) with (256 * 256 ^ (k - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    rewrite <- Z.div_div by (try lia; apply Z.pow_pos_nonneg; lia).
    replace ((b + 256 * le l) / 256) with (le l).
    + apply IH; auto; lia.
    + rewrite Z.mul_comm, Z_div_plus_full by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma little_byte: forall l k, Forall byte_ok l -> 0 <= k < Zlength l ->
  Z.shiftr (little l) (8 * k) mod 256 = Znth k l.
Proof.
  intros. rewrite Z.shiftr_div_pow2 by lia. rewrite <- pow256 by lia. rewrite little_le by auto.
  apply le_byte; auto.
Qed.

Lemma little4: forall a b c d,
  little [a; b; c; d] = Z.lor (Z.lor (Z.lor a (Z.shiftl b 8)) (Z.shiftl c 16)) (Z.shiftl d 24).
Proof.
  intros. unfold little. change (range (Zlength [a; b; c; d])) with [0; 1; 2; 3]. cbn [fold_left].
  change (Znth 0 [a; b; c; d]) with a. change (Znth 1 [a; b; c; d]) with b.
  change (Znth 2 [a; b; c; d]) with c. change (Znth 3 [a; b; c; d]) with d.
  change (8 * 0) with 0. change (8 * 1) with 8. change (8 * 2) with 16. change (8 * 3) with 24.
  rewrite Z.shiftl_0_r, Z.lor_0_l. reflexivity.
Qed.

Lemma sublist_4_8: forall (bs: list Z), 8 <= Zlength bs ->
  sublist 4 8 bs = [Znth 4 bs; Znth 5 bs; Znth 6 bs; Znth 7 bs].
Proof. intros. list_solve. Qed.

(* The C's 32-bit composition of four bytes. *)
Lemma compose32: forall a b c d, 0 <= a <= 255 -> 0 <= b <= 255 -> 0 <= c <= 255 -> 0 <= d <= 255 ->
  Int.or (Int.or (Int.or (Int.repr a) (Int.shl (Int.repr b) (Int.repr 8)))
                 (Int.shl (Int.repr c) (Int.repr 16))) (Int.shl (Int.repr d) (Int.repr 24)) =
  Int.repr (little [a; b; c; d]).
Proof.
  intros. unfold Int.shl. rewrite !Int.unsigned_repr by rep_lia.
  rewrite little4. rewrite !or_repr. reflexivity.
Qed.

(* One step of the C's 64-bit composition: byte b or-ed in at bit 8 k. *)
Lemma compose64_step: forall l b, 0 <= b <= 255 -> 0 <= Zlength l < 8 ->
  Int64.or (Int64.repr (little l)) (Int64.shl (Int64.repr b) (Int64.repr (8 * Zlength l))) =
  Int64.repr (little (l ++ [b])).
Proof.
  intros. rewrite little_snoc. unfold Int64.shl. rewrite !Int64.unsigned_repr by rep_lia.
  apply or64_repr.
Qed.

(* The C's byte k of a 64-bit chunk: (uint8_t)(chunk >> 8 k). *)
Lemma chunk_byte: forall l k, Forall byte_ok l -> Zlength l <= 8 -> 0 <= k < Zlength l ->
  Int.zero_ext 8 (Int.repr (Int64.unsigned (Int64.shru (Int64.repr (little l)) (Int64.repr (8 * k))))) =
  Int.repr (Znth k l).
Proof.
  intros. pose proof (little_u64 l H H0). unfold u64_ok in H2.
  unfold Int64.shru. rewrite (Int64.unsigned_repr (little l)) by rep_lia.
  rewrite (Int64.unsigned_repr (8 * k)) by rep_lia.
  assert (0 <= Z.shiftr (little l) (8 * k) <= little l).
  { rewrite Z.shiftr_div_pow2 by lia. split; [ apply Z.div_pos; try lia; apply Z.pow_pos_nonneg; lia | ].
    apply Z.div_le_upper_bound; [ apply Z.pow_pos_nonneg; lia | ].
    assert (1 <= 2 ^ (8 * k)) by (apply Z.pow_le_mono_r with (a := 2) (b := 0) (c := 8 * k); lia). nia. }
  rewrite Int64.unsigned_repr by rep_lia.
  apply Int.same_if_eq. unfold Int.eq. rewrite Int.zero_ext_mod by (change Int.zwordsize with 32; lia).
  rewrite Int.unsigned_repr_eq. rewrite (Int.unsigned_repr (Znth k l)).
  - change (two_p 8) with 256. rewrite <- (Znumtheory.Zmod_div_mod 256 Int.modulus) by (try rep_lia; apply (Znumtheory.Zdivide_intro 256 Int.modulus 16777216); reflexivity).
    rewrite little_byte by auto. rewrite zeq_true. reflexivity.
  - pose proof (byte_at l k H H1). rep_lia.
Qed.

(* ---------- the checksum ---------- *)

Lemma checksum_snoc: forall l b, checksum (l ++ [b]) = (checksum l + b) mod 256.
Proof. intros. unfold checksum. rewrite fold_left_app. reflexivity. Qed.

Lemma checksum_acc_range: forall l a, 0 <= a < 256 -> 0 <= fold_left (fun c b => (c + b) mod 256) l a < 256.
Proof.
  induction l as [ | b l IH]; intros a H; simpl; [ auto | ]. apply IH. apply Z.mod_pos_bound. lia.
Qed.

Lemma checksum_range: forall l, 0 <= checksum l < 256.
Proof. intros. unfold checksum. apply checksum_acc_range. lia. Qed.

Lemma checksum_step: forall c b, 0 <= c <= 255 -> 0 <= b <= 255 ->
  Int.zero_ext 8 (Int.add (Int.repr c) (Int.repr b)) = Int.repr ((c + b) mod 256).
Proof.
  intros. rewrite add_repr. apply Int.same_if_eq. unfold Int.eq.
  rewrite Int.zero_ext_mod by (change Int.zwordsize with 32; lia). rewrite !Int.unsigned_repr by (try rep_lia; pose proof (Z.mod_pos_bound (c + b) 256); rep_lia).
  change (two_p 8) with 256. rewrite zeq_true. reflexivity.
Qed.

Lemma sublist_snoc: forall {A} {d: Inhabitant A} (l: list A) k, 0 <= k < Zlength l ->
  sublist 0 (k + 1) l = sublist 0 k l ++ [Znth k l].
Proof. intros. rewrite (sublist_split 0 k (k + 1)) by lia. rewrite sublist_len_1 by lia. reflexivity. Qed.

(* ---------- the padding ---------- *)

Lemma land_mask8: forall a, 0 <= a < 2 ^ 32 -> Z.land a 4294967288 = a / 8 * 8.
Proof.
  intros. replace 4294967288 with (Z.ldiff (Z.ones 32) (Z.ones 3)) by reflexivity.
  replace (a / 8 * 8) with (Z.shiftl (Z.shiftr a 3) 3)
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; reflexivity).
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
  destruct (Z_lt_le_dec n 3).
  - rewrite Z.shiftl_spec_low by lia. replace (n <? 3) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite !andb_false_r. reflexivity.
  - rewrite Z.shiftl_spec by lia. rewrite Z.shiftr_spec by lia. replace (n - 3 + 3) with n by lia.
    replace (n <? 3) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (Z_lt_le_dec n 32).
    + replace (n <? 32) with true by (symmetry; apply Z.ltb_lt; lia). rewrite andb_true_r. reflexivity.
    + replace (n <? 32) with false by (symmetry; apply Z.ltb_ge; lia).
      replace a with (a mod 2 ^ 32) by (apply Z.mod_small; lia).
      rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma padded_int: forall len, 0 <= len <= MAX_SDT_BYTES ->
  Int.and (Int.add (Int.repr len) (Int.repr 7)) (Int.not (Int.repr 7)) = Int.repr (padded len).
Proof.
  intros. unfold MAX_SDT_BYTES in H. rewrite add_repr.
  assert (E: Int.not (Int.repr 7) = Int.repr 4294967288) by (apply Int.same_if_eq; vm_compute; reflexivity).
  rewrite E, and_repr.
  unfold padded. rewrite land_mask8 by lia. reflexivity.
Qed.

Lemma padded_bounds: forall len, 0 <= len -> len <= padded len <= len + 7.
Proof. intros. unfold padded. pose proof (Z.div_mod (len + 7) 8). pose proof (Z.mod_pos_bound (len + 7) 8). lia. Qed.

(* ---------- comparisons as VST leaves them ---------- *)

Lemma zlt_ltb: forall a b, proj_sumbool (zlt a b) = (a <? b).
Proof. intros. destruct (zlt a b); destruct (Z.ltb_spec a b); auto; lia. Qed.

Lemma zeq_eqb: forall a b, proj_sumbool (zeq a b) = (a =? b).
Proof. intros. destruct (zeq a b); destruct (Z.eqb_spec a b); auto; lia. Qed.

Lemma bint_orb_true: forall a b, a = true -> Vint (Int.repr 1) = Vint (bint (a || b)).
Proof. intros. subst. reflexivity. Qed.

Lemma bint_orb_false: forall a b, a = false -> bint (a || b) = bint b.
Proof. intros. subst. reflexivity. Qed.

Lemma bint_negb: forall b, Int.eq (bint b) Int.zero = negb b.
Proof. intros [ | ]; reflexivity. Qed.

(* The header's length field, bytes 4..7, as the C composes it. *)
Lemma length32: forall bs, 8 <= Zlength bs -> Forall byte_ok bs ->
  Int.or (Int.or (Int.or (Int.repr (Znth 4 bs)) (Int.shl (Int.repr (Znth 5 bs)) (Int.repr 8)))
                 (Int.shl (Int.repr (Znth 6 bs)) (Int.repr 16))) (Int.shl (Int.repr (Znth 7 bs)) (Int.repr 24)) =
  Int.repr (little (sublist 4 8 bs)).
Proof.
  intros. rewrite sublist_4_8 by auto. apply compose32; apply byte_at; auto; lia.
Qed.

Lemma length32_u32: forall bs, 8 <= Zlength bs -> Forall byte_ok bs -> u32_ok (little (sublist 4 8 bs)).
Proof. intros. apply little_u32. apply Forall_sublist; auto. rewrite Zlength_sublist by lia. lia. Qed.

Lemma zext8_mod: forall z, 0 <= z <= Int.max_unsigned -> Int.zero_ext 8 (Int.repr z) = Int.repr (z mod 256).
Proof.
  intros. apply Int.same_if_eq. unfold Int.eq.
  rewrite Int.zero_ext_mod by (change Int.zwordsize with 32; lia).
  rewrite !Int.unsigned_repr by (try rep_lia; pose proof (Z.mod_pos_bound z 256); rep_lia).
  change (two_p 8) with 256. rewrite zeq_true. reflexivity.
Qed.

Lemma checksum_next: forall bs k, 0 <= k < Zlength bs -> Forall byte_ok bs ->
  vi (checksum (sublist 0 (k + 1) bs)) =
  Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int.repr (checksum (sublist 0 k bs) + Znth k bs)))).
Proof.
  intros. rewrite sublist_snoc, checksum_snoc by lia. unfold vi. f_equal.
  pose proof (checksum_range (sublist 0 k bs)). pose proof (byte_at bs k H0 H).
  rewrite zext8_mod by rep_lia. rewrite zext8_small; [ reflexivity | ].
  pose proof (Z.mod_pos_bound (checksum (sublist 0 k bs) + Znth k bs) 256). lia.
Qed.

Lemma eq64_true: forall a b, u64_ok a -> u64_ok b -> Int64.eq (Int64.repr a) (Int64.repr b) = true -> a = b.
Proof. intros. rewrite eq64_repr in H1 by auto. apply Z.eqb_eq; auto. Qed.

Lemma eq64_false: forall a b, u64_ok a -> u64_ok b -> Int64.eq (Int64.repr a) (Int64.repr b) = false -> a <> b.
Proof. intros. rewrite eq64_repr in H1 by auto. apply Z.eqb_neq; auto. Qed.

Lemma eq32_true: forall a b, u32_ok a -> u32_ok b -> Int.eq (Int.repr a) (Int.repr b) = true -> a = b.
Proof. intros. rewrite eq32_repr in H1 by auto. apply Z.eqb_eq; auto. Qed.

Lemma eq32_false: forall a b, u32_ok a -> u32_ok b -> Int.eq (Int.repr a) (Int.repr b) = false -> a <> b.
Proof. intros. rewrite eq32_repr in H1 by auto. apply Z.eqb_neq; auto. Qed.

Ltac uconst :=
  repeat match goal with
  | H: context [Int.unsigned (Int.repr ?c)] |- _ =>
      let v := eval compute in (Int.unsigned (Int.repr c)) in change (Int.unsigned (Int.repr c)) with v in H
  | |- context [Int.unsigned (Int.repr ?c)] =>
      let v := eval compute in (Int.unsigned (Int.repr c)) in change (Int.unsigned (Int.repr c)) with v
  end.

Lemma modu_repr: forall a b, u32_ok a -> u32_ok b -> Int.modu (Int.repr a) (Int.repr b) = Int.repr (a mod b).
Proof. intros. unfold Int.modu. unfold u32_ok in *. rewrite !Int.unsigned_repr by auto. reflexivity. Qed.

Lemma divu_repr: forall a b, u32_ok a -> u32_ok b -> Int.divu (Int.repr a) (Int.repr b) = Int.repr (a / b).
Proof. intros. unfold Int.divu. unfold u32_ok in *. rewrite !Int.unsigned_repr by auto. reflexivity. Qed.

Lemma repr_nonzero: forall z, 0 < z <= Int.max_unsigned -> Int.repr z <> Int.zero.
Proof.
  intros z H E. apply (f_equal Int.unsigned) in E. rewrite Int.unsigned_repr in E by rep_lia.
  rewrite Int.unsigned_zero in E. lia.
Qed.

(* ---------- splitting byte objects ---------- *)

Lemma split2_bytes: forall sh (bs: list Z) n n1 p, Zlength bs = n -> 0 <= n1 <= n ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) (bytes_val bs) p =
  (data_at sh (tarray tuchar n1) (bytes_val (sublist 0 n1 bs)) p *
   data_at sh (tarray tuchar (n - n1)) (bytes_val (sublist n1 n bs)) (offset_val n1 p))%logic.
Proof.
  intros. rewrite (split2_data_at_Tarray_tuchar sh n n1) by (rewrite ?Zlength_bytes_val; lia).
  rewrite !sublist_bytes_val. change (Tarray tuchar n noattr) with (tarray tuchar n).
  rewrite arr_field_address0 by (auto; lia). change (sizeof tuchar * n1) with (1 * n1).
  rewrite Z.mul_1_l. reflexivity.
Qed.

Lemma split3_bytes: forall sh (bs: list Z) n n1 n2 p, Zlength bs = n -> 0 <= n1 <= n2 -> n2 <= n ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) (bytes_val bs) p =
  (data_at sh (tarray tuchar n1) (bytes_val (sublist 0 n1 bs)) p *
   data_at sh (tarray tuchar (n2 - n1)) (bytes_val (sublist n1 n2 bs)) (offset_val n1 p) *
   data_at sh (tarray tuchar (n - n2)) (bytes_val (sublist n2 n bs)) (offset_val n2 p))%logic.
Proof.
  intros. rewrite (split3_data_at_Tarray_tuchar sh n n1 n2) by (rewrite ?Zlength_bytes_val; lia).
  rewrite !sublist_bytes_val. change (Tarray tuchar n noattr) with (tarray tuchar n).
  rewrite !arr_field_address0 by (auto; lia). change (sizeof tuchar * n1) with (1 * n1).
  change (sizeof tuchar * n2) with (1 * n2). rewrite !Z.mul_1_l. reflexivity.
Qed.

(* ---------- pointer arithmetic as VST leaves it ---------- *)

Lemma add_ptr_uchar_uint: forall p n, isptr p ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tuint p (Vint n)) = offset_val (Int.unsigned n) p.
Proof.
  intros. destruct p; try contradiction. simpl. unfold sem_add_ptr_int. simpl. f_equal. f_equal.
  unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Ptrofs.mul_commut, Ptrofs.mul_one. reflexivity.
Qed.

Lemma mul_uint: forall a b, eval_binop Omul tuint tuint (Vint (Int.repr a)) (Vint (Int.repr b)) = Vint (Int.repr (a * b)).
Proof. intros. simpl. unfold sem_mul. simpl. rewrite mul_repr. reflexivity. Qed.

(* The C's loop step physical |= (uint64_t)bytes[o + k] << (k * 8u), on bytes o .. o + k - 1 so far. *)
Lemma compose64_at: forall (l: list Z) o k, 0 <= o -> 0 <= k < 8 -> o + k < Zlength l -> Forall byte_ok l ->
  Int64.or (Int64.repr (little (sublist o (o + k) l)))
    (Int64.shl (Int64.repr (Int.unsigned (Int.repr (Znth (o + k) l))))
       (Int64.repr (Int.unsigned (Int.mul (Int.repr k) (Int.repr 8))))) =
  Int64.repr (little (sublist o (o + (k + 1)) l)).
Proof.
  intros. pose proof (byte_at l (o + k) H2 ltac:(lia)).
  rewrite mul_repr, !Int.unsigned_repr by rep_lia.
  replace (o + (k + 1)) with (o + k + 1) by lia.
  rewrite (sublist_split o (o + k) (o + k + 1)) by lia. rewrite sublist_len_1 by lia.
  replace (k * 8) with (8 * Zlength (sublist o (o + k) l)) by (rewrite Zlength_sublist by lia; lia).
  apply compose64_step; [ lia | rewrite Zlength_sublist by lia; lia ].
Qed.

Lemma compose64_0: forall (l: list Z) k, 0 <= k < 8 -> k < Zlength l -> Forall byte_ok l ->
  Int64.or (Int64.repr (little (sublist 0 k l)))
    (Int64.shl (Int64.repr (Int.unsigned (Int.repr (Znth k l))))
       (Int64.repr (Int.unsigned (Int.mul (Int.repr k) (Int.repr 8))))) =
  Int64.repr (little (sublist 0 (k + 1) l)).
Proof. intros. pose proof (compose64_at l 0 k ltac:(lia) H ltac:(lia) H1). simpl in H2. exact H2. Qed.

Lemma shift8_ok: forall k, 0 <= k < 8 -> Int.ltu (Int.mul (Int.repr k) (Int.repr 8)) Int64.iwordsize' = true.
Proof.
  intros. rewrite mul_repr. unfold Int.ltu. rewrite Int.unsigned_repr by rep_lia.
  change (Int.unsigned Int64.iwordsize') with 64. destruct (zlt (k * 8) 64); [ reflexivity | lia ].
Qed.

(* Comparisons of words the C made, as hypotheses, turned into comparisons of their values. *)
Ltac w64 :=
  repeat match goal with
  | H: Int64.repr ?a = Int64.zero |- _ => change Int64.zero with (Int64.repr 0) in H
  | H: Int64.repr ?a <> Int64.zero |- _ => change Int64.zero with (Int64.repr 0) in H
  | H: Int64.eq (Int64.repr ?a) Int64.zero = _ |- _ => change Int64.zero with (Int64.repr 0) in H
  | H: Int64.eq (Int64.repr ?a) (Int64.repr ?b) = true |- _ =>
      apply eq64_true in H; [ | unfold u64_ok in *; rep_lia | unfold u64_ok in *; rep_lia ]
  | H: Int64.eq (Int64.repr ?a) (Int64.repr ?b) = false |- _ =>
      apply eq64_false in H; [ | unfold u64_ok in *; rep_lia | unfold u64_ok in *; rep_lia ]
  | H: Int64.repr ?a <> Int64.repr ?b |- _ => apply repr64_neq in H
  | H: Int64.repr ?a = Int64.repr ?b |- _ =>
      apply repr64_inj in H; [ | unfold u64_ok in *; rep_lia | unfold u64_ok in *; rep_lia ]
  | H: Int.repr ?a <> Int.repr ?b |- _ => apply repr32_neq in H
  | H: Int.repr ?a = Int.repr ?b |- _ =>
      apply repr32_inj in H; [ | unfold u32_ok in *; rep_lia | unfold u32_ok in *; rep_lia ]
  end.

Lemma decode_entries_w': forall kind len, kind = 1 \/ kind = 2 ->
  exists w, (w = 4 \/ w = 8) /\ (if kind =? 1 then 4 else 8) = w /\
  decode_entries kind len =
   (if len <? HEADER_BYTES then inl S_ROOT_HEADER
   else if negb ((len - HEADER_BYTES) mod w =? 0) then inl S_ROOT_WIDTH
   else if MAX_ENTRIES <? (len - HEADER_BYTES) / w then inl S_ROOT_ENTRIES
   else inr ((len - HEADER_BYTES) / w, w)).
Proof. intros. destruct H; subst; eexists; (split; [ | split; [ reflexivity | reflexivity ] ]); auto. Qed.

(* ---------- the root's addresses ---------- *)

Lemma decode_from_cons: forall vec w e rest pre,
  decode_from vec w (e :: rest) pre =
  (let a := entry_at vec w e in
   if (a =? 0) || (MAX_U32 <? a) then inl S_ROOT_ENTRY_ADDRESS
   else if existsb (Z.eqb a) pre then inl S_ROOT_ENTRY_DUPLICATE
   else decode_from vec w rest (pre ++ [a])).
Proof. reflexivity. Qed.

Lemma sublist_range_cons: forall e n, 0 <= e < n -> sublist e n (range n) = e :: sublist (e + 1) n (range n).
Proof.
  intros. rewrite (sublist_split e (e + 1) n) by (try rewrite Zlength_range; lia).
  rewrite sublist_len_1 by (try rewrite Zlength_range; lia). rewrite Znth_range by lia. reflexivity.
Qed.

Lemma existsb_false: forall a pre, (forall i, 0 <= i < Zlength pre -> Znth i pre <> a) -> existsb (Z.eqb a) pre = false.
Proof.
  intros. destruct (existsb (Z.eqb a) pre) eqn:E; [ | reflexivity ].
  apply existsb_exists in E as [y [I Y]]. apply Z.eqb_eq in Y. subst y.
  apply In_Znth in I as [i [R Ei]]. exfalso. apply (H i R Ei).
Qed.

Lemma existsb_true: forall a pre i, 0 <= i < Zlength pre -> Znth i pre = a -> existsb (Z.eqb a) pre = true.
Proof.
  intros. apply existsb_exists. exists (Znth i pre). split; [ apply Znth_In; auto | subst; apply Z.eqb_refl ].
Qed.

Definition addr_ok (a: Z) : Prop := 0 < a <= MAX_U32.

Lemma entry_at_nonneg: forall vec w e, Forall byte_ok vec -> 0 <= entry_at vec w e.
Proof. intros. unfold entry_at. apply little_bound. apply Forall_sublist. auto. Qed.

Lemma decode_from_inr: forall vec w es pre out, Forall byte_ok vec ->
  decode_from vec w es pre = inr out -> Forall addr_ok pre ->
  Zlength out = Zlength pre + Zlength es /\ Forall addr_ok out.
Proof.
  intros vec w es. induction es as [ | e es IH]; intros pre out BV H F.
  - simpl in H. inversion H; subst. rewrite Zlength_nil. split; [ lia | auto ].
  - rewrite decode_from_cons in H. cbv zeta in H.
    destruct ((entry_at vec w e =? 0) || (MAX_U32 <? entry_at vec w e)) eqn:B; [ discriminate | ].
    destruct (existsb _ pre); [ discriminate | ].
    apply IH in H as [L F']; auto.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil in L. rewrite Zlength_cons. split; [ lia | auto ].
    + apply Forall_app; split; auto. constructor; [ | constructor ].
      apply orb_false_iff in B as [B1 B2]. apply Z.eqb_neq in B1. apply Z.ltb_ge in B2.
      unfold addr_ok. pose proof (entry_at_nonneg vec w e BV). lia.
Qed.

(* ---------- splitting arrays at one cell ---------- *)

Lemma split_cell64: forall sh (L: list val) i p, 0 <= i < MAX_ENTRIES -> Zlength L = MAX_ENTRIES ->
  field_compatible (tarray tulong MAX_ENTRIES) [] p ->
  data_at sh (tarray tulong MAX_ENTRIES) L p =
  (data_at sh (tarray tulong i) (sublist 0 i L) p *
   data_at sh tulong (Znth i L) (offset_val (8 * i) p) *
   data_at sh (tarray tulong (MAX_ENTRIES - (i + 1))) (sublist (i + 1) MAX_ENTRIES L) (offset_val (8 * (i + 1)) p))%logic.
Proof.
  intros. unfold MAX_ENTRIES in *.
  assert (H0': @Zlength (reptype tulong) L = 256) by exact H0.
  assert (E: @sublist (reptype tulong) 0 256 L = L) by (apply sublist_same; lia).
  rewrite (split3_data_at_Tarray sh tulong 256 i (i + 1) L L (sublist 0 i L) (sublist i (i + 1) L)
             (sublist (i + 1) 256 L)).
  2: (repeat split; simpl; auto; try reflexivity). 2: lia. 2: (split; [ lia | apply Z.eq_le_incl; symmetry; exact H0 ]).
  2: (symmetry; exact E).
  change (Tarray tulong 256 noattr) with (tarray tulong 256).
  rewrite !arr_field_address0 by (auto; lia). change (sizeof tulong) with 8.
  replace (i + 1 - i) with 1 by lia. rewrite sublist_len_1 by lia.
  change (Tarray tulong 1 noattr) with (tarray tulong 1).
  rewrite (data_at_singleton_array_eq sh tulong (Znth i L) [Znth i L]) by reflexivity.
  reflexivity.
all: reflexivity.
Qed.

Lemma decode_entry_ok: forall vec count w index, index < count -> (w = 4 \/ w = 8) ->
  decode_entry vec count w index =
  (let a := entry_at vec w index in if (a =? 0) || (MAX_U32 <? a) then inl S_ROOT_ENTRY_ADDRESS else inr a).
Proof.
  intros. unfold decode_entry. rewrite (proj2 (Z.leb_gt count index)) by lia.
  destruct H0; subst; reflexivity.
Qed.

Lemma Znth_pre: forall (pre: list Z) a (rest: list val) j, 0 <= j < Zlength pre ->
  Znth j (map vl (pre ++ [a]) ++ rest) = vl (Znth j pre).
Proof.
  intros. rewrite Znth_app1 by (rewrite Zlength_map, Zlength_app, Zlength_cons, Zlength_nil; lia).
  rewrite Znth_map by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia). rewrite Znth_app1 by lia. reflexivity.
Qed.

Lemma Znth_cur: forall (pre: list Z) a (rest: list val), Znth (Zlength pre) (map vl (pre ++ [a]) ++ rest) = vl a.
Proof.
  intros. pose proof (Zlength_nonneg pre). rewrite Znth_app1 by (rewrite Zlength_map, Zlength_app, Zlength_cons, Zlength_nil; lia).
  rewrite Znth_map by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia). rewrite Znth_app2 by lia.
  replace (Zlength pre - Zlength pre) with 0 by lia. reflexivity.
Qed.

Lemma decode_addresses_from: forall vec w count, 0 <= count ->
  decode_addresses vec w count = decode_from vec w (sublist 0 count (range count)) [].
Proof. intros. unfold decode_addresses. rewrite sublist_same by (rewrite ?Zlength_range; lia). reflexivity. Qed.

Lemma ltu64_true: forall a b, u64_ok a -> u64_ok b -> Int64.ltu (Int64.repr a) (Int64.repr b) = true -> a < b.
Proof. intros. rewrite ltu64_repr in H1 by auto. apply Z.ltb_lt; auto. Qed.
Lemma ltu64_false: forall a b, u64_ok a -> u64_ok b -> Int64.ltu (Int64.repr a) (Int64.repr b) = false -> b <= a.
Proof. intros. rewrite ltu64_repr in H1 by auto. apply Z.ltb_ge; auto. Qed.

(* Unsigned 64-bit comparisons the C made, as hypotheses, turned into comparisons of their values. *)
Ltac u64h :=
  repeat match goal with
  | H: Int64.ltu (Int64.repr ?a) (Int64.repr ?b) = true |- _ =>
      apply ltu64_true in H; [ | unfold u64_ok in *; rep_lia | unfold u64_ok in *; rep_lia ]
  | H: Int64.ltu (Int64.repr ?a) (Int64.repr ?b) = false |- _ =>
      apply ltu64_false in H; [ | unfold u64_ok in *; rep_lia | unfold u64_ok in *; rep_lia ]
  end.

Lemma ret_zero: forall r, Int.min_signed <= r <= Int.max_signed -> Int.repr r = Int.zero -> r = 0.
Proof. intros. apply (f_equal Int.signed) in H0. rewrite Int.signed_repr in H0 by auto. exact H0. Qed.

Lemma ret_nonzero: forall r, Int.repr r <> Int.zero -> r <> 0.
Proof. intros r H E. subst. apply H. reflexivity. Qed.

Ltac sconst :=
  repeat match goal with
  | H: context [Int.signed (Int.repr ?c)] |- _ =>
      let v := eval compute in (Int.signed (Int.repr c)) in change (Int.signed (Int.repr c)) with v in H
  | |- context [Int.signed (Int.repr ?c)] =>
      let v := eval compute in (Int.signed (Int.repr c)) in change (Int.signed (Int.repr c)) with v
  end.

Lemma cmpu_ne64: forall a b, u64_ok a -> u64_ok b -> Int64.cmpu Cne (Int64.repr a) (Int64.repr b) = negb (a =? b).
Proof. intros. unfold Int64.cmpu. rewrite eq64_repr by auto. reflexivity. Qed.

Lemma cmpu_le64: forall a b, u64_ok a -> u64_ok b -> Int64.cmpu Cle (Int64.repr a) (Int64.repr b) = (a <=? b).
Proof.
  intros. unfold Int64.cmpu. rewrite ltu64_repr by auto.
  destruct (Z.ltb_spec b a); destruct (Z.leb_spec a b); auto; lia.
Qed.

(* The write-back: byte k of the exposed chunk, (uint8_t)(exposed >> (k * 8u)). *)
Lemma chunk_byte_at: forall l k, Forall byte_ok l -> Zlength l <= 8 -> 0 <= k < Zlength l ->
  Int.zero_ext 8 (Int.repr (Int64.unsigned (Int64.shru (Int64.repr (little l))
                                              (Int64.repr (Int.unsigned (Int.mul (Int.repr k) (Int.repr 8))))))) =
  Int.repr (Znth k l).
Proof.
  intros. rewrite mul_repr, Int.unsigned_repr by rep_lia. rewrite Z.mul_comm. apply chunk_byte; auto.
Qed.

Lemma upd_Znth_same: forall {A} {d: Inhabitant A} (l: list A) i v, 0 <= i < Zlength l -> Znth i l = v ->
  upd_Znth i l v = l.
Proof. intros. subst v. list_solve. Qed.

Lemma zext8_mod_any: forall z, Int.zero_ext 8 (Int.repr z) = Int.repr (z mod 256).
Proof.
  intros. apply Int.same_if_eq. unfold Int.eq.
  rewrite Int.zero_ext_mod by (change Int.zwordsize with 32; lia).
  rewrite Int.unsigned_repr_eq. rewrite (Int.unsigned_repr (z mod 256)) by (pose proof (Z.mod_pos_bound z 256); rep_lia).
  change (two_p 8) with 256.
  rewrite <- (Znumtheory.Zmod_div_mod 256 Int.modulus) by (try rep_lia; apply (Znumtheory.Zdivide_intro 256 Int.modulus 16777216); reflexivity).
  rewrite zeq_true. reflexivity.
Qed.

(* The same, as entailer! leaves it. *)
Lemma wb_byte: forall l i, Forall byte_ok l -> Zlength l <= 8 -> 0 <= i < Zlength l ->
  Int.zero_ext 8 (Int.zero_ext 8 (Int.repr (Int64.Z_mod_modulus (Z.shiftr (Int64.Z_mod_modulus (little l))
                                                                    (Int64.Z_mod_modulus (i * 8)))))) =
  Int.repr (Znth i l).
Proof.
  intros. pose proof (little_u64 l H H0). unfold u64_ok in H2.
  rewrite !Int64.Z_mod_modulus_eq. change Int64.modulus with (Int64.max_unsigned + 1).
  rewrite (Z.mod_small (little l)), (Z.mod_small (i * 8)) by rep_lia.
  assert (0 <= Z.shiftr (little l) (i * 8) <= little l).
  { rewrite Z.shiftr_div_pow2 by lia. split; [ apply Z.div_pos; try lia; apply Z.pow_pos_nonneg; lia | ].
    apply Z.div_le_upper_bound; [ apply Z.pow_pos_nonneg; lia | ].
    assert (1 <= 2 ^ (i * 8)) by (apply Z.pow_le_mono_r with (a := 2) (b := 0) (c := i * 8); lia). nia. }
  rewrite Z.mod_small by rep_lia.
  pose proof (byte_at l i H H1).
  rewrite zext8_mod_any. rewrite zext8_small by (pose proof (Z.mod_pos_bound (Z.shiftr (little l) (i * 8)) 256); lia).
  rewrite Z.mul_comm. rewrite little_byte by auto. reflexivity.
Qed.

Lemma join_cell64: forall sh (pre: list Z) (c: val) (aold: list val) p, Zlength pre < MAX_ENTRIES ->
  Zlength aold = MAX_ENTRIES -> field_compatible (tarray tulong MAX_ENTRIES) [] p ->
  data_at sh (tarray tulong (Zlength pre)) (map vl pre) p *
  data_at sh tulong c (offset_val (8 * Zlength pre) p) *
  data_at sh (tarray tulong (MAX_ENTRIES - (Zlength pre + 1))) (sublist (Zlength pre + 1) MAX_ENTRIES aold)
    (offset_val (8 * (Zlength pre + 1)) p)
  |-- data_at sh (tarray tulong MAX_ENTRIES) (map vl pre ++ [c] ++ sublist (Zlength pre + 1) MAX_ENTRIES aold) p.
Proof.
  intros. pose proof (Zlength_nonneg pre).
  rewrite (split_cell64 sh _ (Zlength pre) p) by (auto; try lia; unfold MAX_ENTRIES in *; list_solve).
  unfold MAX_ENTRIES in *.
  replace (sublist 0 (Zlength pre) (map vl pre ++ [c] ++ sublist (Zlength pre + 1) 256 aold)) with (map vl pre)
    by list_solve.
  replace (Znth (Zlength pre) (map vl pre ++ [c] ++ sublist (Zlength pre + 1) 256 aold)) with c by list_solve.
  replace (sublist (Zlength pre + 1) 256 (map vl pre ++ [c] ++ sublist (Zlength pre + 1) 256 aold))
    with (sublist (Zlength pre + 1) 256 aold) by list_solve.
  apply derives_refl.
Qed.
