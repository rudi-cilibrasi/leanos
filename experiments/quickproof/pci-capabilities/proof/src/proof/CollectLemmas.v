(* Lemmas for the body proofs of boot/pci-capabilities.h (CollectProof.v): pointer tests on maybe_at objects, the
   walk model of Defs.v unfolded one answer at a time in prefix form, the `seen` bitmask of the list loop, and the
   word arithmetic of the C expressions. *)
Require Import VST.floyd.proofauto.
Require Import LeanosCaps.caps.code.
Require Import LeanosCaps.proof.Defs.
Require Import LeanosCaps.proof.CapsSpecs.
#[local] Existing Instance CapsSpecs.CS.
Local Open Scope Z_scope.

(* ---------- NULL tests ---------- *)

Lemma isnull_null: isnull nullval = true.
Proof. unfold isnull. destruct (Val.eq nullval nullval); [ reflexivity | congruence ]. Qed.

Lemma isnull_nonnull: forall p, p <> nullval -> isnull p = false.
Proof. intros. unfold isnull. destruct (Val.eq p nullval); [ congruence | reflexivity ]. Qed.

Lemma isnull_false: forall p, isnull p = false -> p <> nullval.
Proof. intros p H E. subst. rewrite isnull_null in H. discriminate. Qed.

Lemma maybe_valid: forall sh t v p Q, readable_share sh -> sizeof t > 0 ->
  maybe_at sh t v p * Q |-- valid_pointer p.
Proof.
  intros. unfold maybe_at. destruct (Val.eq p nullval).
  - subst. apply valid_pointer_null.
  - apply sepcon_valid_pointer1. apply data_at_valid_ptr; auto.
Qed.

Lemma maybe_read_valid: forall Dev p Q, maybe_read Dev p * Q |-- valid_pointer p.
Proof.
  intros. unfold maybe_read. destruct (Val.eq p nullval).
  - subst. apply valid_pointer_null.
  - apply sepcon_valid_pointer1. apply func_ptr'_valid_pointer.
Qed.

Lemma maybe_at_nonnull: forall sh t v p, p <> nullval -> maybe_at sh t v p = data_at sh t v p.
Proof. intros. unfold maybe_at. destruct (Val.eq p nullval); [ contradiction | reflexivity ]. Qed.

Lemma maybe_at_null: forall sh t v, maybe_at sh t v nullval = emp.
Proof. intros. unfold maybe_at. destruct (Val.eq nullval nullval); [ reflexivity | congruence ]. Qed.

Lemma maybe_read_nonnull: forall Dev p, p <> nullval -> maybe_read Dev p = func_ptr' (read_spec Dev) p.
Proof. intros. unfold maybe_read. destruct (Val.eq p nullval); [ contradiction | reflexivity ]. Qed.

Ltac tc_ptr :=
  match goal with |- _ |-- denote_tc_test_eq ?p _ =>
    apply denote_tc_test_eq_split;
    [ first
      [ match goal with |- context [maybe_at ?sh ?t ?v p] =>
          eapply derives_trans; [ | apply (maybe_valid sh t v p TT); [ auto | simpl; try rewrite Z.max_r by lia; try lia ] ];
          cancel end
      | match goal with |- context [maybe_read ?D p] =>
          eapply derives_trans; [ | apply (maybe_read_valid D p TT) ]; cancel end ]
    | apply valid_pointer_null ]
  end.

Lemma notbool_ptr: forall p, is_pointer_or_null p ->
  force_val (sem_cast_i2bool (force_val (option_map (fun b : bool => bool2val (negb b)) (bool_val_p p)))) =
  Vint (Int.repr (b2z (isnull p))).
Proof.
  intros. destruct p; try contradiction.
  - simpl in H. subst. change (Vlong Int64.zero) with nullval. rewrite isnull_null. reflexivity.
  - rewrite isnull_nonnull by (intro X; inv X). reflexivity.
Qed.

Lemma b2z_true: forall c, Int.repr (b2z c) <> Int.zero -> c = true.
Proof. intros [ | ] H; [ reflexivity | exfalso; apply H; reflexivity ]. Qed.
Lemma b2z_false: forall c, Int.repr (b2z c) = Int.zero -> c = false.
Proof. intros [ | ] H; [ exfalso; apply Int.one_not_zero; exact H | reflexivity ]. Qed.

Ltac bfix :=
  repeat match goal with
  | H: Int.repr (b2z _) <> Int.zero |- _ => apply b2z_true in H
  | H: Int.repr (b2z _) = Int.zero |- _ => apply b2z_false in H
  end.

Lemma orb_false_l': forall a b, a = false -> (a || b)%bool = b.
Proof. intros. subst. reflexivity. Qed.
Lemma orb_true_l': forall a b, a = true -> (a || b)%bool = true.
Proof. intros. subst. reflexivity. Qed.

Ltac orb_l := match goal with
  | H: ?c = true |- context [(?c || _)%bool] => rewrite (orb_true_l' _ _ H)
  | H: ?c = false |- context [(?c || _)%bool] => rewrite (orb_false_l' _ _ H)
  end.

Ltac brw := repeat match goal with
  | H: ?c = true |- context [?c] => lazymatch c with true => fail | false => fail | _ => rewrite H end
  | H: ?c = false |- context [?c] => lazymatch c with true => fail | false => fail | _ => rewrite H end
  end.

Ltac t_then := forward; entailer!; bfix; first [ orb_l; reflexivity | brw; reflexivity ].
Ltac t_ptr := bfix; forward; [ entailer!; tc_ptr | entailer!; rewrite notbool_ptr by auto; orb_l; reflexivity ].

Lemma bool2val_b2z: forall b, bool2val b = Vint (Int.repr (b2z b)).
Proof. intros [ | ]; reflexivity. Qed.

(* ---------- word arithmetic ---------- *)

Lemma land_range: forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  0 <= Z.land a b <= Int.max_unsigned.
Proof.
  intros. split; [ apply Z.land_nonneg; lia | ].
  destruct (Z.eq_dec (Z.land a b) 0) as [E | E]; [ rewrite E; rep_lia | ].
  assert (P: 0 < Z.land a b) by (pose proof (proj2 (Z.land_nonneg a b) (or_introl (proj1 H))); lia).
  destruct (Z.eq_dec b 0) as [B | B]; [ subst; rewrite Z.land_0_r in P; lia | ].
  assert (L: Z.log2 (Z.land a b) <= Z.log2 b) by (pose proof (Z.log2_land a b); lia).
  assert (Lb: Z.log2 b < 32) by (apply Z.log2_lt_pow2; rep_lia).
  assert (Z.land a b < 2 ^ 32) by (apply Z.log2_lt_pow2; lia).
  rep_lia.
Qed.

Lemma repr_eq_iff: forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  (Int.repr a = Int.repr b <-> a = b).
Proof. intros. split; [ apply repr_inj_unsigned; auto | intros; subst; reflexivity ]. Qed.

Lemma and_repr_eq: forall a b m, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  0 <= m <= Int.max_unsigned ->
  (Int.and (Int.repr a) (Int.repr m) = Int.and (Int.repr b) (Int.repr m) <-> Z.land a m = Z.land b m).
Proof.
  intros. rewrite !and_repr. apply repr_eq_iff; apply land_range; auto.
Qed.

Lemma ltu_repr: forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.ltu (Int.repr a) (Int.repr b) = (a <? b).
Proof.
  intros. unfold Int.ltu. rewrite !Int.unsigned_repr by auto.
  destruct (zlt a b); destruct (Z.ltb_spec a b); auto; lia.
Qed.

Lemma eq_repr: forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.eq (Int.repr a) (Int.repr b) = (a =? b).
Proof.
  intros. unfold Int.eq. rewrite !Int.unsigned_repr by auto.
  destruct (zeq a b); destruct (Z.eqb_spec a b); auto; lia.
Qed.

Lemma shiftr_range: forall a n, 0 <= a <= Int.max_unsigned -> 0 <= n -> 0 <= Z.shiftr a n <= Int.max_unsigned.
Proof.
  intros. rewrite Z.shiftr_div_pow2 by lia. split; [ apply Z.div_pos; [ lia | apply Z.pow_pos_nonneg; lia ] | ].
  apply Z.le_trans with a; [ apply Z.div_le_upper_bound; [ apply Z.pow_pos_nonneg; lia | ] | lia ].
  assert (1 <= 2 ^ n) by (apply Z.pow_le_mono_r with (a := 2) (b := 0) (c := n) in H0; [ simpl in H0; lia | lia ]).
  nia.
Qed.

Lemma shru_repr: forall a n, 0 <= a <= Int.max_unsigned -> 0 <= n <= Int.max_unsigned ->
  Int.shru (Int.repr a) (Int.repr n) = Int.repr (Z.shiftr a n).
Proof. intros. unfold Int.shru. rewrite !Int.unsigned_repr by auto. reflexivity. Qed.

Lemma land_ones_eq: forall a k, 0 <= k -> Z.land a (2 ^ k - 1) = a mod 2 ^ k.
Proof. intros. replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia). apply Z.land_ones. auto. Qed.

Lemma land_low_range: forall a k, 0 <= k <= 32 -> 0 <= Z.land a (2 ^ k - 1) < 2 ^ k.
Proof. intros. rewrite land_ones_eq by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. Qed.

Lemma land3_range: forall a, 0 <= Z.land a 3 < 4.
Proof. intros. apply (land_low_range a 2). lia. Qed.
Lemma land127_range: forall a, 0 <= Z.land a 127 < 128.
Proof. intros. apply (land_low_range a 7). lia. Qed.
Lemma land255_range: forall a, 0 <= Z.land a 255 < 256.
Proof. intros. apply (land_low_range a 8). lia. Qed.
Lemma land65535_range: forall a, 0 <= Z.land a 65535 < 65536.
Proof. intros. apply (land_low_range a 16). lia. Qed.

Ltac bdecide :=
  repeat match goal with
  | |- context [?a <=? ?b] => destruct (Z.leb_spec a b)
  | |- context [?a <? ?b] => destruct (Z.ltb_spec a b)
  | |- context [?a =? ?b] => destruct (Z.eqb_spec a b)
  | |- context [zlt ?a ?b] => destruct (zlt a b)
  | |- context [zeq ?a ?b] => destruct (zeq a b)
  end; try lia; reflexivity.

Lemma repr_m1: Int.repr (-1) = Int.repr 4294967295.
Proof.
  transitivity (Int.repr (Int.unsigned (Int.repr (-1)))); [ symmetry; apply Int.repr_unsigned | reflexivity ].
Qed.

Lemma land3_mod: forall x, Z.land x 3 = x mod 4.
Proof. intros. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma aligned_le: forall x, x <= 255 -> Z.land x 3 = 0 -> x <= 252.
Proof. intros. rewrite land3_mod in H0. pose proof (Z_div_mod_eq_full x 4). lia. Qed.

(* ---------- the header reads ---------- *)

Definition hc_off (i: Z) : Z := fst (Znth i header_checks).
Definition hc_mask (i: Z) : Z := snd (Znth i header_checks).

Lemma hc_cases: forall i, 0 <= i < 4 -> i = 0 \/ i = 1 \/ i = 2 \/ i = 3.
Proof. intros. lia. Qed.

Lemma hc_facts: forall i, 0 <= i < 4 ->
  0 <= hc_off i <= 252 /\ Z.land (hc_off i) 3 = 0 /\ 0 <= hc_off i / 4 < 16 /\ 0 <= hc_mask i <= Int.max_unsigned.
Proof. intros. destruct (hc_cases i H) as [ -> | [ -> | [ -> | -> ] ] ]; compute; repeat split; congruence. Qed.

Lemma sublist_hc: forall i, 0 <= i < 4 ->
  sublist i 4 header_checks = (hc_off i, hc_mask i) :: sublist (i + 1) 4 header_checks.
Proof. intros. destruct (hc_cases i H) as [ -> | [ -> | [ -> | -> ] ] ]; reflexivity. Qed.

(* The invariant of the header loop: the reads h answered the first i checks, all passing. *)
Definition hdr_inv (words: list Z) (i: Z) (h: list answer) : Prop :=
  Zlength h = i /\ forall rest, walk words (h ++ rest) = walk_header (sublist i 4 header_checks) words rest.

Lemma hdr_inv_0: forall words, hdr_inv words 0 [].
Proof. intros. split; [ reflexivity | intros; reflexivity ]. Qed.

Lemma hdr_read_failed: forall words i h v, 0 <= i < 4 -> hdr_inv words i h ->
  walk words (h ++ [(hc_off i, false, v)]) = Some (S_READ_FAILED, hc_off i, []).
Proof.
  intros. destruct H0 as [_ H0]. rewrite H0, sublist_hc by auto. cbn [walk_header app]. rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma hdr_changed: forall words i h v, 0 <= i < 4 -> hdr_inv words i h ->
  Z.land v (hc_mask i) <> Z.land (Znth (hc_off i / 4) words) (hc_mask i) ->
  walk words (h ++ [(hc_off i, true, v)]) = Some (S_HEADER_CHANGED, hc_off i, []).
Proof.
  intros. destruct H0 as [_ H0]. rewrite H0, sublist_hc by auto. cbn [walk_header app]. rewrite Z.eqb_refl.
  apply Z.eqb_neq in H1. rewrite H1. reflexivity.
Qed.

Lemma hdr_pass: forall words i h v, 0 <= i < 4 -> hdr_inv words i h ->
  Z.land v (hc_mask i) = Z.land (Znth (hc_off i / 4) words) (hc_mask i) ->
  hdr_inv words (i + 1) (h ++ [(hc_off i, true, v)]).
Proof.
  intros. destruct H0 as [L H0]. split; [ rewrite Zlength_app, Zlength_cons, Zlength_nil; lia | ].
  intros. rewrite <- app_assoc. cbn [app]. rewrite H0, sublist_hc by auto. cbn [walk_header]. rewrite Z.eqb_refl.
  apply Z.eqb_eq in H1. rewrite H1. reflexivity.
Qed.

(* ---------- the list loop ---------- *)

(* The invariant of the list loop: the reads h brought the walk to pointer next with the headers acc (latest first). *)
Definition chain_inv (words: list Z) (h: list answer) (next count: Z) (acc: list (Z * Z)) : Prop :=
  forall rest, walk words (h ++ rest) = walk_chain (Z.to_nat (50 - count)) next count (map fst acc) acc rest.

Lemma chain_inv_start: forall words h, hdr_inv words 4 h -> chain_inv words h (list_head words) 0 [].
Proof. intros. destruct H as [_ H]. intro. rewrite H. reflexivity. Qed.

Lemma fuel_succ: forall count, 0 <= count <= 48 -> Z.to_nat (50 - count) = S (Z.to_nat (50 - (count + 1))).
Proof. intros. rewrite <- Z2Nat.inj_succ by lia. f_equal. lia. Qed.

Lemma chain_unfold: forall count next seen acc ans, 0 <= count <= 48 ->
  walk_chain (Z.to_nat (50 - count)) next count seen acc ans =
  if next =? 0 then final (S_OK, 0, rev acc) ans
  else if ((next <? 64) || negb (Z.land next 3 =? 0))%bool then final (S_POINTER, next, nil) ans
  else if existsb (Z.eqb next) seen then final (S_CYCLE, next, nil) ans
  else if count =? 48 then final (S_POINTER, next, nil) ans
  else match ans with
       | (o, ok, v) :: rest =>
         if negb (o =? next) then None
         else if negb ok then final (S_READ_FAILED, next, nil) rest
         else if Z.land v 255 =? 255 then final (S_ABSENT, next, nil) rest
         else walk_chain (Z.to_nat (50 - (count + 1))) (Z.land (Z.shiftr v 8) 255) (count + 1) (next :: seen)
                ((next, v) :: acc) rest
       | nil => None
       end.
Proof. intros. rewrite fuel_succ by auto. reflexivity. Qed.

Lemma chain_ok: forall words h count acc, 0 <= count <= 48 -> chain_inv words h 0 count acc ->
  walk words h = Some (S_OK, 0, rev acc).
Proof. intros. rewrite <- (app_nil_r h), H0, chain_unfold by auto. reflexivity. Qed.

Definition bad_ptr (next: Z) : bool := ((next <? 64) || negb (Z.land next 3 =? 0))%bool.

Lemma chain_pointer: forall words h next count acc, 0 <= count <= 48 -> chain_inv words h next count acc ->
  next <> 0 -> bad_ptr next = true -> walk words h = Some (S_POINTER, next, []).
Proof.
  intros. unfold bad_ptr in H2. rewrite <- (app_nil_r h), H0, chain_unfold by auto.
  apply Z.eqb_neq in H1. rewrite H1, H2. reflexivity.
Qed.

Lemma chain_cycle: forall words h next count acc, 0 <= count <= 48 -> chain_inv words h next count acc ->
  next <> 0 -> bad_ptr next = false -> existsb (Z.eqb next) (map fst acc) = true ->
  walk words h = Some (S_CYCLE, next, []).
Proof.
  intros. unfold bad_ptr in H2. rewrite <- (app_nil_r h), H0, chain_unfold by auto.
  apply Z.eqb_neq in H1. rewrite H1, H2, H3. reflexivity.
Qed.

Lemma chain_full: forall words h next acc, chain_inv words h next 48 acc ->
  next <> 0 -> bad_ptr next = false -> existsb (Z.eqb next) (map fst acc) = false ->
  walk words h = Some (S_POINTER, next, []).
Proof.
  intros. unfold bad_ptr in H1. rewrite <- (app_nil_r h), H, chain_unfold by lia.
  apply Z.eqb_neq in H0. rewrite H0, H1, H2. reflexivity.
Qed.

Lemma chain_read_failed: forall words h next count acc v, 0 <= count < 48 -> chain_inv words h next count acc ->
  next <> 0 -> bad_ptr next = false -> existsb (Z.eqb next) (map fst acc) = false ->
  walk words (h ++ [(next, false, v)]) = Some (S_READ_FAILED, next, []).
Proof.
  intros. unfold bad_ptr in H2. rewrite H0, chain_unfold by lia.
  apply Z.eqb_neq in H1. rewrite H1, H2, H3. rewrite (proj2 (Z.eqb_neq count 48)) by lia.
  rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma chain_absent: forall words h next count acc v, 0 <= count < 48 -> chain_inv words h next count acc ->
  next <> 0 -> bad_ptr next = false -> existsb (Z.eqb next) (map fst acc) = false -> Z.land v 255 = 255 ->
  walk words (h ++ [(next, true, v)]) = Some (S_ABSENT, next, []).
Proof.
  intros. unfold bad_ptr in H2. rewrite H0, chain_unfold by lia.
  apply Z.eqb_neq in H1. rewrite H1, H2, H3. rewrite (proj2 (Z.eqb_neq count 48)) by lia.
  rewrite Z.eqb_refl, H4. reflexivity.
Qed.

Lemma chain_step: forall words h next count acc v, 0 <= count < 48 -> chain_inv words h next count acc ->
  next <> 0 -> bad_ptr next = false -> existsb (Z.eqb next) (map fst acc) = false -> Z.land v 255 <> 255 ->
  chain_inv words (h ++ [(next, true, v)]) (Z.land (Z.shiftr v 8) 255) (count + 1) ((next, v) :: acc).
Proof.
  intros. unfold bad_ptr in H2. intro rest. rewrite <- app_assoc. cbn [app]. rewrite H0, chain_unfold by lia.
  apply Z.eqb_neq in H1. rewrite H1, H2, H3. rewrite (proj2 (Z.eqb_neq count 48)) by lia.
  rewrite Z.eqb_refl. apply Z.eqb_neq in H4. rewrite H4. reflexivity.
Qed.

(* ---------- the seen bitmask ---------- *)

Definition bitidx (x: Z) : Z := (x - 64) / 4.
Definition voff (x: Z) : Prop := 64 <= x <= 252 /\ Z.land x 3 = 0.

(* Bit k of sv is set exactly when some offset of seen maps to bit k. *)
Definition seen_rep (sv: int64) (seen: list Z) : Prop :=
  forall k, 0 <= k < 64 -> Int64.testbit sv k = existsb (fun s => bitidx s =? k) seen.

Lemma voff_bitidx: forall x, voff x -> 0 <= bitidx x < 48.
Proof.
  unfold voff, bitidx. intros x [H1 H2]. split; [ apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia ].
Qed.

Lemma bitidx_inj: forall x y, voff x -> voff y -> bitidx x = bitidx y -> x = y.
Proof.
  unfold voff, bitidx. intros x y [Hx Ax] [Hy Ay] E. rewrite land3_mod in Ax, Ay.
  pose proof (Z_div_mod_eq_full x 4). pose proof (Z_div_mod_eq_full y 4).
  assert (Ex: (x - 64) / 4 = x / 4 - 16).
  { replace (x - 64) with (x / 4 * 4 + (-16) * 4) by lia. rewrite Z.div_add by lia.
    rewrite Z.div_mul by lia. lia. }
  assert (Ey: (y - 64) / 4 = y / 4 - 16).
  { replace (y - 64) with (y / 4 * 4 + (-16) * 4) by lia. rewrite Z.div_add by lia.
    rewrite Z.div_mul by lia. lia. }
  lia.
Qed.

Lemma seen_rep_nil: seen_rep (Int64.repr 0) [].
Proof. intros k Hk. apply Int64.bits_zero. Qed.

Lemma seen_rep_cons: forall sv seen x, seen_rep sv seen -> voff x ->
  seen_rep (Int64.or sv (Int64.shl (Int64.repr 1) (Int64.repr (bitidx x)))) (x :: seen).
Proof.
  intros sv seen x H Vx k Hk. pose proof (voff_bitidx x Vx).
  change Int64.zwordsize with 64 in *.
  rewrite Int64.bits_or by (change Int64.zwordsize with 64; lia).
  rewrite Int64.bits_shl by (change Int64.zwordsize with 64; lia).
  rewrite Int64.unsigned_repr by rep_lia. rewrite H by auto. simpl existsb.
  destruct (zlt k (bitidx x)).
  - rewrite (proj2 (Z.eqb_neq (bitidx x) k)) by lia. rewrite orb_false_r. reflexivity.
  - change (Int64.repr 1) with Int64.one. rewrite Int64.bits_one.
    destruct (zeq (k - bitidx x) 0).
    + rewrite (proj2 (Z.eqb_eq (bitidx x) k)) by lia. rewrite orb_true_r. reflexivity.
    + rewrite (proj2 (Z.eqb_neq (bitidx x) k)) by lia. rewrite orb_false_r. reflexivity.
Qed.

Lemma seen_test: forall sv seen k, seen_rep sv seen -> 0 <= k < 64 ->
  (Int64.and sv (Int64.shl (Int64.repr 1) (Int64.repr k)) = Int64.zero <->
   existsb (fun s => bitidx s =? k) seen = false).
Proof.
  intros sv seen k H Hk. rewrite <- H by auto. split.
  - intros E. assert (B := f_equal (fun z => Int64.testbit z k) E). simpl in B.
    rewrite Int64.bits_zero, Int64.bits_and, Int64.bits_shl in B by (change Int64.zwordsize with 64; lia).
    rewrite Int64.unsigned_repr in B by rep_lia.
    destruct (zlt k k); [ lia | ]. change (Int64.repr 1) with Int64.one in B. rewrite Int64.bits_one in B.
    destruct (zeq (k - k) 0); [ | lia ]. rewrite andb_true_r in B. exact B.
  - intros T. apply Int64.same_bits_eq. intros i Hi.
    rewrite Int64.bits_zero, Int64.bits_and, Int64.bits_shl by auto.
    rewrite Int64.unsigned_repr by rep_lia.
    destruct (zlt i k); [ apply andb_false_r | ].
    change (Int64.repr 1) with Int64.one. rewrite Int64.bits_one.
    destruct (zeq (i - k) 0); [ | apply andb_false_r ].
    assert (i = k) by lia. subst i. rewrite T. reflexivity.
Qed.

Lemma existsb_bitidx: forall seen x, Forall voff seen -> voff x ->
  existsb (fun s => bitidx s =? bitidx x) seen = existsb (Z.eqb x) seen.
Proof.
  induction seen as [ | s seen IH]; intros x F Vx; [ reflexivity | ].
  inv F. simpl. rewrite IH by auto. f_equal.
  destruct (Z.eqb_spec (bitidx s) (bitidx x)) as [E | E]; destruct (Z.eqb_spec x s) as [E' | E']; auto.
  - exfalso. apply E'. symmetry. apply bitidx_inj; auto.
  - subst. contradiction.
Qed.

(* ---------- the snapshot's headers ---------- *)

Definition hdrs (acc: list (Z * Z)) (hs0: list (reptype t_cap)) : list (reptype t_cap) :=
  map cap_val (rev acc) ++ sublist (Zlength acc) 48 hs0.

Lemma Zlength_hdrs: forall acc hs0, Zlength hs0 = 48 -> Zlength acc <= 48 -> Zlength (hdrs acc hs0) = 48.
Proof.
  intros. unfold hdrs. rewrite Zlength_app, Zlength_map, Zlength_rev, Zlength_sublist by (try list_solve; lia).
  lia.
Qed.

Lemma hdrs_nil: forall hs0, Zlength hs0 = 48 -> hdrs [] hs0 = hs0.
Proof. intros. unfold hdrs. simpl. rewrite sublist_same by (auto; lia). reflexivity. Qed.

Lemma hdrs_upd: forall acc hs0 x, Zlength hs0 = 48 -> Zlength acc < 48 ->
  upd_Znth (Zlength acc) (hdrs acc hs0) (cap_val x) = hdrs (x :: acc) hs0.
Proof.
  intros. pose proof (Zlength_nonneg acc). unfold hdrs.
  rewrite upd_Znth_app2 by (rewrite Zlength_map, Zlength_rev, Zlength_sublist by lia; lia).
  rewrite Zlength_map, Zlength_rev, Z.sub_diag.
  rewrite (sublist_next (Zlength acc) 48 hs0) by lia. rewrite upd_Znth0.
  simpl rev. rewrite map_app, <- app_assoc. simpl. rewrite Zlength_cons. reflexivity.
Qed.

Lemma value_fits_snapshot: forall v, value_fits t_snapshot v -> Zlength (snd v) = 48.
Proof.
  intros v H. rewrite value_fits_eq in H. simpl in H. destruct H as [_ H].
  rewrite value_fits_eq in H. simpl in H. destruct H as [H _]. rewrite ?Z.max_r in H by lia. exact H.
Qed.

Lemma args_disj: forall dev fn words,
  (negb (dev <=? 31) || negb (fn <=? 7) || negb (Z.land (Z.shiftr (Znth 3 words) 16) 127 <=? 1) ||
   (Z.land (Znth 0 words) 65535 =? 65535))%bool = negb (args_ok dev fn words).
Proof.
  intros. unfold args_ok.
  destruct (dev <=? 31), (fn <=? 7), (Z.land (Z.shiftr (Znth 3 words) 16) 127 <=? 1),
    (Z.land (Znth 0 words) 65535 =? 65535); reflexivity.
Qed.

(* ---------- facts used by the list loop ---------- *)

Lemma zext8_small: forall x, 0 <= x <= 255 -> Int.zero_ext 8 (Int.repr x) = Int.repr x.
Proof.
  intros. rewrite Int.zero_ext_and by lia. change (two_p 8 - 1) with (2 ^ 8 - 1).
  rewrite and_repr, land_ones_eq by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma zext8_land: forall x, Int.zero_ext 8 (Int.repr x) = Int.repr (Z.land x 255).
Proof. intros. rewrite Int.zero_ext_and by lia. change (two_p 8 - 1) with 255. apply and_repr. Qed.

Lemma list_head_range: forall words, 0 <= list_head words <= 255.
Proof.
  intros. unfold list_head. destruct (_ =? 0); [ lia | pose proof (land255_range (Znth 13 words)); lia ].
Qed.

Lemma bad_ptr_voff: forall next, 0 <= next <= 255 -> bad_ptr next = false -> voff next.
Proof.
  unfold bad_ptr, voff. intros next R H. apply orb_false_iff in H. destruct H as [A B].
  apply Z.ltb_ge in A. apply negb_false_iff, Z.eqb_eq in B.
  split; [ split; [ lia | apply aligned_le; auto; lia ] | auto ].
Qed.

Lemma bit_divs: forall next, 64 <= next <= 255 ->
  Int.divs (Int.repr (next - 64)) (Int.repr 4) = Int.repr (bitidx next).
Proof.
  intros. unfold Int.divs, bitidx. rewrite !Int.signed_repr by rep_lia.
  rewrite Z.quot_div_nonneg by lia. reflexivity.
Qed.

Lemma bit_unsigned: forall next, voff next ->
  Int.unsigned (Int.divs (Int.sub (Int.repr next) (Int.repr 64)) (Int.repr 4)) = bitidx next.
Proof.
  intros next V. pose proof (voff_bitidx next V). destruct V as [V1 V2].
  rewrite sub_repr, bit_divs by lia. rewrite Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma bit_range: forall next, 64 <= next <= 255 -> 0 <= (next - 64) / 4 < 64.
Proof. intros. split; [ apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia ]. Qed.

Lemma seen_hit: forall sv (acc: list (Z * Z)) next, seen_rep sv (map fst acc) -> Forall voff (map fst acc) -> voff next ->
  Int64.and sv (Int64.shl (Int64.repr 1) (Int64.repr (bitidx next))) <> Int64.zero ->
  existsb (Z.eqb next) (map fst acc) = true.
Proof.
  intros. pose proof (voff_bitidx next H1). rewrite <- existsb_bitidx by auto.
  destruct (existsb _ _) eqn:E; auto. exfalso. apply H2.
  apply (proj2 (seen_test sv (map fst acc) (bitidx next) H ltac:(lia))). exact E.
Qed.

Lemma seen_miss: forall sv (acc: list (Z * Z)) next, seen_rep sv (map fst acc) -> Forall voff (map fst acc) -> voff next ->
  Int64.and sv (Int64.shl (Int64.repr 1) (Int64.repr (bitidx next))) = Int64.zero ->
  existsb (Z.eqb next) (map fst acc) = false.
Proof.
  intros. pose proof (voff_bitidx next H1). rewrite <- existsb_bitidx by auto.
  exact (proj1 (seen_test sv (map fst acc) (bitidx next) H ltac:(lia)) H2).
Qed.

Lemma hdrs_store: forall acc hs0 next v, Zlength hs0 = 48 -> Zlength acc < 48 ->
  upd_Znth (Zlength acc)
    (upd_Znth (Zlength acc) (hdrs acc hs0) (Vint (Int.repr next), snd (Znth (Zlength acc) (hdrs acc hs0))))
    (fst (Znth (Zlength acc)
            (upd_Znth (Zlength acc) (hdrs acc hs0) (Vint (Int.repr next), snd (Znth (Zlength acc) (hdrs acc hs0))))),
     Vint (Int.repr v))
  = hdrs ((next, v) :: acc) hs0.
Proof.
  intros. pose proof (Zlength_nonneg acc). pose proof (Zlength_hdrs acc hs0 H ltac:(lia)).
  rewrite upd_Znth_twice by lia. rewrite upd_Znth_same by lia. cbn [fst].
  change (Vint (Int.repr next), Vint (Int.repr v)) with (cap_val (next, v)).
  apply hdrs_upd; auto.
Qed.

Lemma next_ptr: forall v, 0 <= v <= Int.max_unsigned ->
  Int.zero_ext 8 (Int.zero_ext 8 (Int.shru (Int.repr v) (Int.repr 8))) = Int.repr (Z.land (Z.shiftr v 8) 255).
Proof.
  intros. rewrite Int.zero_ext_idem by lia. rewrite shru_repr by rep_lia. apply zext8_land.
Qed.

Lemma and255_eq: forall v, 0 <= v <= Int.max_unsigned ->
  (Int.and (Int.repr v) (Int.repr 255) = Int.repr 255 <-> Z.land v 255 = 255).
Proof.
  intros. rewrite and_repr. pose proof (land255_range v). apply repr_eq_iff; rep_lia.
Qed.

Lemma typed_true_uchar: forall x, typed_true tuchar (Vint (Int.repr x)) -> x <> 0.
Proof. intros x H E. subst x. compute in H. discriminate. Qed.

Lemma typed_false_uchar: forall x, 0 <= x <= 255 -> typed_false tuchar (Vint (Int.repr x)) -> x = 0.
Proof.
  intros x R H. unfold typed_false, strict_bool_val in H. simpl in H.
  destruct (Int.eq (Int.repr x) Int.zero) eqn:E; [ | discriminate ].
  apply Int.same_if_eq in E. apply (f_equal Int.unsigned) in E. rewrite Int.unsigned_repr in E by rep_lia.
  exact E.
Qed.
