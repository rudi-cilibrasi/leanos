(* Lemmas for the body proof of qotom_build_copy_roots (BuildProof.v): pointer tests on maybe_at objects, word
   arithmetic of the leaf and alias computations, and the list facts behind the loop invariants. *)
Require Import VST.floyd.proofauto.
Require Import LeanosRoots.roots.code.
Require Import LeanosRoots.proof.Defs.
Require Import LeanosRoots.proof.RootsSpecs.
#[local] Existing Instance RootsSpecs.CS.
Local Open Scope Z_scope.

(* ---------- NULL tests ---------- *)

Definition isnull (p: val) : bool := if Val.eq p nullval then true else false.

Lemma isnull_null: isnull nullval = true.
Proof. unfold isnull. destruct (Val.eq nullval nullval); [ reflexivity | congruence ]. Qed.

Lemma isnull_nonnull: forall p, p <> nullval -> isnull p = false.
Proof. intros. unfold isnull. destruct (Val.eq p nullval); [ congruence | reflexivity ]. Qed.

Lemma isnull_false: forall p, isnull p = false -> p <> nullval.
Proof. intros p H E. subst. rewrite isnull_null in H. discriminate. Qed.

Lemma notbool_val: forall t p, is_pointer_or_null p ->
  (t = t_root \/ t = tulong \/ t = t_alias \/ t = t_result) ->
  force_val (sem_cast tint tbool (eval_unop Onotbool (tptr t) p)) = Vint (Int.repr (b2z (isnull p))).
Proof.
  intros t p H T. destruct p; try contradiction.
  - simpl in H. subst. change (Vlong Int64.zero) with nullval. rewrite isnull_null.
    destruct T as [ -> | [ -> | [ -> | -> ] ] ]; reflexivity.
  - rewrite isnull_nonnull by (intro X; inv X).
    destruct T as [ -> | [ -> | [ -> | -> ] ] ]; reflexivity.
Qed.

Lemma notbool_ptr: forall p, is_pointer_or_null p ->
  force_val (sem_cast_i2bool (force_val (option_map (fun b : bool => bool2val (negb b)) (bool_val_p p)))) =
  Vint (Int.repr (b2z (isnull p))).
Proof.
  intros. destruct p; try contradiction.
  - simpl in H. subst. change (Vlong Int64.zero) with nullval. rewrite isnull_null. reflexivity.
  - rewrite isnull_nonnull by (intro X; inv X). reflexivity.
Qed.

Lemma maybe_valid: forall sh t v p Q, readable_share sh -> sizeof t > 0 ->
  maybe_at sh t v p * Q |-- valid_pointer p.
Proof.
  intros. unfold maybe_at. destruct (Val.eq p nullval).
  - subst. apply valid_pointer_null.
  - apply sepcon_valid_pointer1. apply data_at_valid_ptr; auto.
Qed.

Lemma maybe_at_nonnull: forall sh t v p, p <> nullval -> maybe_at sh t v p = data_at sh t v p.
Proof. intros. unfold maybe_at. destruct (Val.eq p nullval); [ contradiction | reflexivity ]. Qed.

Ltac tc_ptr :=
  match goal with |- _ |-- denote_tc_test_eq ?p _ =>
    match goal with |- context [maybe_at ?sh ?t ?v p] =>
      apply denote_tc_test_eq_split;
      [ eapply derives_trans; [ | apply (maybe_valid sh t v p TT); [ auto | simpl; try rewrite Z.max_r by lia; try lia ] ];
        cancel
      | apply valid_pointer_null ]
    end end.

Lemma b2z_orb: forall a b, Vint (Int.repr (b2z (a || b))) =
  (if a then Vint (Int.repr 1) else Vint (Int.repr (b2z b))).
Proof. destruct a, b; reflexivity. Qed.

Lemma b2z_true: forall c, Int.repr (b2z c) <> Int.zero -> c = true.
Proof. intros [ | ] H; [ reflexivity | exfalso; apply H; reflexivity ]. Qed.
Lemma b2z_false: forall c, Int.repr (b2z c) = Int.zero -> c = false.
Proof. intros [ | ] H; [ exfalso; apply Int.one_not_zero; exact H | reflexivity ]. Qed.

Ltac bfix :=
  repeat match goal with
  | H: Int.repr (b2z _) <> Int.zero |- _ => apply b2z_true in H
  | H: Int.repr (b2z _) = Int.zero |- _ => apply b2z_false in H
  end.

Lemma notbool_b2z: forall c,
  force_val (sem_cast tint tbool (eval_unop Onotbool tint (Vint (Int.repr (b2z c))))) =
  Vint (Int.repr (b2z (negb c))).
Proof. intros [ | ]; reflexivity. Qed.

Lemma orb_false_l': forall a b, a = false -> (a || b)%bool = b.
Proof. intros. subst. reflexivity. Qed.
Lemma orb_true_l': forall a b, a = true -> (a || b)%bool = true.
Proof. intros. subst. reflexivity. Qed.

Lemma phys_fail: forall source closed copy frames aliases result src sp kp cp fs n al m,
  (isnull source || isnull closed || isnull copy || isnull frames || isnull aliases || isnull result ||
   negb (phys_ok sp) || negb (phys_ok kp) || negb (phys_ok cp) || negb (disjoint sp kp) ||
   negb (disjoint sp cp) || negb (disjoint kp cp))%bool = true ->
  ~ (source <> nullval /\ closed <> nullval /\ copy <> nullval /\ frames <> nullval /\
     aliases <> nullval /\ result <> nullval /\ build_ok src sp kp cp fs n al m = true).
Proof.
  intros until m. intros H (A1 & A2 & A3 & A4 & A5 & A6 & B).
  rewrite !isnull_nonnull in H by assumption. unfold build_ok in B.
  destruct (phys_ok sp), (phys_ok kp), (phys_ok cp), (disjoint sp kp), (disjoint sp cp), (disjoint kp cp);
    simpl in *; discriminate.
Qed.

Lemma phys_pass: forall source closed copy frames aliases result sp kp cp,
  (isnull source || isnull closed || isnull copy || isnull frames || isnull aliases || isnull result ||
   negb (phys_ok sp) || negb (phys_ok kp) || negb (phys_ok cp) || negb (disjoint sp kp) ||
   negb (disjoint sp cp) || negb (disjoint kp cp))%bool = false ->
  source <> nullval /\ closed <> nullval /\ copy <> nullval /\ frames <> nullval /\
  aliases <> nullval /\ result <> nullval /\
  (phys_ok sp && phys_ok kp && phys_ok cp && disjoint sp kp && disjoint sp cp && disjoint kp cp)%bool = true.
Proof.
  intros. repeat rewrite orb_false_iff in H.
  destruct H as (((((((((((B1 & B2) & B3) & B4) & B5) & B6) & B7) & B8) & B9) & B10) & B11) & B12).
  apply negb_false_iff in B7, B8, B9, B10, B11, B12.
  rewrite B7, B8, B9, B10, B11, B12.
  repeat split; try reflexivity; apply isnull_false; assumption.
Qed.

Lemma build_anc_false: forall src sp kp cp fs n al m,
  ancestors_ok src sp = false -> build_ok src sp kp cp fs n al m = false.
Proof. intros. unfold build_ok. rewrite H. rewrite andb_false_r. reflexivity. Qed.
Lemma build_inv_false: forall src sp kp cp fs n al m,
  inventory_ok fs n = false -> build_ok src sp kp cp fs n al m = false.
Proof. intros. unfold build_ok. rewrite H. rewrite andb_false_r. reflexivity. Qed.
Lemma build_al_false: forall src sp kp cp fs n al m,
  aliases_ok src (sublist 0 n fs) al m = false -> build_ok src sp kp cp fs n al m = false.
Proof. intros. unfold build_ok. rewrite H. rewrite andb_false_r. reflexivity. Qed.
Ltac iff_fail L := split; [ intro; lia | intros (_ & _ & _ & _ & _ & _ & B); rewrite L in B; discriminate ].

Lemma repr64_eq: forall a b, word_ok a -> word_ok b -> Int64.repr a = Int64.repr b -> a = b.
Proof. unfold word_ok. intros. apply repr_inj_unsigned64; auto. Qed.
Lemma repr64_neq: forall a b, Int64.repr a <> Int64.repr b -> a <> b.
Proof. intros a b H E. subst. contradiction. Qed.
Ltac l64 := repeat match goal with
 | H: Int64.repr ?a = Int64.zero |- _ => change Int64.zero with (Int64.repr 0) in H
 | H: Int64.repr ?a <> Int64.zero |- _ => change Int64.zero with (Int64.repr 0) in H
 | H: Int64.repr ?a = Int64.repr ?b |- _ =>
     apply repr64_eq in H; [ | unfold word_ok in *; rep_lia | unfold word_ok in *; rep_lia ]
 | H: Int64.repr ?a <> Int64.repr ?b |- _ => apply repr64_neq in H
 end.

Lemma cmpu_z: forall c a b, word_ok a -> word_ok b ->
  Int64.cmpu c (Int64.repr a) (Int64.repr b) =
  match c with Ceq => a =? b | Cne => negb (a =? b) | Clt => a <? b | Cle => a <=? b
             | Cgt => b <? a | Cge => b <=? a end.
Proof.
  unfold word_ok. intros. unfold Int64.cmpu, Int64.ltu, Int64.eq.
  rewrite !Int64.unsigned_repr by lia.
  destruct c;
   [ destruct (zeq a b); destruct (Z.eqb_spec a b)
   | destruct (zeq a b); destruct (Z.eqb_spec a b)
   | destruct (zlt a b); destruct (Z.ltb_spec a b)
   | destruct (zlt b a); destruct (Z.leb_spec a b)
   | destruct (zlt b a); destruct (Z.ltb_spec b a)
   | destruct (zlt a b); destruct (Z.leb_spec b a) ]; simpl; try reflexivity; lia.
Qed.
Lemma bool2val_b2z: forall b, bool2val b = Vint (Int.repr (b2z b)).
Proof. intros [ | ]; reflexivity. Qed.

Lemma inv_count_false: forall fs n, ((n =? 0) || (16 <? n))%bool = true -> word_ok n -> inventory_ok fs n = false.
Proof.
  unfold word_ok. intros. unfold inventory_ok.
  apply orb_prop in H. destruct H as [H | H]; [ apply Z.eqb_eq in H | apply Z.ltb_lt in H ].
  - subst. reflexivity.
  - rewrite (proj2 (Z.leb_gt n 16)) by lia. rewrite andb_false_r. reflexivity.
Qed.
Lemma count_ok: forall n, ((n =? 0) || (16 <? n))%bool = false -> word_ok n -> 1 <= n <= 16.
Proof.
  unfold word_ok. intros. apply orb_false_iff in H. destruct H as [H1 H2].
  apply Z.eqb_neq in H1. apply Z.ltb_ge in H2. lia.
Qed.

(* ---------- lists ---------- *)

Lemma Zlength_longs: forall l, Zlength (longs l) = Zlength l.
Proof. intros. unfold longs. apply Zlength_map. Qed.

Lemma Znth_longs: forall i l, 0 <= i < Zlength l -> Znth i (longs l) = Vlong (Int64.repr (Znth i l)).
Proof. intros. unfold longs. rewrite Znth_map by lia. reflexivity. Qed.

Lemma longs_app: forall a b, longs (a ++ b) = longs a ++ longs b.
Proof. intros. unfold longs. apply map_app. Qed.

Lemma sublist_snoc: forall {A} {d: Inhabitant A} (l: list A) i, 0 <= i < Zlength l ->
  sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l].
Proof. intros. rewrite (sublist_split 0 i (i + 1)) by lia. rewrite sublist_len_1 by lia. reflexivity. Qed.

Lemma member_app: forall x a b, member x (a ++ b) = (member x a || member x b)%bool.
Proof. intros. unfold member. apply existsb_app. Qed.

Lemma member_one: forall x y, member x [y] = (x =? y).
Proof. intros. unfold member. simpl. apply orb_false_r. Qed.

Lemma distinct_snoc: forall l x, distinct (l ++ [x]) = (distinct l && negb (member x l))%bool.
Proof.
  induction l as [ | a l IH ]; intros; simpl.
  - reflexivity.
  - rewrite IH, member_app, member_one. rewrite (Z.eqb_sym a x).
    destruct (member a l), (x =? a), (distinct l), (member x l); reflexivity.
Qed.

Lemma distinct_app_l: forall a b, distinct (a ++ b) = true -> distinct a = true.
Proof.
  induction a as [ | x a IH ]; intros; simpl in *; [ reflexivity | ].
  rewrite member_app in H. apply andb_prop in H. destruct H as [H1 H2].
  rewrite (IH b H2). destruct (member x a); simpl in *; [ discriminate | reflexivity ].
Qed.

Lemma forallb_app_l: forall {A} (f: A -> bool) a b, forallb f (a ++ b) = true -> forallb f a = true.
Proof. intros. rewrite forallb_app in H. apply andb_prop in H. tauto. Qed.

Lemma member_In: forall x l, member x l = true <-> In x l.
Proof.
  intros. unfold member. rewrite existsb_exists. split.
  - intros (y & Hy & E). apply Z.eqb_eq in E. subst. exact Hy.
  - intros H. exists x. split; [ exact H | apply Z.eqb_refl ].
Qed.

Lemma member_sublist_Znth: forall l j i, 0 <= j < i -> i <= Zlength l ->
  member (Znth j l) (sublist 0 i l) = true.
Proof.
  intros. apply member_In.
  replace (Znth j l) with (Znth j (sublist 0 i l)) by (rewrite Znth_sublist by lia; f_equal; lia).
  apply Znth_In. rewrite Zlength_sublist by lia. lia.
Qed.

(* A repeated element at j < i < n makes the first n elements not distinct. *)
Lemma distinct_dup: forall l j i n, 0 <= j < i -> i < n -> n <= Zlength l -> Znth j l = Znth i l ->
  distinct (sublist 0 n l) = false.
Proof.
  intros. destruct (distinct (sublist 0 n l)) eqn:D; [ exfalso | reflexivity ].
  rewrite (sublist_split 0 (i + 1) n) in D by lia. apply distinct_app_l in D.
  rewrite sublist_snoc in D by lia. rewrite distinct_snoc in D.
  rewrite <- H2 in D. rewrite member_sublist_Znth in D by lia.
  rewrite andb_false_r in D. discriminate.
Qed.

(* An element at i < n failing f makes forallb f fail on the first n. *)
Lemma forallb_fail: forall {A} {d: Inhabitant A} (f: A -> bool) (l: list A) i n, 0 <= i < n -> n <= Zlength l ->
  f (Znth i l) = false -> forallb f (sublist 0 n l) = false.
Proof.
  intros. destruct (forallb f (sublist 0 n l)) eqn:F; [ exfalso | reflexivity ].
  rewrite forallb_forall in F.
  assert (IN: In (Znth i l) (sublist 0 n l)).
  { replace (Znth i l) with (Znth i (sublist 0 n l)) by (rewrite Znth_sublist by lia; f_equal; lia).
    apply Znth_In. rewrite Zlength_sublist by lia. lia. }
  specialize (F _ IN). congruence.
Qed.

Lemma forallb_snoc_sub: forall {A} {d: Inhabitant A} (f: A -> bool) (l: list A) i, 0 <= i < Zlength l ->
  forallb f (sublist 0 (i + 1) l) = (forallb f (sublist 0 i l) && f (Znth i l))%bool.
Proof. intros. rewrite sublist_snoc by lia. rewrite forallb_app. simpl. rewrite andb_true_r. reflexivity. Qed.

Lemma distinct_snoc_sub: forall l i, 0 <= i < Zlength l ->
  distinct (sublist 0 (i + 1) l) = (distinct (sublist 0 i l) && negb (member (Znth i l) (sublist 0 i l)))%bool.
Proof. intros. rewrite sublist_snoc by lia. apply distinct_snoc. Qed.

Lemma member_snoc_sub: forall x l j, 0 <= j < Zlength l ->
  member x (sublist 0 (j + 1) l) = (member x (sublist 0 j l) || (x =? Znth j l))%bool.
Proof. intros. rewrite sublist_snoc by lia. rewrite member_app, member_one. reflexivity. Qed.

(* The local copy of a prefix: storing element i extends it. *)
Lemma upd_prefix: forall (l: list Z) i k, 0 <= i < Zlength l -> i < k ->
  upd_Znth i (longs (sublist 0 i l) ++ Zrepeat Vundef (k - i)) (Vlong (Int64.repr (Znth i l))) =
  longs (sublist 0 (i + 1) l) ++ Zrepeat Vundef (k - (i + 1)).
Proof.
  intros. rewrite sublist_snoc by lia. rewrite longs_app. unfold longs at 2. simpl map.
  rewrite upd_Znth_app2 by (rewrite Zlength_longs, Zlength_sublist by lia; list_solve).
  rewrite Zlength_longs, Zlength_sublist by lia.
  replace (i - (i - 0)) with 0 by lia.
  replace (k - i) with (1 + (k - (i + 1))) by lia.
  rewrite <- Zrepeat_app by lia. rewrite upd_Znth_app1 by (rewrite Zlength_Zrepeat; lia).
  rewrite <- app_assoc. f_equal.
Qed.

Lemma Znth_prefix: forall (l: list Z) i j k, 0 <= j < i -> i <= Zlength l -> i <= k ->
  Znth j (longs (sublist 0 i l) ++ Zrepeat Vundef (k - i)) = Vlong (Int64.repr (Znth j l)).
Proof.
  intros. rewrite Znth_app1 by (rewrite Zlength_longs, Zlength_sublist by lia; lia).
  rewrite Znth_longs by (rewrite Zlength_sublist by lia; lia). rewrite Znth_sublist by lia.
  do 3 f_equal. lia.
Qed.

(* ---------- the inventory and alias tests ---------- *)

#[export] Instance Inhabitant_alias : Inhabitant alias := mkalias 0 0 0.

Lemma inv_big_false: forall fs n i, 0 <= i < n -> n <= Zlength fs -> 2 ^ 40 <= Znth i fs ->
  inventory_ok fs n = false.
Proof.
  intros. unfold inventory_ok.
  rewrite (forallb_fail (fun f => f <? 2 ^ 40) fs i n) by (auto; apply Z.ltb_ge; lia).
  rewrite andb_false_r. reflexivity.
Qed.

Lemma inv_dup_false: forall fs n i j, 0 <= j < i -> i < n -> n <= Zlength fs -> Znth i fs = Znth j fs ->
  inventory_ok fs n = false.
Proof.
  intros. unfold inventory_ok. rewrite (distinct_dup fs j i n) by auto. apply andb_false_r.
Qed.

Lemma inv_ok: forall fs n, 1 <= n <= 16 -> forallb (fun f => f <? 2 ^ 40) (sublist 0 n fs) = true ->
  distinct (sublist 0 n fs) = true -> inventory_ok fs n = true.
Proof.
  intros. unfold inventory_ok. rewrite H0, H1.
  rewrite (proj2 (Z.leb_le 1 n)), (proj2 (Z.leb_le n 16)) by lia. reflexivity.
Qed.

Lemma al_count_false: forall src inv al m, ((m =? 0) || (2 <? m))%bool = true -> word_ok m ->
  aliases_ok src inv al m = false.
Proof.
  unfold word_ok. intros. unfold aliases_ok.
  apply orb_prop in H. destruct H as [H | H]; [ apply Z.eqb_eq in H | apply Z.ltb_lt in H ].
  - subst. reflexivity.
  - rewrite (proj2 (Z.leb_gt m 2)) by lia. rewrite andb_false_r. reflexivity.
Qed.

Lemma al_count_ok: forall m, ((m =? 0) || (2 <? m))%bool = false -> word_ok m -> 1 <= m <= 2.
Proof.
  unfold word_ok. intros. apply orb_false_iff in H. destruct H as [H1 H2].
  apply Z.eqb_neq in H1. apply Z.ltb_ge in H2. lia.
Qed.

Lemma al_bad_false: forall src inv al m i, 0 <= i < m -> m <= Zlength al ->
  alias_ok src inv (Znth i al) = false -> aliases_ok src inv al m = false.
Proof.
  intros. unfold aliases_ok. rewrite (forallb_fail (alias_ok src inv) al i m) by auto.
  rewrite !andb_false_r. reflexivity.
Qed.

Lemma al_dup_page_false: forall src inv al m i j, 0 <= j < i -> i < m -> m <= Zlength al ->
  a_page (Znth i al) = a_page (Znth j al) -> aliases_ok src inv al m = false.
Proof.
  intros. unfold aliases_ok. rewrite <- sublist_map.
  rewrite (distinct_dup (map a_page al) j i m) by (rewrite ?Zlength_map, ?Znth_map by lia; auto).
  rewrite andb_false_r. reflexivity.
Qed.

Lemma al_dup_frame_false: forall src inv al m i j, 0 <= j < i -> i < m -> m <= Zlength al ->
  a_frame (Znth i al) = a_frame (Znth j al) -> aliases_ok src inv al m = false.
Proof.
  intros. unfold aliases_ok. rewrite <- (sublist_map a_frame).
  rewrite (distinct_dup (map a_frame al) j i m) by (rewrite ?Zlength_map, ?Znth_map by lia; auto).
  apply andb_false_r.
Qed.

Lemma al_ok: forall src inv al m, 1 <= m <= 2 -> forallb (alias_ok src inv) (sublist 0 m al) = true ->
  distinct (map a_page (sublist 0 m al)) = true -> distinct (map a_frame (sublist 0 m al)) = true ->
  aliases_ok src inv al m = true.
Proof.
  intros. unfold aliases_ok. rewrite H0, H1, H2.
  rewrite (proj2 (Z.leb_le 1 m)), (proj2 (Z.leb_le m 2)) by lia. reflexivity.
Qed.

Lemma build_true: forall src sp kp cp fs n al m,
  (phys_ok sp && phys_ok kp && phys_ok cp && disjoint sp kp && disjoint sp cp && disjoint kp cp)%bool = true ->
  ancestors_ok src sp = true -> inventory_ok fs n = true -> aliases_ok src (sublist 0 n fs) al m = true ->
  build_ok src sp kp cp fs n al m = true.
Proof. intros. unfold build_ok. rewrite H, H0, H1, H2. reflexivity. Qed.

Lemma map_snoc_sub: forall {A B} {d: Inhabitant A} (f: A -> B) (l: list A) i, 0 <= i < Zlength l ->
  map f (sublist 0 (i + 1) l) = map f (sublist 0 i l) ++ [f (Znth i l)].
Proof. intros. rewrite sublist_snoc by lia. rewrite map_app. reflexivity. Qed.

(* ---------- word arithmetic ---------- *)

Lemma lor_small: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  0 <= Z.lor a b <= Int64.max_unsigned.
Proof.
  intros. assert (L: forall x, 0 <= x <= Int64.max_unsigned -> x = 0 \/ (0 < x /\ Z.log2 x < 64)).
  { intros x Hx. destruct (Z.eq_dec x 0); [ left; auto | right; split; [ lia | ] ].
    apply Z.log2_lt_pow2; [ lia | ]. change (2 ^ 64) with (Int64.max_unsigned + 1). lia. }
  split; [ apply Z.lor_nonneg; lia | ].
  destruct (Z.eq_dec (Z.lor a b) 0) as [E | E]; [ rewrite E; rep_lia | ].
  assert (Z.lor a b < 2 ^ 64); [ | change (2 ^ 64) with (Int64.max_unsigned + 1) in *; lia ].
  apply Z.log2_lt_pow2; [ pose proof (Z.lor_nonneg a b); lia | ].
  rewrite Z.log2_lor by lia.
  destruct (L a H) as [ -> | [ _ La ] ]; destruct (L b H0) as [ -> | [ _ Lb ] ]; simpl; lia.
Qed.

Lemma or_repr: forall x y, 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.or (Int64.repr x) (Int64.repr y) = Int64.repr (Z.lor x y).
Proof. intros. unfold Int64.or. rewrite !Int64.unsigned_repr by lia. reflexivity. Qed.

Lemma alias_leaf_range: forall a, 0 <= alias_leaf a <= Int64.max_unsigned.
Proof.
  intros. unfold alias_leaf.
  assert (M: 0 <= (a_frame a * 4096) mod W <= Int64.max_unsigned).
  { pose proof (Z.mod_pos_bound (a_frame a * 4096) W ltac:(unfold W; rep_lia)). unfold W in *. rep_lia. }
  repeat apply lor_small; try assumption; try (destruct (a_writable a =? 0)); unfold NX; rep_lia.
Qed.

Lemma alias_leaf_int: forall a, word_ok (a_frame a) ->
  Int64.or (Int64.or (Int64.or (Int64.shl (Int64.repr (a_frame a)) (Int64.repr 12)) (Int64.repr 1))
                     (Int64.shl (Int64.repr 1) (Int64.repr 63)))
           (Int64.repr (if a_writable a =? 0 then 0 else 2)) = Int64.repr (alias_leaf a).
Proof.
  unfold word_ok. intros.
  assert (S1: Int64.shl (Int64.repr (a_frame a)) (Int64.repr 12) = Int64.repr ((a_frame a * 4096) mod W)).
  { unfold Int64.shl. rewrite (Int64.unsigned_repr (a_frame a)) by lia. rewrite (Int64.unsigned_repr 12) by rep_lia.
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 12) with 4096.
    rewrite <- (Int64.repr_unsigned (Int64.repr (a_frame a * 4096))), Int64.unsigned_repr_eq. reflexivity. }
  assert (S2: Int64.shl (Int64.repr 1) (Int64.repr 63) = Int64.repr NX) by reflexivity.
  assert (M: 0 <= (a_frame a * 4096) mod W <= Int64.max_unsigned).
  { pose proof (Z.mod_pos_bound (a_frame a * 4096) W ltac:(unfold W; rep_lia)). unfold W in *. rep_lia. }
  rewrite S1, S2. unfold alias_leaf.
  rewrite or_repr by (auto; rep_lia).
  rewrite or_repr by (try apply lor_small; auto; unfold NX; rep_lia).
  rewrite or_repr by (repeat apply lor_small; auto; try (destruct (a_writable a =? 0)); unfold NX; rep_lia).
  reflexivity.
Qed.

Lemma and1_int: forall s, word_ok s ->
  Int64.and (Int64.repr s) (Int64.repr 1) = Int64.repr (if Z.odd s then 1 else 0).
Proof.
  unfold word_ok. intros. unfold Int64.and. rewrite !Int64.unsigned_repr by rep_lia.
  change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
  rewrite Zmod_odd. reflexivity.
Qed.

Lemma land_mask_range: forall s, word_ok s -> 0 <= Z.land s ADDRESS_MASK <= Int64.max_unsigned.
Proof.
  unfold word_ok. intros. split; [ apply Z.land_nonneg; lia | ].
  destruct (Z.eq_dec (Z.land s ADDRESS_MASK) 0) as [E | E]; [ rewrite E; rep_lia | ].
  assert (Z.land s ADDRESS_MASK < 2 ^ 64); [ | change (2 ^ 64) with (Int64.max_unsigned + 1) in *; lia ].
  assert (0 <= Z.land s ADDRESS_MASK) by (apply Z.land_nonneg; lia).
  apply Z.log2_lt_pow2; [ lia | ].
  pose proof (Z.log2_land s ADDRESS_MASK ltac:(lia) ltac:(unfold ADDRESS_MASK; lia)).
  assert (Z.log2 ADDRESS_MASK = 51) by reflexivity. lia.
Qed.

Lemma frame_of_int: forall s, word_ok s ->
  Int64.shru (Int64.and (Int64.repr s) (Int64.repr ADDRESS_MASK)) (Int64.repr 12) = Int64.repr (frame_of s).
Proof.
  intros. pose proof (land_mask_range s H). unfold word_ok in H.
  unfold Int64.shru, Int64.and. rewrite (Int64.unsigned_repr s) by lia.
  rewrite (Int64.unsigned_repr ADDRESS_MASK) by (unfold ADDRESS_MASK; rep_lia).
  rewrite Int64.unsigned_repr by lia. rewrite (Int64.unsigned_repr 12) by rep_lia. reflexivity.
Qed.

Lemma frame_of_range: forall s, word_ok s -> word_ok (frame_of s).
Proof.
  intros. pose proof (land_mask_range s H). unfold word_ok, frame_of.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 12) with 4096. split.
  - apply Z.div_pos; lia.
  - apply Z.le_trans with (Z.land s ADDRESS_MASK); [ | lia ]. apply Z.div_le_upper_bound; lia.
Qed.

(* ---------- what the builder writes ---------- *)

Lemma longs_Zrepeat: forall x n, longs (Zrepeat x n) = Zrepeat (Vlong (Int64.repr x)) n.
Proof. intros. unfold longs, Zrepeat. induction (Z.to_nat n); simpl; congruence. Qed.

Lemma longs_upd: forall i l x, upd_Znth i (longs l) (Vlong (Int64.repr x)) = longs (upd_Znth i l x).
Proof. intros. unfold longs. apply (upd_Znth_map (fun x => Vlong (Int64.repr x))). Qed.

Lemma zero_step: forall (k: list val) z i, Zlength k = 512 -> 0 <= i < 512 ->
  upd_Znth i (Zrepeat z i ++ sublist i 512 k) z = Zrepeat z (i + 1) ++ sublist (i + 1) 512 k.
Proof. intros. list_solve. Qed.

Lemma zero_start: forall (k: list val) z, Zlength k = 512 -> Zrepeat z 0 ++ sublist 0 512 k = k.
Proof. intros. list_solve. Qed.

Lemma zero_end: forall (k: list val) z, Zlength k = 512 -> Zrepeat z 512 ++ sublist 512 512 k = Zrepeat z 512.
Proof. intros. list_solve. Qed.

Lemma Zlength_idx: forall n, 0 <= n -> Zlength (idx n) = n.
Proof. intros. unfold idx. rewrite Zlength_map, Zlength_correct, length_seq. apply Z2Nat.id. lia. Qed.

Lemma Znth_idx: forall n j, 0 <= j < n -> Znth j (idx n) = j.
Proof.
  intros. unfold idx. rewrite Znth_map by (rewrite Zlength_correct, length_seq; lia).
  unfold Znth. destruct (zlt j 0); [ lia | ]. destruct (Z_lt_dec j 0); [ lia | ]. rewrite seq_nth by lia. lia.
Qed.

Definition pd_part (phys i: Z) : list Z := map (fun j => if j <? i then table_entry phys (3 + j) else 0) (idx 512).

Lemma pd_part_0: forall phys, longs (pd_part phys 0) = Zrepeat (Vlong (Int64.repr 0)) 512.
Proof.
  intros. apply Znth_eq_ext.
  - rewrite Zlength_longs, Zlength_Zrepeat by lia. unfold pd_part. rewrite Zlength_map, Zlength_idx; lia.
  - intros j Hj. rewrite Zlength_longs in Hj. unfold pd_part in *. rewrite Zlength_map, Zlength_idx in Hj by lia.
    rewrite Znth_Zrepeat by lia. rewrite Znth_longs by (rewrite Zlength_map, Zlength_idx; lia).
    rewrite Znth_map by (rewrite Zlength_idx; lia). rewrite Znth_idx by lia.
    rewrite (proj2 (Z.ltb_ge j 0)) by lia. reflexivity.
Qed.

Lemma pd_part_step: forall phys i, 0 <= i < 512 ->
  upd_Znth i (longs (pd_part phys i)) (Vlong (Int64.repr (table_entry phys (3 + i)))) = longs (pd_part phys (i + 1)).
Proof.
  intros. rewrite longs_upd. f_equal. unfold pd_part.
  assert (LI: Zlength (idx 512) = 512) by (apply Zlength_idx; lia).
  apply Znth_eq_ext.
  - rewrite Zlength_upd_Znth, !Zlength_map. reflexivity.
  - intros j Hj. rewrite Zlength_upd_Znth, Zlength_map, LI in Hj.
    rewrite (Znth_map j) by lia. rewrite Znth_idx by lia.
    destruct (Z.eq_dec j i) as [ -> | Ne ].
    + rewrite upd_Znth_same by (rewrite Zlength_map; lia). rewrite (proj2 (Z.ltb_lt i (i + 1))) by lia. reflexivity.
    + rewrite upd_Znth_diff by (rewrite ?Zlength_map; lia). rewrite Znth_map by lia. rewrite Znth_idx by lia.
      destruct (Z.ltb_spec j i), (Z.ltb_spec j (i + 1)); try reflexivity; lia.
Qed.

Lemma pd_part_8: forall phys, pd_part phys 8 = map (pd_entry phys) (idx 512).
Proof. reflexivity. Qed.

Lemma table0: forall x, upd_Znth 0 (Zrepeat (Vlong (Int64.repr 0)) 512) (Vlong (Int64.repr x)) =
  longs (upd_Znth 0 (Zrepeat 0 512) x).
Proof. intros. rewrite <- longs_upd, longs_Zrepeat. reflexivity. Qed.

(* The leaf loop: the first p leaves are written, the rest still hold the old words. *)
Lemma leaf_step: forall (g: Z -> Z) (l: list Z) (k: list val) p, Zlength l = 4096 -> Zlength k = 4096 -> 0 <= p < 4096 ->
  upd_Znth p (longs (map g (sublist 0 p l)) ++ sublist p 4096 k) (Vlong (Int64.repr (g (Znth p l)))) =
  longs (map g (sublist 0 (p + 1) l)) ++ sublist (p + 1) 4096 k.
Proof.
  intros. rewrite map_snoc_sub by lia. rewrite longs_app. unfold longs at 2. simpl map.
  rewrite upd_Znth_app2 by (rewrite Zlength_longs, Zlength_map, Zlength_sublist by lia; list_solve).
  rewrite Zlength_longs, Zlength_map, Zlength_sublist by lia. replace (p - (p - 0)) with 0 by lia.
  rewrite (sublist_split p (p + 1) 4096) by lia. rewrite (sublist_len_1 p) by lia. simpl app.
  rewrite upd_Znth0. rewrite <- app_assoc. reflexivity.
Qed.

Lemma leaf_start: forall (g: Z -> Z) (l: list Z) (k: list val), Zlength k = 4096 ->
  longs (map g (sublist 0 0 l)) ++ sublist 0 4096 k = k.
Proof. intros. rewrite sublist_nil. simpl. rewrite sublist_same by lia. reflexivity. Qed.

Lemma leaf_end: forall (g: Z -> Z) (l: list Z) (k: list val), Zlength l = 4096 ->
  longs (map g (sublist 0 4096 l)) ++ sublist 4096 4096 k = longs (map g l).
Proof. intros. rewrite sublist_nil, app_nil_r. rewrite sublist_same by lia. reflexivity. Qed.

Lemma Zlength_filter_le: forall {A} (f: A -> bool) l, 0 <= Zlength (filter f l) <= Zlength l.
Proof.
  induction l as [ | x l IH ]; simpl; [ rewrite Zlength_nil; lia | ].
  rewrite Zlength_cons. destruct (f x); [ rewrite Zlength_cons | ]; lia.
Qed.

Lemma removed_step: forall inv l p, 0 <= p < Zlength l ->
  removed_count inv (sublist 0 (p + 1) l) = removed_count inv (sublist 0 p l) + (if removes inv (Znth p l) then 1 else 0).
Proof.
  intros. unfold removed_count. rewrite sublist_snoc by lia. rewrite filter_app, Zlength_app. simpl.
  destruct (removes inv (Znth p l)); reflexivity.
Qed.

Lemma retained_step: forall inv l p, 0 <= p < Zlength l ->
  retained_count inv (sublist 0 (p + 1) l) =
  retained_count inv (sublist 0 p l) + (if (Z.odd (Znth p l) && negb (member (frame_of (Znth p l)) inv))%bool then 1 else 0).
Proof.
  intros. unfold retained_count. rewrite sublist_snoc by lia. rewrite filter_app, Zlength_app. simpl.
  destruct (Z.odd (Znth p l) && negb (member (frame_of (Znth p l)) inv))%bool; reflexivity.
Qed.

Lemma removed_range: forall inv l p, 0 <= p <= Zlength l -> 0 <= removed_count inv (sublist 0 p l) <= p.
Proof.
  intros. unfold removed_count. pose proof (Zlength_filter_le (removes inv) (sublist 0 p l)).
  rewrite Zlength_sublist in H0 by lia. lia.
Qed.

Lemma retained_range: forall inv l p, 0 <= p <= Zlength l -> 0 <= retained_count inv (sublist 0 p l) <= p.
Proof.
  intros. unfold retained_count.
  pose proof (Zlength_filter_le (fun s => Z.odd s && negb (member (frame_of s) inv))%bool (sublist 0 p l)).
  rewrite Zlength_sublist in H0 by lia. lia.
Qed.

Lemma install_snoc: forall l a base, install (l ++ [a]) base = upd_Znth (a_page a) (install l base) (alias_leaf a).
Proof. induction l as [ | b l IH ]; intros; simpl; [ reflexivity | apply IH ]. Qed.

Lemma Zlength_install: forall l base, Zlength (install l base) = Zlength base.
Proof. induction l as [ | b l IH ]; intros; simpl; [ reflexivity | rewrite IH; apply Zlength_upd_Znth ]. Qed.

Lemma eq_z: forall a b, word_ok a -> word_ok b -> Int64.eq (Int64.repr a) (Int64.repr b) = (a =? b).
Proof. intros. exact (cmpu_z Ceq a b H H0). Qed.

Lemma word_Znth: forall l i, words_ok l -> word_ok (Znth i l).
Proof.
  intros. destruct (zlt i 0); [ rewrite Znth_underflow by lia; unfold word_ok; cbv [default Inhabitant_Z]; rep_lia | ].
  destruct (zlt i (Zlength l)); [ apply Forall_Znth; auto; lia | ].
  rewrite Znth_overflow by lia. unfold word_ok; cbv [default Inhabitant_Z]; rep_lia.
Qed.
Lemma alias_ok_split: forall src inv a, alias_ok src inv a =
  (negb ((4096 <=? a_page a) || (1 <? a_writable a) || negb (Znth (a_page a) (pt src) =? 0)) &&
   member (a_frame a) inv)%bool.
Proof.
  intros. unfold alias_ok, LEAVES.
  destruct (Z.ltb_spec (a_page a) 4096), (Z.leb_spec 4096 (a_page a)); try lia;
  destruct (Z.leb_spec (a_writable a) 1), (Z.ltb_spec 1 (a_writable a)); try lia;
  destruct (Znth (a_page a) (pt src) =? 0), (member (a_frame a) inv); reflexivity.
Qed.

Lemma sub_sub: forall {A} (l: list A) n, 0 <= n <= Zlength l -> sublist 0 n (sublist 0 n l) = sublist 0 n l.
Proof. intros. rewrite sublist_same; auto. rewrite Zlength_sublist by lia. lia. Qed.

Lemma retype16: forall sh (l: list Z) k v, Zlength l = k -> 0 <= k <= 16 ->
  data_at sh (tarray tulong 16) (longs l ++ Zrepeat Vundef (16 - k)) v =
  data_at sh (tarray tulong (Zlength l + Zlength (Zrepeat Vundef (16 - k)))) (longs l ++ Zrepeat Vundef (16 - k)) v.
Proof. intros. rewrite Zlength_Zrepeat by lia. replace (Zlength l + (16 - k)) with 16 by lia. reflexivity. Qed.

Lemma root_pt: forall r, (let (_, y) := let (_, y) := let (_, y) := root_val r in y in y in y) = longs (pt r).
Proof. reflexivity. Qed.

Lemma upd_prefix_map: forall (f: alias -> Z) al i k, 0 <= i < Zlength al -> i < k ->
  upd_Znth i (longs (sublist 0 i (map f al)) ++ Zrepeat Vundef (k - i)) (Vlong (Int64.repr (f (Znth i al)))) =
  longs (sublist 0 (i + 1) (map f al)) ++ Zrepeat Vundef (k - (i + 1)).
Proof. intros. rewrite <- (Znth_map i f) by lia. apply upd_prefix; [ rewrite Zlength_map | ]; lia. Qed.

Lemma Znth_prefix_map: forall (f: alias -> Z) al i j k, 0 <= j < i -> i <= Zlength al -> i <= k ->
  Znth j (longs (sublist 0 i (map f al)) ++ Zrepeat Vundef (k - i)) = Vlong (Int64.repr (f (Znth j al))).
Proof. intros. rewrite Znth_prefix by (rewrite ?Zlength_map; lia). rewrite Znth_map by lia. reflexivity. Qed.

Lemma al_ok': forall src inv al m, 1 <= m <= 2 -> m <= Zlength al ->
  forallb (alias_ok src inv) (sublist 0 m al) = true ->
  distinct (sublist 0 m (map a_page al)) = true -> distinct (sublist 0 m (map a_frame al)) = true ->
  aliases_ok src inv al m = true.
Proof. intros. apply al_ok; auto; rewrite <- sublist_map; auto. Qed.

Lemma forallb_Znth_sub: forall {A} {d: Inhabitant A} (f: A -> bool) (l: list A) i m, 0 <= i < m -> m <= Zlength l ->
  forallb f (sublist 0 m l) = true -> f (Znth i l) = true.
Proof.
  intros. destruct (f (Znth i l)) eqn:F; [ reflexivity | ].
  rewrite (forallb_fail f l i m) in H1 by auto. discriminate.
Qed.

Lemma alias_ok_page: forall src inv a, alias_ok src inv a = true -> a_page a < 4096.
Proof.
  intros. unfold alias_ok in H. apply andb_prop in H. destruct H as [H _]. apply andb_prop in H. destruct H as [H _].
  apply andb_prop in H. destruct H as [H _]. apply Z.ltb_lt in H. exact H.
Qed.

Lemma install_step: forall al base i, 0 <= i < Zlength al ->
  upd_Znth (a_page (Znth i al)) (longs (install (sublist 0 i al) base)) (Vlong (Int64.repr (alias_leaf (Znth i al)))) =
  longs (install (sublist 0 (i + 1) al) base).
Proof. intros. rewrite longs_upd. rewrite sublist_snoc by lia. rewrite install_snoc. reflexivity. Qed.

Lemma install_start: forall al base, install (sublist 0 0 al) base = base.
Proof. intros. rewrite sublist_nil. reflexivity. Qed.

Lemma root_val_eq: forall r, root_val r = (longs (pml4 r), (longs (pdpt r), (longs (pd r), longs (pt r)))).
Proof. reflexivity. Qed.

Lemma root_fields: forall sh (a b c d: list val) p,
  data_at sh t_root (a, (b, (c, d))) p =
  sepcon (field_at sh t_root (DOT _pml4) a p) (sepcon (field_at sh t_root (DOT _pdpt) b p)
    (sepcon (field_at sh t_root (DOT _pd) c p) (field_at sh t_root (DOT _pt) d p))).
Proof. intros. unfold_data_at (data_at _ _ _ _). reflexivity. Qed.

Lemma result_fields: forall sh (a b c d: val) p,
  data_at sh t_result (a, (b, (c, d))) p =
  sepcon (field_at sh t_result (DOT _protected_count) a p) (sepcon (field_at sh t_result (DOT _removed_aliases) b p)
    (sepcon (field_at sh t_result (DOT _retained_present) c p) (field_at sh t_result (DOT _alias_count) d p))).
Proof. intros. unfold_data_at (data_at _ _ _ _). reflexivity. Qed.
