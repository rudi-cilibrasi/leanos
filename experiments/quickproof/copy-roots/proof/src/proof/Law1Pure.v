(* Law copy_roots_exact: pure lemmas connecting the harness's C restatements (tables_at, inventory_ok,
   aliases_ok, the per-page leaf loop, the counts) to Defs.v. *)
Require Import VST.floyd.proofauto.
Require Import LeanosRoots.proof.Defs.
Require Import LeanosRoots.proof.RootsSpecs.
Require Import LeanosRoots.proof.Law1Specs.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 64-bit words                                                            *)
(* ---------------------------------------------------------------------- *)

Lemma eq_repr: forall a b, word_ok a -> word_ok b -> Int64.eq (Int64.repr a) (Int64.repr b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold word_ok in *. unfold Int64.eq. rewrite !Int64.unsigned_repr by lia.
  destruct (zeq a b); destruct (Z.eqb_spec a b); congruence.
Qed.

Lemma ltu_repr: forall a b, word_ok a -> word_ok b -> Int64.ltu (Int64.repr a) (Int64.repr b) = (a <? b).
Proof.
  intros a b Ha Hb. unfold word_ok in *. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt a b); destruct (Z.ltb_spec a b); first [ reflexivity | exfalso; lia ].
Qed.

Lemma word_testbit: forall x n, word_ok x -> 64 <= n -> Z.testbit x n = false.
Proof.
  intros x n Hx Hn. unfold word_ok in Hx. change Int64.max_unsigned with (2 ^ 64 - 1) in Hx.
  rewrite <- (Z.mod_small x (2 ^ 64)) by lia. apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma word_of_bits: forall x, 0 <= x -> (forall n, 64 <= n -> Z.testbit x n = false) -> word_ok x.
Proof.
  intros x Hx Hb. unfold word_ok. change Int64.max_unsigned with (2 ^ 64 - 1).
  assert (E: x = x mod 2 ^ 64).
  { apply Z.bits_inj'. intros n Hn. destruct (zlt n 64).
    - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
    - rewrite Z.mod_pow2_bits_high by lia. apply Hb. lia. }
  rewrite E. pose proof (Z.mod_pos_bound x (2 ^ 64) ltac:(lia)). lia.
Qed.

Lemma land_word: forall x y, word_ok x -> word_ok (Z.land x y).
Proof.
  intros x y Hx. apply word_of_bits.
  - apply Z.land_nonneg. left. unfold word_ok in Hx. lia.
  - intros n Hn. rewrite Z.land_spec, (word_testbit x n Hx Hn). reflexivity.
Qed.

Lemma lor_word: forall x y, word_ok x -> word_ok y -> word_ok (Z.lor x y).
Proof.
  intros x y Hx Hy. apply word_of_bits.
  - apply Z.lor_nonneg. unfold word_ok in *. lia.
  - intros n Hn. rewrite Z.lor_spec, (word_testbit x n Hx Hn), (word_testbit y n Hy Hn). reflexivity.
Qed.

Lemma mod_word: forall x, word_ok (x mod W).
Proof.
  intros x. unfold word_ok, W. pose proof (Z.mod_pos_bound x Int64.modulus ltac:(rep_lia)). rep_lia.
Qed.

Lemma and_not_repr: forall x ig,
  Int64.and (Int64.repr x) (Int64.not (Int64.repr ig)) = Int64.repr (Z.land x (Z.lnot ig)).
Proof.
  intros x ig. apply Int64.same_bits_eq. intros i Hi.
  rewrite Int64.bits_and by lia. rewrite Int64.bits_not by lia. rewrite !Int64.testbit_repr by lia.
  rewrite Z.land_spec, Z.lnot_spec by lia. reflexivity.
Qed.

Lemma and_repr: forall x y, Int64.and (Int64.repr x) (Int64.repr y) = Int64.repr (Z.land x y).
Proof.
  intros x y. apply Int64.same_bits_eq. intros i Hi.
  rewrite Int64.bits_and by lia. rewrite !Int64.testbit_repr by lia. rewrite Z.land_spec. reflexivity.
Qed.

Lemma or_repr: forall x y, Int64.or (Int64.repr x) (Int64.repr y) = Int64.repr (Z.lor x y).
Proof.
  intros x y. apply Int64.same_bits_eq. intros i Hi.
  rewrite Int64.bits_or by lia. rewrite !Int64.testbit_repr by lia. rewrite Z.lor_spec. reflexivity.
Qed.

Lemma land_1: forall s, Z.land s 1 = if Z.odd s then 1 else 0.
Proof. intros s. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. apply Zmod_odd. Qed.

Lemma table_entry_word: forall phys k, word_ok (table_entry phys k).
Proof.
  intros. unfold table_entry. apply lor_word; [ apply mod_word | unfold word_ok; rep_lia ].
Qed.

Lemma alias_leaf_word: forall a, word_ok (alias_leaf a).
Proof.
  intros. unfold alias_leaf, NX.
  repeat apply lor_word; first [ apply mod_word | unfold word_ok; rep_lia | destruct (_ =? _); unfold word_ok; rep_lia ].
Qed.

(* ---------------------------------------------------------------------- *)
(* Lists                                                                   *)
(* ---------------------------------------------------------------------- *)

Lemma Zlength_idx: forall n, 0 <= n -> Zlength (idx n) = n.
Proof.
  intros n Hn. unfold idx. rewrite Zlength_map, Zlength_correct, seq_length. lia.
Qed.

Lemma Znth_idx: forall n j, 0 <= j < n -> Znth j (idx n) = j.
Proof.
  intros n j Hj. unfold idx. rewrite Znth_map by (rewrite Zlength_correct, seq_length; lia).
  rewrite <- nth_Znth by (rewrite Zlength_correct, seq_length; lia).
  rewrite seq_nth by lia. lia.
Qed.

Lemma forallb_idx: forall f n, 0 <= n -> (forallb f (idx n) = true <-> forall j, 0 <= j < n -> f j = true).
Proof.
  intros f n Hn. unfold idx. rewrite forallb_forall. split.
  - intros H j Hj. apply H. apply in_map_iff. exists (Z.to_nat j). split; [ apply Z2Nat.id; lia | ].
    apply in_seq. lia.
  - intros H x Hx. apply in_map_iff in Hx. destruct Hx as (k & <- & Hk). apply in_seq in Hk. apply H. lia.
Qed.

Lemma forallb_idx1: forall f, forallb f (map (Z.add 1) (idx 511)) = true <-> forall j, 1 <= j < 512 -> f j = true.
Proof.
  intros f. rewrite forallb_forall. split.
  - intros H j Hj. apply H. apply in_map_iff. exists (j - 1). split; [ lia | ].
    unfold idx. apply in_map_iff. exists (Z.to_nat (j - 1)). split; [ apply Z2Nat.id; lia | ].
    apply in_seq. lia.
  - intros H x Hx. apply in_map_iff in Hx. destruct Hx as (y & <- & Hy).
    unfold idx in Hy. apply in_map_iff in Hy. destruct Hy as (k & <- & Hk). apply in_seq in Hk. apply H. lia.
Qed.

Lemma member_Znth: forall f l, member f l = true <-> exists i, 0 <= i < Zlength l /\ Znth i l = f.
Proof.
  intros f l. unfold member. rewrite existsb_exists. split.
  - intros (x & Hin & Heq). apply Z.eqb_eq in Heq. subst x. apply In_Znth in Hin.
    destruct Hin as (i & Hi & E). exists i. split; auto.
  - intros (i & Hi & E). exists (Znth i l). split; [ apply Znth_In; auto | apply Z.eqb_eq; auto ].
Qed.

Lemma member_false: forall f l, member f l = false <-> forall i, 0 <= i < Zlength l -> Znth i l <> f.
Proof.
  intros f l. split.
  - intros H i Hi E. assert (member f l = true) by (apply member_Znth; eauto). congruence.
  - intros H. destruct (member f l) eqn:M; auto. apply member_Znth in M. destruct M as (i & Hi & E).
    exfalso. exact (H i Hi E).
Qed.

Lemma distinct_Znth: forall l, distinct l = true <->
  forall i j, 0 <= i -> i < j -> j < Zlength l -> Znth i l <> Znth j l.
Proof.
  induction l as [ | x t IH ]; simpl.
  - split; auto. intros _ i j H1 H2 H3. rewrite Zlength_nil in H3. lia.
  - rewrite andb_true_iff, negb_true_iff, IH. split.
    + intros [Hm Hd] i j Hi Hij Hj. rewrite Zlength_cons in Hj.
      destruct (zeq i 0).
      * subst i. rewrite Znth_0_cons. rewrite Znth_pos_cons by lia. intro E.
        assert (member x t = true) by (apply member_Znth; exists (j - 1); split; [ lia | congruence ]).
        congruence.
      * rewrite !Znth_pos_cons by lia. apply Hd; lia.
    + intros H. split.
      * apply member_false. intros k Hk E.
        apply (H 0 (k + 1)); [ lia | lia | rewrite Zlength_cons; lia | ].
        rewrite Znth_0_cons, Znth_pos_cons by lia. replace (k + 1 - 1) with k by lia. auto.
      * intros i j Hi Hij Hj. specialize (H (i + 1) (j + 1) ltac:(lia) ltac:(lia) ltac:(rewrite Zlength_cons; lia)).
        rewrite !Znth_pos_cons in H by lia. replace (i + 1 - 1) with i in H by lia.
        replace (j + 1 - 1) with j in H by lia. exact H.
Qed.

Lemma Zlength_filter1: forall {A} (f: A -> bool) x, Zlength (filter f [x]) = if f x then 1 else 0.
Proof. intros. simpl. destruct (f x); reflexivity. Qed.

Lemma filter_step: forall {A} {d: Inhabitant A} (f: A -> bool) (l: list A) p, 0 <= p < Zlength l ->
  Zlength (filter f (sublist 0 (p + 1) l)) = Zlength (filter f (sublist 0 p l)) + (if f (Znth p l) then 1 else 0).
Proof.
  intros. rewrite (sublist_last_1 0 p l) by lia. rewrite filter_app, Zlength_app, Zlength_filter1. reflexivity.
Qed.

Lemma filter_le: forall {A} (f: A -> bool) (l: list A), 0 <= Zlength (filter f l) <= Zlength l.
Proof.
  intros. rewrite !Zlength_correct. pose proof (filter_length_le f l). lia.
Qed.

Lemma Znth_upd_other: forall {A} {d: Inhabitant A} i j (l: list A) v, 0 <= i < Zlength l -> i <> j ->
  Znth i (upd_Znth j l v) = Znth i l.
Proof.
  intros. destruct (zle 0 j); [ destruct (zlt j (Zlength l)) | ].
  - apply upd_Znth_diff; auto.
  - rewrite upd_Znth_out_of_range by lia. reflexivity.
  - rewrite upd_Znth_out_of_range by lia. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* The builder's outputs                                                   *)
(* ---------------------------------------------------------------------- *)

Lemma install_length: forall al l, Zlength (install al l) = Zlength l.
Proof.
  induction al as [ | a t IH ]; intros l; simpl; auto. rewrite IH, Zlength_upd_Znth. reflexivity.
Qed.

Lemma install_words: forall al l, words_ok l -> words_ok (install al l).
Proof.
  induction al as [ | a t IH ]; intros l Hl; simpl; auto. apply IH. apply Forall_upd_Znth; auto.
  apply alias_leaf_word.
Qed.

Lemma Znth_install: forall al l p, 0 <= p < Zlength l -> Znth p (install al l) = pick al p (Znth p l).
Proof.
  induction al as [ | a t IH ]; intros l p Hp; simpl; auto.
  rewrite IH by (rewrite Zlength_upd_Znth; lia). f_equal.
  destruct (Z.eqb_spec (a_page a) p).
  - subst. apply upd_Znth_same. lia.
  - apply Znth_upd_other; auto.
Qed.

Lemma closed_leaves_words: forall inv l, words_ok l -> words_ok (map (closed_leaf inv) l).
Proof.
  intros inv l H. apply Forall_map. eapply Forall_impl; [ | exact H ]. intros s Hs. simpl.
  unfold closed_leaf. destruct (removes inv s); auto. unfold word_ok. rep_lia.
Qed.

Lemma root_ok_built: forall phys leaves, Zlength leaves = LEAVES -> words_ok leaves ->
  root_ok (built_root phys leaves).
Proof.
  intros phys leaves HL HW. unfold root_ok, built_root; cbn [pml4 pdpt pd pt].
  assert (R: words_ok (Zrepeat 0 512)) by (apply Forall_repeat; unfold word_ok; rep_lia).
  assert (P: words_ok (map (pd_entry phys) (idx 512))).
  { apply Forall_map. apply Forall_forall. intros x _. simpl. unfold pd_entry.
    destruct (x <? 8); [ apply table_entry_word | unfold word_ok; rep_lia ]. }
  rewrite !Zlength_upd_Znth, Zlength_map, Zlength_idx, Zlength_Zrepeat by lia.
  refine (conj eq_refl (conj eq_refl (conj eq_refl (conj HL (conj _ (conj _ (conj P HW))))))).
  - apply Forall_upd_Znth; auto. apply table_entry_word.
  - apply Forall_upd_Znth; auto. apply table_entry_word.
Qed.

Lemma root_ok_closed: forall src inv kp, root_ok src -> root_ok (closed_out src inv kp).
Proof.
  intros src inv kp H. unfold closed_out. destruct H as (_ & _ & _ & HL & _ & _ & _ & HW).
  apply root_ok_built.
  - rewrite Zlength_map. auto.
  - apply closed_leaves_words; auto.
Qed.

Lemma root_ok_copy: forall src inv al cp, root_ok src -> root_ok (copy_out src inv al cp).
Proof.
  intros src inv al cp H. unfold copy_out. destruct H as (_ & _ & _ & HL & _ & _ & _ & HW).
  apply root_ok_built.
  - rewrite install_length, Zlength_map. auto.
  - apply install_words, closed_leaves_words; auto.
Qed.

Lemma tables_ok_built: forall phys leaves, tables_ok (built_root phys leaves) phys 0 = true.
Proof.
  intros phys leaves. unfold tables_ok, built_root; cbn [pml4 pdpt pd].
  change (Z.lnot 0) with (-1). rewrite !Z.land_m1_r.
  assert (Z0: 0 < Zlength (Zrepeat 0 512)) by (rewrite Zlength_Zrepeat; lia).
  rewrite !upd_Znth_same by lia. rewrite !Z.eqb_refl. cbn [andb].
  apply andb_true_iff. split.
  - apply forallb_idx1. intros j Hj. rewrite !Znth_upd_other by (try rewrite Zlength_Zrepeat; lia).
    rewrite Znth_Zrepeat by lia. reflexivity.
  - apply forallb_idx; [ lia | ]. intros j Hj.
    rewrite Znth_map by (rewrite Zlength_idx; lia). rewrite Znth_idx by lia. rewrite Z.land_m1_r. apply Z.eqb_refl.
Qed.

Lemma ancestors_tables: forall r phys, ancestors_ok r phys = tables_ok r phys 32.
Proof. reflexivity. Qed.
