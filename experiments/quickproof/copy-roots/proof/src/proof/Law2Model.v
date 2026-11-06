(* Law window_roots_isolated (harness/window_roots_isolated.c): the pure part.  The harness's own checks as
   functions of its inputs (apart, tables_ok, pre_ok, slots_ok, counts_ok), the proof that its restatement of
   frame_window_build's acceptance is RootsSpecs.window_ok, and the leaves of the roots window_build writes.
   No program here. *)
Require Import VST.floyd.proofauto.
Require Import Coq.btauto.Btauto.
Require Import LeanosRoots.proof.Defs.
Require Import LeanosRoots.proof.RootsSpecs.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* ---------------------------------------------------------------------- *)
(* 64-bit words                                                           *)
(* ---------------------------------------------------------------------- *)

Lemma W_eq: W = 2 ^ 64.
Proof. reflexivity. Qed.

Lemma w_repr_mod: forall x, Int64.repr (x mod W) = Int64.repr x.
Proof. intros. unfold W. rewrite <- Int64.unsigned_repr_eq. apply Int64.repr_unsigned. Qed.

Lemma w_mod: forall x, word_ok (x mod W).
Proof. intros. unfold word_ok, W. pose proof (Z.mod_pos_bound x Int64.modulus ltac:(rep_lia)). rep_lia. Qed.

Lemma w_mod_small: forall x, word_ok x -> x mod W = x.
Proof. intros x H. unfold word_ok in H. apply Z.mod_small. unfold W. rep_lia. Qed.

Lemma w_of_mod: forall x, x mod W = x -> word_ok x.
Proof. intros x H. rewrite <- H. apply w_mod. Qed.

Lemma w_land: forall a b, word_ok a -> word_ok (Z.land a b).
Proof.
  intros a b H. apply w_of_mod. rewrite W_eq, <- Z.land_ones by lia.
  rewrite <- Z.land_assoc, (Z.land_comm b), Z.land_assoc. f_equal.
  rewrite Z.land_ones by lia. rewrite <- W_eq. apply w_mod_small; auto.
Qed.

Lemma w_lor: forall a b, word_ok a -> word_ok b -> word_ok (Z.lor a b).
Proof.
  intros a b Ha Hb. apply w_of_mod. rewrite W_eq, <- Z.land_ones by lia.
  rewrite Z.land_lor_distr_l, !Z.land_ones by lia. rewrite <- W_eq, !w_mod_small; auto.
Qed.

Lemma w_shiftr: forall a k, word_ok a -> 0 <= k -> word_ok (Z.shiftr a k).
Proof.
  intros a k H Hk. unfold word_ok in *. rewrite Z.shiftr_div_pow2 by lia.
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  split; [ apply Z.div_pos; lia | ].
  apply Z.le_trans with a; [ | lia ]. apply Z.div_le_upper_bound; [ lia | ]. nia.
Qed.

Lemma eq64_mod: forall a b, Int64.eq (Int64.repr a) (Int64.repr b) = (a mod W =? b mod W).
Proof.
  intros. unfold Int64.eq. rewrite !Int64.unsigned_repr_eq. fold W.
  destruct (zeq (a mod W) (b mod W)); symmetry; [ apply Z.eqb_eq | apply Z.eqb_neq ]; auto.
Qed.

Lemma ltu64_mod: forall a b, Int64.ltu (Int64.repr a) (Int64.repr b) = (a mod W <? b mod W).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr_eq. fold W.
  destruct (zlt (a mod W) (b mod W)); symmetry; [ apply Z.ltb_lt | apply Z.ltb_ge ]; lia.
Qed.

Lemma eq64_w: forall a b, word_ok a -> word_ok b -> Int64.eq (Int64.repr a) (Int64.repr b) = (a =? b).
Proof. intros. rewrite eq64_mod, !w_mod_small; auto. Qed.

Lemma ltu64_w: forall a b, word_ok a -> word_ok b -> Int64.ltu (Int64.repr a) (Int64.repr b) = (a <? b).
Proof. intros. rewrite ltu64_mod, !w_mod_small; auto. Qed.

Lemma not64_repr: forall x, Int64.not (Int64.repr x) = Int64.repr (Z.lnot x).
Proof.
  intros. apply Int64.same_bits_eq. intros i Hi.
  rewrite Int64.bits_not by auto. rewrite !Int64.testbit_repr by auto.
  rewrite Z.lnot_spec by lia. reflexivity.
Qed.

Lemma shru64_repr: forall x k, word_ok x -> 0 <= k < 64 ->
  Int64.shru (Int64.repr x) (Int64.repr k) = Int64.repr (Z.shiftr x k).
Proof.
  intros x k Hx Hk. unfold word_ok in Hx. unfold Int64.shru.
  rewrite !Int64.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma shl64_repr: forall x k, 0 <= k < 64 ->
  Int64.shl (Int64.repr x) (Int64.repr k) = Int64.repr (x * 2 ^ k).
Proof.
  intros x k Hk. rewrite Int64.shl_mul_two_p. rewrite Int64.unsigned_repr by rep_lia.
  rewrite mul64_repr, two_p_equiv. reflexivity.
Qed.

Lemma divu64_repr: forall x d, word_ok x -> 0 < d <= Int64.max_unsigned ->
  Int64.divu (Int64.repr x) (Int64.repr d) = Int64.repr (x / d).
Proof.
  intros x d Hx Hd. unfold word_ok in Hx. unfold Int64.divu.
  rewrite !Int64.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma modu64_repr: forall x d, word_ok x -> 0 < d <= Int64.max_unsigned ->
  Int64.modu (Int64.repr x) (Int64.repr d) = Int64.repr (x mod d).
Proof.
  intros x d Hx Hd. unfold word_ok in Hx. unfold Int64.modu.
  rewrite !Int64.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma land4095: forall a, 0 <= a -> Z.land a 4095 = a mod 4096.
Proof. intros. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma land1: forall s, 0 <= s -> Z.land s 1 = if Z.odd s then 1 else 0.
Proof.
  intros. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
  apply Zmod_odd.
Qed.

Lemma table_entry_word: forall phys k, word_ok (table_entry phys k).
Proof. intros. unfold table_entry. apply w_lor; [ apply w_mod | unfold word_ok; rep_lia ]. Qed.

Lemma frame_of_word: forall s, word_ok s -> word_ok (frame_of s).
Proof. intros. unfold frame_of. apply w_shiftr; [ apply w_land; auto | lia ]. Qed.

Lemma words_Znth: forall l i, words_ok l -> 0 <= i < Zlength l -> word_ok (Znth i l).
Proof. intros l i H Hi. exact (proj1 (Forall_Znth l _) H i Hi). Qed.

(* ---------------------------------------------------------------------- *)
(* Lists                                                                  *)
(* ---------------------------------------------------------------------- *)

Lemma Zlength_idx: forall n, 0 <= n -> Zlength (idx n) = n.
Proof.
  intros. unfold idx. rewrite Zlength_map, Zlength_correct, length_seq. apply Z2Nat.id; auto.
Qed.

Lemma In_idx: forall n i, In i (idx n) <-> 0 <= i < n.
Proof.
  intros. unfold idx. rewrite in_map_iff. split.
  - intros [k [E Hk]]. apply in_seq in Hk. subst. lia.
  - intros H. exists (Z.to_nat i). split; [ apply Z2Nat.id; lia | ]. apply in_seq. lia.
Qed.

Lemma Znth_idx: forall n i, 0 <= i < n -> Znth i (idx n) = i.
Proof.
  intros. unfold idx. rewrite Znth_map by (rewrite Zlength_correct, length_seq; lia).
  rewrite <- nth_Znth by (rewrite Zlength_correct, length_seq; lia).
  rewrite seq_nth by lia. simpl. apply Z2Nat.id; lia.
Qed.

Lemma idx_snoc: forall n, 0 <= n -> idx (n + 1) = idx n ++ [n].
Proof.
  intros. unfold idx. rewrite Z2Nat.inj_add by lia. rewrite Nat.add_1_r, seq_S, map_app. simpl.
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma forallb_idx_snoc: forall f n, 0 <= n -> forallb f (idx (n + 1)) = (forallb f (idx n) && f n)%bool.
Proof. intros. rewrite idx_snoc, forallb_app by auto. simpl. rewrite andb_true_r. reflexivity. Qed.

Lemma forallb_In_false: forall {A} (f: A -> bool) l x, In x l -> f x = false -> forallb f l = false.
Proof.
  intros A f l x Hin Hf. destruct (forallb f l) eqn:E; auto.
  rewrite forallb_forall in E. rewrite E in Hf by auto. discriminate.
Qed.

Lemma forallb_idx_true: forall f n, (forall i, 0 <= i < n -> f i = true) -> forallb f (idx n) = true.
Proof. intros. apply forallb_forall. intros i Hi. apply In_idx in Hi. auto. Qed.

Lemma forallb_idx_false: forall f n i, 0 <= i < n -> f i = false -> forallb f (idx n) = false.
Proof. intros. apply (forallb_In_false f _ i); auto. apply In_idx; auto. Qed.

Lemma member_true_iff: forall f l, member f l = true <-> In f l.
Proof.
  intros. unfold member. rewrite existsb_exists. split.
  - intros [x [Hin E]]. apply Z.eqb_eq in E. subst. auto.
  - intros. exists f. split; auto. apply Z.eqb_refl.
Qed.

Lemma member_app: forall f l1 l2, member f (l1 ++ l2) = (member f l1 || member f l2)%bool.
Proof. intros. unfold member. apply existsb_app. Qed.

Lemma member_one: forall f x, member f [x] = (f =? x).
Proof. intros. unfold member. simpl. apply orb_false_r. Qed.

Lemma sublist_snoc: forall (l: list Z) i, 0 <= i < Zlength l -> sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l].
Proof. intros. rewrite (sublist_split 0 i (i + 1)) by lia. rewrite sublist_len_1 by lia. reflexivity. Qed.

Lemma distinct_spec: forall l, distinct l = true <-> (forall a b, 0 <= a /\ a < b /\ b < Zlength l -> Znth a l <> Znth b l).
Proof.
  induction l as [ | x t IH ]; simpl.
  - split; auto. intros _ a b H. rewrite Zlength_nil in H. lia.
  - rewrite andb_true_iff, negb_true_iff, IH. rewrite Zlength_cons. split.
    + intros [Hm Hd] a b Hab E.
      destruct (Z.eq_dec a 0).
      * subst a. rewrite Znth_0_cons, Znth_pos_cons in E by lia.
        assert (In x t) by (rewrite E; apply Znth_In; lia).
        apply member_true_iff in H. congruence.
      * rewrite !Znth_pos_cons in E by lia. apply (Hd (a - 1) (b - 1)); auto; lia.
    + intros H. split.
      * destruct (member x t) eqn:E; auto. apply member_true_iff in E.
        apply In_Znth in E. destruct E as [b [Hb E]].
        exfalso. apply (H 0 (b + 1)); [ lia | ]. rewrite Znth_0_cons, Znth_pos_cons by lia.
        replace (b + 1 - 1) with b by lia. auto.
      * intros a b Hab E. apply (H (a + 1) (b + 1)); [ lia | ].
        rewrite !Znth_pos_cons by lia. replace (a + 1 - 1) with a by lia. replace (b + 1 - 1) with b by lia.
        auto.
Qed.

Lemma Znth_upd_Znth_eq: forall (l: list Z) i j x, 0 <= j < Zlength l -> 0 <= i < Zlength l ->
  Znth i (upd_Znth j l x) = if Z.eq_dec i j then x else Znth i l.
Proof.
  intros. destruct (Z.eq_dec i j).
  - subst. apply upd_Znth_same; auto.
  - apply upd_Znth_diff; auto.
Qed.

(* ---------------------------------------------------------------------- *)
(* The harness's checks                                                   *)
(* ---------------------------------------------------------------------- *)

(* apart(a, b): a + ROOT_BYTES <= b || b + ROOT_BYTES <= a, in uint64_t. *)
Definition apart (a b: Z) : bool := ((a + ROOT_BYTES) mod W <=? b) || ((b + ROOT_BYTES) mod W <=? a).

(* x & ~ignore. *)
Definition clear_bits (x ig: Z) : Z := Z.land x (Z.lnot ig).

(* tables_at(r, phys, ignore) != 0. *)
Definition tables_ok (r: root) (phys ig: Z) : bool :=
  (clear_bits (Znth 0 (pml4 r)) ig =? table_entry phys 1) &&
  (clear_bits (Znth 0 (pdpt r)) ig =? table_entry phys 2) &&
  forallb (fun i => (Znth i (pml4 r) =? 0) && (Znth i (pdpt r) =? 0)) (map (Z.add 1) (idx 511)) &&
  forallb (fun i => clear_bits (Znth i (pd r)) ig =? pd_entry phys i) (idx 512).

Lemma tables_ok_accessed: forall r phys, tables_ok r phys ACCESSED = ancestors_ok r phys.
Proof. reflexivity. Qed.

(* The first thirteen conjuncts of the harness's `valid`. *)
Definition pre_ok (src: root) (sp kp: Z) (fs: list Z) (n: Z) (w: window) : bool :=
  phys_ok sp && phys_ok kp && phys_ok (w_fetch_phys w) && phys_ok (w_send_phys w) &&
  apart sp kp && apart sp (w_fetch_phys w) && apart sp (w_send_phys w) && apart kp (w_fetch_phys w) &&
  apart kp (w_send_phys w) && apart (w_fetch_phys w) (w_send_phys w) &&
  geometry_ok w && ancestors_ok src sp && inventory_ok fs n.

(* The window-frame membership and zero-slot loop. *)
Definition slot_ok (src: root) (inv: list Z) (w: window) (i: Z) : bool :=
  member (Z.shiftr (w_base w) 12 + i) inv && (Znth (w_slot w + i) (pt src) =? 0).
Definition slots_ok (src: root) (inv: list Z) (w: window) : bool := forallb (slot_ok src inv w) (idx (pages_of w)).

(* The pre-pass's counts against first, when built is set. *)
Definition counts_ok (src: root) (inv: list Z) (n built: Z) (fr: counts) : bool :=
  (built =? 0) || ((c_protected fr =? n) && (c_removed fr =? removed_count inv (pt src)) &&
                   (c_retained fr =? retained_count inv (pt src))).

(* ---------------------------------------------------------------------- *)
(* The restatement is window_ok                                           *)
(* ---------------------------------------------------------------------- *)

Lemma apart_disjoint: forall a b, word_ok a -> word_ok b -> phys_ok a = true -> phys_ok b = true ->
  apart a b = disjoint a b.
Proof.
  intros a b Ha Hb Pa Pb. unfold phys_ok, ROOT_BYTES in *. unfold word_ok in *.
  rewrite !andb_true_iff in Pa, Pb. destruct Pa as [[_ _] Pa]. destruct Pb as [[_ _] Pb].
  apply Z.leb_le in Pa. apply Z.leb_le in Pb.
  unfold apart, disjoint, ROOT_BYTES. rewrite !Z.mod_small by (unfold W; rep_lia).
  destruct (Z.leb_spec a b);
  destruct (Z.leb_spec (a + 45056) b); destruct (Z.leb_spec (b + 45056) a);
  destruct (Z.leb_spec 45056 (b - a)); destruct (Z.leb_spec 45056 (a - b)); simpl; auto; lia.
Qed.

Lemma geometry_facts: forall w, window_wf w -> geometry_ok w = true ->
  w_base w mod 4096 = 0 /\ 0 <= w_base w < w_limit w /\ w_limit w <= 16777216 /\
  (pages_of w = 1 \/ pages_of w = 2) /\ pages_of w * 4096 = w_limit w - w_base w /\
  1 <= w_slot w /\ w_slot w + pages_of w <= LEAVES /\ Z.shiftr (w_base w) 12 + pages_of w <= 4097.
Proof.
  intros [fp sp b l s] Hw G. unfold window_wf, word_ok in Hw.
  unfold geometry_ok, pages_of, LEAVES in *. cbn [w_base w_limit w_slot w_fetch_phys w_send_phys] in *.
  rewrite !andb_true_iff, orb_true_iff in G.
  destruct G as [[[[[[G1 G2] G3] G4] G5] G6] G7].
  rewrite Z.eqb_eq in G1. rewrite Z.ltb_lt in G2. rewrite Z.leb_le in G3, G6, G7.
  rewrite negb_true_iff, Z.eqb_neq in G5. rewrite land4095 in G1 by lia.
  rewrite (Z.mod_small (l - b)) in * by (unfold W; rep_lia).
  rewrite !Z.eqb_eq in G4.
  assert (Hp: (l - b) / 4096 = 1 \/ (l - b) / 4096 = 2) by (destruct G4 as [E | E]; rewrite E; auto).
  assert (0 <= (l - b) / 4096 <= 2) by lia.
  rewrite Z.mod_small in G7 by (unfold W; rep_lia).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 12) with 4096.
  assert (b / 4096 <= 4096) by (apply Z.div_le_upper_bound; lia).
  assert (Eb: b = 4096 * (b / 4096) + b mod 4096) by (apply Z.div_mod; lia).
  assert (El: l - b = 4096 * ((l - b) / 4096)) by (destruct G4 as [E | E]; rewrite E; reflexivity).
  repeat split; try lia.
Qed.

Lemma page_of_alias: forall w x i, 0 <= w_slot w -> 0 <= i -> w_slot w + i <= LEAVES ->
  a_page (window_alias w x i) = w_slot w + i.
Proof. intros. unfold window_alias. simpl. apply Z.mod_small. unfold W, LEAVES in *. rep_lia. Qed.

Lemma frame_of_alias: forall w x i, 0 <= w_base w -> 0 <= i -> Z.shiftr (w_base w) 12 + i <= 4097 ->
  a_frame (window_alias w x i) = Z.shiftr (w_base w) 12 + i.
Proof.
  intros. unfold window_alias. simpl. apply Z.mod_small.
  assert (0 <= Z.shiftr (w_base w) 12) by (apply Z.shiftr_nonneg; lia). unfold W. rep_lia.
Qed.

Lemma idx1: idx 1 = [0].
Proof. reflexivity. Qed.
Lemma idx2: idx 2 = [0; 1].
Proof. reflexivity. Qed.

Lemma aliases_slots: forall src inv w x, window_wf w -> geometry_ok w = true -> 0 <= x <= 1 ->
  aliases_ok src inv (window_aliases w x) (pages_of w) = slots_ok src inv w.
Proof.
  intros src inv w x Hw G Hx.
  destruct (geometry_facts w Hw G) as (Gm & Gb & Gl & Gp & Gpl & Gs & Gsp & Gf).
  assert (Sb: 0 <= Z.shiftr (w_base w) 12) by (apply Z.shiftr_nonneg; lia).
  unfold aliases_ok, window_aliases, slots_ok, LEAVES in *.
  destruct Gp as [Hp | Hp]; rewrite Hp in *; [ rewrite idx1 | rewrite idx2 ]; simpl map;
    rewrite sublist_same by (simpl; auto); simpl forallb; simpl map;
    unfold alias_ok, slot_ok, LEAVES;
    rewrite ?page_of_alias, ?frame_of_alias by (unfold LEAVES; lia); simpl a_writable;
    rewrite (proj2 (Z.leb_le x 1)) by lia.
  - rewrite (proj2 (Z.ltb_lt (w_slot w + 0) 4096)) by lia. simpl. btauto.
  - rewrite (proj2 (Z.ltb_lt (w_slot w + 0) 4096)) by lia. rewrite (proj2 (Z.ltb_lt (w_slot w + 1) 4096)) by lia.
    simpl.
    rewrite (Z.mod_small (w_slot w + 0)), (Z.mod_small (w_slot w + 1)), (Z.mod_small (Z.shiftr (w_base w) 12 + 0)),
      (Z.mod_small (Z.shiftr (w_base w) 12 + 1)) by (unfold W; rep_lia).
    rewrite (proj2 (Z.eqb_neq (w_slot w + 0) (w_slot w + 1))) by lia.
    rewrite (proj2 (Z.eqb_neq (Z.shiftr (w_base w) 12 + 0) (Z.shiftr (w_base w) 12 + 1))) by lia.
    simpl. btauto.
Qed.

Theorem valid_window_ok: forall src sp kp fs n w built fr,
  word_ok sp -> word_ok kp -> window_wf w ->
  (pre_ok src sp kp fs n w && slots_ok src (sublist 0 n fs) w && counts_ok src (sublist 0 n fs) n built fr)%bool
  = window_ok src sp kp fs n w built fr.
Proof.
  intros src sp kp fs n w built fr Hsp Hkp Hw.
  pose proof Hw as Hw'. destruct Hw' as (Hf & Hs & _).
  unfold window_ok, build_ok, pre_ok, counts_ok. cbv zeta.
  destruct (phys_ok sp) eqn:P1; [ | simpl; btauto ].
  destruct (phys_ok kp) eqn:P2; [ | simpl; btauto ].
  destruct (phys_ok (w_fetch_phys w)) eqn:P3; [ | simpl; btauto ].
  destruct (phys_ok (w_send_phys w)) eqn:P4; [ | simpl; btauto ].
  rewrite !apart_disjoint by auto.
  destruct (geometry_ok w) eqn:G; [ | simpl; btauto ].
  rewrite !aliases_slots by (auto; lia).
  btauto.
Qed.

(* ---------------------------------------------------------------------- *)
(* The roots window_build writes                                          *)
(* ---------------------------------------------------------------------- *)

Lemma Zlength_install: forall al l, Zlength (install al l) = Zlength l.
Proof.
  induction al as [ | a t IH ]; intros; simpl; auto. rewrite IH. apply Zlength_upd_Znth.
Qed.

Lemma alias_leaf_word: forall a, word_ok (alias_leaf a).
Proof.
  intros. unfold alias_leaf. repeat apply w_lor; try apply w_mod; unfold word_ok, NX; try rep_lia.
  destruct (a_writable a =? 0); rep_lia.
Qed.

Lemma install_words: forall al l, words_ok l -> words_ok (install al l).
Proof.
  induction al as [ | a t IH ]; intros; simpl; auto. apply IH. apply Forall_upd_Znth; auto. apply alias_leaf_word.
Qed.

Lemma closed_leaf_word: forall inv s, word_ok s -> word_ok (closed_leaf inv s).
Proof. intros. unfold closed_leaf. destruct (removes inv s); auto. unfold word_ok; rep_lia. Qed.

Lemma Forall_Zrepeat: forall (P: Z -> Prop) x n, P x -> Forall P (Zrepeat x n).
Proof. intros. unfold Zrepeat. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. subst; auto. Qed.

Lemma built_root_ok: forall phys leaves, Zlength leaves = LEAVES -> words_ok leaves -> root_ok (built_root phys leaves).
Proof.
  intros phys leaves Hl Hw. unfold root_ok, built_root, words_ok. cbn [pml4 pdpt pd pt].
  rewrite !Zlength_upd_Znth, Zlength_map, Zlength_idx by lia. rewrite Zlength_Zrepeat by lia.
  repeat split; auto.
  - apply Forall_upd_Znth; [ apply Forall_Zrepeat; unfold word_ok; rep_lia | apply table_entry_word ].
  - apply Forall_upd_Znth; [ apply Forall_Zrepeat; unfold word_ok; rep_lia | apply table_entry_word ].
  - apply Forall_map. apply Forall_forall. intros i _. change (word_ok (pd_entry phys i)). unfold pd_entry.
    destruct (i <? 8); [ apply table_entry_word | unfold word_ok; rep_lia ].
Qed.

Lemma closed_out_ok: forall src inv kp, root_ok src -> root_ok (closed_out src inv kp).
Proof.
  intros src inv kp (_ & _ & _ & L & _ & _ & _ & Wd). unfold closed_out. apply built_root_ok.
  - rewrite Zlength_map; auto.
  - apply Forall_map. eapply Forall_impl; [ | exact Wd ]. intros. apply closed_leaf_word; auto.
Qed.

Lemma copy_out_ok: forall src inv al cp, root_ok src -> root_ok (copy_out src inv al cp).
Proof.
  intros src inv al cp (_ & _ & _ & L & _ & _ & _ & Wd). unfold copy_out. apply built_root_ok.
  - rewrite Zlength_install, Zlength_map; auto.
  - apply install_words. apply Forall_map. eapply Forall_impl; [ | exact Wd ]. intros. apply closed_leaf_word; auto.
Qed.

Lemma tables_built: forall phys leaves, tables_ok (built_root phys leaves) phys 0 = true.
Proof.
  intros. unfold tables_ok, clear_bits. change (Z.lnot 0) with (-1). rewrite !Z.land_m1_r.
  apply andb_true_iff; split; [ apply andb_true_iff; split; [ apply andb_true_iff; split | ] | ].
  - unfold built_root; cbn [pml4]. rewrite upd_Znth_same by (rewrite Zlength_Zrepeat; lia). apply Z.eqb_refl.
  - unfold built_root; cbn [pdpt]. rewrite upd_Znth_same by (rewrite Zlength_Zrepeat; lia). apply Z.eqb_refl.
  - apply forallb_forall. intros j Hj. apply in_map_iff in Hj. destruct Hj as [k [E Hk]]. apply In_idx in Hk.
    subst j. unfold built_root; cbn [pml4 pdpt].
    rewrite !upd_Znth_diff by (rewrite ?Zlength_Zrepeat; lia). rewrite !Znth_Zrepeat by lia. reflexivity.
  - apply forallb_forall. intros i Hi. apply In_idx in Hi. unfold built_root; cbn [pd].
    rewrite Znth_map by (rewrite Zlength_idx; lia). rewrite Znth_idx by lia. rewrite Z.land_m1_r. apply Z.eqb_refl.
Qed.

Lemma closed_pt: forall src inv kp p, 0 <= p < Zlength (pt src) ->
  Znth p (pt (closed_out src inv kp)) = closed_leaf inv (Znth p (pt src)).
Proof. intros. unfold closed_out, built_root. cbn [pt]. rewrite Znth_map by lia. reflexivity. Qed.

Lemma copy_pt: forall src inv w x cp p, root_ok src -> window_wf w -> geometry_ok w = true -> 0 <= p < LEAVES ->
  Znth p (pt (copy_out src inv (window_aliases w x) cp)) =
  if ((w_slot w <=? p) && (p <? w_slot w + pages_of w))%bool then alias_leaf (window_alias w x (p - w_slot w))
  else closed_leaf inv (Znth p (pt src)).
Proof.
  intros src inv w x cp p Hr Hw G Hp.
  destruct Hr as (_ & _ & _ & L & _).
  destruct (geometry_facts w Hw G) as (Gm & Gb & Gl & Gp & Gpl & Gs & Gsp & Gf).
  unfold copy_out, built_root, window_aliases. cbn [pt].
  assert (Lm: Zlength (map (closed_leaf inv) (pt src)) = LEAVES) by (rewrite Zlength_map; auto).
  unfold LEAVES in *.
  destruct Gp as [Hq | Hq]; rewrite Hq in *; [ rewrite idx1 | rewrite idx2 ]; simpl map; simpl install;
    rewrite ?(Z.mod_small (w_slot w + 0)), ?(Z.mod_small (w_slot w + 1)) by (unfold W; rep_lia).
  - rewrite Znth_upd_Znth_eq by lia. rewrite Z.add_0_r.
    destruct (Z.eq_dec p (w_slot w)).
    + subst p. rewrite Z.leb_refl, (proj2 (Z.ltb_lt _ _)) by lia. simpl. rewrite Z.sub_diag. reflexivity.
    + rewrite Znth_map by lia.
      destruct (Z.leb_spec (w_slot w) p); destruct (Z.ltb_spec p (w_slot w + 1)); simpl; auto; lia.
  - rewrite Znth_upd_Znth_eq by (rewrite ?Zlength_upd_Znth; lia).
    rewrite Znth_upd_Znth_eq by lia. rewrite Z.add_0_r.
    destruct (Z.eq_dec p (w_slot w + 1)).
    + subst p. rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia. simpl.
      f_equal. f_equal. lia.
    + destruct (Z.eq_dec p (w_slot w)).
      * subst p. rewrite Z.leb_refl, (proj2 (Z.ltb_lt _ _)) by lia. simpl. rewrite Z.sub_diag. reflexivity.
      * rewrite Znth_map by lia.
        destruct (Z.leb_spec (w_slot w) p); destruct (Z.ltb_spec p (w_slot w + 2)); simpl; auto; lia.
Qed.

(* The harness's alias word ((base >> 12) + i) << 12 | PRESENT | NX, with WRITABLE when x is 1. *)
Lemma alias_leaf_value: forall w x i, window_wf w -> geometry_ok w = true -> 0 <= i < pages_of w ->
  alias_leaf (window_alias w x i) =
  Z.lor (Z.lor (Z.lor ((Z.shiftr (w_base w) 12 + i) * 4096) 1) NX) (if x =? 0 then 0 else 2).
Proof.
  intros w x i Hw G Hi.
  destruct (geometry_facts w Hw G) as (Gm & Gb & Gl & Gp & Gpl & Gs & Gsp & Gf).
  assert (Sb: 0 <= Z.shiftr (w_base w) 12) by (apply Z.shiftr_nonneg; lia).
  unfold alias_leaf. rewrite frame_of_alias by lia. simpl a_writable.
  rewrite Z.mod_small by (unfold W; rep_lia). reflexivity.
Qed.
