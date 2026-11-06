(* Pure facts about Defs.v for the window proofs (WindowProof.v): the roots the builder writes have the source
   hierarchy's shape at their physical address, and copy_out with the window's aliases over closed_out passes
   the window scan leaf by leaf. *)
Require Import VST.floyd.proofauto.
Require Import LeanosRoots.proof.Defs.
Local Open Scope Z_scope.

(* A default alias for Znth on alias lists; local here and in WindowProof.v. *)
Definition window_alias_default : Inhabitant alias := mkalias 0 0 0.
#[local] Existing Instance window_alias_default.

Lemma W_val: W = 18446744073709551616.
Proof. reflexivity. Qed.

Lemma max_unsigned_W: Int64.max_unsigned = W - 1.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* Index lists                                                            *)
(* ---------------------------------------------------------------------- *)

Lemma idx_Zlength: forall n, 0 <= n -> Zlength (idx n) = n.
Proof. intros. unfold idx. rewrite Zlength_map, Zlength_correct, length_seq. lia. Qed.

Lemma In_idx: forall n p, In p (idx n) <-> 0 <= p < n.
Proof.
  intros. unfold idx. rewrite in_map_iff. split.
  - intros [k [Hk Hin]]. apply in_seq in Hin. subst. lia.
  - intros Hp. exists (Z.to_nat p). split; [ lia | ]. apply in_seq. lia.
Qed.

Lemma forallb_idx: forall (f: Z -> bool) n, forallb f (idx n) = true <-> (forall p, 0 <= p < n -> f p = true).
Proof.
  intros. rewrite forallb_forall. split; intros H p Hp.
  - apply H. apply In_idx. exact Hp.
  - apply H. apply In_idx. exact Hp.
Qed.

Lemma forallb_idx_false: forall (f: Z -> bool) n p, 0 <= p < n -> f p = false -> forallb f (idx n) = false.
Proof.
  intros f n p Hp Hf. destruct (forallb f (idx n)) eqn:E; [ | reflexivity ].
  rewrite forallb_idx in E. rewrite E in Hf by exact Hp. discriminate.
Qed.

Lemma Znth_idx: forall n i, 0 <= i < n -> Znth i (idx n) = i.
Proof.
  intros. unfold idx, Znth. destruct (Z_lt_dec i 0); [ lia | ].
  rewrite nth_indep with (d' := Z.of_nat 0) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. lia.
Qed.

Lemma Zlength_filter_le: forall {A} (f: A -> bool) (l: list A), Zlength (filter f l) <= Zlength l.
Proof. intros. rewrite !Zlength_correct. pose proof (filter_length_le f l). lia. Qed.

(* ---------------------------------------------------------------------- *)
(* Words                                                                  *)
(* ---------------------------------------------------------------------- *)

Lemma lor_range: forall a b, 0 <= a < W -> 0 <= b < W -> 0 <= Z.lor a b < W.
Proof.
  intros a b Ha Hb. rewrite W_val in *. split; [ apply Z.lor_nonneg; lia | ].
  change 18446744073709551616 with (2 ^ 64) in *.
  rewrite <- (Z.mod_small a (2 ^ 64)) by lia. rewrite <- (Z.mod_small b (2 ^ 64)) by lia.
  rewrite <- !Z.land_ones by lia. rewrite <- Z.land_lor_distr_l. rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound (Z.lor a b) (2 ^ 64)). lia.
Qed.

Lemma word_lor: forall a b, word_ok a -> word_ok b -> word_ok (Z.lor a b).
Proof.
  unfold word_ok. intros a b Ha Hb. rewrite max_unsigned_W in *.
  pose proof (lor_range a b ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma word_modW: forall x, word_ok (x mod W).
Proof.
  intros. unfold word_ok. rewrite max_unsigned_W. pose proof (Z.mod_pos_bound x W ltac:(rewrite W_val; lia)).
  lia.
Qed.

Lemma table_entry_word: forall phys k, word_ok (table_entry phys k).
Proof. intros. unfold table_entry. apply word_lor; [ apply word_modW | unfold word_ok; rep_lia ]. Qed.

Lemma alias_leaf_word: forall a, word_ok (alias_leaf a).
Proof.
  intros. unfold alias_leaf.
  repeat apply word_lor; try apply word_modW; unfold word_ok, NX; try rep_lia.
  destruct (a_writable a =? 0); rep_lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* The shape of a built root                                              *)
(* ---------------------------------------------------------------------- *)

Lemma testbit_page: forall x m, x mod 4096 = 0 -> 0 <= m < 12 -> Z.testbit x m = false.
Proof.
  intros x m H Hm. rewrite (Z.div_mod x 4096) by lia. rewrite H, Z.add_0_r.
  replace (4096 * (x / 4096)) with ((x / 4096) * 2 ^ 12) by (change (2 ^ 12) with 4096; lia).
  apply Z.mul_pow2_bits_low. lia.
Qed.

Lemma clear_accessed_id: forall y, Z.testbit y 5 = false -> clear_accessed y = y.
Proof.
  intros y H. unfold clear_accessed, ACCESSED. apply Z.bits_inj'. intros m Hm.
  rewrite Z.land_spec, Z.lnot_spec by lia.
  destruct (Z.eq_dec m 5).
  - subst. rewrite H. reflexivity.
  - change 32 with (2 ^ 5). rewrite Z.pow2_bits_eqb by lia.
    rewrite (proj2 (Z.eqb_neq 5 m)) by lia. simpl negb. apply andb_true_r.
Qed.

Lemma table_entry_clear: forall phys k, phys mod 4096 = 0 -> clear_accessed (table_entry phys k) = table_entry phys k.
Proof.
  intros phys k Hp. apply clear_accessed_id. unfold table_entry. rewrite Z.lor_spec.
  rewrite testbit_page; [ reflexivity | | lia ].
  rewrite <- Zmod_div_mod; [ | lia | rewrite W_val; lia | ].
  - rewrite Z_mod_plus_full. exact Hp.
  - exists 4503599627370496. rewrite W_val. reflexivity.
Qed.

Lemma phys_ok_page: forall a, phys_ok a = true -> a mod 4096 = 0.
Proof.
  intros a H. unfold phys_ok in H. apply andb_prop in H as [H _]. apply andb_prop in H as [_ H].
  apply Z.eqb_eq. exact H.
Qed.

Lemma ancestors_built: forall phys leaves, phys mod 4096 = 0 -> ancestors_ok (built_root phys leaves) phys = true.
Proof.
  intros phys leaves Hp. unfold ancestors_ok, built_root; cbn [pml4 pdpt pd pt].
  assert (Zr: Zlength (Zrepeat 0 512) = 512) by (apply Zlength_Zrepeat; lia).
  rewrite !upd_Znth_same by lia.
  rewrite !table_entry_clear by exact Hp. rewrite !Z.eqb_refl. cbn [andb].
  apply andb_true_intro; split.
  - apply forallb_forall. intros i Hi. apply in_map_iff in Hi. destruct Hi as [j [Hj Hin]].
    apply In_idx in Hin. subst i.
    rewrite !upd_Znth_diff by lia. rewrite Znth_Zrepeat by lia. reflexivity.
  - apply forallb_idx. intros i Hi. rewrite Znth_map by (rewrite idx_Zlength; lia). rewrite Znth_idx by lia.
    unfold pd_entry. destruct (i <? 8).
    + rewrite table_entry_clear by exact Hp. apply Z.eqb_refl.
    + reflexivity.
Qed.

Lemma words_ok_Zrepeat0: forall n, words_ok (Zrepeat 0 n).
Proof.
  intros. unfold words_ok, Zrepeat. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst.
  unfold word_ok; rep_lia.
Qed.

Lemma built_root_ok: forall phys leaves, Zlength leaves = LEAVES -> words_ok leaves ->
  root_ok (built_root phys leaves).
Proof.
  intros phys leaves HL HW. unfold root_ok, built_root; cbn [pml4 pdpt pd pt].
  assert (Zr: Zlength (Zrepeat 0 512) = 512) by (apply Zlength_Zrepeat; lia).
  split; [ rewrite upd_Znth_Zlength; lia | ].
  split; [ rewrite upd_Znth_Zlength; lia | ].
  split; [ rewrite Zlength_map, idx_Zlength; lia | ].
  split; [ exact HL | ].
  split; [ apply Forall_upd_Znth; [ apply words_ok_Zrepeat0 | apply table_entry_word ] | ].
  split; [ apply Forall_upd_Znth; [ apply words_ok_Zrepeat0 | apply table_entry_word ] | ].
  split; [ | exact HW ].
  unfold words_ok. apply Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as [i [Hi _]]. subst.
  unfold pd_entry. destruct (i <? 8); [ apply table_entry_word | unfold word_ok; rep_lia ].
Qed.

Lemma closed_leaves_len: forall inv l, Zlength (map (closed_leaf inv) l) = Zlength l.
Proof. intros. apply Zlength_map. Qed.

Lemma closed_leaves_ok: forall inv l, words_ok l -> words_ok (map (closed_leaf inv) l).
Proof.
  intros inv l H. unfold words_ok in *. rewrite Forall_forall in *. intros x Hx. apply in_map_iff in Hx.
  destruct Hx as [y [Hy Hin]]. subst. unfold closed_leaf. destruct (removes inv y).
  - unfold word_ok; rep_lia.
  - apply H. exact Hin.
Qed.

Lemma install_ok: forall al l, words_ok l -> words_ok (install al l).
Proof.
  induction al; intros l H; simpl; [ exact H | ]. apply IHal. apply Forall_upd_Znth; [ exact H | ].
  apply alias_leaf_word.
Qed.

Lemma install_len: forall al l, Zlength (install al l) = Zlength l.
Proof.
  induction al; intros l; simpl; [ reflexivity | ]. rewrite IHal. unfold upd_Znth.
  destruct (Sumbool.sumbool_and _ _ _ _ _ _); [ | reflexivity ].
  rewrite Zlength_app, Zlength_cons, !Zlength_sublist by lia. lia.
Qed.

Lemma closed_out_ok: forall src inv kp, root_ok src -> root_ok (closed_out src inv kp).
Proof.
  intros src inv kp (_ & _ & _ & HL & _ & _ & _ & HW). unfold closed_out. apply built_root_ok.
  - rewrite closed_leaves_len. exact HL.
  - apply closed_leaves_ok. exact HW.
Qed.

Lemma copy_out_ok: forall src inv al cp, root_ok src -> root_ok (copy_out src inv al cp).
Proof.
  intros src inv al cp (_ & _ & _ & HL & _ & _ & _ & HW). unfold copy_out. apply built_root_ok.
  - rewrite install_len, closed_leaves_len. exact HL.
  - apply install_ok. apply closed_leaves_ok. exact HW.
Qed.

(* ---------------------------------------------------------------------- *)
(* The window                                                             *)
(* ---------------------------------------------------------------------- *)

Lemma geometry_slots: forall w, 0 <= w_slot w -> geometry_ok w = true ->
  (pages_of w = 1 \/ pages_of w = 2) /\ 1 <= w_slot w /\ w_slot w + pages_of w <= LEAVES.
Proof.
  intros w Hs G. unfold geometry_ok in G.
  apply andb_prop in G as [G G7]. apply andb_prop in G as [G G6]. apply andb_prop in G as [G G5].
  apply andb_prop in G as [G G4]. apply andb_prop in G as [G _].
  assert (HP: pages_of w = 1 \/ pages_of w = 2).
  { unfold pages_of. apply orb_prop in G4. destruct G4 as [E | E]; apply Z.eqb_eq in E; rewrite E;
      [ left | right ]; reflexivity. }
  apply negb_true_iff, Z.eqb_neq in G5. apply Z.leb_le in G6. apply Z.leb_le in G7.
  unfold LEAVES in *. rewrite Z.mod_small in G7 by (rewrite W_val; lia).
  split; [ exact HP | split; lia ].
Qed.

Lemma pages_word: forall w, word_ok (pages_of w).
Proof.
  intros. unfold word_ok, pages_of. pose proof (Z.mod_pos_bound (w_limit w - w_base w) W ltac:(rewrite W_val; lia)).
  rewrite max_unsigned_W. split; [ apply Z.div_pos; lia | ].
  apply Z.le_trans with ((w_limit w - w_base w) mod W); [ apply Z.div_le_upper_bound; lia | lia ].
Qed.

Lemma window_aliases_len: forall w wr, Zlength (window_aliases w wr) = pages_of w.
Proof.
  intros. unfold window_aliases. rewrite Zlength_map, idx_Zlength; [ reflexivity | ].
  unfold pages_of. apply Z.div_pos; [ | lia ]. apply Z.mod_pos_bound. rewrite W_val; lia.
Qed.

Lemma Znth_window_aliases: forall w wr i, 0 <= i < pages_of w ->
  Znth i (window_aliases w wr) = window_alias w wr i.
Proof.
  intros. unfold window_aliases. rewrite Znth_map by (rewrite idx_Zlength; lia). rewrite Znth_idx by lia.
  reflexivity.
Qed.

Lemma install_window: forall w wr L p, 0 <= w_slot w -> geometry_ok w = true -> Zlength L = LEAVES ->
  0 <= p < LEAVES ->
  Znth p (install (window_aliases w wr) L) =
  if in_slots w p then alias_leaf (window_alias w wr (p - w_slot w)) else Znth p L.
Proof.
  intros w wr L p Hs G HL Hp. destruct (geometry_slots w Hs G) as [[HP | HP] [S1 S2]];
    unfold window_aliases, in_slots; rewrite HP in *; unfold LEAVES in *.
  - change (idx 1) with [0]. cbn [map install].
    unfold window_alias at 1; cbn [a_page].
    rewrite Z.add_0_r, (Z.mod_small (w_slot w)) by (rewrite W_val; lia).
    rewrite (Z.mod_small (w_slot w + 1)) by (rewrite W_val; lia).
    destruct (Z.eq_dec p (w_slot w)).
    + subst p. rewrite upd_Znth_same by lia. rewrite Z.leb_refl, (proj2 (Z.ltb_lt _ _)) by lia.
      cbn [andb]. rewrite Z.sub_diag. reflexivity.
    + rewrite upd_Znth_diff by lia.
      destruct (Z.leb_spec (w_slot w) p); destruct (Z.ltb_spec p (w_slot w + 1)); cbn [andb];
        try reflexivity; lia.
  - change (idx 2) with [0; 1]. cbn [map install].
    unfold window_alias at 1 2; cbn [a_page].
    rewrite Z.add_0_r, (Z.mod_small (w_slot w)) by (rewrite W_val; lia).
    rewrite (Z.mod_small (w_slot w + 1)) by (rewrite W_val; lia).
    rewrite (Z.mod_small (w_slot w + 2)) by (rewrite W_val; lia).
    assert (HL1: forall x, Zlength (upd_Znth (w_slot w) L x) = 4096).
    { intros. rewrite upd_Znth_Zlength; lia. }
    destruct (Z.eq_dec p (w_slot w + 1)); [ | destruct (Z.eq_dec p (w_slot w)) ].
    + subst p. rewrite upd_Znth_same by (rewrite HL1; lia).
      rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia.
      cbn [andb]. replace (w_slot w + 1 - w_slot w) with 1 by lia. reflexivity.
    + subst p. rewrite upd_Znth_diff by (rewrite ?HL1; lia). rewrite upd_Znth_same by lia.
      rewrite Z.leb_refl, (proj2 (Z.ltb_lt _ _)) by lia.
      cbn [andb]. rewrite Z.sub_diag. reflexivity.
    + rewrite upd_Znth_diff by (rewrite ?HL1; lia). rewrite upd_Znth_diff by lia.
      destruct (Z.leb_spec (w_slot w) p); destruct (Z.ltb_spec p (w_slot w + 2)); cbn [andb];
        try reflexivity; lia.
Qed.

Lemma removes_zero: forall inv, removes inv 0 = false.
Proof. reflexivity. Qed.

(* The roots the builder writes for the window pass the window scan. *)
Lemma scan_built: forall src inv w wr cp kp,
  Zlength (pt src) = LEAVES -> 0 <= w_slot w -> geometry_ok w = true ->
  cp mod 4096 = 0 -> kp mod 4096 = 0 ->
  scan_ok (copy_out src inv (window_aliases w wr) cp) (closed_out src inv kp) cp kp inv w (negb (wr =? 0)) = true.
Proof.
  intros src inv w wr cp kp HL Hs G Hc Hk. unfold scan_ok, copy_out, closed_out.
  rewrite !ancestors_built by assumption. cbn [andb].
  apply forallb_idx. intros p Hp. unfold built_root; cbn [pt].
  rewrite install_window by (try rewrite closed_leaves_len; assumption).
  rewrite Znth_map by (unfold LEAVES in *; lia).
  set (s := Znth p (pt src)).
  apply andb_true_intro; split.
  - unfold closed_leaf. destruct (removes inv s) eqn:E; [ reflexivity | rewrite E; reflexivity ].
  - unfold scan_leaf. destruct (in_slots w p) eqn:E; [ | apply Z.eqb_refl ].
    unfold in_slots in E. apply andb_prop in E as [E1 _]. apply Z.leb_le in E1.
    unfold alias_leaf, window_alias; cbn [a_frame a_writable].
    rewrite (Z.mod_small (p - w_slot w) W) by (rewrite W_val; unfold LEAVES in *; lia).
    destruct (wr =? 0); apply Z.eqb_refl.
Qed.

(* What build_ok gives the window proofs. *)
Lemma build_ok_facts: forall src sp kp cp fs n al m, build_ok src sp kp cp fs n al m = true ->
  phys_ok kp = true /\ phys_ok cp = true /\ 1 <= n <= 16.
Proof.
  intros. unfold build_ok in H.
  apply andb_prop in H as [H H9]. apply andb_prop in H as [H H8]. apply andb_prop in H as [H _].
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [_ H2].
  unfold inventory_ok in H8. apply andb_prop in H8 as [H8 _]. apply andb_prop in H8 as [H8 _].
  apply andb_prop in H8 as [N1 N2]. apply Z.leb_le in N1. apply Z.leb_le in N2.
  split; [ exact H2 | split; [ exact H3 | lia ] ].
Qed.

Lemma removed_word: forall inv l, Zlength l = LEAVES -> word_ok (removed_count inv l).
Proof.
  intros. unfold word_ok, removed_count. pose proof (Zlength_filter_le (removes inv) l).
  pose proof (Zlength_nonneg (filter (removes inv) l)). unfold LEAVES in *. rep_lia.
Qed.

Lemma retained_word: forall inv l, Zlength l = LEAVES -> word_ok (retained_count inv l).
Proof.
  intros. unfold word_ok, retained_count.
  pose proof (Zlength_filter_le (fun s => Z.odd s && negb (member (frame_of s) inv))%bool l).
  pose proof (Zlength_nonneg (filter (fun s => Z.odd s && negb (member (frame_of s) inv))%bool l)).
  unfold LEAVES in *. rep_lia.
Qed.
