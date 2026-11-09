(* Law enumeration_exact: on OK, entry k of the published snapshot and entry k of the device's seen[] are the
   same header: the k-th found, whole. *)
Require Import VST.floyd.proofauto.
Require Import LeanosEnum.proof.Defs.
Require LeanosEnum.proof.EnumSpecs.
Require Import LeanosEnum.proof.LawProg LeanosEnum.proof.LawRun LeanosEnum.proof.LawSpecs LeanosEnum.proof.LawSeen.
Local Open Scope Z_scope.

Lemma seen_full {d: Inhabitant hv}: forall (fs: list (Z * list Z)) seen k,
  seen_ok fs seen -> Forall complete fs -> Zlength fs <= 16 -> 0 <= k < Zlength fs ->
  @Znth hv d k seen = hdr_v (fst (Znth k (rev fs))) (words_v (snd (Znth k (rev fs)))).
Proof.
  intros fs seen k S C L16 Hk. unfold seen_ok, holds in S. destruct S as (Ls & Lw & Hs).
  unfold CAPACITY, found in *.
  rewrite (Znth_d d (@Inhabitant_pair _ _ Inhabitant_val (@Inhabitant_pair _ _ Inhabitant_val
             (@Inhabitant_pair _ _ Inhabitant_val (@Inhabitant_list val)))) k seen) by lia.
  clear d.
  destruct (Hs k Hk) as (tail & E & L). rewrite E.
  assert (Cf: Zlength (snd (Znth k (rev fs))) = 16).
  { assert (Cr: Forall complete (rev fs)) by (apply Forall_rev; exact C).
    rewrite <- Zlength_rev in Hk. exact (proj1 (Forall_Znth _ _) Cr k Hk). }
  assert (Lt: Zlength tail = 0) by (unfold WORDS in L; lia).
  apply Zlength_nil_inv in Lt. subst tail. rewrite app_nil_r. reflexivity.
Qed.

Lemma pub_full {d: Inhabitant hv}: forall (fs: list (Z * list Z)) (rest: list hv) k, 0 <= k < Zlength fs ->
  @Znth hv d k (map EnumSpecs.header_val (rev fs) ++ rest) =
  hdr_v (fst (Znth k (rev fs))) (words_v (snd (Znth k (rev fs)))).
Proof.
  intros fs rest k Hk. rewrite Znth_app1 by (rewrite Zlength_map, Zlength_rev; lia).
  rewrite Znth_map by (rewrite Zlength_rev; lia). reflexivity.
Qed.

Lemma found_index: forall (fs: list (Z * list Z)) k, Forall (fun f => 0 <= fst f < FUNCTIONS) fs ->
  0 <= k < Zlength fs -> 0 <= fst (Znth k (rev fs)) < FUNCTIONS.
Proof.
  intros fs k F Hk. assert (Fr: Forall (fun f => 0 <= fst f < FUNCTIONS) (rev fs)) by (apply Forall_rev; exact F).
  rewrite <- Zlength_rev in Hk. exact (proj1 (Forall_Znth _ _) Fr k Hk).
Qed.

Lemma found_words: forall (fs: list (Z * list Z)) k, Forall complete fs ->
  0 <= k < Zlength fs -> Zlength (snd (Znth k (rev fs))) = 16.
Proof.
  intros fs k F Hk. assert (Fr: Forall complete (rev fs)) by (apply Forall_rev; exact F).
  rewrite <- Zlength_rev in Hk. exact (proj1 (Forall_Znth _ _) Fr k Hk).
Qed.

Lemma words_Znth {d: Inhabitant val}: forall ws w, 0 <= w < Zlength ws ->
  @Znth val d w (words_v ws) = Vint (Int.repr (Znth w ws)).
Proof.
  intros ws w Hw. unfold words_v.
  rewrite (Znth_d d Inhabitant_val) by (rewrite Zlength_map; lia).
  rewrite Znth_map by lia. reflexivity.
Qed.
