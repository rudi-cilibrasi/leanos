(* Law enumeration_exact: seen[] as device_read updates it.  On a function found (fewer than 16 before), entry
   |fs| gets its location and identity; on a dword, the latest entry gets that dword. *)
Require Import VST.floyd.proofauto.
Require Import LeanosEnum.proof.Defs.
Require Import LeanosEnum.proof.LawProg LeanosEnum.proof.LawRun LeanosEnum.proof.LawSpecs.
Local Open Scope Z_scope.

Lemma words_len: forall seen k, Forall (fun x: hv => Zlength (snd (snd (snd x))) = WORDS) seen ->
  0 <= k < Zlength seen -> Zlength (snd (snd (snd (Znth k seen)))) = 16.
Proof. intros seen k F Hk. exact (proj1 (Forall_Znth _ _) F k Hk). Qed.

(* Znth in range does not depend on the default value (VST's loads use the reptype's). *)
Lemma Znth_d {A: Type} (d1 d2: Inhabitant A): forall k (l: list A), 0 <= k < Zlength l ->
  @Znth A d1 k l = @Znth A d2 k l.
Proof.
  intros k l Hk. unfold Znth. rewrite !if_false by lia. apply nth_indep.
  rewrite Zlength_correct in Hk. lia.
Qed.

Lemma seen_new {d: Inhabitant hv}: forall (fs: list (Z * list Z)) seen i v,
  seen_ok fs seen -> Zlength fs < 16 ->
  seen_ok ((i, [v]) :: fs)
    (upd_Znth (Zlength fs) seen
       (hdr_v i (upd_Znth 0 (snd (snd (snd (@Znth hv d (Zlength fs) seen)))) (Vint (Int.repr v))))).
Proof.
  intros fs seen i v S Lf.
  pose proof S as (Ls0 & _ & _). unfold CAPACITY in Ls0.
  rewrite (Znth_d d (@Inhabitant_pair _ _ Inhabitant_val (@Inhabitant_pair _ _ Inhabitant_val (@Inhabitant_pair _ _ Inhabitant_val (@Inhabitant_list val)))) (Zlength fs) seen) by (pose proof (Zlength_nonneg fs); lia).
  clear d. unfold seen_ok, holds in *. destruct S as (Ls & Lw & Hs).
  unfold CAPACITY, WORDS, found in *.
  pose proof (Zlength_nonneg fs) as L0.
  pose proof (words_len seen (Zlength fs) Lw ltac:(lia)) as LX.
  split; [ rewrite upd_Znth_Zlength by lia; unfold CAPACITY; lia | ].
  split.
  - apply Forall_upd_Znth; [ exact Lw | ]. unfold hdr_v. simpl. rewrite upd_Znth_Zlength by lia. exact LX.
  - intros j Hj. rewrite Zlength_cons in Hj. simpl rev.
    destruct (Z.eq_dec j (Zlength fs)) as [->|Hne].
    + rewrite Znth_app2 by (rewrite Zlength_rev; lia). rewrite Zlength_rev, Z.sub_diag, Znth_0_cons.
      rewrite upd_Znth_same by lia. simpl fst; simpl snd.
      exists (sublist 1 16 (snd (snd (snd (Znth (Zlength fs) seen))))). split.
      * unfold words_v. simpl map. rewrite upd_Znth0_old by lia. rewrite LX. reflexivity.
      * rewrite Zlength_sublist by lia. rewrite Zlength_cons, Zlength_nil. unfold WORDS. lia.
    + rewrite Znth_app1 by (rewrite Zlength_rev; lia).
      rewrite upd_Znth_diff by lia. apply Hs. lia.
Qed.

Lemma seen_word {d: Inhabitant hv}: forall (i: Z) ws (rest: list (Z * list Z)) seen v k,
  seen_ok ((i, ws) :: rest) seen -> Zlength ws < 16 -> Zlength rest < 16 -> k = Zlength rest ->
  seen_ok ((i, ws ++ [v]) :: rest)
    (upd_Znth k seen
       (fst (@Znth hv d k seen), (fst (snd (@Znth hv d k seen)), (fst (snd (snd (@Znth hv d k seen))),
        upd_Znth (Zlength ws) (snd (snd (snd (@Znth hv d k seen)))) (Vint (Int.repr v)))))).
Proof.
  intros i ws rest seen v k S Lws Lr ->.
  pose proof S as (Ls0 & _ & _). unfold CAPACITY in Ls0.
  rewrite (Znth_d d (@Inhabitant_pair _ _ Inhabitant_val (@Inhabitant_pair _ _ Inhabitant_val (@Inhabitant_pair _ _ Inhabitant_val (@Inhabitant_list val)))) (Zlength rest) seen) by (pose proof (Zlength_nonneg rest); lia).
  clear d. unfold seen_ok, holds in *. destruct S as (Ls & Lw & Hs).
  unfold CAPACITY, WORDS, found in *.
  rewrite Zlength_cons in Hs.
  pose proof (Zlength_nonneg rest) as L0.
  assert (Hk := Hs (Zlength rest) ltac:(lia)).
  simpl rev in Hk. rewrite Znth_app2 in Hk by (rewrite Zlength_rev; lia).
  rewrite Zlength_rev, Z.sub_diag, Znth_0_cons in Hk.
  destruct Hk as (tail & Ex & Lt). simpl fst in Ex; simpl snd in Ex, Lt.
  pose proof (Zlength_nonneg ws) as Lw0.
  split; [ rewrite upd_Znth_Zlength by lia; unfold CAPACITY; lia | ].
  split.
  - apply Forall_upd_Znth; [ exact Lw | ]. simpl. rewrite upd_Znth_Zlength.
    + exact (words_len seen (Zlength rest) Lw ltac:(lia)).
    + rewrite (words_len seen (Zlength rest) Lw ltac:(lia)). lia.
  - intros j Hj. rewrite Zlength_cons in Hj. simpl rev.
    destruct (Z.eq_dec j (Zlength rest)) as [->|Hne].
    + rewrite Znth_app2 by (rewrite Zlength_rev; lia). rewrite Zlength_rev, Z.sub_diag, Znth_0_cons.
      rewrite upd_Znth_same by lia. rewrite Ex. unfold hdr_v. simpl fst; simpl snd.
      exists (sublist 1 (Zlength tail) tail). unfold words_v in *.
      assert (Lt1: 1 <= Zlength tail) by lia.
      split.
      * assert (EW: upd_Znth (Zlength ws) (map (fun w => Vint (Int.repr w)) ws ++ tail) (Vint (Int.repr v)) =
                    map (fun w => Vint (Int.repr w)) (ws ++ [v]) ++ sublist 1 (Zlength tail) tail).
        { rewrite upd_Znth_app2 by (rewrite Zlength_map; lia).
          rewrite Zlength_map, Z.sub_diag. rewrite upd_Znth0_old by lia.
          rewrite map_app, <- app_assoc. reflexivity. }
        rewrite EW. reflexivity.
      * rewrite Zlength_sublist by lia. rewrite Zlength_app, Zlength_cons, Zlength_nil. unfold WORDS. lia.
    + rewrite Znth_app1 by (rewrite Zlength_rev; lia).
      rewrite upd_Znth_diff by lia.
      assert (X := Hs j ltac:(lia)). simpl rev in X. rewrite Znth_app1 in X by (rewrite Zlength_rev; lia).
      exact X.
Qed.
