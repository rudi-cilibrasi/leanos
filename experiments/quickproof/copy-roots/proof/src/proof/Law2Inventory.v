(* Law window_roots_isolated: the body of the harness's inventory_ok. *)
Require Import VST.floyd.proofauto.
Require Import LeanosRoots.proof.Defs.
Require Import LeanosRoots.proof.RootsSpecs.
Require Import LeanosRoots.proof.Law2Model.
Require Import LeanosRoots.proof.Law2Helpers.
Require Import LeanosRoots.harness.window_roots_isolated.code.
#[local] Existing Instance RootsSpecs.CS.

Ltac shl40 :=
  match goal with H: context [Int64.shl (Int64.repr 1) (Int64.repr 40)] |- _ =>
    rewrite shl64_repr in H by lia; change (1 * 2 ^ 40) with (2 ^ 40) in H;
    rewrite !Int64.unsigned_repr in H by (unfold word_ok in *; rep_lia)
  end.

Lemma body_inventory_ok: semax_body Hvprog Hgprog f_inventory_ok h_inventory_ok_spec.
Proof.
  start_function.
  forward_if (temp _t'1 (Vint (Int.repr (b2z ((n <? 1) || (16 <? n)))))).
  { forward. bdone. rewrite !Int64.unsigned_repr in H3 by (unfold word_ok in *; rep_lia). zcases. }
  { forward. bdone. rewrite !Int64.unsigned_repr in H3 by (unfold word_ok in *; rep_lia). n64. cmp64. zcases. }
  forward_if.
  { forward. entailer!. unfold inventory_ok.
    rewrite orb_true_iff, !Z.ltb_lt in H3.
    destruct (Z.leb_spec 1 n); destruct (Z.leb_spec n 16); simpl; auto; lia. }
  rewrite orb_false_iff, !Z.ltb_ge in H3.
  assert (Hn: n <= Zlength fs) by lia.
  unfold word_ok in H0.
  forward_for_simple_bound n
    (EX i: Z,
     PROP (forall k, 0 <= k < i -> Znth k fs < 2 ^ 40;
           forall k j, 0 <= k < i -> k < j < n -> Znth k fs <> Znth j fs)
     LOCAL (temp _frames p; temp _n (Vlong (Int64.repr n)))
     SEP (data_at sh (tarray tulong (Zlength fs)) (longs fs) p)).
  { entailer!. }
  { cbv beta. assert (Wi := words_Znth fs i H ltac:(lia)).
    forward.
    { entailer!. rewrite Znth_longs by lia. exact I. }
    rewrite Znth_longs by lia.
    forward_if.
    { shl40. forward. entailer!. unfold inventory_ok.
      rewrite (forallb_In_false (fun f => f <? 2 ^ 40) (sublist 0 n fs) (Znth i fs));
        [ | apply In_sublist_Znth; lia | apply Z.ltb_ge; lia ].
      rewrite andb_false_r. reflexivity. }
    shl40.
    forward_for_simple_bound n
      (EX j: Z,
       PROP (i + 1 <= j; forall j', i + 1 <= j' < j -> Znth i fs <> Znth j' fs)
       LOCAL (temp _i (Vlong (Int64.repr i)); temp _frames p; temp _n (Vlong (Int64.repr n)))
       SEP (data_at sh (tarray tulong (Zlength fs)) (longs fs) p)).
    { forward. Exists (i + 1). entailer!; try (intros; lia). }
    { cbv beta. rename i0 into j.
      assert (Wj := words_Znth fs j H ltac:(lia)).
      forward.
      { entailer!. rewrite Znth_longs by lia. exact I. }
      forward.
      { entailer!. rewrite Znth_longs by lia. exact I. }
      rewrite !Znth_longs by lia.
      forward_if.
      { forward. entailer!. unfold inventory_ok.
        destruct (distinct (sublist 0 n fs)) eqn:D; [ | rewrite andb_false_r; reflexivity ].
        exfalso. rewrite distinct_spec in D. apply (D i j).
        - rewrite Zlength_sublist by lia. lia.
        - rewrite !Znth_sublist by lia. rewrite !Z.add_0_r. apply Int64.same_if_eq in H11. apply repr64_inj; auto. }
      { forward. entailer!. intros j' Hj'.
        destruct (Z.eq_dec j' j).
        { subst j'. match goal with Hq: Int64.repr _ <> Int64.repr _ |- _ =>
            intro E; apply Hq; rewrite E; reflexivity end. }
        apply H10. lia. } }
    entailer!. split.
    - intros k Hk. destruct (Z.eq_dec k i); [ subst; auto | apply H5; lia ].
    - intros k j Hk Hj. destruct (Z.eq_dec k i); [ subst; apply H9; lia | apply H6; lia ]. }
  forward. entailer!.
  assert (Iv: inventory_ok fs n = true); [ | rewrite Iv; reflexivity ].
  unfold inventory_ok.
  rewrite (proj2 (Z.leb_le 1 n)), (proj2 (Z.leb_le n 16)) by lia. rewrite !andb_true_l.
  rewrite andb_true_iff. split.
  - apply forallb_forall. intros x Hx. apply In_Znth in Hx. destruct Hx as [k [Hk E]].
    rewrite Zlength_sublist in Hk by lia. rewrite Znth_sublist in E by lia. rewrite Z.add_0_r in E. subst x.
    apply Z.ltb_lt. apply H4. lia.
  - apply distinct_spec. intros a b Hab. rewrite Zlength_sublist in Hab by lia.
    rewrite !Znth_sublist by lia. rewrite !Z.add_0_r. apply H5; lia.
Qed.

