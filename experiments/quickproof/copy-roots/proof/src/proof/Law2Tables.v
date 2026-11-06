(* Law window_roots_isolated: the body of the harness's tables_at. *)
Require Import VST.floyd.proofauto.
Require Import LeanosRoots.proof.Defs.
Require Import LeanosRoots.proof.RootsSpecs.
Require Import LeanosRoots.proof.Law2Model.
Require Import LeanosRoots.proof.Law2Helpers.
Require Import LeanosRoots.harness.window_roots_isolated.code.
#[local] Existing Instance RootsSpecs.CS.

Lemma clear64: forall x ig, Int64.and (Int64.repr x) (Int64.not (Int64.repr ig)) = Int64.repr (clear_bits x ig).
Proof. intros. rewrite not64_repr, and64_repr. reflexivity. Qed.

Ltac uns64 :=
  repeat match goal with Hc: context [Int64.unsigned (Int64.repr ?a)] |- _ =>
    rewrite (Int64.unsigned_repr a) in Hc by (unfold word_ok in *; rep_lia) end.

Ltac ldl := forward; try (entailer!; rewrite Znth_longs by lia; exact I); try rewrite Znth_longs by lia.

Lemma body_tables_at: semax_body Hvprog Hgprog f_tables_at h_tables_at_spec.
Proof.
  start_function.
  destruct rv as [pm pp pdl ptl]. destruct H as (L1 & L2 & L3 & L4 & W1 & W2 & W3 & W4).
  cbn [pml4 pdpt pd pt] in *. unfold root_val. cbn [pml4 pdpt pd pt].
  assert (Wm0 := words_Znth pm 0 W1 ltac:(lia)). assert (Wp0 := words_Znth pp 0 W2 ltac:(lia)).
  forward_call (phys, 1).
  ldl.
  forward_if (temp _t'2 (Vint (Int.repr (b2z (negb ((clear_bits (Znth 0 pm) ig =? table_entry phys 1) &&
                                                    (clear_bits (Znth 0 pp) ig =? table_entry phys 2))))))).
  { forward. bdone. rewrite clear64 in H. apply repr64_neq in H. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. }
  { forward_call (phys, 2). ldl. forward. bdone. rewrite !clear64 in *.
    rewrite eq64_w in H by first [ apply w_land; assumption | apply table_entry_word ].
    rewrite H, cmpu_ne64, eq64_w by first [ apply w_land; assumption | apply table_entry_word ]. reflexivity. }
  forward_if.
  { forward. entailer!. unfold tables_ok. cbn [pml4 pdpt pd pt]. rewrite H. reflexivity. }
  forward_for_simple_bound 512
    (EX i: Z,
     PROP (1 <= i; forall j, 1 <= j < i -> Znth j pm = 0; forall j, 1 <= j < i -> Znth j pp = 0)
     LOCAL (temp _r r; temp _phys (Vlong (Int64.repr phys)); temp _ignore (Vlong (Int64.repr ig)))
     SEP (data_at sh t_root (root_val (mkroot pm pp pdl ptl)) r)).
  { entailer!. }
  { cbv beta. unfold root_val; cbn [pml4 pdpt pd pt]. assert (Wm := words_Znth pm i W1 ltac:(lia)). assert (Wp := words_Znth pp i W2 ltac:(lia)).
    ldl.
    forward_if (temp _t'4 (Vint (Int.repr (b2z (negb ((Znth i pm =? 0) && (Znth i pp =? 0))))))).
    { forward. bdone. match goal with Hc: Int64.repr _ <> Int64.repr _ |- _ => apply repr64_neq in Hc;
        rewrite (proj2 (Z.eqb_neq _ _) Hc) end. reflexivity. }
    { ldl. forward. bdone. unfold Int64.zero in *. match goal with Hc: Int64.repr _ = Int64.repr _ |- _ =>
        apply repr64_inj in Hc; [ rewrite Hc | auto | unfold word_ok; rep_lia ] end.
      rewrite cmpu_ne64, eq64_w by (auto; unfold word_ok; rep_lia). reflexivity. }
    forward_if.
    { forward. entailer!. unfold tables_ok. cbn [pml4 pdpt pd pt].
      rewrite (forallb_In_false _ (map (Z.add 1) (idx 511)) i).
      - rewrite andb_false_r. reflexivity.
      - apply in_map_iff. exists (i - 1). split; [ lia | apply In_idx; lia ].
      - destruct ((Znth i pm =? 0) && (Znth i pp =? 0))%bool; [ discriminate | reflexivity ]. }
    { forward. entailer!.
      destruct (Z.eqb_spec (Znth i pm) 0); destruct (Z.eqb_spec (Znth i pp) 0); simpl in *; try discriminate.
      split; intros j Hj; (destruct (Z.eq_dec j i); [ subst; auto | ]); first [ apply H4 | apply H5 ]; lia. } }
  Intros.
  forward_for_simple_bound 512
    (EX i: Z,
     PROP (forall j, 0 <= j < i -> clear_bits (Znth j pdl) ig = pd_entry phys j)
     LOCAL (temp _r r; temp _phys (Vlong (Int64.repr phys)); temp _ignore (Vlong (Int64.repr ig)))
     SEP (data_at sh t_root (root_val (mkroot pm pp pdl ptl)) r)).
  { entailer!. }
  { cbv beta. assert (Wd := words_Znth pdl i W3 ltac:(lia)).
    forward_if (temp _t'5 (Vlong (Int64.repr (pd_entry phys i)))).
    { uns64.
      forward_call (phys, 3 + i).
      forward. entailer!. unfold pd_entry. rewrite (proj2 (Z.ltb_lt i 8)) by lia. reflexivity. }
    { uns64.
      forward. entailer!. unfold pd_entry. rewrite (proj2 (Z.ltb_ge i 8)) by lia. reflexivity. }
    unfold root_val; cbn [pml4 pdpt pd pt].
    ldl.
    assert (Wpe: word_ok (pd_entry phys i)) by (unfold pd_entry; destruct (i <? 8);
      [ apply table_entry_word | unfold word_ok; rep_lia ]).
    forward_if.
    { forward. entailer!. rewrite clear64 in *.
      match goal with Hc: Int64.repr _ <> Int64.repr _ |- _ => apply repr64_neq in Hc; rename Hc into Hne end.
      unfold tables_ok. cbn [pml4 pdpt pd pt].
      rewrite (forallb_idx_false _ 512 i) by (auto; apply Z.eqb_neq; auto).
      rewrite andb_false_r. reflexivity. }
    { forward. entailer!. rewrite clear64 in *.
      match goal with Hc: Int64.eq _ _ = true |- _ => apply Int64.same_if_eq in Hc end.
      match goal with Hc: Int64.repr _ = Int64.repr _ |- _ =>
        apply repr64_inj in Hc; [ rename Hc into Heq | apply w_land; auto | auto ] end.
      intros j Hj. destruct (Z.eq_dec j i); [ subst; auto | ].
      match goal with Hf: forall j, _ -> clear_bits _ _ = _ |- _ => apply Hf; lia end. } }
  forward. entailer!.
  assert (T: tables_ok (mkroot pm pp pdl ptl) phys ig = true); [ | rewrite T; reflexivity ].
  unfold tables_ok. cbn [pml4 pdpt pd pt]. rewrite H.
  rewrite andb_true_l. apply andb_true_iff. split.
  - apply forallb_forall. intros j Hj. apply in_map_iff in Hj. destruct Hj as [k [E Hk]]. apply In_idx in Hk.
    subst j.
    match goal with Hf: forall j, 1 <= j < 512 -> Znth j pm = 0 |- _ => rewrite Hf by lia end.
    match goal with Hf: forall j, 1 <= j < 512 -> Znth j pp = 0 |- _ => rewrite Hf by lia end.
    reflexivity.
  - apply forallb_forall. intros j Hj. apply In_idx in Hj. apply Z.eqb_eq.
    match goal with Hf: forall j, 0 <= j < 512 -> clear_bits _ _ = _ |- _ => apply Hf; lia end.
Qed.
