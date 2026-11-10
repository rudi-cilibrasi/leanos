(* Law image_exact: the body of the harness's check_policy. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import LeanosDeviceProgramImage.harness.image_exact.code.
Require Import LeanosDeviceProgramImage.proof.Defs.
Require Import LeanosDeviceProgramImage.proof.LawProg LeanosDeviceProgramImage.proof.LawSpecs
  LeanosDeviceProgramImage.proof.LawLib LeanosDeviceProgramImage.proof.LawSplit
  LeanosDeviceProgramImage.proof.LawFocus.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Lemma desc_eqb_refl: forall d, desc_eqb d d = true.
Proof. intros. unfold desc_eqb. rewrite !Z.eqb_refl. reflexivity. Qed.

Ltac unfocus :=
  match goal with |- context [?A -* ?B] => sep_apply (modus_ponens_wand A B) end.

(* A branch of an && chain of comparisons of equal values. *)
Ltac eq_true_branch := entailer!; rewrite ?Int.eq_true, ?Int64.eq_true; reflexivity.
Ltac eq_false_branch :=
  exfalso;
  match goal with
  | H: ?a <> ?a |- _ => apply H; reflexivity
  | H: Int.repr ?a <> Int.repr ?a |- _ => apply H; reflexivity
  | H: Int64.repr ?a <> Int64.repr ?a |- _ => apply H; reflexivity
  | H: Int.repr 1 = Int.zero |- _ => inversion H
  | H: Int.repr 1 = Int.repr 0 |- _ => inversion H
  end.
Ltac gp_one := forward_call (Int.repr 1);
  try (match goal with |- ENTAIL _, _ |-- _ => idtac end;
       entailer!; rewrite ?Int.eq_true, ?Int64.eq_true; reflexivity).

Lemma body_check_policy : semax_body Vlaw Glaw f_check_policy check_policy_spec.
Proof.
  start_function.
  destruct H as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & PS & PLs & PFs & PD & PLd & PFd).
  destruct H0 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & QLs & QFs & Q9 & QLd & QFd).
  destruct H1 as (ss & ds & ->).
  unfold MAX_SINKS, MAX_DESCS in *.
  rewrite !pol_val_vals, pol_rep_vals, !pol_split. unfold pol_fields. Intros.
  unfold store; cbn [pl_present pl_dma pl_window pl_cfg_read pl_cfg_write pl_cmd_clear pl_cmd_set pl_sink_count
    pl_sinks pl_desc_count pl_descs].
  unfold MAX_SINKS, MAX_DESCS.
  forward. forward.
  forward_if (temp _t'1 (Vint (Int.repr 1))).
  { forward. forward. forward. eq_true_branch. }
  { eq_false_branch. }
  forward_if (temp _t'2 (Vint (Int.repr 1))).
  { forward. forward. forward. eq_true_branch. }
  { eq_false_branch. }
  gp_one.
  forward. forward.
  forward_if (temp _t'3 (Vint (Int.repr 1))).
  { forward. forward. forward. eq_true_branch. }
  { eq_false_branch. }
  gp_one.
  forward. forward.
  forward_if (temp _t'4 (Vint (Int.repr 1))).
  { forward. forward. forward. eq_true_branch. }
  { eq_false_branch. }
  gp_one.
  forward. forward.
  forward_if (temp _t'5 (Vint (Int.repr 1))).
  { forward. forward. forward. eq_true_branch. }
  { eq_false_branch. }
  gp_one.
  set (S := pl_sink_count P) in *. set (D := pl_desc_count P) in *.
  assert (LP: Zlength (pl_sinks P ++ sublist S 8 (pl_sinks Q)) = 8) by (rewrite Zlength_app, Zlength_sublist; lia).
  forward_for_simple_bound 8 (EX i: Z,
    PROP ()
    LOCAL (temp _got g; temp _want w; temp _prior q)
    SEP (pol_fields gsh g (Vint (Int.repr (pl_present P))) (Vint (Int.repr (pl_dma P)))
          (Vint (Int.repr (pl_window P))) (Vlong (Int64.repr (pl_cfg_read P))) (Vlong (Int64.repr (pl_cfg_write P)))
          (Vint (Int.repr (pl_cmd_clear P))) (Vint (Int.repr (pl_cmd_set P))) (Vint (Int.repr S))
          (words_val (pl_sinks P ++ sublist S 8 (pl_sinks Q))) (Vint (Int.repr D))
          (map desc_val (pl_descs P ++ sublist D 16 (pl_descs Q)));
         pol_fields wsh w (Vint (Int.repr (pl_present P))) (Vint (Int.repr (pl_dma P)))
          (Vint (Int.repr (pl_window P))) (Vlong (Int64.repr (pl_cfg_read P))) (Vlong (Int64.repr (pl_cfg_write P)))
          (Vint (Int.repr (pl_cmd_clear P))) (Vint (Int.repr (pl_cmd_set P))) (Vint (Int.repr S))
          (words_val (pl_sinks P) ++ ss) (Vint (Int.repr D)) (map desc_val (pl_descs P) ++ ds);
         pol_fields qsh q (Vint (Int.repr (pl_present Q))) (Vint (Int.repr (pl_dma Q)))
          (Vint (Int.repr (pl_window Q))) (Vlong (Int64.repr (pl_cfg_read Q))) (Vlong (Int64.repr (pl_cfg_write Q)))
          (Vint (Int.repr (pl_cmd_clear Q))) (Vint (Int.repr (pl_cmd_set Q))) (Vint (Int.repr (pl_sink_count Q)))
          (words_val (pl_sinks Q)) (Vint (Int.repr (pl_desc_count Q))) (map desc_val (pl_descs Q))))%assert.
  { unfold pol_fields. entailer!. }
  { unfold pol_fields. Intros. forward.
    forward_if.
    - assert (E1: Znth i (pl_sinks P ++ sublist S 8 (pl_sinks Q)) = Znth i (pl_sinks P)) by (rewrite Znth_app1; lia).
      assert (E2: forall dv, @Znth val dv i (words_val (pl_sinks P) ++ ss) = Vint (Int.repr (Znth i (pl_sinks P))))
        by (intros; rewrite Znth_app1 by (rewrite Zlength_map; lia); rewrite Znth_map by lia; reflexivity).
      forward. rewrite E1.
      forward; [ rewrite E2; entailer! | rewrite E2 ].
      gp_one. unfold pol_fields. entailer!.
    - assert (E1: Znth i (pl_sinks P ++ sublist S 8 (pl_sinks Q)) = Znth i (pl_sinks Q))
        by (rewrite Znth_app2, Znth_sublist by lia; f_equal; lia).
      forward. rewrite E1. forward.
      gp_one. unfold pol_fields. entailer!. }
  assert (LD: Zlength (pl_descs P ++ sublist D 16 (pl_descs Q)) = 16) by (rewrite Zlength_app, Zlength_sublist; lia).
  forward_for_simple_bound 16 (EX i: Z,
    PROP ()
    LOCAL (temp _got g; temp _want w; temp _prior q)
    SEP (pol_fields gsh g (Vint (Int.repr (pl_present P))) (Vint (Int.repr (pl_dma P)))
          (Vint (Int.repr (pl_window P))) (Vlong (Int64.repr (pl_cfg_read P))) (Vlong (Int64.repr (pl_cfg_write P)))
          (Vint (Int.repr (pl_cmd_clear P))) (Vint (Int.repr (pl_cmd_set P))) (Vint (Int.repr S))
          (words_val (pl_sinks P ++ sublist S 8 (pl_sinks Q))) (Vint (Int.repr D))
          (map desc_val (pl_descs P ++ sublist D 16 (pl_descs Q)));
         pol_fields wsh w (Vint (Int.repr (pl_present P))) (Vint (Int.repr (pl_dma P)))
          (Vint (Int.repr (pl_window P))) (Vlong (Int64.repr (pl_cfg_read P))) (Vlong (Int64.repr (pl_cfg_write P)))
          (Vint (Int.repr (pl_cmd_clear P))) (Vint (Int.repr (pl_cmd_set P))) (Vint (Int.repr S))
          (words_val (pl_sinks P) ++ ss) (Vint (Int.repr D)) (map desc_val (pl_descs P) ++ ds);
         pol_fields qsh q (Vint (Int.repr (pl_present Q))) (Vint (Int.repr (pl_dma Q)))
          (Vint (Int.repr (pl_window Q))) (Vlong (Int64.repr (pl_cfg_read Q))) (Vlong (Int64.repr (pl_cfg_write Q)))
          (Vint (Int.repr (pl_cmd_clear Q))) (Vint (Int.repr (pl_cmd_set Q))) (Vint (Int.repr (pl_sink_count Q)))
          (words_val (pl_sinks Q)) (Vint (Int.repr (pl_desc_count Q))) (map desc_val (pl_descs Q))))%assert.
  { unfold pol_fields. entailer!. }
  { unfold pol_fields. Intros. forward.
    forward_if.
    - assert (E1: forall dv, @Znth desc_t dv i (map desc_val (pl_descs P ++ sublist D 16 (pl_descs Q))) =
                             desc_val (Znth i (pl_descs P)))
        by (intros; rewrite Znth_map by lia; rewrite Znth_app1 by lia; reflexivity).
      assert (E2: forall dv, @Znth desc_t dv i (map desc_val (pl_descs P) ++ ds) = desc_val (Znth i (pl_descs P)))
        by (intros; rewrite Znth_app1 by (rewrite Zlength_map; lia); rewrite Znth_map by lia; reflexivity).
      assert (Di: desc_wf (Znth i (pl_descs P))) by (apply Forall_Znth; auto; lia).
      sep_apply (descs_focus gsh (map desc_val (pl_descs P ++ sublist D 16 (pl_descs Q))) g i ltac:(lia)).
      sep_apply (descs_focus wsh (map desc_val (pl_descs P) ++ ds) w i ltac:(lia)).
      rewrite E1, E2. Intros.
      forward_call (gsh, field_address t_policy (DOT _descs SUB i) g, Znth i (pl_descs P),
                    wsh, field_address t_policy (DOT _descs SUB i) w, Znth i (pl_descs P)).
      { entailer!. desc_arg. desc_arg. }
      rewrite desc_eqb_refl.
      gp_one.
      unfocus. unfocus. unfold pol_fields. entailer!.
    - assert (E1: forall dv, @Znth desc_t dv i (map desc_val (pl_descs P ++ sublist D 16 (pl_descs Q))) =
                             desc_val (Znth i (pl_descs Q)))
        by (intros; rewrite Znth_map by lia; rewrite Znth_app2, Znth_sublist by lia; do 2 f_equal; lia).
      assert (E2: forall dv, @Znth desc_t dv i (map desc_val (pl_descs Q)) = desc_val (Znth i (pl_descs Q)))
        by (intros; rewrite Znth_map by lia; reflexivity).
      assert (Di: desc_wf (Znth i (pl_descs Q))) by (apply Forall_Znth; auto; lia).
      sep_apply (descs_focus gsh (map desc_val (pl_descs P ++ sublist D 16 (pl_descs Q))) g i ltac:(lia)).
      sep_apply (descs_focus qsh (map desc_val (pl_descs Q)) q i ltac:(lia)).
      rewrite E1, E2. Intros.
      forward_call (gsh, field_address t_policy (DOT _descs SUB i) g, Znth i (pl_descs Q),
                    qsh, field_address t_policy (DOT _descs SUB i) q, Znth i (pl_descs Q)).
      { entailer!. desc_arg. desc_arg. }
      rewrite desc_eqb_refl.
      gp_one.
      unfocus. unfocus. unfold pol_fields. entailer!. }
  rewrite !pol_val_vals, pol_rep_vals, !pol_split. unfold pol_fields, store.
  cbn [pl_present pl_dma pl_window pl_cfg_read pl_cfg_write pl_cmd_clear pl_cmd_set pl_sink_count
    pl_sinks pl_desc_count pl_descs].
  unfold MAX_SINKS, MAX_DESCS. entailer!.
Qed.
