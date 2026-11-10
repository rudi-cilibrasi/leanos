(* Law image_exact: the body of admission_case: the law's expectation (its within, Service and Source as the
   harness writes them) against the unit's answer. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import LeanosDeviceProgramImage.harness.image_exact.code.
Require Import LeanosDeviceProgramImage.proof.Defs.
Require LeanosDeviceProgramImage.proof.Specs.
Require Import LeanosDeviceProgramImage.proof.LawProg LeanosDeviceProgramImage.proof.LawSpecs
  LeanosDeviceProgramImage.proof.LawLib LeanosDeviceProgramImage.proof.LawLaw.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

(* Source(t, p, max) clause by clause, in the harness's order. *)
Definition src_l (T: target) (P M: policy) : list bool :=
  [tg_bus T =? 0; tg_dev T =? 0; tg_fn T =? 0; tg_id T =? 4294967295; tg_window T =? pl_window M;
   negb (pl_present P =? 0); pl_sink_count P =? 0; pl_desc_count P =? 0; pl_window P <=? pl_window M;
   pl_dma P =? 0; pl_cfg_read P =? 0; pl_cfg_write P =? 0; pl_cmd_clear P =? 0; pl_cmd_set P =? 0].

Definition src_pre (T: target) (P M: policy) (k: nat) : bool := fold_left andb (firstn k (src_l T P M)) true.

Lemma src_pre_S: forall T P M k, (k < 14)%nat ->
  src_pre T P M (S k) = (src_pre T P M k && nth k (src_l T P M) false)%bool.
Proof. intros T P M k Hk. do 14 (destruct k as [|k]; [ reflexivity | ]). lia. Qed.

Lemma source_pre: forall T P M, source T P M = src_pre T P M 14.
Proof. reflexivity. Qed.

Lemma Int_eq_m1: forall x, u32_ok x -> Int.eq (Int.repr x) (Int.repr (-1)) = (x =? 4294967295).
Proof.
  intros x X. unfold u32_ok in X. unfold Int.eq. rewrite Int.unsigned_repr by lia.
  change (Int.unsigned (Int.repr (-1))) with 4294967295.
  destruct (zeq x 4294967295); destruct (Z.eqb_spec x 4294967295); auto; lia.
Qed.

Ltac unfocus :=
  match goal with |- context [?A -* ?B] => sep_apply (modus_ponens_wand A B) end.

Ltac bsub :=
  repeat match goal with
  | H: ?c = true |- context [?c] => match type of c with bool => rewrite H end
  | H: ?c = false |- context [?c] => match type of c with bool => rewrite H end
  end.

Ltac src_fin :=
  bsub; cbn [andb nth src_l]; rewrite ?Int_eq_m1 by assumption; bfix; bdec.

Local Opaque within service source.

Lemma body_admission_case : semax_body Vlaw Glaw f_admission_case admission_case_spec.
Proof.
  start_function.
  destruct lv as (c0 & rest). simpl fst in *. subst c0.
  forward_call (Tsh, v_t). Intros T.
  forward_call (Tsh, v_want). Intros W.
  forward_call (Tsh, v_p, true). Intros P.
  forward_call (Tsh, v_max, true). Intros M.
  cbn iota in *.
  match goal with H: policy_bounded P |- _ => pose proof H as PB end.
  match goal with H: policy_bounded M |- _ => pose proof H as MB end.
  pose proof PB as [PW _]. pose proof MB as [MW _].
  assert (TWt: target_wf T) by auto. assert (TWw: target_wf W) by auto.
  forward.
  forward_if (EX e: Z,
    PROP ()
    LOCAL (temp _expect (Vint (Int.repr e)); temp _got (Vint (Int.repr e));
           lvar _max (Tstruct _wifi_policy noattr) v_max; lvar _p (Tstruct _wifi_policy noattr) v_p;
           lvar _want (Tstruct _wifi_target noattr) v_want; lvar _t (Tstruct _wifi_target noattr) v_t; temp _m m)
    SEP (data_at Tsh t_target (target_val T) v_t; data_at Tsh t_target (target_val W) v_want;
         data_at Tsh t_policy (policy_val P) v_p; data_at Tsh t_policy (policy_val M) v_max;
         data_at msh t_law (Vint (Int.repr c), rest) m))%assert.
  - forward_call (Tsh, v_p, P, Tsh, v_max, M).
    rewrite (pol_cs Tsh (policy_val P) v_p), (pol_cs Tsh (policy_val M) v_max).
    forward_call (Tsh, v_p, P, Tsh, v_max, M).
    forward.
    rewrite <- !pol_cs.
    Exists (Z.b2z (within P M)). entailer!.
  - forward.
    forward_if.
    + forward_call (Tsh, v_t, T, Tsh, v_want, W).
      forward_if (temp _t'4 (Vint (Int.repr (Z.b2z (target_eqb T W && negb (pl_present P =? 0))%bool)))).
      { forward. forward. entailer!. bfix. bsub. destruct PW as (PW1 & _).
        rewrite Int_eq_u32 by (auto; unfold u32_ok; rep_lia). simpl andb.
        destruct (pl_present P =? 0); reflexivity. }
      { forward. entailer!. bfix. bsub. reflexivity. }
      forward_if (temp _t'5 (Vint (Int.repr (Z.b2z (service T P W M))))).
      { forward_call (Tsh, v_p, P, Tsh, v_max, M). forward. entailer!. Transparent service. unfold service.
        bfix. bsub. destruct (within P M); reflexivity. }
      { forward. entailer!. Transparent service. unfold service. bfix. bsub. reflexivity. }
      forward.
      rewrite (pol_cs Tsh (policy_val P) v_p), (pol_cs Tsh (policy_val M) v_max),
        (tg_cs Tsh (target_val T) v_t), (tg_cs Tsh (target_val W) v_want).
      forward_call (Tsh, v_t, T, Tsh, v_p, P, Tsh, v_want, W, Tsh, v_max, M).
      forward.
      rewrite <- !pol_cs, <- !tg_cs.
      Exists (Z.b2z (service T P W M)). entailer!.
    + assert (C4: c = 4) by (bfix; lia).
      destruct TWt as (T1 & T2 & T3 & T4 & T5 & T6).
      destruct PW as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & _ & _ & P9 & _).
      destruct MW as (M1 & M2 & M3 & _).
      forward.
      forward_if (temp _t'8 (Vint (Int.repr (Z.b2z (src_pre T P M 2))))).
      { forward. forward. entailer!. unfold src_pre; simpl. bfix. bdec. }
      { forward. entailer!. unfold src_pre; simpl. bfix. bdec. }
      forward_if (temp _t'9 (Vint (Int.repr (Z.b2z (src_pre T P M 3))))).
      { forward. forward. entailer!. rewrite (src_pre_S T P M 2) by lia. bfix. src_fin. }
      { forward. entailer!. rewrite (src_pre_S T P M 2) by lia. bfix. bsub. reflexivity. }
      forward_if (temp _t'10 (Vint (Int.repr (Z.b2z (src_pre T P M 4))))).
      { forward. forward. entailer!. rewrite (src_pre_S T P M 3) by lia. bfix. src_fin. }
      { forward. entailer!. rewrite (src_pre_S T P M 3) by lia. bfix. bsub. reflexivity. }
      forward_if (temp _t'11 (Vint (Int.repr (Z.b2z (src_pre T P M 5))))).
      { forward. forward. forward. entailer!. rewrite (src_pre_S T P M 4) by lia. bfix. src_fin. }
      { forward. entailer!. rewrite (src_pre_S T P M 4) by lia. bfix. bsub. reflexivity. }
      forward_if (temp _t'12 (Vint (Int.repr (Z.b2z (src_pre T P M 6))))).
      { forward. forward. entailer!. rewrite (src_pre_S T P M 5) by lia. bfix. src_fin. }
      { forward. entailer!. rewrite (src_pre_S T P M 5) by lia. bfix. bsub. reflexivity. }
      forward_if (temp _t'13 (Vint (Int.repr (Z.b2z (src_pre T P M 7))))).
      { forward. forward. entailer!. rewrite (src_pre_S T P M 6) by lia. bfix. src_fin. }
      { forward. entailer!. rewrite (src_pre_S T P M 6) by lia. bfix. bsub. reflexivity. }
      forward_if (temp _t'14 (Vint (Int.repr (Z.b2z (src_pre T P M 8))))).
      { forward. forward. entailer!. rewrite (src_pre_S T P M 7) by lia. bfix. src_fin. }
      { forward. entailer!. rewrite (src_pre_S T P M 7) by lia. bfix. bsub. reflexivity. }
      forward_if (temp _t'15 (Vint (Int.repr (Z.b2z (src_pre T P M 9))))).
      { forward. forward. forward. entailer!. rewrite (src_pre_S T P M 8) by lia. bfix. src_fin. }
      { forward. entailer!. rewrite (src_pre_S T P M 8) by lia. bfix. bsub. reflexivity. }
      forward_if (temp _t'16 (Vint (Int.repr (Z.b2z (src_pre T P M 10))))).
      { forward. forward. entailer!. rewrite (src_pre_S T P M 9) by lia. bfix. src_fin. }
      { forward. entailer!. rewrite (src_pre_S T P M 9) by lia. bfix. bsub. reflexivity. }
      forward_if (temp _t'17 (Vint (Int.repr (Z.b2z (src_pre T P M 11))))).
      { forward. forward. entailer!. rewrite (src_pre_S T P M 10) by lia. bfix. src_fin. }
      { forward. entailer!. rewrite (src_pre_S T P M 10) by lia. bfix. bsub. reflexivity. }
      forward_if (temp _t'18 (Vint (Int.repr (Z.b2z (src_pre T P M 12))))).
      { forward. forward. entailer!. rewrite (src_pre_S T P M 11) by lia. bfix. src_fin. }
      { forward. entailer!. rewrite (src_pre_S T P M 11) by lia. bfix. bsub. reflexivity. }
      forward_if (temp _t'19 (Vint (Int.repr (Z.b2z (src_pre T P M 13))))).
      { forward. forward. entailer!. rewrite (src_pre_S T P M 12) by lia. bfix. src_fin. }
      { forward. entailer!. rewrite (src_pre_S T P M 12) by lia. bfix. bsub. reflexivity. }
      forward_if (temp _t'20 (Vint (Int.repr (Z.b2z (src_pre T P M 14))))).
      { forward. forward. entailer!. rewrite (src_pre_S T P M 13) by lia. bfix. src_fin. }
      { forward. entailer!. rewrite (src_pre_S T P M 13) by lia. bfix. bsub. reflexivity. }
      forward.
      rewrite (pol_cs Tsh (policy_val P) v_p), (pol_cs Tsh (policy_val M) v_max), (tg_cs Tsh (target_val T) v_t).
      forward_call (Tsh, v_t, T, Tsh, v_p, P, Tsh, v_max, M).
      forward.
      rewrite <- !pol_cs, <- !tg_cs.
      Exists (Z.b2z (source T P M)). rewrite source_pre. entailer!.
  - Intros e.
    forward_call (Int.repr 1).
    { entailer!. rewrite Int.eq_true. reflexivity. }
    try_clean_up_stackframe.
    sep_apply (data_at_data_at_ Tsh t_policy (policy_val P) v_p).
    sep_apply (data_at_data_at_ Tsh t_policy (policy_val M) v_max).
    sep_apply (data_at_data_at_ Tsh t_target (target_val T) v_t).
    sep_apply (data_at_data_at_ Tsh t_target (target_val W) v_want).
    go_lower. cancel.
Qed.
