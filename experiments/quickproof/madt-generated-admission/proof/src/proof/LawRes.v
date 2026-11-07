(* Law admission_exact: the body of the harness's admission-result export against result_query_spec Ora_law: its
   checks follow from the call the model expects (result_call); the answer it records keeps the oracle's invariant,
   and after the fourth the verdict is the model's result_check, writing word 3 on OK. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosMadtAdmission.harness.admission_exact.code.
Require Import LeanosMadtAdmission.proof.Defs.
Require Import LeanosMadtAdmission.proof.MgaSpecs.
Require Import LeanosMadtAdmission.proof.LawProg LeanosMadtAdmission.proof.LawDefs LeanosMadtAdmission.proof.LawFacts
  LeanosMadtAdmission.proof.LawLib.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Existing Instance LawProg.LCS.

Definition Gres : funspecs := [any_u64_spec; gp_assert_spec; stop_spec].

Ltac res_stop q p x s a FCa r :=
  forward_call (q, vi (ls_expect s), vi (ls_verdict s), r);
  rewrite <- (answer_at _ _ FCa);
  unfold Ora_law; Exists p (mk_lst (ls_args s) E_NOTHING r (ls_at s) (ls_word s) (ls_state s) a (ls_id s));
  unfold lfields; lst_cbn; entailer!;
  rej_close (result_check (ls_args s) a) r.

Lemma body_result_query: semax_body Vlaw Gres f_leanos_boot_machine_topology_admission_result_query
  (result_query_spec Ora_law).
Proof.
  start_function.
  unfold Ora_law. Intros p s.
  rename H into N, H0 into Hx, H1 into Hs, H2 into HJ.
  destruct (result_call _ _ _ _ _ N HJ) as (cur & R & G & ->).
  pose proof G as (E & Aa & C & W). subst args cur.
  pose proof Hx as Hx'. inputs_facts Hx'. pose proof Hs as Hs'. lst_facts Hs'.
  rng_list (ls_args s) 10.
  rewrite Zlength_sublist by lia. rewrite Z.sub_0_r.
  unfold lfields. Intros.
  forward.
  unfold E_RESULT in E.
  if1. gp.
  if1. if1. gp.
  if1. if1. gp.
  if1. gp.
  if1. gp.
  deadvars!.
  forward_call tt. Intros v.
  change (vl (ls_word s)) with (Vlong (Int64.repr (ls_word s))).
  forward.
  rewrite upd_Znth_map_vl.
  forward_if.
  - (* a word of the result *)
    uns64_hyps. forward. forward.
    Exists v. unfold Ora_law. Exists p (s_more s v). unfold lfields, s_more; lst_cbn. entailer!.
    split; [ apply lst_ok_more; auto; lia | ].
    apply (J_snoc_intro x h _ v _ R).
    rewrite res_step_more by (rewrite Zlength_sublist; lia).
    apply go_res_more; auto; lia.
  - (* its fourth word: the verdict *)
    assert (W3: ls_word s = 3) by (uns64_hyps; lia).
    set (a := upd_Znth 3 (ls_answer s) v).
    assert (Lan: Zlength a = 16) by (unfold a; rewrite upd_Znth_Zlength; lia).
    assert (Fan: Forall u64_ok a) by (apply Forall_upd; auto).
    rng_list a 16.
    pose proof (res_last x s v a (ls_args s) Hs W3 eq_refl) as EL.
    replace (upd_Znth (ls_word s) (ls_answer s) v) with a by (unfold a; rewrite W3; reflexivity).
    assert_PROP (field_compatible t_law (DOT _answer) (gv _law)) as FCa by entailer!.
    rewrite (answer_at _ _ FCa).
    forward. fix_offset _a.
    set (g := ExpectResult (ls_args s) (sublist 0 (ls_word s) (ls_answer s))) in *.
    forward.
    forward_if (PROP () LOCAL (temp _v (vl v)) SEP (Ora_law gv x (h ++ [(expected x g, v)]))).
    { (* ABI *) u64c. res_stop (gv _law) p x s a FCa S_RESULT_ABI. }
    u64c.
    forward.
    forward_if.
    { (* STATUS *) u64c. res_stop (gv _law) p x s a FCa S_RESULT_STATUS. }
    u64c.
    forward.
    forward_if.
    { (* ERROR *) u64c. res_stop (gv _law) p x s a FCa S_RESULT_ERROR. }
    u64c.
    forward.
    change (Int.unsigned (Int.repr (-1))) with 4294967295.
    forward_if (temp _t'9 (Vint (Int.repr (Z.b2z (negb (Znth 3 a <? 4294967296) ||
                                                   negb (Znth 3 a =? Znth 8 (ls_args s))))))).
    { change (Int.unsigned (Int.repr (-1))) with 4294967295 in *. forward. entailer!. bool_fin. }
    { change (Int.unsigned (Int.repr (-1))) with 4294967295 in *. forward. forward. forward. entailer!. bool_fin. }
    forward_if (temp _t'10 (Vint (Int.repr (Z.b2z (negb (Znth 3 a <? 4294967296) ||
                                                    negb (Znth 3 a =? Znth 8 (ls_args s)) ||
                                                    negb (Znth 3 a =? Znth 9 (ls_args s))))))).
    { forward. entailer!. bool_fin. }
    { forward. forward. forward. entailer!. bool_fin. }
    forward_if.
    { (* APIC_ID *) res_stop (gv _law) p x s a FCa S_RESULT_APIC_ID. }
    (* OK, writing word 3 *)
    forward. forward.
    forward_call (gv _law, vi (ls_expect s), vi (ls_verdict s), S_OK).
    rewrite <- (answer_at _ _ FCa).
    unfold Ora_law; Exists p (mk_lst (ls_args s) E_NOTHING S_OK (ls_at s) (ls_word s) (ls_state s) a (Znth 3 a)).
    unfold lfields; lst_cbn; entailer!.
    split; [ unfold lst_ok; lst_cbn; split_and; auto; unfold u32_ok, u64_ok, E_NOTHING, S_OK; rep_lia | ].
    apply J_snoc_intro; [ assumption | ]. rewrite EL.
    replace (result_check (ls_args s) a) with S_OK
      by (unfold result_check; change (2 ^ 32) with 4294967296; bool_dec).
    unfold Jp, result_end, ret_inv; simpl; auto.
    forward. Exists v. entailer!. apply derives_refl.
Qed.
