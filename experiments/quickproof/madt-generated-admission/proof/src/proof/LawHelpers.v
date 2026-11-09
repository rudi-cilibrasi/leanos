(* Law admission_exact: the bodies of the harness's helpers any_u64, stop, begin_entries and envelope_done. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosMadtAdmission.harness.admission_exact.code.
Require Import LeanosMadtAdmission.proof.Defs.
Require Import LeanosMadtAdmission.proof.MgaSpecs.
Require Import LeanosMadtAdmission.proof.LawProg LeanosMadtAdmission.proof.LawDefs LeanosMadtAdmission.proof.LawFacts
  LeanosMadtAdmission.proof.LawLib.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

(* The posts of begin_entries and envelope_done keep the result's arguments (when entailer! left it). *)
Ltac args_same :=
  match goal with |- _ /\ ls_args _ = ls_args _ => split; [ | first [ reflexivity | assumption ] ] | _ => idtac end.

Lemma body_any_u64: semax_body nil [nondet_u32_spec] f_any_u64 any_u64_spec.
Proof.
  start_function.
  rewrite <- seq_assoc. forward_call. Intros hi. forward.
  rewrite <- seq_assoc. forward_call. Intros lo. forward.
  forward.
  Exists (Int64.unsigned (Int64.or (Int64.shl (Int64.repr hi) (Int64.repr 32)) (Int64.repr lo))).
  entailer!. split; [ apply Int64.unsigned_range_2 | unfold vl; rewrite Int64.repr_unsigned; reflexivity ].
Qed.

Lemma body_stop: semax_body nil nil f_stop stop_spec.
Proof. start_function. forward. forward. entailer!. Qed.

Lemma body_begin_entries: semax_body nil [stop_spec] f_begin_entries begin_entries_spec.
Proof.
  start_function.
  rename H into Hx, H0 into Hs, H1 into Ha.
  pose proof Hx as Hx'. inputs_facts Hx'. pose proof Hs as Hs'. lst_facts Hs'.
  unfold lfields. Intros.
  forward.
  forward_if (temp _t'1 (Vint (Int.repr (Z.b2z ((i_length x <=? 44) || (255 <? i_executing x)))))).
  { forward. entailer!. bool_fin. }
  { forward. forward. entailer!. bool_fin. }
  forward_if.
  - (* the bounds *)
    try b2z_hyp.
    forward_call (q, vi (ls_expect s), vi (ls_verdict s), S_ENTRIES_BOUNDS).
    forward.
    Exists (s_stop s S_ENTRIES_BOUNDS). unfold lfields, s_stop; lst_cbn. entailer!.
    split; [ apply lst_ok_stop; auto; unfold u32_ok, S_ENTRIES_BOUNDS; rep_lia | ].
    args_same.
    unfold Jp, begin_entries. rewrite H. unfold ret_inv; simpl. auto.
  - (* offset 44 with the initial state *)
    try b2z_hyp.
    freeze_but [_state] false F.
    forward_for_simple_bound 12
      (EX k: Z, PROP () LOCAL (temp _m q)
       SEP (FRZL F; field_at Ews t_law (DOT _state) (map vl (Zrepeat 0 k ++ sublist k 12 (ls_state s))) q))%assert.
    { replace (Zrepeat 0 0 ++ sublist 0 12 (ls_state s)) with (ls_state s) by list_solve. entailer!. }
    { forward. change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with (vl 0).
      rewrite upd_Znth_map_vl.
      replace (upd_Znth i (Zrepeat 0 i ++ sublist i 12 (ls_state s)) 0) with (Zrepeat 0 (i + 1) ++ sublist (i + 1) 12 (ls_state s))
        by list_solve.
      entailer!. }
    thaw F.
    forward. forward. forward. forward. forward.
    Exists (mk_lst (ls_args s) E_ENTRIES (ls_verdict s) 44 0 initial_entries (ls_answer s) (ls_id s)).
    unfold lfields; lst_cbn.
    change (Vlong (Int64.repr (Int.signed (Int.repr 44)))) with (vl 44).
    change (Vlong (Int64.repr (Int.signed (Int.repr 256)))) with (vl 256).
    change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with (vl 0).
    change (Vint (Int.repr 1)) with (vi E_ENTRIES).
    rewrite !upd_Znth_map_vl.
    replace (upd_Znth 7 (upd_Znth 0 (Zrepeat 0 12 ++ sublist 12 12 (ls_state s)) 44) 256) with initial_entries
      by (unfold initial_entries; list_solve).
    entailer!.
    split; [ apply lst_ok_entries0; auto | ].
    args_same.
    unfold Jp. rewrite begin_entries_go by auto. apply go_entries0; auto.
    apply orb_false_iff in H as [H _]. apply Z.leb_gt in H. lia.
Qed.

Lemma body_envelope_done: semax_body nil [stop_spec; begin_entries_spec] f_envelope_done envelope_done_spec.
Proof.
  start_function.
  rename H into Hx, H0 into Hs, H1 into Ha.
  pose proof Hx as Hx'. inputs_facts Hx'. pose proof Hs as Hs'. lst_facts Hs'.
  rng_list (ls_state s) 12. pose proof (call_code_range (i_call x)).
  unfold lfields. Intros.
  forward. forward.
  forward_if.
  { u64c. stop_ret q s S_ENVELOPE_LENGTH.
    args_same.
    unfold Jp. rewrite envelope_done_length by auto. unfold ret_inv; simpl; auto. }
  forward.
  forward_if.
  { u64c. stop_ret q s S_ENVELOPE_CHECKSUM.
    args_same.
    unfold Jp. rewrite envelope_done_checksum by auto. unfold ret_inv; simpl; auto. }
  forward.
  forward_if.
  { u64c. stop_end q s S_OK.
    args_same.
    unfold Jp. rewrite envelope_done_ok by auto. match goal with E: call_code (i_call x) = 0 |- _ => rewrite (call_code_0 _ E) end. unfold ret_inv; simpl; auto. }
  { u64c. sep_apply (lfields_fold_s q p x s).
    forward_call (q, p, x, s). Intros s'.
    Exists s'. entailer!.
    args_same.
    unfold Jp. rewrite envelope_done_ok by auto.
    match goal with E: call_code (i_call x) <> 0 |- _ => destruct (i_call x); simpl in E; try contradiction; auto end. }
Qed.
