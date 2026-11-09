(* Law admission_exact: the body of the harness's entry-stream export against entry_step_spec Ora_law: its checks
   follow from the call the model expects (entry_call), and the answer it records keeps the oracle's invariant (the
   transition's last word: LawEntTail). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosMadtAdmission.harness.admission_exact.code.
Require Import LeanosMadtAdmission.proof.Defs.
Require Import LeanosMadtAdmission.proof.MgaSpecs.
Require Import LeanosMadtAdmission.proof.LawProg LeanosMadtAdmission.proof.LawDefs LeanosMadtAdmission.proof.LawFacts
  LeanosMadtAdmission.proof.LawLib LeanosMadtAdmission.proof.LawEntTail.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Lemma body_entry_step: semax_body Vlaw Gent f_leanos_boot_machine_madt_entry_stream_byte_step_query
  (entry_step_spec Ora_law).
Proof.
  start_function.
  unfold Ora_law. Intros p s.
  rename H into N, H0 into Hx, H1 into Hs, H2 into HJ.
  destruct (entry_call _ _ _ _ _ _ _ _ _ N HJ) as (cur & R & G & -> & -> & -> & ->).
  pose proof G as (E & I & St & C & W & A & Ar). subst off st cur.
  pose proof Hx as Hx'. inputs_facts Hx'. pose proof Hs as Hs'. lst_facts Hs'.
  rng_list (ls_state s) 12.
  assert (Rb: 0 <= Znth (ls_at s) (i_bytes x) <= Byte.max_unsigned) by (apply Forall_byte_Znth; auto; lia).
  rewrite Zlength_sublist by lia. rewrite Z.sub_0_r.
  unfold lfields. Intros.
  forward.
  unfold E_ENTRIES in E.
  if1. gp.
  if1. if1. if1. gp.
  if1. if1. if1. gp.
  if1. if1. if1. gp.
  if1. gp.
  to_branch. forward_if (temp _t'12 (Vint Int.one)).
  { forward. forward. change (vl (ls_at s)) with (Vlong (Int64.repr (ls_at s))). forward.
    { entailer!. rewrite Znth_bytes_val by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite Znth_bytes_val by lia.
    forward. entailer!; cmp_close. }
  { else_false. }
  gp.
  deadvars!.
  forward_call tt. Intros v.
  change (vl (ls_word s)) with (Vlong (Int64.repr (ls_word s))).
  forward.
  rewrite upd_Znth_map_vl.
  forward_if.
  - (* a word of the transition *)
    uns64_hyps. forward. forward.
    Exists v. unfold Ora_law. Exists p (s_more s v). unfold lfields, s_more; lst_cbn. entailer!.
    split; [ apply lst_ok_more; auto; lia | ].
    apply (J_snoc_intro x h _ v _ R).
    rewrite ent_step_more by (rewrite Zlength_sublist; lia).
    apply go_ent_more; auto; lia.
  - (* its last word *)
    assert (W15: ls_word s = 15) by (uns64_hyps; lia).
    change (Vlong (Int64.repr (ls_word s))) with (vl (ls_word s)).
    sep_apply (lfields_fold (gv _law) p x (ls_args s) (ls_expect s) (ls_verdict s) (ls_at s) (ls_word s) (ls_state s)
                 (upd_Znth (ls_word s) (ls_answer s) v) (ls_id s)).
    eapply semax_pre; [ | apply (ent_tail gv x h s p v); first [ reflexivity | assumption | auto ] ].
    entailer!. apply derives_refl.
Qed.
