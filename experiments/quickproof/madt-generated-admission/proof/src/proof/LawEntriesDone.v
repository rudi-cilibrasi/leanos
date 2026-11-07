(* Law admission_exact: the body of the harness's helper entries_done (the entry stream's final checks, then the
   APIC ID for the entries alone or the result's arguments in an admission). *)
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

Lemma body_entries_done: semax_body nil [stop_spec] f_entries_done entries_done_spec.
Proof.
  start_function.
  rename H into Hx, H0 into Hs, H1 into Ha.
  pose proof Hx as Hx'. inputs_facts Hx'. pose proof Hs as Hs'. lst_facts Hs'.
  unfold lfields. Intros.
  set (st := ls_state s) in *.
  rng_list st 12. pose proof (call_code_range (i_call x)).
  assert_PROP (field_compatible t_law (DOT _state) q) as FCs by entailer!.
  rewrite (state_at _ q FCs).
  forward. fix_offset _s.
  forward.
  forward_if (temp _t'1 (Vint (Int.repr (Z.b2z (negb ((Znth 1 st =? 0) && (Znth 2 st =? 0))))))).
  { forward. entailer!. bool_fin. }
  { forward. forward. entailer!. bool_fin. }
  forward_if (temp _t'2 (Vint (Int.repr (Z.b2z (negb ((Znth 1 st =? 0) && (Znth 2 st =? 0) && (Znth 3 st =? 0))))))).
  { forward. entailer!. bool_fin. }
  { forward. forward. entailer!. bool_fin. }
  forward_if (temp _t'3 (Vint (Int.repr (Z.b2z (negb ((Znth 1 st =? 0) && (Znth 2 st =? 0) && (Znth 3 st =? 0) &&
                                                       (Znth 4 st =? 0))))))).
  { forward. entailer!. bool_fin. }
  { forward. forward. entailer!. bool_fin. }
  forward_if (temp _t'4 (Vint (Int.repr (Z.b2z (negb (rec_clean st)))))).
  { forward. entailer!. unfold rec_clean. bool_fin. }
  { forward. forward. entailer!. unfold rec_clean. bool_fin. }
  forward_if.
  { (* a record field set *)
    assert (Rc: rec_clean st = false) by (first [ assumption | apply negb_true_iff; assumption ]).
    rewrite <- (state_at _ q FCs). stop_ret q s S_ENTRIES_RECORD.
    unfold Jp. rewrite entries_done_record by auto. unfold ret_inv; simpl; auto. }
  assert (Rc: rec_clean st = true) by (first [ assumption | apply negb_false_iff; assumption ]).
  forward.
  forward_if.
  { (* not enabled *)
    u64c. rewrite <- (state_at _ q FCs). stop_ret q s S_ENTRIES_ENABLED.
    unfold Jp. rewrite entries_done_enabled by auto. unfold ret_inv; simpl; auto. }
  u64c.
  forward. forward.
  forward_if.
  { (* another APIC ID *)
    u64c. rewrite <- (state_at _ q FCs). stop_ret q s S_ENTRIES_APIC_ID.
    unfold Jp. rewrite entries_done_apic by auto. unfold ret_inv; simpl; auto. }
  u64c.
  forward.
  forward_if (temp _t'5 (Vint (Int.repr (Z.b2z ((Znth 8 st =? 0) && (Znth 9 st =? 0)))))).
  { forward. forward. entailer!. bool_fin. }
  { forward. entailer!. bool_fin. }
  forward_if (temp _t'6 (Vint (Int.repr (Z.b2z ((Znth 8 st =? 0) && (Znth 9 st =? 0) && (Znth 10 st =? 0)))))).
  { forward. forward. entailer!. bool_fin. }
  { forward. entailer!. bool_fin. }
  forward_if (temp _t'7 (Vint (Int.repr (Z.b2z (none_seen st))))).
  { forward. forward. entailer!. unfold none_seen. bool_fin. }
  { forward. entailer!. unfold none_seen. bool_fin. }
  forward_if.
  { (* none seen *)
    rewrite <- (state_at _ q FCs). stop_ret q s S_ENTRIES_SEEN.
    unfold Jp. rewrite entries_done_seen by auto. unfold ret_inv; simpl; auto. }
  assert (Ns: none_seen st = false) by (first [ assumption | apply negb_true_iff; assumption ]).
  deadvars!.
  forward.
  forward_if.
  { (* the entries alone: OK, writing s7 *)
    u64c. forward. forward.
    forward_call (q, vi (ls_expect s), vi (ls_verdict s), S_OK). forward.
    rewrite <- (state_at _ q FCs).
    Exists (mk_lst (ls_args s) E_NOTHING S_OK (ls_at s) (ls_word s) st (ls_answer s) (Znth 7 st)).
    unfold lfields; lst_cbn. entailer!.
    split.
    - unfold lst_ok; lst_cbn. split_and; auto; unfold u32_ok, u64_ok, E_NOTHING, S_OK; rep_lia.
    - unfold Jp. rewrite entries_done_ok by auto.
      match goal with E: call_code (i_call x) = 1 |- _ => rewrite (call_code_1 _ E) end.
      unfold ret_inv; simpl; auto. }
  u64c.
  forward. forward. forward. forward. forward. forward. forward. forward. forward.
  rewrite <- (state_at _ q FCs).
  Exists (mk_lst (upd_Znth 9 (upd_Znth 8 (upd_Znth 7 (upd_Znth 6 (upd_Znth 5 (ls_args s) 1) 1) 0) (Znth 7 st))
                    (i_executing x))
                 E_RESULT (ls_verdict s) (ls_at s) 0 st (ls_answer s) (ls_id s)).
  unfold lfields; lst_cbn.
  change (Vlong (Int64.repr (Int.signed (Int.repr 1)))) with (vl 1).
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with (vl 0).
  rewrite Int.unsigned_repr by rep_lia. change (Vlong (Int64.repr (i_executing x))) with (vl (i_executing x)).
  change (Vint (Int.repr 2)) with (vi E_RESULT).
  rewrite !upd_Znth_map_vl.
  entailer!.
  split; [ apply lst_ok_result0; auto; unfold u64_ok, u32_ok; rep_lia | ].
  unfold Jp. rewrite entries_done_ok by auto.
  match goal with E: call_code (i_call x) <> 1 |- _ =>
    destruct (i_call x) eqn:C; simpl in E; try (exfalso; apply E; reflexivity) end;
    apply go_result0; auto.
Qed.
