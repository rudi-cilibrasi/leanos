(* Law admission_exact: the entry-stream export after the answer of the transition's last word is recorded (word 15):
   the test of the transition, then the next offset (and after the last one entries_done) or the rejection. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosMadtAdmission.harness.admission_exact.code.
Require Import LeanosMadtAdmission.proof.Defs.
Require Import LeanosMadtAdmission.proof.MgaSpecs.
Require Import LeanosMadtAdmission.proof.LawProg LeanosMadtAdmission.proof.LawDefs LeanosMadtAdmission.proof.LawFacts
  LeanosMadtAdmission.proof.LawLib.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Definition Gent : funspecs := [any_u64_spec; gp_assert_spec; stop_spec; entries_done_spec].

Definition Delta_ent : tycontext :=
  func_tycontext f_leanos_boot_machine_madt_entry_stream_byte_step_query Vlaw Gent nil.
Definition Post_ent gv x h c : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tulong
       (EX v: Z, PROP (u64_ok v) RETURN (vl v) SEP (Ora_law gv x (h ++ [(c, v)])))%argsassert)
    (stackframe_of f_leanos_boot_machine_madt_entry_stream_byte_step_query).

(* The statement after `if (word < 15) { ...; return v; }`. *)
Definition s_ent_tail : statement := ltac:(
  let b := eval cbv delta [f_leanos_boot_machine_madt_entry_stream_byte_step_query] beta iota zeta
             in (fn_body f_leanos_boot_machine_madt_entry_stream_byte_step_query) in
  match b with
  | context [Ssequence (Sifthenelse (Ebinop Olt (Etempvar _word tulong) (Econst_int (Int.repr 15) tint) tint) _ Sskip)
               ?rest] => exact rest
  end).

Ltac ent_stop q p x s a FCa r :=
  forward_call (q, vi (ls_expect s), vi (ls_verdict s), r);
  rewrite <- (answer_at _ _ FCa);
  unfold Ora_law; Exists p (mk_lst (ls_args s) E_NOTHING r (ls_at s) (ls_word s) (ls_state s) a (ls_id s));
  unfold lfields; lst_cbn; entailer!;
  rej_close (entries_check x (ls_at s) a) r.

Lemma ent_tail {Espec: OracleKind} gv x h s p v:
  inputs_ok x -> lst_ok s ->
  run x (start x) h = Some (Go (ExpectEntries (ls_at s) (ls_state s) (sublist 0 (ls_word s) (ls_answer s)))) ->
  go_inv x (ExpectEntries (ls_at s) (ls_state s) (sublist 0 (ls_word s) (ls_answer s))) s ->
  ls_word s = 15 -> u64_ok v ->
  forall Delta R c, Delta = Delta_ent ->
  R = Post_ent gv x h (expected x (ExpectEntries (ls_at s) (ls_state s) (sublist 0 (ls_word s) (ls_answer s)))) ->
  c = s_ent_tail ->
  semax Delta
    (PROP ()
     LOCAL (temp _v (vl v); temp _m (gv _law); gvars gv)
     SEP (lfields (gv _law) p x (s_store s v); data_at Ews (tarray tuchar (i_length x)) (bytes_val (i_bytes x)) p))
    c R.
Proof.
  intros Hx Hs Rn G W15 Hv Delta R c -> -> ->.
  unfold s_ent_tail, Delta_ent, Post_ent. start_tail.
  pose proof Hx as Hx'. inputs_facts Hx'. pose proof Hs as Hs'. lst_facts Hs'.
  pose proof G as (E & _ & _ & _ & W & A & Ar). unfold E_ENTRIES in E.
  assert (Rb: 0 <= Znth (ls_at s) (i_bytes x) <= Byte.max_unsigned) by (apply Forall_byte_Znth; auto; lia).
  set (a := upd_Znth 15 (ls_answer s) v).
  assert (Lan: Zlength a = 16) by (unfold a; rewrite upd_Znth_Zlength; lia).
  assert (Fan: Forall u64_ok a) by (apply Forall_upd; auto).
  rng_list a 16.
  pose proof (ent_last x s v a Hs W15 eq_refl) as EL.
  unfold lfields, s_store; lst_cbn.
  replace (upd_Znth (ls_word s) (ls_answer s) v) with a by (unfold a; rewrite W15; reflexivity). Intros.
  assert_PROP (field_compatible t_law (DOT _answer) (gv _law)) as FCa by entailer!.
  rewrite (answer_at _ _ FCa).
  set (g := ExpectEntries (ls_at s) (ls_state s) (sublist 0 (ls_word s) (ls_answer s))) in *.
  assert (Rt: 0 <= terminal x (ls_at s) <= 1) by (unfold terminal; destruct (ls_at s + 1 =? i_length x); lia).
  assert (R31: 0 <= (if ls_at s + 1 =? i_length x then 3 else 1) <= 3) by (destruct (ls_at s + 1 =? i_length x); lia).
  forward. forward. forward.
  rewrite last_val by lia.
  forward. fix_offset _a.
  forward.
  forward_if (PROP () LOCAL (temp _v (vl v)) SEP (Ora_law gv x (h ++ [(expected x g, v)]))).
  { (* ABI *) u64c. ent_stop (gv _law) p x s a FCa S_ENTRIES_ABI. }
  u64c.
  forward_if (temp _t'14 (vi (if ls_at s + 1 =? i_length x then 3 else 1))).
  { forward. entailer!. unfold terminal in *. destruct (Z.eqb_spec (ls_at s + 1) (i_length x)); [ reflexivity | contradiction ]. }
  { forward. entailer!. u64c. unfold terminal in *. destruct (Z.eqb_spec (ls_at s + 1) (i_length x)); [ lia | reflexivity ]. }
  forward.
  forward_if.
  { (* STATUS *) u64c. ent_stop (gv _law) p x s a FCa S_ENTRIES_STATUS. }
  u64c.
  forward.
  forward_if.
  { (* ERROR *) u64c. ent_stop (gv _law) p x s a FCa S_ENTRIES_ERROR. }
  u64c.
  forward. forward.
  forward_if.
  { (* NEXT_OFFSET *) u64c. ent_stop (gv _law) p x s a FCa S_ENTRIES_NEXT_OFFSET. }
  u64c.
  forward. forward. forward.
  change (vl (ls_at s)) with (Vlong (Int64.repr (ls_at s))).
  forward.
  { entailer!. rewrite Znth_bytes_val by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  rewrite Znth_bytes_val by lia.
  forward_if.
  { (* EXPOSED *) u64c. ent_stop (gv _law) p x s a FCa S_ENTRIES_EXPOSED. }
  u64c.
  (* accepted: the next offset *)
  assert (Ck: entries_check x (ls_at s) a = S_OK) by (unfold entries_check; bool_dec).
  assert (EL': step x g v = entries_from x (ls_at s + 1) (sublist 3 15 a)) by (rewrite EL, Ck; reflexivity).
  assert (Ok': lst_ok (ent_next s a)) by (apply lst_ok_ent_next; auto; lia).
  freeze_but [_state] false F.
  forward_for_simple_bound 12
    (EX k: Z, PROP ()
     LOCAL (temp _last (vl (terminal x (ls_at s))); temp _a (offset_val 224 (gv _law)); temp _v (vl v);
            temp _m (gv _law); gvars gv)
     SEP (FRZL F; data_at Ews (tarray tulong 16) (map vl a) (offset_val 224 (gv _law));
          field_at Ews t_law (DOT _state) (map vl (sublist 3 (3 + k) a ++ sublist k 12 (ls_state s))) (gv _law)))%assert.
  { entailer!. replace (sublist 3 3 a ++ sublist 0 12 (ls_state s)) with (ls_state s) by list_solve.
    apply derives_refl. }
  { forward. forward. rewrite upd_Znth_map_vl.
    replace (upd_Znth i (sublist 3 (3 + i) a ++ sublist i 12 (ls_state s)) (Znth (i + 3) a))
      with (sublist 3 (3 + (i + 1)) a ++ sublist (i + 1) 12 (ls_state s)) by list_solve.
    entailer!. }
  thaw F.
  replace (sublist 3 (3 + 12) a ++ sublist 12 12 (ls_state s)) with (sublist 3 15 a) by list_solve.
  forward. forward. forward.
  change (Int.signed (Int.repr 1)) with 1. rewrite add64_repr'.
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with (vl 0).
  change (Vlong (Int64.repr (ls_at s + 1))) with (vl (ls_at s + 1)).
  rewrite <- (answer_at _ _ FCa).
  forward_if.
  { (* the last offset: entries_done *)
    assert (Lst: ls_at s + 1 = i_length x)
      by (u64c; unfold terminal in *; destruct (Z.eqb_spec (ls_at s + 1) (i_length x)); [ auto | lia ]).
    sep_apply (lfields_fold (gv _law) p x (ls_args s) (ls_expect s) (ls_verdict s) (ls_at s + 1) 0
                 (sublist 3 15 a) a (ls_id s)).
    fold (ent_next s a).
    forward_call (gv _law, p, x, ent_next s a).
    Intros s'.
    unfold Ora_law. Exists p s'. entailer!.
    apply J_snoc_intro; [ assumption | ]. rewrite EL'. unfold entries_from.
    rewrite (proj2 (Z.eqb_eq _ _) Lst). assumption. }
  { (* another offset *)
    assert (Lst: ls_at s + 1 <> i_length x)
      by (u64c; unfold terminal in *; destruct (Z.eqb_spec (ls_at s + 1) (i_length x)); [ lia | auto ]).
    forward.
    unfold Ora_law. Exists p (ent_next s a). unfold lfields, ent_next; lst_cbn. entailer!.
    apply J_snoc_intro; [ assumption | ]. rewrite EL'. unfold entries_from.
    rewrite (proj2 (Z.eqb_neq _ _) Lst). apply go_ent_next; auto; lia. }
  forward. Exists v. entailer!.
Qed.
