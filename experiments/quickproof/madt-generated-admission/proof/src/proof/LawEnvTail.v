(* Law admission_exact: the envelope export after the answer of the transition's last word is recorded (word 6): the
   test of the transition, then the next byte (and after the last one envelope_done) or the rejection. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosMadtAdmission.harness.admission_exact.code.
Require Import LeanosMadtAdmission.proof.Defs.
Require Import LeanosMadtAdmission.proof.MgaSpecs.
Require Import LeanosMadtAdmission.proof.LawProg LeanosMadtAdmission.proof.LawDefs LeanosMadtAdmission.proof.LawFacts
  LeanosMadtAdmission.proof.LawLib.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Definition Genv : funspecs := [any_u64_spec; gp_assert_spec; stop_spec; envelope_done_spec].

Definition Delta_env : tycontext :=
  func_tycontext f_leanos_boot_machine_madt_envelope_byte_step_query Vlaw Genv nil.
Definition Post_env gv x h c : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tulong
       (EX v: Z, PROP (u64_ok v) RETURN (vl v) SEP (Ora_law gv x (h ++ [(c, v)])))%argsassert)
    (stackframe_of f_leanos_boot_machine_madt_envelope_byte_step_query).

(* The statement after `if (word < 6) { ...; return v; }`. *)
Definition s_env_tail : statement := ltac:(
  let b := eval cbv delta [f_leanos_boot_machine_madt_envelope_byte_step_query] beta iota zeta
             in (fn_body f_leanos_boot_machine_madt_envelope_byte_step_query) in
  match b with
  | context [Ssequence (Sifthenelse (Ebinop Olt (Etempvar _word tulong) (Econst_int (Int.repr 6) tint) tint) _ Sskip)
               ?rest] => exact rest
  end).

Ltac env_stop q p x s a FCa r :=
  forward_call (q, vi (ls_expect s), vi (ls_verdict s), r);
  rewrite <- (answer_at _ _ FCa);
  unfold Ora_law; Exists p (mk_lst (ls_args s) E_NOTHING r (ls_at s) (ls_word s) (ls_state s) a (ls_id s));
  unfold lfields; lst_cbn; entailer!;
  rej_close (envelope_check x (ls_at s) a) r.

Lemma env_tail {Espec: OracleKind} gv x h s p v:
  inputs_ok x -> lst_ok s ->
  run x (start x) h =
    Some (Go (ExpectEnvelope (ls_at s) (sublist 0 3 (ls_state s)) (sublist 0 (ls_word s) (ls_answer s)))) ->
  go_inv x (ExpectEnvelope (ls_at s) (sublist 0 3 (ls_state s)) (sublist 0 (ls_word s) (ls_answer s))) s ->
  ls_word s = 6 -> u64_ok v ->
  forall Delta R c, Delta = Delta_env ->
  R = Post_env gv x h
        (expected x (ExpectEnvelope (ls_at s) (sublist 0 3 (ls_state s)) (sublist 0 (ls_word s) (ls_answer s)))) ->
  c = s_env_tail ->
  semax Delta
    (PROP ()
     LOCAL (temp _v (vl v); temp _last (vl (terminal x (ls_at s))); temp _m (gv _law); gvars gv)
     SEP (lfields (gv _law) p x (s_store s v); data_at Ews (tarray tuchar (i_length x)) (bytes_val (i_bytes x)) p))
    c R.
Proof.
  intros Hx Hs Rn G W6 Hv Delta R c -> -> ->.
  unfold s_env_tail, Delta_env, Post_env. start_tail.
  pose proof Hx as Hx'. inputs_facts Hx'. pose proof Hs as Hs'. lst_facts Hs'.
  pose proof G as (E & _ & _ & _ & W & A & Ar). unfold E_ENVELOPE in E.
  assert (Rb: 0 <= Znth (ls_at s) (i_bytes x) <= Byte.max_unsigned) by (apply Forall_byte_Znth; auto; lia).
  set (a := upd_Znth 6 (ls_answer s) v).
  assert (Lan: Zlength a = 16) by (unfold a; rewrite upd_Znth_Zlength; lia).
  assert (Fan: Forall u64_ok a) by (apply Forall_upd; auto).
  rng_list a 16.
  pose proof (env_last x s v a Hs W6 eq_refl) as EL.
  unfold lfields, s_store; lst_cbn.
  replace (upd_Znth (ls_word s) (ls_answer s) v) with a by (unfold a; rewrite W6; reflexivity). Intros.
  assert_PROP (field_compatible t_law (DOT _answer) (gv _law)) as FCa by entailer!.
  rewrite (answer_at _ _ FCa).
  forward. fix_offset _a.
  set (g := ExpectEnvelope (ls_at s) (sublist 0 3 (ls_state s)) (sublist 0 (ls_word s) (ls_answer s))) in *.
  assert (Rt: 0 <= terminal x (ls_at s) <= 1) by (unfold terminal; destruct (ls_at s + 1 =? i_length x); lia).
  assert (R31: 0 <= (if ls_at s + 1 =? i_length x then 3 else 1) <= 3) by (destruct (ls_at s + 1 =? i_length x); lia).
  forward.
  forward_if (PROP () LOCAL (temp _v (vl v)) SEP (Ora_law gv x (h ++ [(expected x g, v)]))).
  { (* ABI *) u64c. env_stop (gv _law) p x s a FCa S_ENVELOPE_ABI. }
  u64c.
  forward_if (temp _t'7 (vi (if ls_at s + 1 =? i_length x then 3 else 1))).
  { forward. entailer!. unfold terminal in *. destruct (Z.eqb_spec (ls_at s + 1) (i_length x)); [ reflexivity | contradiction ]. }
  { forward. entailer!. u64c. unfold terminal in *. destruct (Z.eqb_spec (ls_at s + 1) (i_length x)); [ lia | reflexivity ]. }
  forward.
  forward_if.
  { (* STATUS *) u64c. env_stop (gv _law) p x s a FCa S_ENVELOPE_STATUS. }
  u64c.
  forward.
  forward_if.
  { (* ERROR *) u64c. env_stop (gv _law) p x s a FCa S_ENVELOPE_ERROR. }
  u64c.
  forward. forward.
  forward_if.
  { (* NEXT_BYTE *) u64c. env_stop (gv _law) p x s a FCa S_ENVELOPE_NEXT_BYTE. }
  u64c.
  forward. forward. forward.
  change (vl (ls_at s)) with (Vlong (Int64.repr (ls_at s))).
  forward.
  { entailer!. rewrite Znth_bytes_val by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  rewrite Znth_bytes_val by lia.
  forward_if.
  { (* EXPOSED *) u64c. env_stop (gv _law) p x s a FCa S_ENVELOPE_EXPOSED. }
  u64c.
  (* accepted: the next byte *)
  forward. forward. forward. forward. forward. forward. forward. forward. forward.
  change (Int.signed (Int.repr 1)) with 1. rewrite add64_repr'.
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with (vl 0).
  change (Vlong (Int64.repr (ls_at s + 1))) with (vl (ls_at s + 1)).
  rewrite !upd_Znth_map_vl.
  rewrite <- (answer_at _ _ FCa).
  assert (Ck: envelope_check x (ls_at s) a = S_OK) by (unfold envelope_check; bool_dec).
  assert (EL': step x g v = envelope_from x (ls_at s + 1) [Znth 3 a; Znth 4 a; Znth 5 a]) by (rewrite EL, Ck; reflexivity).
  assert (Ok': lst_ok (env_next s a)) by (apply lst_ok_env_next; auto; lia).
  forward_if.
  { (* the last byte: envelope_done *)
    assert (Lst: ls_at s + 1 = i_length x)
      by (u64c; unfold terminal in *; destruct (Z.eqb_spec (ls_at s + 1) (i_length x)); [ auto | lia ]).
    sep_apply (lfields_fold (gv _law) p x (ls_args s) (ls_expect s) (ls_verdict s) (ls_at s + 1) 0
                 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 (ls_state s) (Znth 3 a)) (Znth 4 a)) (Znth 5 a)) a (ls_id s)).
    fold (env_next s a).
    forward_call (gv _law, p, x, env_next s a).
    Intros s'.
    unfold Ora_law. Exists p s'. entailer!.
    apply J_snoc_intro; [ assumption | ]. rewrite EL'. unfold envelope_from.
    rewrite (proj2 (Z.eqb_eq _ _) Lst). rewrite <- (env_next_state s a Hs). assumption. }
  { (* another byte *)
    assert (Lst: ls_at s + 1 <> i_length x)
      by (u64c; unfold terminal in *; destruct (Z.eqb_spec (ls_at s + 1) (i_length x)); [ lia | auto ]).
    forward.
    unfold Ora_law. Exists p (env_next s a). unfold lfields, env_next; lst_cbn. entailer!.
    apply J_snoc_intro; [ assumption | ]. rewrite EL'. unfold envelope_from.
    rewrite (proj2 (Z.eqb_neq _ _) Lst). apply go_env_next; auto; lia. }
  forward. Exists v. entailer!.
Qed.
