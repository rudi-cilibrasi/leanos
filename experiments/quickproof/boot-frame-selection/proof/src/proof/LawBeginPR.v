(* Law frame_selection_exact: the bodies of main's begin_publication_check and begin_rescan: the publication
   check's verdict and the rescan's order checks, as the model's start of their steps. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosFrameSelection.harness.frame_selection_exact.code.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Require Import LeanosFrameSelection.proof.LawProg LeanosFrameSelection.proof.LawDefs LeanosFrameSelection.proof.LawFacts
  LeanosFrameSelection.proof.LawLib LeanosFrameSelection.proof.LawLib2 LeanosFrameSelection.proof.LawRows
  LeanosFrameSelection.proof.LawLib3 LeanosFrameSelection.proof.LawBegin.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Existing Instance LawProg.LCS.

(* The publication result as the publication check reads it, through its field's address. *)
Lemma pub_at: forall q v, field_compatible t_law (DOT _publication_expect) q ->
  field_at Ews t_law (DOT _publication_expect) v q = data_at Ews (tarray tulong 5) v (offset_val 2784 q).
Proof. intros. rewrite field_at_data_at, field_compatible_field_address by auto. reflexivity. Qed.

Lemma pub_addr: forall q, field_compatible t_law (DOT _publication_expect) q ->
  eval_field (Tstruct _law__1 noattr) _publication_expect q = field_address t_law (DOT _publication_expect) q.
Proof.
  intros q FC. pose proof (field_compatible_isptr _ _ _ FC) as P. destruct q; try contradiction.
  unfold field_address. rewrite if_true by auto. reflexivity.
Qed.

(* `p[4] != m->selected + 1` in uint64_t. *)
Lemma eq_succ64: forall a S, 0 <= a <= Int64.max_unsigned -> 0 <= S <= Int64.max_unsigned ->
  Int64.eq (Int64.repr a) (Int64.add (Int64.repr S) (Int64.repr 1)) = (a =? (S + 1) mod 2 ^ 64).
Proof.
  intros a S A B. rewrite add64_repr'. unfold Int64.eq. rewrite Int64.unsigned_repr by auto.
  rewrite Int64.unsigned_repr_eq. change Int64.modulus with (2 ^ 64).
  destruct (zeq a ((S + 1) mod 2 ^ 64)); destruct (Z.eqb_spec a ((S + 1) mod 2 ^ 64)); auto; lia.
Qed.

Lemma repr64_mod: forall a, Int64.repr a = Int64.repr (a mod 2 ^ 64).
Proof. intros. rewrite <- (Int64.repr_unsigned (Int64.repr a)), Int64.unsigned_repr_eq. reflexivity. Qed.

Ltac pc_leaf q s x k Fz F :=
  forward_call (q, vi (w_expect s), vi (w_verdict s), k);
  Exists (set_stop (set_step s ST_PUBLICATION_CHECK) k);
  assert (Ek: publication_check x (i_mem x) = k) by (unfold publication_check; chk_cond);
  let HJ' := fresh "HJ'" in
  assert (HJ': J x (start x) (set_stop (set_step s ST_PUBLICATION_CHECK) k))
    by (unfold start; rewrite F, Ek; apply J_begin_ret; auto; try congruence;
        unfold u32_ok, ST_PUBLICATION_CHECK, status_ok in *; unfold_S; rep_lia);
  thaw Fz; rewrite <- pub_at by auto;
  unfold lfields; set_unfold; lst_cbn; entailer!.

Lemma body_begin_publication_check:
  semax_body nil [stop_spec] f_begin_publication_check begin_publication_check_spec.
Proof.
  start_function.
  rename H into F, H0 into Ix, H1 into Hs, H2 into Q.
  lst_facts Hs. inputs_facts Ix. mem_facts Im.
  rng_list (m_publication (i_mem x)) 5.
  unfold lfields. Intros.
  freeze_but [_step; _expect; _verdict; _selected; _publication_expect] (@nil val) Fz.
  forward.
  assert_PROP (field_compatible t_law (DOT _publication_expect) q) as FC by entailer!.
  rewrite pub_at by auto.
  forward.
  forward.
  forward_if.
  { u64c. pc_leaf q s x S_PUBLICATION_VERSION Fz F. }
  u64c. forward.
  forward_if.
  { u64c. pc_leaf q s x S_PUBLICATION_STATUS Fz F. }
  u64c. forward.
  forward_if.
  { u64c. pc_leaf q s x S_PUBLICATION_ERROR Fz F. }
  u64c. forward. forward.
  forward_if.
  { u64c. pc_leaf q s x S_PUBLICATION_FRAME Fz F. }
  u64c. forward. forward.
  assert (Rs1: 0 <= (i_selected x + 1) mod 2 ^ 64 <= Int64.max_unsigned)
    by (pose proof (Z.mod_pos_bound (i_selected x + 1) (2 ^ 64) ltac:(lia)); unfold Int64.max_unsigned, Int64.modulus;
        simpl; lia).
  forward_if.
  { rewrite ?add64_repr' in *. rewrite ?(repr64_mod (i_selected x + 1)) in *. u64c.
    pc_leaf q s x S_PUBLICATION_OBJECT Fz F. }
  rewrite ?add64_repr' in *. rewrite ?(repr64_mod (i_selected x + 1)) in *. u64c. pc_leaf q s x S_OK Fz F.
Qed.

Lemma body_begin_rescan: semax_body nil [stop_spec] f_begin_rescan begin_rescan_spec.
Proof.
  start_function.
  rename H into F, H0 into Ix, H1 into Hs, H2 into Q.
  lst_facts Hs. inputs_facts Ix.
  unfold lfields. Intros.
  freeze_but [_step; _expect; _verdict; _next; _published; _candidate; _scan] (@nil val) Fz.
  forward. forward.
  forward_if.
  { u64c. forward_call (q, vi (w_expect s), vi (w_verdict s), S_UNPUBLISHED_LIMIT).
    Exists (set_stop (set_step s ST_RESCAN) S_UNPUBLISHED_LIMIT).
    assert (Ek: rescan_order x = S_UNPUBLISHED_LIMIT) by (unfold rescan_order; chk_cond).
    assert (HJ': J x (start x) (set_stop (set_step s ST_RESCAN) S_UNPUBLISHED_LIMIT))
      by (unfold start; rewrite F, Ek; cbn; apply J_begin_ret; auto; try congruence;
          unfold u32_ok, ST_RESCAN, status_ok in *; unfold_S; rep_lia).
    thaw Fz. unfold lfields; set_unfold; lst_cbn. entailer!. }
  u64c. forward. forward.
  forward_if.
  { u64c. forward_call (q, vi (w_expect s), vi (w_verdict s), S_UNPUBLISHED_ORDER).
    Exists (set_stop (set_step s ST_RESCAN) S_UNPUBLISHED_ORDER).
    assert (Ek: rescan_order x = S_UNPUBLISHED_ORDER) by (unfold rescan_order; chk_cond).
    assert (HJ': J x (start x) (set_stop (set_step s ST_RESCAN) S_UNPUBLISHED_ORDER))
      by (unfold start; rewrite F, Ek; cbn; apply J_begin_ret; auto; try congruence;
          unfold u32_ok, ST_RESCAN, status_ok in *; unfold_S; rep_lia).
    thaw Fz. unfold lfields; set_unfold; lst_cbn. entailer!. }
  u64c. forward. forward. forward. forward.
  Exists (set_expect (set_scan (set_candidate (set_step s ST_RESCAN) (i_next x)) 1) E_DECODE).
  assert (Ek: rescan_order x = S_OK) by (unfold rescan_order; chk_cond).
  assert (HJ': J x (start x) (set_expect (set_scan (set_candidate (set_step s ST_RESCAN) (i_next x)) 1) E_DECODE)).
  { unfold start. rewrite F, Ek. cbn. Jtac. }
  thaw Fz. unfold lfields; set_unfold; lst_cbn. entailer!.
Qed.
