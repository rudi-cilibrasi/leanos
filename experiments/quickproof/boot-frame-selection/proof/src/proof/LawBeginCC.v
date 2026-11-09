(* Law frame_selection_exact: the body of main's begin_cross_check: the cross-check's verdict, without a call, as
   the model's start of the step. *)
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


Lemma body_begin_cross_check: semax_body nil [stop_spec] f_begin_cross_check begin_cross_check_spec.
Proof.
  start_function.
  rename H into F, H0 into Ix, H1 into Hs, H2 into Q.
  lst_facts Hs. inputs_facts Ix. mem_facts Im.
  pose proof (mem_ok_states (i_mem x) Im) as (Ls & L0 & F0 & L1 & F1).
  rng_at (Znth 0 (m_states (i_mem x))) [11; 14; 15; 16; 17]. rng_at (i_decoded x) [11; 17].
  rng_at (m_terminal (i_mem x)) [3].
  unfold lfields. Intros.
  freeze_but [_step; _expect; _verdict; _selected; _selected_manifest; _states_expect; _terminal_expect; _decoded]
    (@nil val) Fz.
  forward.
  assert_PROP (field_compatible t_law (DOT _states_expect) q /\ isptr q) as FCP by entailer!.
  destruct FCP as [FC Pq].
  rewrite (states_rows q (m_states (i_mem x))) by auto. Intros. unfold t_state.
  forward.
  rewrite srow_field0 by auto.
  forward.
  rewrite semax_seq_skip.
  forward_if (PROP ()
    LOCAL (temp _m q)
    SEP (FRZL Fz; data_at Ews (tarray tulong 41) (map vl (Znth 0 (m_states (i_mem x)))) (srow q 0);
         data_at Ews (tarray tulong 41) (map vl (Znth 1 (m_states (i_mem x)))) (srow q 1);
         field_at Ews t_law (DOT _step) (vi ST_CROSS_CHECK) q;
         field_at Ews t_law (DOT _expect) (vi E_NOTHING) q;
         field_at Ews t_law (DOT _verdict) (vi (cross_check x (i_mem x))) q;
         field_at Ews t_law (DOT _selected) (vl (i_selected x)) q;
         field_at Ews t_law (DOT _selected_manifest) (vl (i_selected_manifest x)) q;
         field_at Ews t_law (DOT _terminal_expect) (map vl (m_terminal (i_mem x))) q;
         field_at Ews t_law (DOT _decoded) (map vl (i_decoded x)) q)).
  { u64c. forward_call (q, vi (w_expect s), vi (w_verdict s), S_AUTHORITY_NONE).
    replace (cross_check x (i_mem x)) with S_AUTHORITY_NONE by (unfold cross_check; chk_cond). entailer!. }
  { u64c. forward. forward.
    forward_if.
    { u64c. forward_call (q, vi (w_expect s), vi (w_verdict s), S_AUTHORITY_NOMINATION).
      replace (cross_check x (i_mem x)) with S_AUTHORITY_NOMINATION by (unfold cross_check; chk_cond). entailer!. }
    u64c. forward. forward.
    forward_if.
    { u64c. forward_call (q, vi (w_expect s), vi (w_verdict s), S_AUTHORITY_TARGET).
      replace (cross_check x (i_mem x)) with S_AUTHORITY_TARGET by (unfold cross_check; chk_cond). entailer!. }
    u64c. forward. forward.
    forward_if.
    { u64c. forward_call (q, vi (w_expect s), vi (w_verdict s), S_AUTHORITY_ENTRY_COUNT).
      replace (cross_check x (i_mem x)) with S_AUTHORITY_ENTRY_COUNT by (unfold cross_check; chk_cond). entailer!. }
    u64c. forward. forward.
    forward_if.
    { u64c. forward_call (q, vi (w_expect s), vi (w_verdict s), S_AUTHORITY_HIGHEST).
      replace (cross_check x (i_mem x)) with S_AUTHORITY_HIGHEST by (unfold cross_check; chk_cond). entailer!. }
    u64c. forward.
    forward_if.
    { u64c. forward_call (q, vi (w_expect s), vi (w_verdict s), S_AUTHORITY_USABLE).
      replace (cross_check x (i_mem x)) with S_AUTHORITY_USABLE by (unfold cross_check; chk_cond). entailer!. }
    u64c. forward.
    forward_if.
    { u64c. forward_call (q, vi (w_expect s), vi (w_verdict s), S_AUTHORITY_BLOCKED).
      replace (cross_check x (i_mem x)) with S_AUTHORITY_BLOCKED by (unfold cross_check; chk_cond). entailer!. }
    u64c. forward.
    forward_if.
    { u64c. forward_call (q, vi (w_expect s), vi (w_verdict s), S_AUTHORITY_MANIFEST).
      replace (cross_check x (i_mem x)) with S_AUTHORITY_MANIFEST by (unfold cross_check; chk_cond). entailer!. }
    u64c. forward_call (q, vi (w_expect s), vi (w_verdict s), S_OK).
    replace (cross_check x (i_mem x)) with S_OK by (unfold cross_check; chk_cond). entailer!. }
  try (normalize_postcondition; eapply semax_pre; [ | apply semax_skip ]).
  unfold stackframe_of; cbn [fn_vars f_begin_cross_check map fold_right]. rewrite sepcon_emp.
  Exists (set_stop (set_step s ST_CROSS_CHECK) (cross_check x (i_mem x))). thaw Fz.
  sep_apply (states_rows_fold' q (m_states (i_mem x))); auto.
  assert (Sst: status_ok (cross_check x (i_mem x))) by checks_ok.
  assert (HJ': J x (start x) (set_stop (set_step s ST_CROSS_CHECK) (cross_check x (i_mem x)))).
  { unfold start. rewrite F. apply J_begin_ret; auto; try congruence. unfold u32_ok, ST_CROSS_CHECK; rep_lia. }
  unfold lfields. set_unfold; lst_cbn. entailer!.
Qed.
