(* Law handoff_decode_exact: the body of the harness's stream reset export against stream_init_spec Ora_law: its
   checks follow from the call the model expects, and the answer it records moves the law's record as the model's
   step: the next word, or after word 6 the reset's checks and chunk 0 (begin_chunk). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosHandoff.harness.handoff_decode_exact.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.LawProg LeanosHandoff.proof.LawDefs LeanosHandoff.proof.LawFacts
  LeanosHandoff.proof.LawLib LeanosHandoff.proof.LawLib2.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Existing Instance LawProg.LCS.

Definition Ginit : funspecs := [gp_assert_spec; any_u64_spec; stop_spec; begin_chunk_spec].

(* stop(m, st) after the reset's last answer: the oracle at Return st m. *)
Ltac si_stop gv x m a v s ce ie Rn Hm st :=
  u64c;
  let C := fresh "C" in let R' := fresh "R" in
  assert (C: stream_init_check x (m_total m) (a ++ [v]) = st) by (unfold stream_init_check; chk_dec);
  assert (R': stream_init_done x (a ++ [v]) m = Return st m) by (unfold stream_init_done; rewrite C; reflexivity);
  rewrite R' in Rn;
  forward_call (gv _law, vi (w_expect s), vi (w_verdict s), st);
  let Hs2 := fresh "HJ" in
  assert (Hs2: J x (Return st m) (s_stop (s_stream (s_store s v) (a ++ [v])) st))
    by (apply J_stop; auto; unfold u32_ok; unfold_status; rep_lia);
  ora_fin (Return st m) (s_stop (s_stream (s_store s v) (a ++ [v])) st) ce ie.

Lemma body_stream_init: semax_body Vlaw Ginit f_leanos_boot_handoff_stream_init (stream_init_spec Ora_law).
Proof.
  start_function.
  rename H into Nc.
  ora_open x h p s ce ie.
  destruct (next_go x h p _ Hrun Nc) as (g & m & -> & Ec).
  destruct (call_stream_init x g m _ _ _ _ _ (eq_sym Ec)) as (a & -> & -> & -> & -> & -> & ->).
  pose proof HJ as (Hs & Hm & G). cbn [mem_of] in *.
  pose proof G as (Ge & (Pw & Pa) & La & Cc).
  lst_facts Hs. mem_facts Hm. pose proof Ix as Ix'. inputs_facts Ix'.
  unfold E_STREAM_INIT in Ge.
  assert (La0: 0 <= Zlength a) by apply Zlength_nonneg.
  unfold lfields. Intros.
  forward.
  if2. gp.
  if2. if2. if2. gp.
  forward_call tt. Intros v.
  forward. vl_temps. forward.
  upd_vl.
  forward.
  forward_if.
  - (* another word *)
    forward. forward. forward.
    Exists v. u64c.
    assert (Rn: run x (start x) (h ++ [(StreamInit (i_magic x) (i_address x) (m_total m) (i_address x) (Zlength a), v)])
                = Some (Go (ExpectStreamInit (a ++ [v])) m)).
    { rewrite (run_snoc' x h (ExpectStreamInit a) m _ v Hrun Ec). cbn [step].
      rewrite step_more by lia. reflexivity. }
    assert (HJ': J x (Go (ExpectStreamInit (a ++ [v])) m) (s_more s v)).
    { unfold J; split_and; auto.
      - apply lst_ok_more; auto; lia.
      - unfold go_inv, s_more; lst_cbn; split_and; auto.
        + apply prefix_more; [ split; auto | lia ].
        + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
    change (Vlong (Int64.repr (w_word s + 1))) with (vl (w_word s + 1)).
    ora_fin (Go (ExpectStreamInit (a ++ [v])) m) (s_more s v) ce ie.
  - (* word 6: the reset's checks *)
    u64c.
    assert (W6: w_word s = 6) by lia.
    assert (L7: Zlength a = 6) by lia.
    assert (Fa: Forall u64_ok a) by (rewrite <- Pa; apply Forall_u64_sublist; auto).
    assert (Fa': Forall u64_ok (a ++ [v])) by (apply Forall_u64_app1; auto).
    assert (La': Zlength (a ++ [v]) = 7) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    assert (Ea: a ++ [v] = sublist 0 7 (upd_Znth (w_word s) (w_answer s) v))
      by (apply answers_last; auto; [ split; auto | lia | lia ]).
    rng_list (a ++ [v]) 7.
    assert (Rn: run x (start x) (h ++ [(StreamInit (i_magic x) (i_address x) (m_total m) (i_address x) (Zlength a), v)])
                = Some (stream_init_done x (a ++ [v]) m)).
    { rewrite (run_snoc' x h (ExpectStreamInit a) m _ v Hrun Ec). cbn [step].
      rewrite step_last by lia. reflexivity. }
    assert (Lans: Zlength (upd_Znth (w_word s) (w_answer s) v) = WORDS) by (rewrite upd_Znth_Zlength; lia).
    freeze_but [_answer; _stream] (@nil val) FL.
    forward_for_simple_bound 7
      (EX i: Z, PROP ()
       LOCAL (temp _v (Vlong (Int64.repr v)); temp _m (gv _law); gvars gv)
       SEP (FRZL FL; field_at Ews t_law (DOT _answer) (map vl (upd_Znth (w_word s) (w_answer s) v)) (gv _law);
            field_at Ews t_law (DOT _stream) (map vl (sublist 0 i (upd_Znth (w_word s) (w_answer s) v) ++ sublist i 7 (w_stream s))) (gv _law)))%assert.
    { entailer!. rewrite sublist_nil, app_nil_l, sublist_same by lia. apply derives_refl. }
    { forward. try rewrite Znth_map_vl by lia. forward. upd_vl.
      entailer!. apply derives_refl'. do 2 f_equal. list_solve. }
    thaw FL.
    replace (sublist 0 7 (upd_Znth (w_word s) (w_answer s) v) ++ sublist 7 7 (w_stream s)) with (a ++ [v])
      by (rewrite Ea, sublist_nil, app_nil_r; reflexivity).
    assert (Hs1: lst_ok (s_stream (s_store s v) (a ++ [v]))) by (apply lst_ok_stream; auto; apply lst_ok_store; auto).
    forward. norm_vl.
    forward_if (PROP () LOCAL (temp _v (vl v))
      SEP (Ora_law gv (gv _law) (gv _law) x
             (h ++ [(StreamInit (i_magic x) (i_address x) (m_total m) (i_address x) (Zlength a), v)]))).
    { si_stop gv x m a v s ce ie Rn Hm S_STREAM_INIT_VERSION. }
    forward. norm_vl. forward_if.
    { si_stop gv x m a v s ce ie Rn Hm S_STREAM_INIT_STATUS. }
    forward. norm_vl. forward_if.
    { si_stop gv x m a v s ce ie Rn Hm S_STREAM_INIT_ERROR. }
    forward. norm_vl. forward. forward_if.
    { si_stop gv x m a v s ce ie Rn Hm S_STREAM_INIT_IDENTITY. }
    forward. norm_vl. forward. forward_if.
    { si_stop gv x m a v s ce ie Rn Hm S_STREAM_INIT_EXTENT. }
    forward. norm_vl. forward_if.
    { si_stop gv x m a v s ce ie Rn Hm S_STREAM_INIT_OFFSET. }
    { (* chunk 0 *)
      u64c.
      assert (C: stream_init_check x (m_total m) (a ++ [v]) = S_OK) by (unfold stream_init_check; chk_dec).
      assert (R': stream_init_done x (a ++ [v]) m = begin_chunk x 0 (a ++ [v]) m)
        by (unfold stream_init_done; rewrite C; reflexivity).
      rewrite R' in Rn.
      sep_apply (lfields_fold (gv _law) x ce ie m (s_stream (s_store s v) (a ++ [v]))).
      forward_call (gv _law, x, ce, ie, m, s_stream (s_store s v) (a ++ [v]), 0).
      Intros s2. cbn [w_stream s_stream] in *.
      unfold Ora_law. Exists (begin_chunk x 0 (a ++ [v]) m) s2 ce ie. rewrite arrays_begin_chunk.
      entailer!. }
    forward. Exists v. entailer!.
Qed.
