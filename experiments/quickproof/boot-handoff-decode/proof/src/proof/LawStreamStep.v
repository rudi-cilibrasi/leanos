(* Law handoff_decode_exact: the body of the harness's stream transition export against stream_step_spec Ora_law:
   its checks follow from the call the model expects (the carried state, the chunk as read, its offset and
   terminal marker), and the answer it records moves the law's record as the model's step: the next word, or after
   word 8 the transition's checks, then the chunk to the copy and the next chunk (begin_chunk). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosHandoff.harness.handoff_decode_exact.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.LawProg LeanosHandoff.proof.LawDefs LeanosHandoff.proof.LawFacts
  LeanosHandoff.proof.LawLib LeanosHandoff.proof.LawLib2 LeanosHandoff.proof.LawStreamStep2.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Existing Instance LawProg.LCS.

Lemma body_stream_step: semax_body Vlaw Gstep f_leanos_boot_handoff_stream_step (stream_step_spec Ora_law).
Proof.
  start_function.
  rename H into Nc.
  ora_open x h p s ce ie.
  destruct (next_go x h p _ Hrun Nc) as (g & m & -> & Ec).
  destruct (call_stream_step x g m _ _ _ _ _ _ _ (eq_sym Ec)) as (k & c & a & -> & -> & -> & -> & -> & -> & ->).
  pose proof HJ as (Hs & Hm & G). cbn [mem_of] in *.
  pose proof G as (Ge & Gk & Gst & Gc & (Pw & Pa) & La & Gk0 & Gkt & Cc).
  subst k st c.
  lst_facts Hs. mem_facts Hm. pose proof Ix as Ix'. inputs_facts Ix'.
  pose proof Cc as (Ccall & Te & Tm).
  unfold E_STREAM_STEP in Ge.
  assert (La0: 0 <= Zlength a) by apply Zlength_nonneg.
  rng_list (w_stream s) 7.
  unfold lfields. Intros.
  forward.
  if2. gp.
  if2. if2. if2. if2. if2. if2. gp.
  forward. forward. forward. forward.
  change (Int.signed (Int.repr 8)) with 8.
  rewrite mul64_repr', add64_repr', (Int.unsigned_repr (m_total m)) by rep_lia.
  unfold Int64.cmpu. rewrite (Int64_eq_repr (8 * w_chunk s + 8) (m_total m)) by rep_lia.
  rewrite b2z_terminal.
  if3. if3. if3. if3. gp.
  forward_call tt. Intros v.
  forward. vl_temps. forward.
  upd_vl.
  forward.
  forward_if.
  - (* another word *)
    forward. forward. forward.
    Exists v. u64c.
    assert (Rn: run x (start x) (h ++ [(StreamStep (w_stream s) (i_address x) (8 * w_chunk s) 8 (w_value s)
                                          (terminal (m_total m) (w_chunk s)) (Zlength a), v)])
                = Some (Go (ExpectStreamStep (w_chunk s) (w_stream s) (w_value s) (a ++ [v])) m)).
    { rewrite (run_snoc' x h (ExpectStreamStep (w_chunk s) (w_stream s) (w_value s) a) m _ v Hrun Ec). cbn [step].
      rewrite step_more by lia. reflexivity. }
    assert (HJ': J x (Go (ExpectStreamStep (w_chunk s) (w_stream s) (w_value s) (a ++ [v])) m) (s_more s v)).
    { unfold J; split_and; auto.
      - apply lst_ok_more; auto; lia.
      - unfold go_inv, s_more; lst_cbn; split_and; auto.
        + apply prefix_more; [ split; auto | lia ].
        + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
    change (Vlong (Int64.repr (w_word s + 1))) with (vl (w_word s + 1)).
    ora_fin (Go (ExpectStreamStep (w_chunk s) (w_stream s) (w_value s) (a ++ [v])) m) (s_more s v) ce ie.
  - (* word 8: the transition's checks *)
    u64c.
    assert (W8: w_word s = 8) by lia.
    sep_apply (lfields_fold (gv _law) x ce ie m (s_store s v)).
    eapply semax_pre; [ | apply (ss_tail gv x h s m a v ce ie); first [ reflexivity | assumption | auto ] ].
    entailer!.
Qed.
