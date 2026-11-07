(* Law handoff_decode_exact: the bodies of the harness's begin_chunk and begin_transition: the stream's next chunk
   or its final checks (then the copy's end: OK, or the allocation's decoder), and the decoder's next chunk or
   decode_done, as the model's begin_chunk and begin_transition. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosHandoff.harness.handoff_decode_exact.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.LawProg LeanosHandoff.proof.LawDefs LeanosHandoff.proof.LawFacts
  LeanosHandoff.proof.LawLib.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Existing Instance LawProg.LCS.

Ltac norm_vl := repeat (rewrite Znth_map_vl in * by lia).

Lemma body_begin_chunk: semax_body nil [stop_spec; begin_decode_spec] f_begin_chunk begin_chunk_spec.
Proof.
  start_function.
  rename H into Ix, H0 into Hs, H1 into Hm, H2 into Hc, H3 into Hk.
  lst_facts Hs. mem_facts Hm.
  pose proof (call_code_range (i_call x)) as Rc.
  pose proof Hc as (Cc & Te & Tm).
  rng_list (w_stream s) 7.
  unfold lfields. Intros.
  forward.
  forward_if.
  - (* chunk k *)
    u64c.
    forward. forward. forward.
    assert (E: begin_chunk x k (w_stream s) m = Go (ExpectChunk k (w_stream s)) m)
      by (unfold begin_chunk; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
    Exists (mk_lst (w_running s) (w_records s) E_CHUNK (w_verdict s) k (w_word s) (w_block s) (w_value s)
                   (w_stream s) (w_answer s)).
    rewrite E. cbn [mem_of]. unfold lfields; lst_cbn.
    change (Vint (Int.repr 2)) with (vi E_CHUNK).
    entailer!.
    unfold J; split_and; auto.
    + unfold lst_ok; lst_cbn; split_and; auto; unfold u32_ok, u64_ok, E_CHUNK; rep_lia.
    + unfold go_inv; lst_cbn; split_and; auto; lia.
  - (* the stream's final checks *)
    u64c.
    assert (Eb: begin_chunk x k (w_stream s) m = copy_end x (stream_final (m_total m) (w_stream s)) m)
      by (unfold begin_chunk; destruct (Z.ltb_spec (8 * k) (m_total m)); [ lia | reflexivity ]).
    forward. norm_vl.
    forward_if.
    { u64c.
      assert (E: begin_chunk x k (w_stream s) m = Return S_STREAM_INCOMPLETE_STATUS m)
        by (rewrite Eb; unfold copy_end, stream_final;
            rewrite (proj2 (Z.eqb_neq (Znth 1 (w_stream s)) 1)) by assumption; reflexivity).
      forward_call (q, vi (w_expect s), vi (w_verdict s), S_STREAM_INCOMPLETE_STATUS).
      forward.
      Exists (s_stop s S_STREAM_INCOMPLETE_STATUS). rewrite E. cbn [mem_of]. unfold lfields, s_stop; lst_cbn.
      entailer!. apply J_stop; auto; unfold u32_ok, S_STREAM_INCOMPLETE_STATUS; rep_lia. }
    u64c.
    forward. norm_vl. forward.
    forward_if.
    { u64c.
      assert (E: begin_chunk x k (w_stream s) m = Return S_STREAM_INCOMPLETE_OFFSET m)
        by (rewrite Eb; unfold copy_end, stream_final;
            rewrite (proj2 (Z.eqb_eq (Znth 1 (w_stream s)) 1)) by assumption;
            rewrite (proj2 (Z.eqb_neq (Znth 5 (w_stream s)) (m_total m))) by assumption; reflexivity).
      forward_call (q, vi (w_expect s), vi (w_verdict s), S_STREAM_INCOMPLETE_OFFSET).
      forward.
      Exists (s_stop s S_STREAM_INCOMPLETE_OFFSET). rewrite E. cbn [mem_of]. unfold lfields, s_stop; lst_cbn.
      entailer!. apply J_stop; auto; unfold u32_ok, S_STREAM_INCOMPLETE_OFFSET; rep_lia. }
    u64c.
    assert (Ef: stream_final (m_total m) (w_stream s) = S_OK)
      by (unfold stream_final; rewrite (proj2 (Z.eqb_eq (Znth 1 (w_stream s)) 1)) by assumption;
          rewrite (proj2 (Z.eqb_eq (Znth 5 (w_stream s)) (m_total m))) by assumption; reflexivity).
    forward.
    forward_if.
    + (* a copy alone: OK *)
      u64c.
      assert (C: i_call x = FCopy) by (apply call_code_inj; assumption).
      assert (E: begin_chunk x k (w_stream s) m = Return S_OK m)
        by (rewrite Eb, Ef; unfold copy_end; rewrite C; reflexivity).
      forward_call (q, vi (w_expect s), vi (w_verdict s), S_OK).
      Exists (s_stop s S_OK). rewrite E. cbn [mem_of]. unfold lfields, s_stop; lst_cbn.
      entailer!. apply J_stop; auto; unfold u32_ok, S_OK; rep_lia.
    + (* an allocation: the decoder *)
      u64c.
      assert (C: i_call x = FAllocate)
        by (destruct Cc as [C | C]; [ exact C | rewrite C in *; simpl in *; contradiction ]).
      assert (E: begin_chunk x k (w_stream s) m = begin_decode x m)
        by (rewrite Eb, Ef; unfold copy_end; rewrite C; reflexivity).
      assert (Hd: dec_ctx x m) by (apply dec_ctx_of_copy; auto; rewrite C; discriminate).
      sep_apply (lfields_fold q x ce ie m s).
      forward_call (q, x, ce, ie, m, s).
      Intros s'. Exists s'. rewrite E. entailer!.
Qed.

(* A word of the words decoded. *)
Lemma decoded_word: forall x m k, mem_fit x m -> x_fit x -> i_call x <> FCopy -> 0 <= k < Zlength (decoded x m) ->
  u64_ok (Znth k (decoded x m)).
Proof.
  intros x m k F Xf Nc K. unfold decoded in *. unfold x_fit, has_copy in Xf. destruct F as (_ & _ & Fc & _).
  unfold has_copy in Fc. destruct (i_call x) eqn:C.
  - apply Forall_u64_Znth; [ apply Fc; reflexivity | exact K ].
  - contradiction.
  - destruct (Xf eq_refl) as (Xi & _). apply Forall_u64_Znth; auto.
  - destruct (Xf eq_refl) as (Xi & _). apply Forall_u64_Znth; auto.
Qed.

Lemma body_begin_transition: semax_body nil [decode_done_spec] f_begin_transition begin_transition_spec.
Proof.
  start_function.
  rename H into Ix, H0 into Hs, H1 into Hm, H2 into Hd, H3 into Xf, H4 into Hk.
  lst_facts Hs. mem_facts Hm.
  pose proof Hd as (Nc & (Te & Tm) & Td).
  unfold lfields. Intros.
  forward.
  forward_if.
  - (* chunk k *)
    u64c.
    assert (Kd: 0 <= k < Zlength (decoded x m)).
    { split; [ lia | ]. pose proof (Z.div_mod (m_total m) 8 ltac:(lia)) as Dm. rewrite Tm in Dm. lia. }
    pose proof (decoded_word x m k Hm Xf Nc Kd) as Vk. unfold u64_ok in Vk.
    forward. forward. change (temp _k (vl k)) with (temp _k (Vlong (Int64.repr k))). forward.
    try rewrite Znth_map_vl by lia.
    forward. forward. forward. forward.
    assert (E: begin_transition x k m = Go (ExpectDecodeStep k nil) m)
      by (unfold begin_transition; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
    Exists (mk_lst (w_running s) (w_records s) E_DECODE_STEP (w_verdict s) k 0 (w_block s) (Znth k (decoded x m))
                   (w_stream s) (w_answer s)).
    rewrite E. unfold lfields; lst_cbn.
    change (Vint (Int.repr 5)) with (vi E_DECODE_STEP).
    change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with (vl 0).
    entailer!.
    unfold J; split_and; auto.
    + unfold lst_ok; lst_cbn; split_and; auto; unfold u32_ok, u64_ok, E_DECODE_STEP; rep_lia.
    + unfold go_inv; lst_cbn; split_and; auto; try lia.
      * apply prefix_nil. reflexivity.
      * rewrite Zlength_nil. lia.
  - (* the end *)
    u64c.
    assert (E: begin_transition x k m = decode_done x m)
      by (unfold begin_transition; destruct (Z.ltb_spec (8 * k) (m_total m)); [ lia | reflexivity ]).
    sep_apply (lfields_fold q x ce ie m s).
    forward_call (q, x, ce, ie, m, s).
    Intros s'. Exists s'. rewrite E. entailer!.
Qed.
