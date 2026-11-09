(* Law handoff_decode_exact: the bodies of the harness's helpers any_u64, stop, begin_stream and begin_decode
   (begin_chunk and begin_transition are in LawChunk, decode_done in LawDone): each moves the law's record as the
   model's function of the same name moves the model. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosHandoff.harness.handoff_decode_exact.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.LawProg LeanosHandoff.proof.LawDefs LeanosHandoff.proof.LawFacts
  LeanosHandoff.proof.LawLib.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

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

Lemma body_begin_stream: semax_body nil nil f_begin_stream begin_stream_spec.
Proof. start_function. forward. forward. entailer!. Qed.

(* The record after begin_decode, and its invariant. *)
Definition s_decode (s: lst) : lst :=
  mk_lst (w_running s) (w_records s) E_DECODE_INIT (w_verdict s) (w_chunk s) 0 (w_block s) (w_value s)
         (w_stream s) (w_answer s).

Lemma J_begin_decode: forall x m s, lst_ok s -> mem_fit x m -> dec_ctx x m -> J x (begin_decode x m) (s_decode s).
Proof.
  intros x m s Hs Hm Hd. lst_facts Hs. unfold J. split_and.
  - unfold lst_ok, s_decode; lst_cbn. split_and; auto; unfold u32_ok, u64_ok, E_DECODE_INIT; rep_lia.
  - rewrite mem_of_begin_decode. destruct (projection x); [ apply mem_fit_zeros | ]; auto.
  - unfold begin_decode, go_inv. split_and; auto.
    { apply prefix_nil. reflexivity. }
    { rewrite Zlength_nil. lia. }
    { destruct (projection x); [ apply dec_ctx_bitmaps | ]; auto. }
Qed.

Lemma body_begin_decode: semax_body nil nil f_begin_decode begin_decode_spec.
Proof.
  start_function.
  rename H into Ix, H0 into Hs, H1 into Hm, H2 into Hd.
  pose proof (J_begin_decode x m s Hs Hm Hd) as HJ.
  lst_facts Hs. mem_facts Hm.
  try rewrite mem_of_begin_decode in *.
  unfold lfields. Intros.
  forward.
  destruct (projection x) eqn:P; unfold proj_code; rewrite P.
  - (* with a projection: the bitmaps zeroed *)
    cbn [m_usable m_blocked m_reserved m_states m_at m_total m_extent_ok with_bitmaps].
    forward_if (PROP ()
      LOCAL (temp _m q)
      SEP (field_at Ews t_law (DOT _call) (vi (call_code (i_call x))) q;
           field_at Ews t_law (DOT _magic) (vi (i_magic x)) q;
           field_at Ews t_law (DOT _address) (vi (i_address x)) q;
           field_at Ews t_law (DOT _total) (vi (m_total m)) q;
           field_at Ews t_law (DOT _candidate) (vl (target x)) q;
           field_at Ews t_law (DOT _projection) (vi 1) q;
           field_at Ews t_law (DOT _running) (vi (w_running s)) q;
           field_at Ews t_law (DOT _copy_expect) ce q;
           field_at Ews t_law (DOT _info_expect) ie q;
           field_at Ews t_law (DOT _usable_expect) (map vl zeros) q;
           field_at Ews t_law (DOT _blocked_expect) (map vl zeros) q;
           field_at Ews t_law (DOT _reserved_expect) (map vl zeros) q;
           field_at Ews t_law (DOT _states_expect) (states_val (m_states m)) q;
           field_at Ews t_law (DOT _at) (vi (m_at m)) q;
           field_at Ews t_law (DOT _extent_ok) (vi (Z.b2z (m_extent_ok m))) q;
           field_at Ews t_law (DOT _records) (vi (w_records s)) q;
           field_at Ews t_law (DOT _expect) (vi (w_expect s)) q;
           field_at Ews t_law (DOT _verdict) (vi (w_verdict s)) q;
           field_at Ews t_law (DOT _chunk) (vl (w_chunk s)) q;
           field_at Ews t_law (DOT _word) (vl (w_word s)) q;
           field_at Ews t_law (DOT _block) (vl (w_block s)) q;
           field_at Ews t_law (DOT _value) (vl (w_value s)) q;
           field_at Ews t_law (DOT _stream) (map vl (w_stream s)) q;
           field_at Ews t_law (DOT _answer) (map vl (w_answer s)) q)).
    + forward_for_simple_bound 64
        (EX b: Z, PROP ()
         LOCAL (temp _m q)
         SEP (field_at Ews t_law (DOT _call) (vi (call_code (i_call x))) q;
              field_at Ews t_law (DOT _magic) (vi (i_magic x)) q;
              field_at Ews t_law (DOT _address) (vi (i_address x)) q;
              field_at Ews t_law (DOT _total) (vi (m_total m)) q;
              field_at Ews t_law (DOT _candidate) (vl (target x)) q;
              field_at Ews t_law (DOT _projection) (vi 1) q;
              field_at Ews t_law (DOT _running) (vi (w_running s)) q;
              field_at Ews t_law (DOT _copy_expect) ce q;
              field_at Ews t_law (DOT _info_expect) ie q;
              field_at Ews t_law (DOT _usable_expect) (map vl (Zrepeat 0 b ++ sublist b 64 (m_usable m))) q;
              field_at Ews t_law (DOT _blocked_expect) (map vl (Zrepeat 0 b ++ sublist b 64 (m_blocked m))) q;
              field_at Ews t_law (DOT _reserved_expect) (map vl (Zrepeat 0 b ++ sublist b 64 (m_reserved m))) q;
              field_at Ews t_law (DOT _states_expect) (states_val (m_states m)) q;
              field_at Ews t_law (DOT _at) (vi (m_at m)) q;
              field_at Ews t_law (DOT _extent_ok) (vi (Z.b2z (m_extent_ok m))) q;
              field_at Ews t_law (DOT _records) (vi (w_records s)) q;
              field_at Ews t_law (DOT _expect) (vi (w_expect s)) q;
              field_at Ews t_law (DOT _verdict) (vi (w_verdict s)) q;
              field_at Ews t_law (DOT _chunk) (vl (w_chunk s)) q;
              field_at Ews t_law (DOT _word) (vl (w_word s)) q;
              field_at Ews t_law (DOT _block) (vl (w_block s)) q;
              field_at Ews t_law (DOT _value) (vl (w_value s)) q;
              field_at Ews t_law (DOT _stream) (map vl (w_stream s)) q;
              field_at Ews t_law (DOT _answer) (map vl (w_answer s)) q))%assert.
      { rewrite !sublist_same by auto. entailer!. }
      { forward. forward. forward.
        change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with (vl 0).
        rewrite !upd_Znth_map_vl.
        replace (upd_Znth i (Zrepeat 0 i ++ sublist i 64 (m_usable m)) 0)
          with (Zrepeat 0 (i + 1) ++ sublist (i + 1) 64 (m_usable m)) by list_solve.
        replace (upd_Znth i (Zrepeat 0 i ++ sublist i 64 (m_blocked m)) 0)
          with (Zrepeat 0 (i + 1) ++ sublist (i + 1) 64 (m_blocked m)) by list_solve.
        replace (upd_Znth i (Zrepeat 0 i ++ sublist i 64 (m_reserved m)) 0)
          with (Zrepeat 0 (i + 1) ++ sublist (i + 1) 64 (m_reserved m)) by list_solve.
        entailer!. }
      rewrite !sublist_nil, !app_nil_r. entailer!.
    + else_false.
    + forward. forward.
      Exists (s_decode s). unfold lfields, s_decode. lst_cbn.
      change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with (vl 0).
      change (Vint (Int.repr 4)) with (vi E_DECODE_INIT).
      rewrite mem_of_begin_decode, P. unfold proj_code. rewrite P.
      entailer!.
  - (* without one *)
    freeze_but (@nil ident) (@nil val) F.
    forward_if (PROP () LOCAL (temp _m q) SEP (FRZL F)).
    + else_false.
    + forward. entailer!.
    + thaw F. forward. forward.
      Exists (s_decode s). unfold lfields, s_decode. lst_cbn.
      change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with (vl 0).
      change (Vint (Int.repr 4)) with (vi E_DECODE_INIT).
      rewrite mem_of_begin_decode, P. unfold proj_code. rewrite P.
      entailer!.
Qed.
