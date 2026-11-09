(* Law handoff_decode_exact: the decoder transition export from its check of the state's words 23..38 on: those
   checks, then its checks of the chunk, its offset and terminal marker, the answer, and the next word or the
   transition's end (LawDecodeStepDone). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosHandoff.harness.handoff_decode_exact.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.LawProg LeanosHandoff.proof.LawDefs LeanosHandoff.proof.LawFacts
  LeanosHandoff.proof.LawLib LeanosHandoff.proof.LawLib2 LeanosHandoff.proof.LawLib3
  LeanosHandoff.proof.LawDecodeStepDone.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Existing Instance LawProg.LCS.

(* struct law but its states. *)
Definition lfields_ns (q: val) (x: inputs) (ce ie: val) (m: mem) (s: lst) : mpred :=
 (field_at Ews t_law (DOT _call) (vi (call_code (i_call x))) q *
  field_at Ews t_law (DOT _magic) (vi (i_magic x)) q *
  field_at Ews t_law (DOT _address) (vi (i_address x)) q *
  field_at Ews t_law (DOT _total) (vi (m_total m)) q *
  field_at Ews t_law (DOT _candidate) (vl (target x)) q *
  field_at Ews t_law (DOT _projection) (vi (proj_code x)) q *
  field_at Ews t_law (DOT _running) (vi (w_running s)) q *
  field_at Ews t_law (DOT _copy_expect) ce q *
  field_at Ews t_law (DOT _info_expect) ie q *
  field_at Ews t_law (DOT _usable_expect) (map vl (m_usable m)) q *
  field_at Ews t_law (DOT _blocked_expect) (map vl (m_blocked m)) q *
  field_at Ews t_law (DOT _reserved_expect) (map vl (m_reserved m)) q *
  field_at Ews t_law (DOT _at) (vi (m_at m)) q *
  field_at Ews t_law (DOT _extent_ok) (vi (Z.b2z (m_extent_ok m))) q *
  field_at Ews t_law (DOT _records) (vi (w_records s)) q *
  field_at Ews t_law (DOT _expect) (vi (w_expect s)) q *
  field_at Ews t_law (DOT _verdict) (vi (w_verdict s)) q *
  field_at Ews t_law (DOT _chunk) (vl (w_chunk s)) q *
  field_at Ews t_law (DOT _word) (vl (w_word s)) q *
  field_at Ews t_law (DOT _block) (vl (w_block s)) q *
  field_at Ews t_law (DOT _value) (vl (w_value s)) q *
  field_at Ews t_law (DOT _stream) (map vl (w_stream s)) q *
  field_at Ews t_law (DOT _answer) (map vl (w_answer s)) q)%logic.

Lemma lfields_ns_fold: forall q x ce ie m s,
 (field_at Ews t_law (DOT _call) (vi (call_code (i_call x))) q *
  field_at Ews t_law (DOT _magic) (vi (i_magic x)) q *
  field_at Ews t_law (DOT _address) (vi (i_address x)) q *
  field_at Ews t_law (DOT _total) (vi (m_total m)) q *
  field_at Ews t_law (DOT _candidate) (vl (target x)) q *
  field_at Ews t_law (DOT _projection) (vi (proj_code x)) q *
  field_at Ews t_law (DOT _running) (vi (w_running s)) q *
  field_at Ews t_law (DOT _copy_expect) ce q *
  field_at Ews t_law (DOT _info_expect) ie q *
  field_at Ews t_law (DOT _usable_expect) (map vl (m_usable m)) q *
  field_at Ews t_law (DOT _blocked_expect) (map vl (m_blocked m)) q *
  field_at Ews t_law (DOT _reserved_expect) (map vl (m_reserved m)) q *
  field_at Ews t_law (DOT _at) (vi (m_at m)) q *
  field_at Ews t_law (DOT _extent_ok) (vi (Z.b2z (m_extent_ok m))) q *
  field_at Ews t_law (DOT _records) (vi (w_records s)) q *
  field_at Ews t_law (DOT _expect) (vi (w_expect s)) q *
  field_at Ews t_law (DOT _verdict) (vi (w_verdict s)) q *
  field_at Ews t_law (DOT _chunk) (vl (w_chunk s)) q *
  field_at Ews t_law (DOT _word) (vl (w_word s)) q *
  field_at Ews t_law (DOT _block) (vl (w_block s)) q *
  field_at Ews t_law (DOT _value) (vl (w_value s)) q *
  field_at Ews t_law (DOT _stream) (map vl (w_stream s)) q *
  field_at Ews t_law (DOT _answer) (map vl (w_answer s)) q)%logic |-- lfields_ns q x ce ie m s.
Proof. intros. apply derives_refl. Qed.

(* The statement from the check of words 23..38 on. *)
Definition s_dsw : statement := ltac:(
  let b := eval cbv delta [f_leanos_boot_decode_step_v5] beta iota zeta in (fn_body f_leanos_boot_decode_step_v5) in
  match b with context [Ssequence ?A ?B] =>
    let s := first_stmt A in match s with Sset _t'70 _ => exact (Ssequence A B) end end).

Lemma ds_words {Espec: OracleKind} gv x h w m a ce ie:
  inputs_ok x -> x_fit x -> ptr_ok x ce ie ->
  run x (start x) h = Some (Go (ExpectDecodeStep (w_chunk w) a) m) ->
  J x (Go (ExpectDecodeStep (w_chunk w) a) m) w ->
  forall Delta R c, Delta = Delta_ds ->
  R = Post_ds gv x h (DecodeStep (current m) (i_address x) (8 * w_chunk w) (Znth (w_chunk w) (decoded x m))
                        (terminal (m_total m) (w_chunk w)) (Zlength a)) ->
  c = s_dsw ->
  semax Delta
    (PROP ()
     LOCAL (temp _o (row (gv _law) (m_at m)); temp _m (gv _law); gvars gv;
            temp _s23 (vl (Znth 23 (current m))); temp _s24 (vl (Znth 24 (current m)));
            temp _s25 (vl (Znth 25 (current m))); temp _s26 (vl (Znth 26 (current m)));
            temp _s27 (vl (Znth 27 (current m))); temp _s28 (vl (Znth 28 (current m)));
            temp _s29 (vl (Znth 29 (current m))); temp _s30 (vl (Znth 30 (current m)));
            temp _s31 (vl (Znth 31 (current m))); temp _s32 (vl (Znth 32 (current m)));
            temp _s33 (vl (Znth 33 (current m))); temp _s34 (vl (Znth 34 (current m)));
            temp _s35 (vl (Znth 35 (current m))); temp _s36 (vl (Znth 36 (current m)));
            temp _s37 (vl (Znth 37 (current m))); temp _s38 (vl (Znth 38 (current m)));
            temp _stream_identity (vl (i_address x)); temp _stream_offset (vl (8 * w_chunk w));
            temp _chunk (vl (Znth (w_chunk w) (decoded x m)));
            temp _terminal (vl (terminal (m_total m) (w_chunk w))); temp _query (vl (Zlength a)))
     SEP (lfields_ns (gv _law) x ce ie m w; data_at Ews t_state (map vl (current m)) (row (gv _law) (m_at m));
          data_at Ews t_state (map vl (Znth (1 - m_at m) (m_states m))) (row (gv _law) (1 - m_at m));
          arrays x ce ie m))
    c R.
Proof.
  intros Ix Xf Pie Hrun HJ Delta R c -> -> ->.
  unfold s_dsw, Delta_ds, Post_ds. start_tail.
  pose proof HJ as (Hs & Hm & G). cbn [mem_of] in *.
  pose proof G as (Ge & Gk & Gv & (Pw & Pa) & La & Gk0 & Gkt & Dc).
  pose proof Hs as Hs'. lst_facts Hs'. mem_facts Hm. pose proof Ix as Ix'. inputs_facts Ix'.
  pose proof Dc as (Nc' & (Te & Tm) & Td).
  unfold E_DECODE_STEP in Ge.
  assert (La0: 0 <= Zlength a) by apply Zlength_nonneg.
  pose proof (current_ok x m Hm) as Cok.
  assert (Lcs: Zlength (current m) = WORDS) by apply Cok.
  assert (Lmcs: Zlength (map vl (current m)) = WORDS) by (rewrite Zlength_map; lia).
  assert (Kd: 0 <= w_chunk w < Zlength (decoded x m)).
  { split; [ lia | ]. pose proof (Z.div_mod (m_total m) 8 ltac:(lia)) as Dm. rewrite Tm in Dm. lia. }
  assert (Rv: 0 <= w_value w <= Int64.max_unsigned) by lia.
  pose proof (terminal_range (m_total m) (w_chunk w)) as Rt.
  assert (Ec: DecodeStep (current m) (i_address x) (8 * w_chunk w) (Znth (w_chunk w) (decoded x m))
                (terminal (m_total m) (w_chunk w)) (Zlength a) = expected x (ExpectDecodeStep (w_chunk w) a) m)
    by reflexivity.
  assert_PROP (field_compatible t_law (DOT _states_expect) (gv _law)) as FCs
    by (unfold lfields_ns; entailer!).
  unfold lfields_ns. Intros.
  freeze_but (@nil ident) [row (gv _law) (m_at m)] FZ.
  if2. if2. if2. if2. if2. if2. if2. if2. if2. if2.
  if2. if2. if2. if2. if2. gp.
  thaw FZ.
  forward. forward. forward.
  change (Int.signed (Int.repr 8)) with 8.
  rewrite mul64_repr', add64_repr', (Int.unsigned_repr (m_total m)) by rep_lia.
  unfold Int64.cmpu. rewrite (Int64_eq_repr (8 * w_chunk w + 8) (m_total m)) by rep_lia.
  rewrite b2z_terminal.
  if3. if3. if3. gp.
  forward_call tt. Intros v.
  forward. vl_temps. forward.
  upd_vl.
  forward.
  forward_if.
  - (* another word *)
    change (Int.sub (Int.repr 41) (Int.repr 1)) with (Int.repr 40) in *.
    forward. forward. forward.
    Exists v. u64c.
    assert (Rn: run x (start x) (h ++ [(DecodeStep (current m) (i_address x) (8 * w_chunk w)
                                          (Znth (w_chunk w) (decoded x m)) (terminal (m_total m) (w_chunk w))
                                          (Zlength a), v)])
                = Some (Go (ExpectDecodeStep (w_chunk w) (a ++ [v])) m)).
    { rewrite (run_snoc' x h (ExpectDecodeStep (w_chunk w) a) m _ v Hrun Ec). cbn [step].
      rewrite step_more by lia. reflexivity. }
    assert (HJ': J x (Go (ExpectDecodeStep (w_chunk w) (a ++ [v])) m) (s_more w v)).
    { unfold J; split_and; auto.
      - apply lst_ok_more; auto; lia.
      - unfold go_inv, s_more; lst_cbn; split_and; auto.
        + apply prefix_more; [ split; auto | lia ].
        + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
    sep_apply (rows_fold (gv _law) (m_states m) (m_at m) FCs Fsl Fs0 Fs1 Fat).
    change (Vlong (Int64.repr (w_word w + 1))) with (vl (w_word w + 1)).
    ora_fin3 gv x h (Go (ExpectDecodeStep (w_chunk w) (a ++ [v])) m) m m (s_more w v) ce ie Ix Xf Rn HJ' Pie.
  - (* word 40: the transition's state and its end *)
    change (Int.sub (Int.repr 41) (Int.repr 1)) with (Int.repr 40) in *.
    u64c.
    assert (W40: w_word w = 40) by lia.
    sep_apply (rows_fold (gv _law) (m_states m) (m_at m) FCs Fsl Fs0 Fs1 Fat).
    sep_apply (lfields_fold (gv _law) x ce ie m (s_store w v)).
    eapply semax_pre;
      [ | apply (ds_tail gv x h w m (w_chunk w) a v ce ie); first [ reflexivity | assumption | auto ] ].
    entailer!.
Qed.
