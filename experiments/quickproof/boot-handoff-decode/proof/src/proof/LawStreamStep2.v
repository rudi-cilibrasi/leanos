(* Law handoff_decode_exact: the stream transition export after the answer of its last word is recorded (word 8):
   the transition's checks on the answers (read through `a = m->answer`), then the chunk to the copy, the carried
   state, and the next chunk (begin_chunk); or the rejection. *)
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

Definition Gstep : funspecs := [gp_assert_spec; any_u64_spec; stop_spec; begin_chunk_spec].

Definition Delta_ss : tycontext := func_tycontext f_leanos_boot_handoff_stream_step Vlaw Gstep nil.
Definition Post_ss gv x h c : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tulong
       (EX v: Z, PROP (u64_ok v) RETURN (vl v) SEP (Ora_law gv (gv _law) (gv _law) x (h ++ [(c, v)])))%argsassert)
    (stackframe_of f_leanos_boot_handoff_stream_step).

(* The statement from `a = m->answer` on. *)
Definition s_ss_tail : statement := ltac:(
  let b := eval cbv delta [f_leanos_boot_handoff_stream_step] beta iota zeta
             in (fn_body f_leanos_boot_handoff_stream_step) in
  match b with context [Ssequence (Sset _a ?e) ?rest] => exact (Ssequence (Sset _a e) rest) end).

Lemma answer_ptr: forall q o, o = OFS_ANSWER -> offset_val o q = offset_val OFS_ANSWER q.
Proof. intros. subst. reflexivity. Qed.

(* The answer pointer's value, computed. *)
Ltac fix_answer :=
  match goal with |- context [temp _a (offset_val ?o ?q)] =>
    rewrite (answer_ptr q o) by (vm_compute; reflexivity) end.

Ltac ss_stop gv x m a v s ce ie Rn FCa st :=
  u64c;
  let C := fresh "C" in let R' := fresh "R" in
  assert (C: stream_step_check x (m_total m) (w_chunk s) (w_value s) (a ++ [v]) = st)
    by (unfold stream_step_check; chk_dec);
  assert (R': stream_step_done x (w_chunk s) (w_value s) (a ++ [v]) m = Return st m)
    by (unfold stream_step_done; rewrite C; reflexivity);
  rewrite R' in Rn;
  forward_call (gv _law, vi (w_expect s), vi (w_verdict s), st);
  rewrite <- (answer_at _ _ FCa);
  let Hs2 := fresh "HJ" in
  assert (Hs2: J x (Return st m) (s_stop (s_store s v) st))
    by (apply J_stop; auto; [ apply lst_ok_store; auto | unfold u32_ok; unfold_status; rep_lia ]);
  unfold Ora_law; Exists (Return st m) (s_stop (s_store s v) st) ce ie;
  unfold lfields, arrays, s_stop, s_stream, s_store, s_more;
  match goal with Hc: has_copy x = true |- _ => rewrite Hc end;
  mem_cbn; lst_cbn; entailer!.

Lemma ss_tail {Espec: OracleKind} gv x h s m a v ce ie:
  inputs_ok x -> x_fit x -> ptr_ok x ce ie ->
  run x (start x) h = Some (Go (ExpectStreamStep (w_chunk s) (w_stream s) (w_value s) a) m) ->
  J x (Go (ExpectStreamStep (w_chunk s) (w_stream s) (w_value s) a) m) s ->
  w_word s = 8 -> u64_ok v ->
  forall Delta R c, Delta = Delta_ss ->
  R = Post_ss gv x h (StreamStep (w_stream s) (i_address x) (8 * w_chunk s) 8 (w_value s)
                        (terminal (m_total m) (w_chunk s)) (Zlength a)) ->
  c = s_ss_tail ->
  semax Delta
    (PROP ()
     LOCAL (temp _v (Vlong (Int64.repr v)); temp _last (vl (terminal (m_total m) (w_chunk s)));
            temp _end (Vlong (Int64.repr (8 * w_chunk s + 8))); temp _m (gv _law); gvars gv)
     SEP (lfields (gv _law) x ce ie m (s_store s v); arrays x ce ie m))
    c R.
Proof.
  intros Ix Xf Pie Hrun HJ W8 Hv Delta R c -> -> ->.
  unfold s_ss_tail, Delta_ss, Post_ss. start_tail.
  pose proof HJ as (Hs & Hm & G). cbn [mem_of] in *.
  pose proof G as (Ge & _ & _ & _ & (Pw & Pa) & La & Gk0 & Gkt & Cc).
  pose proof Hs as Hs'. lst_facts Hs'. mem_facts Hm. pose proof Ix as Ix'. inputs_facts Ix'.
  pose proof Cc as (Ccall & Te & Tm).
  assert (L8: Zlength a = 8) by lia.
  assert (Fa: Forall u64_ok a) by (rewrite <- Pa; apply Forall_u64_sublist; auto).
  assert (Fa': Forall u64_ok (a ++ [v])) by (apply Forall_u64_app1; auto).
  assert (La': Zlength (a ++ [v]) = 9) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (Ea: a ++ [v] = sublist 0 9 (upd_Znth (w_word s) (w_answer s) v))
    by (apply answers_last; auto; [ split; auto | lia | lia ]).
  assert (EA: forall i, 0 <= i < 9 -> Znth i (upd_Znth (w_word s) (w_answer s) v) = Znth i (a ++ [v])).
  { intros i I. rewrite Ea. rewrite Znth_sublist by lia. f_equal; lia. }
  assert (Lans: Zlength (upd_Znth (w_word s) (w_answer s) v) = WORDS) by (rewrite upd_Znth_Zlength; lia).
  rng_list (a ++ [v]) 9.
  assert (Rn: run x (start x) (h ++ [(StreamStep (w_stream s) (i_address x) (8 * w_chunk s) 8 (w_value s)
                                        (terminal (m_total m) (w_chunk s)) (Zlength a), v)])
              = Some (stream_step_done x (w_chunk s) (w_value s) (a ++ [v]) m)).
  { erewrite (run_snoc' x h _ m); [ | exact Hrun | reflexivity ].
    cbn [step]. rewrite step_last by lia. reflexivity. }
  pose proof (terminal_range (m_total m) (w_chunk s)) as Rt.
  assert (Hc: has_copy x = true) by (unfold has_copy; destruct Ccall as [E | E]; rewrite E; reflexivity).
  unfold lfields, s_store, arrays. rewrite Hc. lst_cbn. Intros.
  assert_PROP (field_compatible t_law (DOT _answer) (gv _law)) as FCa by entailer!.
  rewrite (answer_at _ _ FCa).
  forward. fix_answer.
  forward. norm_vl. rewrite EA by lia.
  forward_if (PROP () LOCAL (temp _v (vl v))
    SEP (Ora_law gv (gv _law) (gv _law) x
           (h ++ [(StreamStep (w_stream s) (i_address x) (8 * w_chunk s) 8 (w_value s)
                     (terminal (m_total m) (w_chunk s)) (Zlength a), v)]))).
  { ss_stop gv x m a v s ce ie Rn FCa S_STREAM_STEP_VERSION. }
  forward. norm_vl. rewrite EA by lia. forward_if.
  { ss_stop gv x m a v s ce ie Rn FCa S_STREAM_STEP_ERROR. }
  forward. norm_vl. rewrite EA by lia. forward. forward_if.
  { ss_stop gv x m a v s ce ie Rn FCa S_STREAM_STEP_IDENTITY. }
  forward. norm_vl. rewrite EA by lia. forward. forward_if.
  { ss_stop gv x m a v s ce ie Rn FCa S_STREAM_STEP_EXTENT. }
  forward. norm_vl. rewrite EA by lia. forward_if.
  { ss_stop gv x m a v s ce ie Rn FCa S_STREAM_STEP_OFFSET. }
  forward. norm_vl. rewrite EA by lia. forward_if.
  { ss_stop gv x m a v s ce ie Rn FCa S_STREAM_STEP_COUNT. }
  forward. norm_vl. rewrite EA by lia. forward. forward_if.
  { ss_stop gv x m a v s ce ie Rn FCa S_STREAM_STEP_EXPOSED. }
  forward. norm_vl. rewrite EA by lia. forward_if.
  { ss_stop gv x m a v s ce ie Rn FCa S_STREAM_STEP_STATUS. }
  { (* accepted: the chunk to the copy, the carried state, the next chunk *)
    u64c.
    assert (C: stream_step_check x (m_total m) (w_chunk s) (w_value s) (a ++ [v]) = S_OK)
      by (unfold stream_step_check; chk_dec).
    assert (Lcp: Zlength (m_copy m) = COPY_WORDS) by (apply Fcl; exact Hc).
    assert (Kc: 0 <= w_chunk s < COPY_WORDS) by lia.
    forward. forward. forward. vl_temps.
    forward. upd_vl.
    freeze_but [_stream] [offset_val OFS_ANSWER (gv _law)] FL.
    forward_for_simple_bound 7
      (EX i: Z, PROP ()
       LOCAL (temp _a (offset_val OFS_ANSWER (gv _law)); temp _v (Vlong (Int64.repr v)); temp _m (gv _law);
              gvars gv)
       SEP (FRZL FL;
            data_at Ews (tarray tulong WORDS) (map vl (upd_Znth (w_word s) (w_answer s) v))
              (offset_val OFS_ANSWER (gv _law));
            field_at Ews t_law (DOT _stream) (map vl (sublist 0 i (a ++ [v]) ++ sublist i 7 (w_stream s)))
              (gv _law)))%assert.
    { entailer!. rewrite sublist_nil, app_nil_l, sublist_same by lia. apply derives_refl. }
    { forward. norm_vl. rewrite EA by lia. forward. upd_vl.
      entailer!. apply derives_refl'. do 2 f_equal. list_solve. }
    thaw FL.
    rewrite sublist_nil, app_nil_r.
    forward.
    rewrite <- (answer_at _ _ FCa).
    set (m' := with_copy m (upd_Znth (w_chunk s) (m_copy m) (w_value s))).
    set (s1 := s_stream (s_store s v) (sublist 0 7 (a ++ [v]))).
    assert (Hs1: lst_ok s1).
    { apply lst_ok_stream; [ apply lst_ok_store; auto | rewrite Zlength_sublist by lia; lia |
        apply Forall_u64_sublist; auto ]. }
    assert (Hm': mem_fit x m').
    { apply mem_fit_copy; auto; intros _; [ rewrite upd_Znth_Zlength by lia; lia | apply Forall_upd; auto ]. }
    assert (R': stream_step_done x (w_chunk s) (w_value s) (a ++ [v]) m =
                begin_chunk x (w_chunk s + 1) (sublist 0 7 (a ++ [v])) m')
      by (unfold stream_step_done; rewrite C; reflexivity).
    rewrite R' in Rn.
    sep_apply (lfields_fold (gv _law) x ce ie m' s1).
    forward_call (gv _law, x, ce, ie, m', s1, w_chunk s + 1).
    Intros s2. unfold s1 in *. cbn [w_stream s_stream] in *.
    unfold Ora_law. Exists (begin_chunk x (w_chunk s + 1) (sublist 0 7 (a ++ [v])) m') s2 ce ie.
    rewrite arrays_begin_chunk. unfold arrays, m'. cbn [m_copy with_copy]. rewrite Hc.
    entailer!. }
  forward. Exists v. entailer!.
Qed.
