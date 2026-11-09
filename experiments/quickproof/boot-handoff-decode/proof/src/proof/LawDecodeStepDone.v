(* Law handoff_decode_exact: the decoder transition export after the answer of its last word is recorded (word
   40): the answers to the other state, which becomes the current one; then decode_done when its error word is not
   0, the entry event's count checks and the record's turn with a projection, or the next chunk
   (begin_transition). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosHandoff.harness.handoff_decode_exact.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.LawProg LeanosHandoff.proof.LawDefs LeanosHandoff.proof.LawFacts
  LeanosHandoff.proof.LawLib LeanosHandoff.proof.LawLib2 LeanosHandoff.proof.LawLib3.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Existing Instance LawProg.LCS.

Definition Gdstep : funspecs := [gp_assert_spec; any_u64_spec; stop_spec; decode_done_spec; begin_transition_spec].

Definition Delta_ds : tycontext := func_tycontext f_leanos_boot_decode_step_v5 Vlaw Gdstep nil.
Definition Post_ds gv x h c : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tulong
       (EX v: Z, PROP (u64_ok v) RETURN (vl v) SEP (Ora_law gv (gv _law) (gv _law) x (h ++ [(c, v)])))%argsassert)
    (stackframe_of f_leanos_boot_decode_step_v5).

(* The statement from `next = 1 - m->at` on. *)
Definition s_ds_tail : statement := ltac:(
  let b := eval cbv delta [f_leanos_boot_decode_step_v5] beta iota zeta in (fn_body f_leanos_boot_decode_step_v5) in
  match b with context [Ssequence (Ssequence (Sset _t'47 ?e1) (Sset _next ?e2)) ?rest] =>
    exact (Ssequence (Ssequence (Sset _t'47 e1) (Sset _next e2)) rest) end).

(* The 32-bit temps as Vint, so that VST computes with them (array indices). *)
Ltac vi_temps := repeat match goal with |- context [temp ?i (vi ?e)] =>
  change (temp i (vi e)) with (temp i (Vint (Int.repr e))) end.

Lemma row_addr': forall q i, isptr q -> 0 <= i <= 1 ->
  force_val (sem_binary_operation' Oadd (tarray (tarray tulong 41) 2) tuint
    (eval_field (Tstruct _law__1 noattr) _states_expect q) (Vint (Int.repr i))) = row q i.
Proof. intros. apply row_addr; auto. Qed.

Ltac ld_row k := forward; try rewrite (Znth_map_vl _ k) by lia.

Lemma ds_tail {Espec: OracleKind} gv x h s m k a v ce ie:
  inputs_ok x -> x_fit x -> ptr_ok x ce ie ->
  run x (start x) h = Some (Go (ExpectDecodeStep k a) m) ->
  J x (Go (ExpectDecodeStep k a) m) s ->
  w_word s = 40 -> u64_ok v ->
  forall Delta R c, Delta = Delta_ds ->
  R = Post_ds gv x h (DecodeStep (current m) (i_address x) (8 * k) (Znth k (decoded x m))
                        (terminal (m_total m) k) (Zlength a)) ->
  c = s_ds_tail ->
  semax Delta
    (PROP ()
     LOCAL (temp _v (Vlong (Int64.repr v)); temp _m (gv _law); gvars gv)
     SEP (lfields (gv _law) x ce ie m (s_store s v); arrays x ce ie m))
    c R.
Proof.
  intros Ix Xf Pie Hrun HJ W40 Hv Delta R c -> -> ->.
  unfold s_ds_tail, Delta_ds, Post_ds. start_tail.
  pose proof HJ as (Hs & Hm & G). cbn [mem_of] in *.
  pose proof G as (Ge & Gk & Gv & (Pw & Pa) & La & Gk0 & Gkt & Dc).
  subst k.
  pose proof Hs as Hs'. lst_facts Hs'. mem_facts Hm. pose proof Ix as Ix'. inputs_facts Ix'.
  pose proof Dc as (Nc & (Te & Tm) & Td).
  assert (L40: Zlength a = 40) by lia.
  assert (Fa: Forall u64_ok a) by (rewrite <- Pa; apply Forall_u64_sublist; auto).
  assert (Fa': Forall u64_ok (a ++ [v])) by (apply Forall_u64_app1; auto).
  assert (La': Zlength (a ++ [v]) = 41) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (Ea: a ++ [v] = sublist 0 41 (upd_Znth (w_word s) (w_answer s) v))
    by (apply answers_last; auto; [ split; auto | lia | lia ]).
  assert (Lans: Zlength (upd_Znth (w_word s) (w_answer s) v) = WORDS) by (rewrite upd_Znth_Zlength; lia).
  assert (Rn: run x (start x) (h ++ [(DecodeStep (current m) (i_address x) (8 * w_chunk s) (Znth (w_chunk s) (decoded x m))
                                        (terminal (m_total m) (w_chunk s)) (Zlength a), v)])
              = Some (decode_step_done x (w_chunk s) (a ++ [v]) m)).
  { erewrite (run_snoc' x h _ m); [ | exact Hrun | reflexivity ].
    cbn [step]. rewrite step_last by lia. reflexivity. }
  set (n := 1 - m_at m) in *.
  assert (Nn: n = 0 \/ n = 1) by (unfold n; lia).
  assert (Ln: Zlength (Znth n (m_states m)) = WORDS) by (destruct Nn as [-> | ->]; [ apply Fs0 | apply Fs1 ]).
  unfold lfields, s_store. lst_cbn. Intros.
  forward. forward.
  rewrite sub_repr'. fold n.
  vi_temps.
  (* the answers to state n *)
  freeze_but [_answer; _states_expect] (@nil val) FL.
  forward_for_simple_bound 41
    (EX i: Z, PROP ()
     LOCAL (temp _next (Vint (Int.repr n)); temp _t'47 (Vint (Int.repr (m_at m)));
            temp _v (Vlong (Int64.repr v)); temp _m (gv _law); gvars gv)
     SEP (FRZL FL; field_at Ews t_law (DOT _answer) (map vl (upd_Znth (w_word s) (w_answer s) v)) (gv _law);
          field_at Ews t_law (DOT _states_expect)
            (states_val (upd_Znth n (m_states m)
               (sublist 0 i (upd_Znth (w_word s) (w_answer s) v) ++ sublist i WORDS (Znth n (m_states m)))))
            (gv _law)))%assert.
  { rewrite row_start by lia. entailer!. }
  { forward. norm_vl. forward.
    entailer!. apply derives_refl'. f_equal.
    etransitivity; [ apply states_store_g; rewrite upd_Znth_Zlength by lia; lia | ].
    f_equal. apply row_step; lia. }
  thaw FL.
  replace (sublist 0 WORDS (upd_Znth (w_word s) (w_answer s) v) ++ sublist WORDS WORDS (Znth n (m_states m)))
    with (a ++ [v]) by (rewrite Ea, sublist_nil, app_nil_r; reflexivity).
  forward.
  assert_PROP (field_compatible t_law (DOT _states_expect) (gv _law)) as FCs by entailer!.
  assert (Pq: isptr (gv _law)) by (destruct FCs; auto).
  forward.
  rewrite row_addr' by (auto; lia).
  set (L' := upd_Znth n (m_states m) (a ++ [v])) in *.
  assert (LL: Zlength L' = 2) by (unfold L'; rewrite upd_Znth_Zlength; lia).
  assert (En: Znth n L' = a ++ [v]) by (unfold L'; rewrite upd_Znth_same by lia; reflexivity).
  assert (Ok': state_ok (a ++ [v])) by (split; auto).
  assert (S0: state_ok (Znth 0 L')) by (unfold L'; destruct Nn as [-> | ->];
    [ rewrite upd_Znth_same by lia | rewrite upd_Znth_diff by lia ]; auto).
  assert (S1: state_ok (Znth 1 L')) by (unfold L'; destruct Nn as [-> | ->];
    [ rewrite upd_Znth_diff by lia | rewrite upd_Znth_same by lia ]; auto).
  rewrite (states_split (gv _law) L' FCs LL S0 S1).
  rewrite (rows_at (gv _law) L' n Nn). Intros.
  assert (Ek: forall i, Znth i (Znth n L') = Znth i (a ++ [v])) by (intros; rewrite En; reflexivity).
  assert (LnL: Zlength (Znth n L') = WORDS) by (rewrite En; lia).
  assert (LmL: Zlength (map vl (Znth n L')) = WORDS) by (rewrite Zlength_map; lia).
  assert (W: forall i, 0 <= i < 41 -> 0 <= Znth i (a ++ [v]) <= Int64.max_unsigned)
    by (intros; apply Forall_u64_Znth; auto; lia).
  pose proof (W 2 ltac:(lia)). pose proof (W 11 ltac:(lia)). pose proof (W 19 ltac:(lia)). clear W.
  set (m' := with_states m L' n) in *.
  assert (Hm': mem_fit x m') by (apply mem_fit_states; auto).
  assert (Dc': dec_ctx x m') by (apply dec_ctx_states; auto).
  assert (Cur: current m' = a ++ [v]) by exact En.
  assert (Ed: decode_step_done x (w_chunk s) (a ++ [v]) m =
              if negb (Znth 2 (a ++ [v]) =? 0) then decode_done x m'
              else if projection x && (Znth 19 (a ++ [v]) =? 1) then
                (if event_check (a ++ [v]) =? S_OK then Go (ExpectRecord (w_chunk s)) m'
                 else Return (event_check (a ++ [v])) m')
              else begin_transition x (w_chunk s + 1) m') by reflexivity.
  rewrite Ed in Rn.
  ld_row 2. rewrite Ek.
  forward_if (PROP () LOCAL (temp _v (vl v))
    SEP (Ora_law gv (gv _law) (gv _law) x
           (h ++ [(DecodeStep (current m) (i_address x) (8 * w_chunk s) (Znth (w_chunk s) (decoded x m))
                     (terminal (m_total m) (w_chunk s)) (Zlength a), v)]))).
  - (* the error word is not 0: decode_done *)
    u64c.
    match goal with H2: Znth 2 (a ++ [v]) <> 0 |- _ => rewrite (proj2 (Z.eqb_neq _ _) H2) in Rn end.
    cbn [negb] in Rn.
    sep_apply (rows_fold (gv _law) L' n FCs LL S0 S1 Nn).
    sep_apply (lfields_fold (gv _law) x ce ie m' (s_store s v)).
    forward_call (gv _law, x, ce, ie, m', s_store s v).
    { split_and; auto; try (apply lst_ok_store; auto). }
    Intros s2.
    match goal with H2: J x (decode_done x m') s2 |- _ => rename H2 into HJ2 end.
    pose proof (ora_close2 gv x h _ _ (decode_done x m') m' m s2 ce ie Ix Xf Rn (mem_of_decode_done x m') HJ2 Pie eq_refl) as OC.
    sep_apply OC. entailer!.
  - u64c.
    match goal with H2: Znth 2 (a ++ [v]) = 0 |- _ => rewrite (proj2 (Z.eqb_eq _ _) H2) in Rn end.
    cbn [negb] in Rn.
    pose proof (proj_code_range x) as Rp.
    forward.
    forward_if (temp _t'39 (Vint (Int.repr (Z.b2z (projection x && (Znth 19 (a ++ [v]) =? 1)))))).
    { ld_row 19. rewrite Ek. forward. entailer!.
      assert (P: projection x = true)
        by (unfold proj_code in *; destruct (projection x); [ reflexivity | exfalso; u64c; lia ]).
      rewrite P. cbn [andb]. unfold Int64.cmpu. rewrite Int64_eq_repr by rep_lia.
      destruct (Znth 19 (a ++ [v]) =? 1); reflexivity. }
    { forward. entailer!.
      assert (P: projection x = false)
        by (unfold proj_code in *; destruct (projection x); [ exfalso; u64c; lia | reflexivity ]).
      rewrite P. reflexivity. }
    forward_if.
    + (* an entry event: its count *)
      match goal with H2: projection x && _ = true |- _ => rename H2 into Pe end.
      rewrite Pe in Rn.
      ld_row 11. rewrite Ek. forward_if.
      { (* COUNT_ZERO *)
        u64c.
        assert (C: event_check (a ++ [v]) = S_PROJECTION_COUNT_ZERO) by (unfold event_check; chk_dec).
        rewrite C in Rn. change (S_PROJECTION_COUNT_ZERO =? S_OK) with false in Rn. cbv iota in Rn.
        forward_call (gv _law, vi (w_expect s), vi (w_verdict s), S_PROJECTION_COUNT_ZERO).
        sep_apply (rows_fold (gv _law) L' n FCs LL S0 S1 Nn).
        assert (HJ2: J x (Return S_PROJECTION_COUNT_ZERO m') (s_stop (s_store s v) S_PROJECTION_COUNT_ZERO))
          by (apply J_stop; auto; [ apply lst_ok_store; auto | unfold u32_ok; unfold_status; rep_lia ]).
        ora_fin3 gv x h (Return S_PROJECTION_COUNT_ZERO m') m' m (s_stop (s_store s v) S_PROJECTION_COUNT_ZERO)
          ce ie Ix Xf Rn HJ2 Pie. }
      ld_row 11. rewrite Ek. forward_if.
      { (* COUNT_LARGE *)
        u64c.
        assert (C: event_check (a ++ [v]) = S_PROJECTION_COUNT_LARGE) by (unfold event_check; chk_dec).
        rewrite C in Rn. change (S_PROJECTION_COUNT_LARGE =? S_OK) with false in Rn. cbv iota in Rn.
        forward_call (gv _law, vi (w_expect s), vi (w_verdict s), S_PROJECTION_COUNT_LARGE).
        sep_apply (rows_fold (gv _law) L' n FCs LL S0 S1 Nn).
        assert (HJ2: J x (Return S_PROJECTION_COUNT_LARGE m') (s_stop (s_store s v) S_PROJECTION_COUNT_LARGE))
          by (apply J_stop; auto; [ apply lst_ok_store; auto | unfold u32_ok; unfold_status; rep_lia ]).
        ora_fin3 gv x h (Return S_PROJECTION_COUNT_LARGE m') m' m (s_stop (s_store s v) S_PROJECTION_COUNT_LARGE)
          ce ie Ix Xf Rn HJ2 Pie. }
      { (* the record's turn *)
        u64c.
        assert (C: event_check (a ++ [v]) = S_OK) by (unfold event_check; chk_dec).
        rewrite C in Rn. change (S_OK =? S_OK) with true in Rn. cbv iota in Rn.
        forward.
        sep_apply (rows_fold (gv _law) L' n FCs LL S0 S1 Nn).
        set (s' := mk_lst (w_running s) (w_records s) E_RECORD (w_verdict s) (w_chunk s) (w_word s) (w_block s)
                          (w_value s) (w_stream s) (upd_Znth (w_word s) (w_answer s) v)).
        assert (HJ2: J x (Go (ExpectRecord (w_chunk s)) m') s').
        { unfold J; split_and; auto.
          - pose proof (lst_ok_store s v Hs Hv) as Hs2. unfold lst_ok, s_store, s' in *; lst_cbn.
            destruct Hs2 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
            split_and; auto. unfold u32_ok, E_RECORD; rep_lia.
          - unfold go_inv, s'; lst_cbn. split_and; auto; try lia; rewrite Cur; lia. }
        change (Vint (Int.repr 6)) with (vi E_RECORD).
        ora_fin3 gv x h (Go (ExpectRecord (w_chunk s)) m') m' m s' ce ie Ix Xf Rn HJ2 Pie. }
    + (* the next chunk *)
      match goal with H2: projection x && _ = false |- _ => rename H2 into Pe end.
      rewrite Pe in Rn.
      forward.
      sep_apply (rows_fold (gv _law) L' n FCs LL S0 S1 Nn).
      sep_apply (lfields_fold (gv _law) x ce ie m' (s_store s v)).
      change (arrays x ce ie m) with (arrays x ce ie m').
      rewrite (arrays_decoded x ce ie m' Pie Fcl (proj1 Dc)). Intros.
      forward_call (gv _law, x, ce, ie, m', s_store s v, w_chunk s + 1, Ews).
      { split_and; auto; try (apply lst_ok_store; auto); try lia. }
      Intros s2.
      match goal with H2: J x (begin_transition x _ m') s2 |- _ => rename H2 into HJ2 end.
      sep_apply (arrays_fold x ce ie m' Pie Fcl (proj1 Dc)).
      pose proof (ora_close2 gv x h _ _ (begin_transition x (w_chunk s + 1) m') m' m' s2 ce ie Ix Xf Rn
                    (mem_of_begin_transition x _ m') HJ2 Pie eq_refl) as OC.
      sep_apply OC. entailer!.
  - forward. Exists v. entailer!.
Qed.