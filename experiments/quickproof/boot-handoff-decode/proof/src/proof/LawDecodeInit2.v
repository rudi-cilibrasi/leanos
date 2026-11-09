(* Law handoff_decode_exact: the decoder reset export after the answer of its last word is recorded (word 40):
   the answers to state 0, the current one; the reset's checks on it (each status prefixed by the call); then chunk
   0 (begin_transition). *)
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

Definition Gdinit : funspecs := [gp_assert_spec; any_u64_spec; stop_spec; begin_transition_spec].

Definition Delta_di : tycontext := func_tycontext f_leanos_boot_decode_init_v5 Vlaw Gdinit nil.
Definition Post_di gv x h c : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tulong
       (EX v: Z, PROP (u64_ok v) RETURN (vl v) SEP (Ora_law gv (gv _law) (gv _law) x (h ++ [(c, v)])))%argsassert)
    (stackframe_of f_leanos_boot_decode_init_v5).

(* The statement from the loop that writes state 0 on. *)
Definition s_di_tail : statement := ltac:(
  let b := eval cbv delta [f_leanos_boot_decode_init_v5] beta iota zeta in (fn_body f_leanos_boot_decode_init_v5) in
  match b with context [Ssequence (Ssequence (Sset _i (Econst_int (Int.repr 0) tint)) ?l) ?rest] =>
    exact (Ssequence (Ssequence (Sset _i (Econst_int (Int.repr 0) tint)) l) rest) end).

Lemma row_addr0: forall q, isptr q ->
  force_val (sem_binary_operation' Oadd (tarray (tarray tulong 41) 2) tint
    (eval_field (Tstruct _law__1 noattr) _states_expect q) (Vint (Int.repr 0))) = row q 0.
Proof.
  intros q P. destruct q; try contradiction.
  unfold row. simpl. f_equal. rewrite Ptrofs.add_assoc. f_equal.
Qed.

Ltac di_stop gv x h m a v s ce ie Ix Xf Pie Rn FCs Fsl L1 FZ st :=
  u64c;
  let C := fresh "C" in let R' := fresh "R" in
  assert (C: decode_init_check x (m_total m) (a ++ [v]) = st)
    by (unfold decode_init_check; chk_dec);
  assert (R': decode_init_done x (a ++ [v]) m = Return st (with_states m (upd_Znth 0 (m_states m) (a ++ [v])) 0))
    by (unfold decode_init_done; cbn [m_total with_states]; rewrite C; unfold by_call;
        destruct (projection x); reflexivity);
  rewrite R' in Rn;
  by_call_if x;
  forward_call (gv _law, vi (w_expect s), vi (w_verdict s), st);
  thaw FZ;
  sep_apply (rows_upd0_fold (gv _law) (m_states m) (a ++ [v]) FCs Fsl ltac:(lia) L1);
  let Hs2 := fresh "HJ" in
  assert (Hs2: J x (Return st (with_states m (upd_Znth 0 (m_states m) (a ++ [v])) 0)) (s_stop (s_store s v) st))
    by (apply J_stop; auto; [ apply lst_ok_store; auto | apply mem_fit_states; auto | apply by_call_u32;
        unfold u32_ok; unfold_status; rep_lia ]);
  ora_fin3 gv x h (Return st (with_states m (upd_Znth 0 (m_states m) (a ++ [v])) 0))
    (with_states m (upd_Znth 0 (m_states m) (a ++ [v])) 0) m (s_stop (s_store s v) st) ce ie Ix Xf Rn Hs2 Pie.

Ltac ld_row k := forward; try rewrite (Znth_map_vl _ k) by lia.

Lemma di_tail {Espec: OracleKind} gv x h s m a v ce ie:
  inputs_ok x -> x_fit x -> ptr_ok x ce ie ->
  run x (start x) h = Some (Go (ExpectDecodeInit a) m) ->
  J x (Go (ExpectDecodeInit a) m) s ->
  w_word s = 40 -> u64_ok v ->
  forall Delta R c, Delta = Delta_di ->
  R = Post_di gv x h (DecodeInit (i_magic x) (i_address x) (m_total m) (target x) (Zlength a)) ->
  c = s_di_tail ->
  semax Delta
    (PROP ()
     LOCAL (temp _v (Vlong (Int64.repr v)); temp _m (gv _law); gvars gv)
     SEP (lfields (gv _law) x ce ie m (s_store s v); arrays x ce ie m))
    c R.
Proof.
  intros Ix Xf Pie Hrun HJ W40 Hv Delta R c -> -> ->.
  unfold s_di_tail, Delta_di, Post_di. start_tail.
  pose proof HJ as (Hs & Hm & G). cbn [mem_of] in *.
  pose proof G as (Ge & (Pw & Pa) & La & Dc).
  pose proof Hs as Hs'. lst_facts Hs'. mem_facts Hm. pose proof Ix as Ix'. inputs_facts Ix'.
  assert (L40: Zlength a = 40) by lia.
  assert (Fa: Forall u64_ok a) by (rewrite <- Pa; apply Forall_u64_sublist; auto).
  assert (Fa': Forall u64_ok (a ++ [v])) by (apply Forall_u64_app1; auto).
  assert (La': Zlength (a ++ [v]) = 41) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (Ea: a ++ [v] = sublist 0 41 (upd_Znth (w_word s) (w_answer s) v))
    by (apply answers_last; auto; [ split; auto | lia | lia ]).
  assert (Lans: Zlength (upd_Znth (w_word s) (w_answer s) v) = WORDS) by (rewrite upd_Znth_Zlength; lia).
  assert (Rn: run x (start x) (h ++ [(DecodeInit (i_magic x) (i_address x) (m_total m) (target x) (Zlength a), v)])
              = Some (decode_init_done x (a ++ [v]) m)).
  { erewrite (run_snoc' x h _ m); [ | exact Hrun | reflexivity ].
    cbn [step]. rewrite step_last by lia. reflexivity. }
  pose proof (target_range x Ix) as Rt. pose proof (proj_code_range x) as Rp.
  pose proof Fs0 as (L0 & _).
  unfold lfields, s_store. lst_cbn. Intros.
  (* the answers to state 0 *)
  freeze_but [_answer; _states_expect] (@nil val) FL.
  forward_for_simple_bound 41
    (EX i: Z, PROP ()
     LOCAL (temp _v (Vlong (Int64.repr v)); temp _m (gv _law); gvars gv)
     SEP (FRZL FL; field_at Ews t_law (DOT _answer) (map vl (upd_Znth (w_word s) (w_answer s) v)) (gv _law);
          field_at Ews t_law (DOT _states_expect)
            (states_val (upd_Znth 0 (m_states m)
               (sublist 0 i (upd_Znth (w_word s) (w_answer s) v) ++ sublist i WORDS (Znth 0 (m_states m)))))
            (gv _law)))%assert.
  { rewrite row_start by lia. entailer!. }
  { forward. norm_vl. forward.
    entailer!. apply derives_refl'. f_equal.
    etransitivity; [ apply states_store_g; rewrite upd_Znth_Zlength by lia; lia | ].
    f_equal. apply row_step; lia. }
  thaw FL.
  replace (sublist 0 WORDS (upd_Znth (w_word s) (w_answer s) v) ++ sublist WORDS WORDS (Znth 0 (m_states m)))
    with (a ++ [v]) by (rewrite Ea, sublist_nil, app_nil_r; reflexivity).
  assert_PROP (field_compatible t_law (DOT _states_expect) (gv _law)) as FCs by entailer!.
  assert (Pq: isptr (gv _law)) by (destruct FCs; auto).
  forward.
  forward.
  rewrite row_addr0 by auto.
  forward.
  pose proof Fs1 as (L1 & _).
  rewrite (rows_upd0 (gv _law) (m_states m) (a ++ [v]) FCs Fsl ltac:(lia) L1). Intros.
  assert (W: forall i, 0 <= i < 41 -> 0 <= Znth i (a ++ [v]) <= Int64.max_unsigned)
    by (intros; apply Forall_u64_Znth; auto; lia).
  pose proof (W 0 ltac:(lia)). pose proof (W 1 ltac:(lia)). pose proof (W 2 ltac:(lia)).
  pose proof (W 3 ltac:(lia)). pose proof (W 4 ltac:(lia)). pose proof (W 5 ltac:(lia)).
  pose proof (W 16 ltac:(lia)). pose proof (W 18 ltac:(lia)). pose proof (W 30 ltac:(lia)). clear W.
  freeze_but [_expect; _verdict; _address; _total; _candidate; _projection] [row (gv _law) 0] FZ.
  ld_row 0.
  forward_if (PROP () LOCAL (temp _v (vl v))
    SEP (Ora_law gv (gv _law) (gv _law) x
           (h ++ [(DecodeInit (i_magic x) (i_address x) (m_total m) (target x) (Zlength a), v)]))).
  { di_stop gv x h m a v s ce ie Ix Xf Pie Rn FCs Fsl L1 FZ (by_call x 26 44). }
  ld_row 1. forward_if.
  { di_stop gv x h m a v s ce ie Ix Xf Pie Rn FCs Fsl L1 FZ (by_call x 27 45). }
  ld_row 2. forward_if.
  { di_stop gv x h m a v s ce ie Ix Xf Pie Rn FCs Fsl L1 FZ (by_call x 28 46). }
  ld_row 3. forward. forward_if.
  { di_stop gv x h m a v s ce ie Ix Xf Pie Rn FCs Fsl L1 FZ (by_call x 29 47). }
  ld_row 4. forward. forward_if.
  { di_stop gv x h m a v s ce ie Ix Xf Pie Rn FCs Fsl L1 FZ (by_call x 30 48). }
  ld_row 5. forward_if.
  { di_stop gv x h m a v s ce ie Ix Xf Pie Rn FCs Fsl L1 FZ (by_call x 31 49). }
  ld_row 16. forward. forward_if.
  { di_stop gv x h m a v s ce ie Ix Xf Pie Rn FCs Fsl L1 FZ (by_call x 32 50). }
  ld_row 18. forward_if.
  { di_stop gv x h m a v s ce ie Ix Xf Pie Rn FCs Fsl L1 FZ (by_call x 33 51). }
  ld_row 30. forward_if.
  { di_stop gv x h m a v s ce ie Ix Xf Pie Rn FCs Fsl L1 FZ (by_call x 34 52). }
  { (* accepted: chunk 0 *)
    u64c.
    assert (C: decode_init_check x (m_total m) (a ++ [v]) = S_OK) by (unfold decode_init_check; chk_dec).
    set (m' := with_states m (upd_Znth 0 (m_states m) (a ++ [v])) 0).
    assert (R': decode_init_done x (a ++ [v]) m = begin_transition x 0 m')
      by (unfold decode_init_done; cbn [m_total with_states]; rewrite C; reflexivity).
    rewrite R' in Rn.
    assert (Hm': mem_fit x m') by (apply mem_fit_states; auto).
    thaw FZ.
    sep_apply (rows_upd0_fold (gv _law) (m_states m) (a ++ [v]) FCs Fsl ltac:(lia) L1).
    sep_apply (lfields_fold (gv _law) x ce ie m' (s_store s v)).
    change (arrays x ce ie m) with (arrays x ce ie m').
    rewrite (arrays_decoded x ce ie m' Pie Fcl (proj1 Dc)). Intros.
    forward_call (gv _law, x, ce, ie, m', s_store s v, 0, Ews).
    { split_and; auto; try (apply lst_ok_store; auto); try lia. }
    Intros s2.
    sep_apply (arrays_fold x ce ie m' Pie Fcl (proj1 Dc)).
    unfold Ora_law. Exists (begin_transition x 0 m') s2 ce ie. rewrite mem_of_begin_transition.
    entailer!. }
  forward. Exists v. entailer!.
Qed.