(* Law handoff_decode_exact: the body of the harness's block projection export against projection_entry_spec
   Ora_law: its checks follow from the call the model expects (the event's entry, the block, the bitmaps' current
   words), and the answer it records moves the law's record as the model's step: the next word, or after word 4
   the checks, then the block's words to the bitmaps and the next block, or after block 63 the next chunk. *)
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

Definition Gentry : funspecs := [gp_assert_spec; any_u64_spec; stop_spec; begin_transition_spec].

Lemma body_projection_entry: semax_body Vlaw Gentry f_leanos_boot_projection_entry (projection_entry_spec Ora_law).
Proof.
  start_function.
  rename H into Nc.
  ora_open x h p s ce ie.
  destruct (next_go x h p _ Hrun Nc) as (g & m & -> & Ec).
  destruct (call_entry x g m _ _ _ _ _ _ _ (eq_sym Ec)) as (k & b & a & -> & -> & -> & -> & -> & -> & -> & ->).
  pose proof HJ as (Hs & Hm & G). cbn [mem_of] in *.
  pose proof G as (Ge & Gk & Gb & Bb & (Pw & Pa) & La & Gk0 & Gkt & Dc).
  subst k b.
  lst_facts Hs. mem_facts Hm.
  pose proof Dc as (Nc' & (Te & Tm) & Td).
  unfold E_ENTRY in Ge.
  assert (La0: 0 <= Zlength a) by apply Zlength_nonneg.
  pose proof (current_ok x m Hm) as Cok.
  assert (Lcs: Zlength (current m) = WORDS) by apply Cok.
  assert (R20: 0 <= Znth 20 (current m) <= Int64.max_unsigned) by (apply state_word; auto; lia).
  assert (R21: 0 <= Znth 21 (current m) <= Int64.max_unsigned) by (apply state_word; auto; lia).
  assert (R22: 0 <= Znth 22 (current m) <= Int64.max_unsigned) by (apply state_word; auto; lia).
  assert (Ru: 0 <= Znth (w_block s) (m_usable m) <= Int64.max_unsigned) by (apply Forall_u64_Znth; auto; lia).
  assert (Rb: 0 <= Znth (w_block s) (m_blocked m) <= Int64.max_unsigned) by (apply Forall_u64_Znth; auto; lia).
  unfold lfields. Intros.
  assert_PROP (field_compatible t_law (DOT _states_expect) (gv _law)) as FCs by entailer!.
  rewrite (states_split (gv _law) (m_states m) FCs Fsl Fs0 Fs1).
  rewrite (rows_at (gv _law) (m_states m) (m_at m) Fat). Intros.
  change (Znth (m_at m) (m_states m)) with (current m).
  change (vl (w_block s)) with (Vlong (Int64.repr (w_block s))).
  forward.
  if3. gp.
  forward. forward.
  rewrite row_addr by (auto; destruct FCs; auto; lia).
  if3. if3. if3. if3. if3. gp.
  forward_call tt. Intros v. assert (Hv: u64_ok v) by (unfold u64_ok in *; auto).
  forward. vl_temps. forward.
  upd_vl.
  forward.
  sep_apply (rows_fold (gv _law) (m_states m) (m_at m) FCs Fsl Fs0 Fs1 Fat).
  forward_if.
  - (* another word *)
    forward. forward. forward.
    Exists v. u64c.
    assert (Rn: run x (start x) (h ++ [(Entry (Znth 20 (current m)) (Znth 21 (current m)) (Znth 22 (current m))
                                          (w_block s) (Znth (w_block s) (m_usable m)) (Znth (w_block s) (m_blocked m))
                                          (Zlength a + 1), v)])
                = Some (Go (ExpectEntry (w_chunk s) (w_block s) (a ++ [v])) m)).
    { rewrite (run_snoc' x h (ExpectEntry (w_chunk s) (w_block s) a) m _ v Hrun Ec). cbn [step].
      rewrite step_more by lia. reflexivity. }
    assert (HJ': J x (Go (ExpectEntry (w_chunk s) (w_block s) (a ++ [v])) m) (s_more s v)).
    { unfold J; split_and; auto.
      - apply lst_ok_more; auto; lia.
      - unfold go_inv, s_more; lst_cbn; split_and; auto; try lia;
          try (apply prefix_more; [ split; auto | lia ]); rewrite Zlength_app, Zlength_cons, Zlength_nil; lia. }
    change (Vlong (Int64.repr (w_word s + 1))) with (vl (w_word s + 1)).
    change (Vlong (Int64.repr (w_block s))) with (vl (w_block s)).
    ora_fin3 gv x h (Go (ExpectEntry (w_chunk s) (w_block s) (a ++ [v])) m) m m (s_more s v) ce ie Ix Xf Rn HJ' Pie.
  - (* word 3: the checks *)
    u64c.
    assert (W3: w_word s = 3) by lia.
    assert (L3: Zlength a = 3) by lia.
    assert (Fa: Forall u64_ok a) by (rewrite <- Pa; apply Forall_u64_sublist; auto).
    assert (Fa': Forall u64_ok (a ++ [v])) by (apply Forall_u64_app1; auto).
    assert (La': Zlength (a ++ [v]) = 4) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    assert (Ea: a ++ [v] = sublist 0 4 (upd_Znth (w_word s) (w_answer s) v))
      by (apply answers_last; auto; [ split; auto | lia | lia ]).
    assert (EA: forall i, 0 <= i < 4 -> Znth i (upd_Znth (w_word s) (w_answer s) v) = Znth i (a ++ [v])).
    { intros i I. rewrite Ea. rewrite Znth_sublist by lia. f_equal; lia. }
    assert (Lans: Zlength (upd_Znth (w_word s) (w_answer s) v) = WORDS) by (rewrite upd_Znth_Zlength; lia).
    assert (W: forall i, 0 <= i < 4 -> 0 <= Znth i (a ++ [v]) <= Int64.max_unsigned)
      by (intros; apply Forall_u64_Znth; auto; lia).
    pose proof (W 0 ltac:(lia)). pose proof (W 1 ltac:(lia)). pose proof (W 2 ltac:(lia)).
    pose proof (W 3 ltac:(lia)). clear W.
    assert (Rn: run x (start x) (h ++ [(Entry (Znth 20 (current m)) (Znth 21 (current m)) (Znth 22 (current m))
                                          (w_block s) (Znth (w_block s) (m_usable m)) (Znth (w_block s) (m_blocked m))
                                          (Zlength a + 1), v)])
                = Some (entry_done x (w_chunk s) (w_block s) (a ++ [v]) m)).
    { rewrite (run_snoc' x h (ExpectEntry (w_chunk s) (w_block s) a) m _ v Hrun Ec). cbn [step].
      rewrite step_last by lia. reflexivity. }
    change (Vlong (Int64.repr (w_block s))) with (vl (w_block s)).
    forward. norm_vl. rewrite EA by lia.
    forward_if (PROP () LOCAL (temp _v (vl v))
      SEP (Ora_law gv (gv _law) (gv _law) x
             (h ++ [(Entry (Znth 20 (current m)) (Znth 21 (current m)) (Znth 22 (current m))
                       (w_block s) (Znth (w_block s) (m_usable m)) (Znth (w_block s) (m_blocked m))
                       (Zlength a + 1), v)]))).
    { (* ENTRY_STATUS *)
      u64c.
      assert (C: entry_check (a ++ [v]) = S_PROJECTION_ENTRY_STATUS) by (unfold entry_check; chk_dec).
      assert (R': entry_done x (w_chunk s) (w_block s) (a ++ [v]) m = Return S_PROJECTION_ENTRY_STATUS m)
        by (unfold entry_done; rewrite C; reflexivity).
      rewrite R' in Rn.
      forward_call (gv _law, vi (w_expect s), vi (w_verdict s), S_PROJECTION_ENTRY_STATUS).
      assert (HJ2: J x (Return S_PROJECTION_ENTRY_STATUS m) (s_stop (s_store s v) S_PROJECTION_ENTRY_STATUS))
        by (apply J_stop; auto; [ apply lst_ok_store; auto | unfold u32_ok; unfold_status; rep_lia ]).
      ora_fin3 gv x h (Return S_PROJECTION_ENTRY_STATUS m) m m (s_stop (s_store s v) S_PROJECTION_ENTRY_STATUS)
        ce ie Ix Xf Rn HJ2 Pie. }
    forward. norm_vl. rewrite EA by lia.
    forward_if.
    { (* ENTRY_ERROR *)
      u64c.
      assert (C: entry_check (a ++ [v]) = S_PROJECTION_ENTRY_ERROR) by (unfold entry_check; chk_dec).
      assert (R': entry_done x (w_chunk s) (w_block s) (a ++ [v]) m = Return S_PROJECTION_ENTRY_ERROR m)
        by (unfold entry_done; rewrite C; reflexivity).
      rewrite R' in Rn.
      forward_call (gv _law, vi (w_expect s), vi (w_verdict s), S_PROJECTION_ENTRY_ERROR).
      assert (HJ2: J x (Return S_PROJECTION_ENTRY_ERROR m) (s_stop (s_store s v) S_PROJECTION_ENTRY_ERROR))
        by (apply J_stop; auto; [ apply lst_ok_store; auto | unfold u32_ok; unfold_status; rep_lia ]).
      ora_fin3 gv x h (Return S_PROJECTION_ENTRY_ERROR m) m m (s_stop (s_store s v) S_PROJECTION_ENTRY_ERROR)
        ce ie Ix Xf Rn HJ2 Pie. }
    { (* the block's words to the bitmaps *)
      u64c.
      assert (C: entry_check (a ++ [v]) = S_OK) by (unfold entry_check; chk_dec).
      set (m' := with_bitmaps m (upd_Znth (w_block s) (m_usable m) (Znth 2 (a ++ [v])))
                   (upd_Znth (w_block s) (m_blocked m) (Znth 3 (a ++ [v]))) (m_reserved m)).
      assert (Hm': mem_fit x m') by (apply mem_fit_bitmaps; auto).
      assert (Dc': dec_ctx x m') by (apply dec_ctx_bitmaps; auto).
      forward. vl_temps. forward. norm_vl. rewrite EA by lia. forward. upd_vl.
      forward. vl_temps. forward. norm_vl. rewrite EA by lia. forward. upd_vl.
      forward.
      forward_if.
      - (* the next block *)
        u64c.
        assert (R': entry_done x (w_chunk s) (w_block s) (a ++ [v]) m = Go (ExpectEntry (w_chunk s) (w_block s + 1) nil) m')
          by (unfold entry_done; rewrite C; cbn [negb Z.eqb]; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
        rewrite R' in Rn.
        forward. forward. forward.
        set (s' := mk_lst (w_running s) (w_records s) (w_expect s) (w_verdict s) (w_chunk s) 0 (w_block s + 1)
                          (w_value s) (w_stream s) (upd_Znth (w_word s) (w_answer s) v)).
        assert (HJ2: J x (Go (ExpectEntry (w_chunk s) (w_block s + 1) nil) m') s').
        { unfold J; split_and; auto.
          - pose proof (lst_ok_store s v Hs Hv) as Hs2. unfold lst_ok, s_store, s' in *; lst_cbn.
            destruct Hs2 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
            split_and; auto; unfold u64_ok; rep_lia.
          - unfold go_inv, s'; lst_cbn. split_and; auto; try lia.
            + apply prefix_nil. reflexivity.
            + rewrite Zlength_nil; lia. }
        change (Vlong (Int64.repr (w_block s + 1))) with (vl (w_block s + 1)).
        change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with (vl 0).
        change (Int.signed (Int.repr 1)) with 1. rewrite add64_repr'. ora_fin3 gv x h (Go (ExpectEntry (w_chunk s) (w_block s + 1) nil) m') m' m s' ce ie Ix Xf Rn HJ2 Pie.
      - (* after block 63: the next chunk *)
        u64c.
        assert (R': entry_done x (w_chunk s) (w_block s) (a ++ [v]) m = begin_transition x (w_chunk s + 1) m')
          by (unfold entry_done; rewrite C; cbn [negb Z.eqb];
              rewrite (proj2 (Z.ltb_ge (w_block s + 1) BLOCKS)) by lia; reflexivity).
        rewrite R' in Rn.
        forward.
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
        sep_apply OC. entailer!. }
    forward. Exists v. entailer!.
Qed.
