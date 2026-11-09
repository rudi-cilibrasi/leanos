(* Law frame_selection_exact: the body of the harness's export leanos_boot_consume_exact_projection against
   consume_spec Ora_law: its checks follow from the consumer call the model expects for candidate c (4096, c,
   words 1, 14 and 15 of state k as the decoder wrote it, and c's manifest answer), and the answer moves the law's
   record as the model's consume_done: the next candidate, the first or second accepted frame, the scan's end. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosFrameSelection.harness.frame_selection_exact.code.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Require Import LeanosFrameSelection.proof.LawProg LeanosFrameSelection.proof.LawDefs LeanosFrameSelection.proof.LawFacts
  LeanosFrameSelection.proof.LawLib LeanosFrameSelection.proof.LawLib2 LeanosFrameSelection.proof.LawRows
  LeanosFrameSelection.proof.LawLib3.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Existing Instance LawProg.LCS.

Definition consume_fspec : ident * funspec := consume_spec Ora_law.

Definition Gconsume : funspecs := [gp_assert_spec; any_u64_spec; stop_spec; select_done_spec; next_candidate_spec].

(* The oracle at progress p' and record s': the run and the answers as one fact, the hypotheses of the run before
   the call cleared (entailer! is slow with them). *)
Ltac ora_pu p' :=
  match goal with Rn: run ?x (start ?x) ?hh = Some _ |- _ =>
    assert (answers_ok hh /\ run x (start x) hh = Some p') by (split; [ apply answers_ok_snoc; auto | exact Rn ]);
    clear Rn
  end.
Ltac clear_runs :=
  repeat match goal with H: run _ (start _) _ = _ |- _ => clear H | H: next_call _ _ = _ |- _ => clear H
                       | H: Go _ _ = _ |- _ => clear H | H: _ = Go _ _ |- _ => clear H | H: seq_ok _ _ _ |- _ => clear H end.
(* The record's fields after set_* (shallow) and the memory's after with_*. *)
Ltac rec_cbn := set_unfold; cbn [w_call w_running w_step w_expect w_verdict w_block w_word w_candidate w_scan w_ms
  w_me w_free w_cm w_first w_fm w_second w_answer w_scrubbed mem_of m_reserved m_terminal m_states m_publication
  m_rescan m_selected m_selected_manifest m_next m_decoder with_reserved with_terminal with_states with_state
  with_publication with_rescan with_records with_decoder].

(* The record after the first accepted frame v with the scan going on into state 1 (scan 1, first v, first_manifest
   the candidate's manifest answer), at candidate c with expect e and verdict st, as one constructor (nested set_*
   unfold exponentially). *)
Definition scan1_rec (s: lst) (v c e st: Z) : lst :=
  mk_lst (w_call s) (w_running s) (w_step s) e st (w_block s) (w_word s) c 1 (w_ms s) (w_me s) (w_free s) (w_cm s)
    v (w_cm s) (w_second s) (w_answer s) (w_scrubbed s).

Ltac ora_close_rest p' s' :=
  match goal with H: answers_ok _ /\ run _ _ _ = Some _ |- _ =>
    unfold Ora_law; Exists p' s';
    repeat (lazymatch goal with
            | |- _ |-- andp (prop _) _ =>
                apply andp_right;
                [ apply prop_right; split_and;
                  first [ assumption | exact (proj1 H) | exact (proj2 H) | reflexivity
                        | (unfold u64_ok in *; rep_lia) ]
                | ]
            end);
    clear H
  end;
  unfold lfields, scan1_rec; rec_cbn;
  cancel.

(* J after the first accepted frame with the scan going on into state 1: the next candidate, or the scan's end. *)
Lemma J_consume_scan1: forall x m s v, lst_ok s -> u64_ok v -> i_step x = FSelect -> w_step s = ST_SELECT ->
  w_second s = FRAMES -> 0 <= w_candidate s + 1 < FRAMES ->
  J x (Go (ExpectDecode (w_candidate s + 1) 1 v (w_cm s)) m) (scan1_rec s v (w_candidate s + 1) E_DECODE (w_verdict s)).
Proof.
  intros x m s v L V F Gst Gse C. lst_facts L. unfold J, scan1_rec. split_and.
  - apply lst_ok_mk; auto; unfold u32_ok, u64_ok, E_DECODE in *; rep_lia.
  - unfold seq_ok. split; intros G; exfalso; congruence.
  - cbn [go_inv]. lst_cbn. split_and; auto; lia.
Qed.

Lemma J_consume_stop1: forall x m s v, lst_ok s -> u64_ok v -> i_step x = FSelect ->
  J x (Return S_OK m) (scan1_rec s v (w_candidate s) E_NOTHING S_OK).
Proof.
  intros x m s v L V F. lst_facts L. unfold J, scan1_rec. split_and.
  - apply lst_ok_mk; auto; unfold u32_ok, u64_ok, E_NOTHING, S_OK in *; rep_lia.
  - unfold seq_ok. split; intros G; exfalso; congruence.
  - unfold ret_inv. lst_cbn. split; reflexivity.
Qed.

Lemma body_consume: semax_body Vlaw Gconsume f_leanos_boot_consume_exact_projection consume_fspec.
Proof.
  start_function.
  match goal with H: next_call _ _ = _ |- _ => rename H into Nc end.
  ora_open p s.
  destruct (next_go x h p _ Hrun Nc) as (g & m & -> & Ec). cbn [mem_of].
  pose proof (progress_of_run x h _ Ix Ah Hrun) as (Fs & Fw & Mm & Km).
  destruct (call_consume x g m cur c ds u bl cm (eq_sym Ec)) as (k & f & fm & -> & Ecur & Eds & Eu & Ebl).
  cbn [stage_step stage_words] in Fs, Fw. destruct Fw as (Wf & Wfm & Wcm).
  pose proof HJ as (Hs & Hq & Ge). cbn [go_inv] in Ge.
  destruct Ge as (Ge & Gst & Gc & Gc' & Gsc & Gk & Gf & Gfm & Gse & Gcm).
  lst_facts Hs. inputs_facts Ix. mem_facts Mm.
  pose proof (mem_ok_states m Mm) as (Ls & L0 & F0 & L1 & F1).
  assert (Lk: Zlength (Znth k (m_states m)) = WORDS /\ Forall u64_ok (Znth k (m_states m)))
    by (destruct Gk as [-> | ->]; auto).
  destruct Lk as [Lk Fk].
  rng_at (Znth k (m_states m)) [1; 14; 15].
  subst cur ds u bl c k f fm cm.
  unfold lfields. Intros.
  freeze_but [_call; _expect; _verdict; _scan; _states_expect; _candidate; _candidate_manifest; _first;
              _first_manifest; _second; _selected_expect; _manifest_expect; _next_expect; _take_next]
    (@nil val) F.
  forward. gp.
  { entailer!. all: try (rewrite Ge; reflexivity). }
  assert_PROP (field_compatible t_law (DOT _states_expect) (gv _law)) as FC by entailer!.
  rewrite (states_rows_k (gv _law) (m_states m) (w_scan s)) by auto. Intros.
  forward. forward.
  rewrite srow_field by (auto; lia).
  do 5 if1.
  forward_call Int.one.
  forward_call tt. Intros v.
  sep_apply (states_rows_k_fold (gv _law) (m_states m) (w_scan s)); auto.
  assert (Rn: run x (start x) (h ++ [(Consume FRAMES (w_candidate s) (Znth 1 (Znth (w_scan s) (m_states m))) (Znth 14 (Znth (w_scan s) (m_states m)))
                                         (Znth 15 (Znth (w_scan s) (m_states m))) (w_cm s), Word v)]) =
              Some (consume_done x (w_candidate s) (w_scan s) (w_first s) (w_fm s) (w_cm s) v m)).
  { rewrite Ec. rewrite (run_word' x h _ m v Hrun) by (intros c' k' E; discriminate). reflexivity. }
  unfold consume_done in Rn.
  apply semax_if_seq. forward_if.
  - (* v >= 4096: the next candidate *)
    u64c. assert (Q: FRAMES <= v) by lia. rewrite (proj2 (Z.leb_le _ _) Q) in Rn.
    replace (@field_at LCS Ews t_law (DOT _second) (vl (w_second s)) (gv _law)) with (@field_at LCS Ews t_law (DOT _second) (vl FRAMES) (gv _law)) by (rewrite Gse; reflexivity).
    forward_call (gv _law, (w_candidate s), (w_first s), (w_fm s), FRAMES, vl (m_selected m), vl (m_selected_manifest m), vl (m_next m),
                  vi (w_expect s), vi (w_verdict s)).
    forward.
    Exists v. thaw F.
    try replace (@field_at LCS Ews t_law (DOT _second) (vl FRAMES) (gv _law)) with (@field_at LCS Ews t_law (DOT _second) (vl (w_second s)) (gv _law)) by (rewrite Gse; reflexivity).
    unfold next_candidate, select_done in Rn.
    destruct (Z.ltb_spec ((w_candidate s) + 1) FRAMES).
    + ora_pu (Go (ExpectDecode ((w_candidate s) + 1) (w_scan s) (w_first s) (w_fm s)) m). clear_runs.
      assert (HJ': J x (Go (ExpectDecode ((w_candidate s) + 1) (w_scan s) (w_first s) (w_fm s)) m) (set_expect (set_candidate s ((w_candidate s) + 1)) E_DECODE)) by Jtac.
      ora_close_rest (Go (ExpectDecode ((w_candidate s) + 1) (w_scan s) (w_first s) (w_fm s)) m) (set_expect (set_candidate s ((w_candidate s) + 1)) E_DECODE).
    + ora_pu (Return S_OK (with_records m (w_first s) (w_fm s) FRAMES)). clear_runs.
      assert (HJ': J x (Return S_OK (with_records m (w_first s) (w_fm s) FRAMES)) (set_stop s S_OK)) by Jtac.
      ora_close_rest (Return S_OK (with_records m (w_first s) (w_fm s) FRAMES)) (set_stop s S_OK).
  - u64c. assert (Q: v < FRAMES) by lia. rewrite (proj2 (Z.leb_gt _ _) Q) in Rn.
    forward.
    apply semax_if_seq. forward_if.
    + (* the first accepted frame *)
      u64c. assert (K0: w_scan s = 0) by lia. rewrite (proj2 (Z.eqb_eq (w_scan s) 0) K0) in Rn.
      forward. forward. forward. forward.
      apply semax_if_seq. forward_if.
      * (* take_next 0: the scan stops *)
        u64c. assert (T0: i_take_next x = 0) by lia. rewrite (proj2 (Z.eqb_eq _ _) T0) in Rn.
        replace (@field_at LCS Ews t_law (DOT _second) (vl (w_second s)) (gv _law)) with (@field_at LCS Ews t_law (DOT _second) (vl FRAMES) (gv _law)) by (rewrite Gse; reflexivity).
        forward_call (gv _law, v, (w_cm s), FRAMES, vl (m_selected m), vl (m_selected_manifest m), vl (m_next m),
                      vi (w_expect s), vi (w_verdict s)).
        forward.
        Exists v. thaw F.
        try replace (@field_at LCS Ews t_law (DOT _second) (vl FRAMES) (gv _law)) with (@field_at LCS Ews t_law (DOT _second) (vl (w_second s)) (gv _law)) by (rewrite Gse; reflexivity).
        unfold select_done in Rn.
        ora_pu (Return S_OK (with_records m v (w_cm s) FRAMES)). clear_runs.
        assert (HJ': J x (Return S_OK (with_records m v (w_cm s) FRAMES)) (set_stop (set_fm (set_first s v) (w_cm s)) S_OK)) by Jtac.
        ora_close_rest (Return S_OK (with_records m v (w_cm s) FRAMES)) (set_stop (set_fm (set_first s v) (w_cm s)) S_OK).
      * (* the scan goes on into state 1 *)
        u64c. assert (T0: i_take_next x <> 0) by lia. rewrite (proj2 (Z.eqb_neq _ _) T0) in Rn.
        forward.
        replace (@field_at LCS Ews t_law (DOT _second) (vl (w_second s)) (gv _law)) with (@field_at LCS Ews t_law (DOT _second) (vl FRAMES) (gv _law)) by (rewrite Gse; reflexivity).
        forward_call (gv _law, (w_candidate s), v, (w_cm s), FRAMES, vl (m_selected m), vl (m_selected_manifest m), vl (m_next m),
                      vi (w_expect s), vi (w_verdict s)).
        forward.
        Exists v. thaw F.
        try replace (@field_at LCS Ews t_law (DOT _second) (vl FRAMES) (gv _law)) with (@field_at LCS Ews t_law (DOT _second) (vl (w_second s)) (gv _law)) by (rewrite Gse; reflexivity).
        unfold next_candidate, select_done in Rn.
        destruct (Z.ltb_spec ((w_candidate s) + 1) FRAMES).
        -- ora_pu (Go (ExpectDecode ((w_candidate s) + 1) 1 v (w_cm s)) m). clear_runs.
           assert (HJ': J x (Go (ExpectDecode ((w_candidate s) + 1) 1 v (w_cm s)) m)
                          (scan1_rec s v ((w_candidate s) + 1) E_DECODE (w_verdict s)))
             by (apply J_consume_scan1; first [ assumption | (unfold u64_ok in *; lia) | (symmetry; assumption) | lia ]).
           ora_close_rest (Go (ExpectDecode ((w_candidate s) + 1) 1 v (w_cm s)) m)
             (scan1_rec s v ((w_candidate s) + 1) E_DECODE (w_verdict s)).
        -- ora_pu (Return S_OK (with_records m v (w_cm s) FRAMES)). clear_runs.
           assert (HJ': J x (Return S_OK (with_records m v (w_cm s) FRAMES))
                          (scan1_rec s v (w_candidate s) E_NOTHING S_OK))
             by (apply J_consume_stop1; first [ assumption | (unfold u64_ok in *; lia) | (symmetry; assumption) ]).
           ora_close_rest (Return S_OK (with_records m v (w_cm s) FRAMES))
             (scan1_rec s v (w_candidate s) E_NOTHING S_OK).
    + (* the second accepted frame: the next frame *)
      u64c. assert (K1: w_scan s = 1) by lia. rewrite (proj2 (Z.eqb_neq (w_scan s) 0) ltac:(lia)) in Rn.
      forward.
      forward_call (gv _law, (w_first s), (w_fm s), v, vl (m_selected m), vl (m_selected_manifest m), vl (m_next m),
                    vi (w_expect s), vi (w_verdict s)).
      forward.
      Exists v. thaw F.
      try replace (@field_at LCS Ews t_law (DOT _second) (vl FRAMES) (gv _law)) with (@field_at LCS Ews t_law (DOT _second) (vl (w_second s)) (gv _law)) by (rewrite Gse; reflexivity).
      unfold select_done in Rn.
      ora_pu (Return S_OK (with_records m (w_first s) (w_fm s) v)). clear_runs.
      assert (HJ': J x (Return S_OK (with_records m (w_first s) (w_fm s) v)) (set_stop (set_second s v) S_OK)) by Jtac.
      ora_close_rest (Return S_OK (with_records m (w_first s) (w_fm s) v)) (set_stop (set_second s v) S_OK).
Qed.
