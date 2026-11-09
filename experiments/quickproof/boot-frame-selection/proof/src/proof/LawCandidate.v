(* Law frame_selection_exact: the body of the harness's export leanos_boot_manifest_candidate against
   candidate_spec Ora_law: its checks follow from the manifest answer the model expects (the selection's candidate
   c, or the rescan's next frame, with the manifest), and the answer moves the law's record as the model's step:
   the consumer next in the selection, the rescan's checks on state 1 and its record. *)
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

Definition candidate_fspec : ident * funspec := candidate_spec Ora_law.

Definition Gcandidate : funspecs := [gp_assert_spec; any_u64_spec; stop_spec; same_manifest_spec].

Lemma J_rescan_done: forall x m s v, lst_ok s -> u64_ok v -> i_step x = FRescan ->
  J x (rescan_done x v m) (set_stop (set_cm s v) (rescan_check x (Znth 1 (m_states m)) v)).
Proof.
  intros x m s v L V F. lst_facts L.
  assert (S: status_ok (rescan_check x (Znth 1 (m_states m)) v)) by checks_ok.
  pose proof (statuses_u32 _ S) as U.
  unfold rescan_done. destruct (Z.eqb_spec (rescan_check x (Znth 1 (m_states m)) v) S_OK) as [E | E].
  - rewrite E in *. Jtac.
  - Jtac.
Qed.

Ltac chk1 :=
  match goal with
  | |- context [if negb (Z.eqb ?a ?b) then _ else _] => destruct (Z.eqb_spec a b); cbn [negb]
  | |- context [if Z.leb ?a ?b then _ else _] => destruct (Z.leb_spec a b)
  | |- context [if Z.eqb ?a ?b then _ else _] => destruct (Z.eqb_spec a b)
  end.
Ltac chk_rescan := unfold rescan_check; repeat (first [ reflexivity | solve [ exfalso; lia ] | chk1 ]).

Lemma rescan_done_mem: forall x v m, mem_of (rescan_done x v m) =
  if rescan_check x (Znth 1 (m_states m)) v =? S_OK
  then with_rescan m [Znth 16 (Znth 1 (m_states m)); Znth 1 (Znth 1 (m_states m)); Znth 14 (Znth 1 (m_states m));
                      Znth 15 (Znth 1 (m_states m)); v]
  else m.
Proof. intros. unfold rescan_done. destruct (_ =? _); reflexivity. Qed.

Lemma states_rows_fold': forall q ss, field_compatible t_law (DOT _states_expect) q -> Zlength ss = 2 ->
  Zlength (Znth 0 ss) = WORDS -> Zlength (Znth 1 ss) = WORDS ->
  (data_at Ews (tarray tulong 41) (map vl (Znth 0 ss)) (srow q 0) *
   data_at Ews (tarray tulong 41) (map vl (Znth 1 ss)) (srow q 1))%logic
  |-- field_at Ews t_law (DOT _states_expect) (states_val ss) q.
Proof. intros. rewrite states_rows by auto. apply derives_refl. Qed.

Lemma upd5: forall (l: list Z) a b c d e, Zlength l = 5 ->
  upd_Znth 4 (upd_Znth 3 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 (map vl l) a) b) c) d) e = [a; b; c; d; e].
Proof.
  intros l a b c d e L. destruct l as [ | r0 [ | r1 [ | r2 [ | r3 [ | r4 [ | r5 l]]]]]];
    try (rewrite ?Zlength_cons, ?Zlength_nil in L; rep_lia). reflexivity.
Qed.

(* A leaf of the rescan's checks: stop(m, k), k its verdict. *)
Ltac rc_leaf q x m v s k :=
  forward_call (q, vi (w_expect s), vi (w_verdict s), k);
  rewrite ?rescan_done_mem;
  replace (rescan_check x (Znth 1 (m_states m)) v) with k by chk_rescan;
  cbn [Z.eqb];
  try match goal with H: w_scan s = 1 |- _ => rewrite H end;
  entailer!.

Lemma body_candidate: semax_body Vlaw Gcandidate f_leanos_boot_manifest_candidate candidate_fspec.
Proof.
  start_function.
  match goal with H: next_call _ _ = _ |- _ => rename H into Nc end.
  ora_open p s.
  destruct (next_go x h p _ Hrun Nc) as (g & m & -> & Ec). cbn [mem_of].
  pose proof (progress_of_run x h _ Ix Ah Hrun) as (Fs & Fw & Mm & Km).
  pose proof HJ as (Hs & Hq & Ge).
  destruct (call_candidate x g m f ms (eq_sym Ec)) as [Gg Ems].
  assert (Gk: w_expect s = E_CANDIDATE /\ w_candidate s = f).
  { destruct Gg as [(k & f' & fm & ->) | (-> & ->)]; cbn [go_inv] in Ge; tauto. }
  destruct Gk as (Ge4 & Gc). subst f.
  lst_facts Hs. inputs_facts Ix. mem_facts Mm.
  pose proof (mem_ok_states m Mm) as (Ls & L0 & F0 & L1 & F1).
  subst ms.
  unfold lfields. Intros.
  freeze_but [_call; _expect; _verdict; _step; _candidate; _manifest; _candidate_manifest; _states_expect; _scan;
              _decoded; _rescan_expect] [v_words] F.
  forward.
  if1.
  forward_call Int.one.
  do 18 forward.
  assert (Lm: Zlength (i_manifest x) = Z.of_nat 18) by (rewrite Iml; reflexivity).
  words_fill (i_manifest x) 18%nat.
  forward_call (gv, v_words, i_manifest x, Tsh).
  forward_call Int.one.
  forward_call tt. Intros v.
  forward.
  forward.
  apply semax_if_seq. forward_if.
  - (* the selection: the consumer next *)
    destruct Gg as [(k & f' & fm & ->) | (-> & Ef)].
    2: { cbn [go_inv] in Ge. exfalso. destruct Ge as (_ & Gst & _). rewrite Gst in *. unfold ST_RESCAN in *. u64c. lia. }
    cbn [go_inv stage_words stage_step] in Ge, Fw, Fs.
    forward. forward.
    Exists v. thaw F.
    assert (Rn: run x (start x) (h ++ [(Candidate (w_candidate s) (i_manifest x), Word v)]) =
                Some (Go (ExpectConsume (w_candidate s) k f' fm v) m)).
    { rewrite Ec. rewrite (run_word' x h _ m v Hrun) by (intros c' k' E; discriminate). reflexivity. }
    assert (HJ': J x (Go (ExpectConsume (w_candidate s) k f' fm v) m) (set_expect (set_cm s v) E_CONSUME)).
    { Jtac. }
    ora_close_tac (Go (ExpectConsume (w_candidate s) k f' fm v) m) (set_expect (set_cm s v) E_CONSUME).
  - (* the rescan of the next frame: the checks on state 1 *)
    destruct Gg as [(k & f' & fm & ->) | (-> & Ef)].
    { cbn [go_inv] in Ge. exfalso. destruct Ge as (_ & Gst & _). rewrite Gst in *. unfold ST_SELECT in *. u64c. lia. }
    cbn [go_inv stage_step] in Ge, Fs. destruct Ge as (_ & Gst & Gcn & Gsc).
    rng_at (Znth 1 (m_states m)) [1; 11; 14; 15; 16; 17]. rng_at (i_decoded x) [11; 17].
    assert_PROP (field_compatible t_law (DOT _states_expect) (gv _law)) as FC by entailer!.
    rewrite (states_rows (gv _law) (m_states m)) by auto. Intros. unfold t_state.
    forward. forward.
    rewrite Gsc. rewrite srow_field by (auto; lia).
    forward. forward.
    forward_if (PROP ()
      LOCAL (temp _v (vl v); temp _m (gv _law); lvar _words (tarray tulong 18) v_words; gvars gv)
      SEP (FRZL F; data_at Tsh (tarray tulong 18) (map vl (i_manifest x)) v_words;
           data_at Ews (tarray tulong 41) (map vl (Znth 0 (m_states m))) (srow (gv _law) 0);
           data_at Ews (tarray tulong 41) (map vl (Znth 1 (m_states m))) (srow (gv _law) 1);
           field_at Ews t_law (DOT _call) (vi (w_call s)) (gv _law);
           field_at Ews t_law (DOT _expect) (vi E_NOTHING) (gv _law);
           field_at Ews t_law (DOT _verdict) (vi (rescan_check x (Znth 1 (m_states m)) v)) (gv _law);
           field_at Ews t_law (DOT _step) (vi (w_step s)) (gv _law);
           field_at Ews t_law (DOT _candidate) (vl (w_candidate s)) (gv _law);
           field_at Ews t_law (DOT _manifest) (map vl (i_manifest x)) (gv _law);
           field_at Ews t_law (DOT _candidate_manifest) (vl v) (gv _law);
           field_at Ews t_law (DOT _scan) (vi (w_scan s)) (gv _law);
           field_at Ews t_law (DOT _decoded) (map vl (i_decoded x)) (gv _law);
           field_at Ews t_law (DOT _rescan_expect) (map vl (m_rescan (mem_of (rescan_done x v m)))) (gv _law))).
    { u64c. rc_leaf (gv _law) x m v s S_RESCAN_ENTRY_COUNT. }
    u64c. forward. forward.
    forward_if.
    { u64c. rc_leaf (gv _law) x m v s S_RESCAN_HIGHEST. }
    u64c. forward. forward.
    forward_if.
    { u64c. rc_leaf (gv _law) x m v s S_RESCAN_TARGET. }
    u64c. forward.
    forward_if.
    { u64c. rc_leaf (gv _law) x m v s S_RESCAN_STATUS. }
    u64c. forward.
    forward_if.
    { u64c. rc_leaf (gv _law) x m v s S_RESCAN_USABLE. }
    u64c. forward.
    forward_if.
    { u64c. rc_leaf (gv _law) x m v s S_RESCAN_BLOCKED. }
    u64c.
    forward_if.
    { u64c. rc_leaf (gv _law) x m v s S_RESCAN_MANIFEST. }
    u64c.
    do 9 forward.
    forward_call (gv _law, vi (w_expect s), vi (w_verdict s), S_OK).
    rewrite ?rescan_done_mem.
    replace (rescan_check x (Znth 1 (m_states m)) v) with S_OK by chk_rescan.
    cbn [Z.eqb m_rescan with_rescan].
    rewrite upd5 by auto.
    try match goal with H: w_scan s = 1 |- _ => rewrite H end.
    entailer!.
  forward.
  Exists v. thaw F.
  sep_apply (states_rows_fold' (gv _law) (m_states m)); auto.
  assert (Rn: run x (start x) (h ++ [(Candidate (w_candidate s) (i_manifest x), Word v)]) = Some (rescan_done x v m)).
  { rewrite Ec. rewrite (run_word' x h _ m v Hrun) by (intros c' k' E; discriminate). reflexivity. }
  pose proof (J_rescan_done x m s v Hs H (eq_sym Fs)) as HJ'.
  unfold Ora_law. Exists (rescan_done x v m) (set_stop (set_cm s v) (rescan_check x (Znth 1 (m_states m)) v)).
  rewrite rescan_done_mem.
  destruct (rescan_check x (Znth 1 (m_states m)) v =? S_OK);
    unfold lfields; set_unfold; lst_cbn;
    cbn [m_reserved m_terminal m_states m_publication m_rescan m_selected m_selected_manifest m_next m_decoder
         with_rescan]; entailer!; apply answers_ok_snoc; auto.
Qed.

