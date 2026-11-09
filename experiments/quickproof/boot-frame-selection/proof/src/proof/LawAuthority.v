(* Law frame_selection_exact: the body of the harness's export leanos_boot_authority_result against authority_spec
   Ora_law: its checks follow from the publication result's word q the model expects (the selected frame, state
   0's words 16, 1, 14 and 15, the manifest answer and a scrubbed frame), the sequence's check (not CALL_ALLOCATE,
   or the scrub answered 1) from seq_ok, and the answer moves the law's record as the model's authority_done. *)
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

Definition authority_fspec : ident * funspec := authority_spec Ora_law.

Definition Gauthority : funspecs := [gp_assert_spec; any_u64_spec; stop_spec].

Lemma J_authority_more: forall x q m s m', J x (Go (ExpectAuthority q) m) s -> q + 1 < PUBLICATION_WORDS ->
  i_step x = FPublicationResult -> J x (Go (ExpectAuthority (q + 1)) m') (set_word s (q + 1)).
Proof.
  intros x q m s m' (L & Q & G) Hq F. cbn [go_inv] in G. destruct G as (Ge & Gw & Gq).
  lst_facts L. unfold J. split_and.
  - unfold set_word. apply lst_ok_mk; auto; unfold u32_ok, u64_ok; rep_lia.
  - destruct Q as [Q1 Q2]. split; [ intros G1; exact (Q1 G1) | intros G1; congruence ].
  - cbn [go_inv]. set_unfold; lst_cbn. split_and; auto; lia.
Qed.

Lemma J_authority_last: forall x q m s m', J x (Go (ExpectAuthority q) m) s -> i_step x = FPublicationResult ->
  J x (Return S_OK m') (set_stop s S_OK).
Proof.
  intros x q m s m' (L & Q & G) F. lst_facts L. unfold J. split_and.
  - unfold set_stop. apply lst_ok_mk; auto; unfold u32_ok, u64_ok, E_NOTHING, S_OK in *; rep_lia.
  - destruct Q as [Q1 Q2]. split; [ intros G1; exact (Q1 G1) | intros G1; congruence ].
  - unfold ret_inv. set_unfold; lst_cbn. split; reflexivity.
Qed.

Lemma states_rows_fold: forall q ss, field_compatible t_law (DOT _states_expect) q -> Zlength ss = 2 ->
  Zlength (Znth 0 ss) = WORDS -> Zlength (Znth 1 ss) = WORDS ->
  (data_at Ews (tarray tulong 41) (map vl (Znth 0 ss)) (srow q 0) *
   data_at Ews (tarray tulong 41) (map vl (Znth 1 ss)) (srow q 1))%logic
  |-- field_at Ews t_law (DOT _states_expect) (states_val ss) q.
Proof. intros. rewrite states_rows by auto. apply derives_refl. Qed.

Lemma body_authority: semax_body Vlaw Gauthority f_leanos_boot_authority_result authority_fspec.
Proof.
  start_function.
  rename s into s0.
  match goal with H: next_call _ _ = _ |- _ => rename H into Nc end.
  ora_open p s.
  destruct (next_go x h p _ Hrun Nc) as (g & m & -> & Ec). cbn [mem_of].
  pose proof (progress_of_run x h _ Ix Ah Hrun) as (Fs & _ & Mm & Km).
  destruct (call_authority x g m s0 t ds u bl sm sc q (eq_sym Ec)) as (-> & Es & Et & Eds & Eu & Ebl & Esm & Esc).
  cbn [stage_step] in Fs.
  pose proof HJ as (Hs & Hq & Ge). cbn [go_inv] in Ge.
  destruct Ge as (Ge & Gw & Gq).
  lst_facts Hs. inputs_facts Ix. mem_facts Mm.
  pose proof (mem_ok_states m Mm) as (Ls & L0 & F0 & L1 & F1).
  rng_at (Znth 0 (m_states m)) [1; 14; 15; 16].
  subst s0 t ds u bl sm sc q.
  unfold lfields. Intros.
  freeze_but [_call; _expect; _verdict; _word; _selected; _selected_manifest; _states_expect; _scrubbed;
              _publication_expect] (@nil val) F.
  forward.
  if1.
  forward_call Int.one.
  assert_PROP (field_compatible t_law (DOT _states_expect) (gv _law)) as FC by entailer!.
  rewrite (states_rows (gv _law) (m_states m)) by auto. Intros.
  unfold t_state.
  forward.
  rewrite srow_field0 by auto.
  do 6 if1.
  forward_call Int.one.
  forward.
  forward_if (temp _t'8 (Vint Int.one)).
  { forward. entailer!. }
  { u64c. assert (Sc: w_scrubbed s = 1) by (destruct Hq as [Hq1 _]; destruct (Hq1 (eq_sym Fs)); [ lia | auto ]).
    forward. forward. entailer!. all: try (rewrite Sc; reflexivity). }
  forward_call Int.one.
  forward_call tt. Intros v.
  forward. vl_temps. forward.
  forward.
  assert (Rn: run x (start x) (h ++ [(Authority (i_selected x) (Znth 16 (Znth 0 (m_states m)))
                                         (Znth 1 (Znth 0 (m_states m))) (Znth 14 (Znth 0 (m_states m)))
                                         (Znth 15 (Znth 0 (m_states m))) (i_selected_manifest x) 1 (w_word s), Word v)]) =
              Some (authority_done (w_word s) (with_publication m (upd_Znth (w_word s) (m_publication m) v)))).
  { rewrite Ec. rewrite (run_word' x h _ m v Hrun) by (intros c k E; discriminate). reflexivity. }
  sep_apply (states_rows_fold (gv _law) (m_states m)); auto.
  apply semax_if_seq. forward_if.
  - (* words 0 .. 3: the next word *)
    u64c. assert (Q4: (w_word s) + 1 < PUBLICATION_WORDS) by lia.
    forward. forward. forward.
    Exists v. thaw F.
    pose proof (J_authority_more x (w_word s) m s (with_publication m (upd_Znth (w_word s) (m_publication m) v)) HJ Q4 (eq_sym Fs))
      as HJ'.
    unfold authority_done in Rn. rewrite (proj2 (Z.ltb_lt _ _) Q4) in Rn.
    ora_close_tac (Go (ExpectAuthority ((w_word s) + 1)) (with_publication m (upd_Znth (w_word s) (m_publication m) v)))
      (set_word s ((w_word s) + 1)).
  - (* word 4: the last *)
    u64c. assert (Q4: PUBLICATION_WORDS <= (w_word s) + 1) by lia.
    forward_call (gv _law, vi (w_expect s), vi (w_verdict s), S_OK).
    forward.
    Exists v. thaw F.
    pose proof (J_authority_last x (w_word s) m s (with_publication m (upd_Znth (w_word s) (m_publication m) v)) HJ
                  (eq_sym Fs)) as HJ'.
    unfold authority_done in Rn. rewrite (proj2 (Z.ltb_ge _ _) Q4) in Rn.
    ora_close_tac (Return S_OK (with_publication m (upd_Znth (w_word s) (m_publication m) v))) (set_stop s S_OK).
Qed.


