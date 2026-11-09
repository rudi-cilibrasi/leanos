(* Law frame_selection_exact: the body of the harness's candidate decoder law_decode against decode_spec Ora_law:
   its checks follow from the decode the model expects (candidate c into state k: the selection's, or the
   rescan's of the next frame into state 1), and its 41 words and status move the law's record and its model of
   memory as the model's decode_done. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosFrameSelection.harness.frame_selection_exact.code.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Require Import LeanosFrameSelection.proof.LawProg LeanosFrameSelection.proof.LawDefs LeanosFrameSelection.proof.LawFacts
  LeanosFrameSelection.proof.LawLib.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Existing Instance LawProg.LCS.

Definition decode_fspec : ident * funspec := (_law_decode, decode_spec Ora_law).

Definition Gdecode : funspecs := [gp_assert_spec; any_u64_spec; stop_spec].

(* The record after the decoder's answer st: the candidate's manifest answer next, or DECODER. *)
Definition s_decoded (s: lst) (st: Z) : lst :=
  if st =? 0 then set_expect (set_word s WORDS) E_CANDIDATE else set_stop (set_word s WORDS) S_DECODER.

Lemma J_decoded: forall x g m s c k st ws, J x (Go g m) s -> expected x g m = Decode c k -> stage_step g = i_step x ->
  u32_ok st -> J x (step x g m (Decoded st ws)) (s_decoded s st).
Proof.
  intros x g m s c k st ws (L & Q & G) E F U. lst_facts L.
  destruct (call_decode x g m c k E) as [(f & fm & ->) | (-> & -> & ->)]; cbn [stage_step] in F;
    unfold step, decode_done; cbn [reply_value reply_state]; unfold s_decoded;
    destruct (Z.eqb_spec st 0); unfold J; split_and.
  all: try (unfold lst_ok; set_unfold; lst_cbn; split_and; auto; unfold u32_ok, u64_ok, E_CANDIDATE, E_NOTHING,
              S_DECODER; rep_lia).
  all: try (split; intros G'; [ congruence | intros m' E'; congruence ]).
  all: try (unfold ret_inv; set_unfold; lst_cbn; split; reflexivity).
  all: cbn [go_inv] in G |- *; set_unfold; lst_cbn; tauto.
Qed.

Lemma mem_decoded: forall x g m c k st ws, expected x g m = Decode c k ->
  mem_of (step x g m (Decoded st ws)) =
  if st =? 0 then with_state m k ws else with_decoder (with_state m k ws) st.
Proof.
  intros x g m c k st ws E.
  destruct (call_decode x g m c k E) as [(f & fm & ->) | (-> & -> & ->)];
    unfold step, decode_done; cbn [reply_value reply_state]; destruct (st =? 0); reflexivity.
Qed.

Lemma Znth_dflt: forall {A} (d1 d2: Inhabitant A) (l: list A) i, 0 <= i < Zlength l ->
  @Znth A d1 i l = @Znth A d2 i l.
Proof.
  intros A d1 d2 l i I. unfold Znth. rewrite !if_false by lia. apply nth_indep.
  rewrite <- ZtoNat_Zlength. apply Z2Nat.inj_lt; lia.
Qed.

(* The row k of the states, written word by word. *)
Lemma states_row_step: forall (d: Inhabitant (list val)) (ss: list (list Z)) k (ws: list Z) i v,
  0 <= k < Zlength ss -> Zlength (Znth k ss) = WORDS -> Zlength ws = i -> 0 <= i < WORDS ->
  upd_Znth k (states_val (upd_Znth k ss (ws ++ sublist i WORDS (Znth k ss))))
    (upd_Znth i (@Znth _ d k (states_val (upd_Znth k ss (ws ++ sublist i WORDS (Znth k ss))))) (vl v))
  = states_val (upd_Znth k ss ((ws ++ [v]) ++ sublist (i + 1) WORDS (Znth k ss))).
Proof.
  intros d ss k ws i v K L W I.
  rewrite (Znth_dflt d Inhabitant_list) by (unfold states_val; rewrite Zlength_map, upd_Znth_Zlength; lia).
  unfold states_val. rewrite Znth_map by (rewrite upd_Znth_Zlength; lia). rewrite upd_Znth_same by lia.
  rewrite upd_Znth_map_vl. rewrite upd_Znth_map. rewrite upd_Znth_twice by lia. f_equal. f_equal. list_solve.
Qed.

Lemma row_eval: forall sp k, isptr sp -> 0 <= k <= 1 ->
  force_val (sem_add_ptr_int (tarray tulong 41) Unsigned sp (vi k)) = row_ptr sp k.
Proof.
  intros sp k P K. destruct sp; try contradiction.
  unfold row_ptr, vi, STATE_BYTES, offset_val. simpl.
  replace (Ptrofs.mul (Ptrofs.repr 328) (Ptrofs.of_intu (Int.repr k))) with (Ptrofs.repr (328 * k)); [ reflexivity | ].
  unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by rep_lia. rewrite ptrofs_mul_repr. reflexivity.
Qed.

Lemma states_row_start: forall (ss: list (list Z)) k, 0 <= k < Zlength ss -> Zlength (Znth k ss) = WORDS ->
  upd_Znth k ss (@nil Z ++ sublist 0 WORDS (Znth k ss)) = ss.
Proof. intros ss k K L. rewrite app_nil_l, sublist_same by auto. apply upd_Znth_triv; auto. Qed.

Lemma states_row_end: forall (ss: list (list Z)) k ws, Zlength (Znth k ss) = WORDS ->
  upd_Znth k ss (ws ++ sublist WORDS WORDS (Znth k ss)) = upd_Znth k ss ws.
Proof. intros. rewrite sublist_nil, app_nil_r. reflexivity. Qed.

Lemma body_law_decode: semax_body Vlaw Gdecode f_law_decode decode_fspec.
Proof.
  start_function.
  match goal with H: next_call _ _ = _ |- _ => rename H into Nc end.
  match goal with H: writable_share _ |- _ => rename H into Wsh end.
  match goal with H: isptr _ |- _ => rename H into Psp end.
  ora_open p s.
  destruct (next_go x h p _ Hrun Nc) as (g & m & -> & Ec). cbn [mem_of].
  pose proof (progress_of_run x h _ Ix Ah Hrun) as (Fs & _ & Mm & Km).
  pose proof HJ as (Hs & Hq & Ge).
  assert (Gk: w_expect s = E_DECODE /\ w_candidate s = c /\ w_scan s = k /\ (k = 0 \/ k = 1)).
  { destruct (call_decode x g m c k (eq_sym Ec)) as [(f & fm & ->) | (-> & -> & ->)]; cbn [go_inv] in Ge; tauto. }
  destruct Gk as (Ge3 & Gc & Gsc & Gk). subst c k.
  lst_facts Hs. inputs_facts Ix. mem_facts Mm.
  pose proof (mem_ok_states m Mm) as (Ls & L0 & F0 & L1 & F1).
  assert (Lk: Zlength (Znth (w_scan s) (m_states m)) = WORDS) by (destruct Gk as [-> | ->]; auto).
  unfold lfields. Intros.
  unfold t_state. rewrite (data_at__arr_cs FrameSpecs.CS LCS).
  freeze_but [_call; _expect; _candidate; _states; _scan; _word; _states_expect; _decoder_expect; _verdict]
    [row_ptr sp (w_scan s)] F.
  forward.
  forward_if (temp _t'1 (Vint Int.one)).
  { forward. forward. entailer!; rewrite ?Ge3; try reflexivity. }
  { else_false. }
  forward_if (temp _t'2 (Vint Int.one)).
  { forward. forward. entailer!; rewrite ?Gc, ?Int64.eq_true; try reflexivity. }
  { else_false. }
  forward_call Int.one.
  forward. forward.
  forward_call Int.one.
  { entailer!. rewrite row_eval by (auto; lia). apply denote_tc_test_eq_split; auto with valid_pointer. }
  { entailer!. destruct sp; try contradiction. unfold row_ptr, offset_val, vi, STATE_BYTES. simpl.
    unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by rep_lia. rewrite ptrofs_mul_repr.
    match goal with |- context [if ?d then _ else _] => destruct d; [ reflexivity | congruence ] end. }
  forward_for_simple_bound 41
    (EX i: Z, EX ws: list Z, EX wv: Z,
     PROP (Zlength ws = i; Forall u64_ok ws)
     LOCAL (temp _m (gv _law); temp _state (row_ptr sp (w_scan s)); gvars gv)
     SEP (FRZL F; field_at Ews t_law (DOT _call) (vi (w_call s)) (gv _law);
          field_at Ews t_law (DOT _expect) (vi (w_expect s)) (gv _law);
          field_at Ews t_law (DOT _candidate) (vl (w_candidate s)) (gv _law);
          field_at Ews t_law (DOT _states) sp (gv _law);
          field_at Ews t_law (DOT _scan) (vi (w_scan s)) (gv _law);
          field_at Ews t_law (DOT _word) (vl wv) (gv _law);
          field_at Ews t_law (DOT _states_expect)
            (states_val (upd_Znth (w_scan s) (m_states m) (ws ++ sublist i WORDS (Znth (w_scan s) (m_states m)))))
            (gv _law);
          field_at Ews t_law (DOT _decoder_expect) (vi (m_decoder m)) (gv _law);
          field_at Ews t_law (DOT _verdict) (vi (w_verdict s)) (gv _law);
          data_at sh (tarray tulong 41) (map vl ws ++ Zrepeat Vundef (41 - i)) (row_ptr sp (w_scan s))))%assert.
  { Exists (@nil Z) (w_word s). rewrite (states_row_start (m_states m) (w_scan s)) by lia.
    rewrite data_at__eq. entailer!. }
  { forward.
    forward_call tt. Intros v.
    forward.
    forward.
    forward.
    Exists (ws ++ [v]) (Int.unsigned (Int.repr i)).
    rewrite (states_row_step _ (m_states m) (w_scan s) ws i v) by (auto; lia).
    replace (upd_Znth i (map vl ws ++ Zrepeat Vundef (41 - i)) (vl v))
      with (map vl (ws ++ [v]) ++ Zrepeat Vundef (41 - (i + 1))) by list_solve.
    entailer!.
    all: try (split; [ list_solve | apply Forall_u64_app1; auto ]). }
  Intros ws wv.
  rewrite (states_row_end (m_states m) (w_scan s) ws) by auto.
  replace (map vl ws ++ Zrepeat Vundef (41 - 41)) with (map vl ws) by list_solve.
  forward.
  rewrite <- seq_assoc. forward_call tt. Intros v. forward.
  rewrite (Int64.unsigned_repr v) by rep_lia. rewrite (low32 v).
  assert (Rv: u32_ok (v mod 2 ^ 32)) by (apply low32_range).
  remember (v mod 2 ^ 32) as st eqn:Est. clear Est. pose proof Rv as Rv'. unfold u32_ok in Rv'.
  change (Vlong (Int64.repr (Int.signed (Int.repr 41)))) with (vl WORDS).
  assert (Rn: run x (start x) (h ++ [(Decode (w_candidate s) (w_scan s), Decoded st ws)]) =
              Some (step x g m (Decoded st ws))) by (apply run_decoded; auto).
  pose proof (J_decoded x g m s (w_candidate s) (w_scan s) st ws HJ (eq_sym Ec) Fs Rv) as HJ'.
  pose proof (mem_decoded x g m _ _ st ws (eq_sym Ec)) as Hm'.
  assert (Rws: reply_ok (Decode (w_candidate s) (w_scan s)) (Decoded st ws)) by (split; auto).
  apply semax_if_seq. forward_if.
  { (* a status other than 0: DECODER *)
    u64c. assert (N: (st =? 0) = false) by (apply Z.eqb_neq; auto).
    forward.
    forward_call (gv _law, vi (w_expect s), vi (w_verdict s), S_DECODER).
    forward.
    Exists st ws. thaw F.
    unfold Ora_law. Exists (step x g m (Decoded st ws)) (s_decoded s st).
    rewrite Hm', N. unfold s_decoded in *. rewrite N in *. unfold lfields. set_unfold; lst_cbn.
    cbn [m_reserved m_terminal m_states m_publication m_rescan m_selected m_selected_manifest m_next m_decoder
         with_state with_states with_decoder].
    rewrite (data_at_arr_cs LCS FrameSpecs.CS sh 41 (map vl ws) (row_ptr sp (w_scan s))). unfold t_state.
    entailer!. apply answers_ok_snoc; auto. }
  { (* status 0: the candidate's manifest answer next *)
    u64c. subst st.
    forward.
    forward.
    Exists 0 ws. thaw F.
    unfold Ora_law. Exists (step x g m (Decoded 0 ws)) (s_decoded s 0).
    rewrite Hm'. unfold s_decoded in *. cbn [Z.eqb] in *. unfold lfields. set_unfold; lst_cbn.
    cbn [m_reserved m_terminal m_states m_publication m_rescan m_selected m_selected_manifest m_next m_decoder
         with_state with_states with_decoder].
    rewrite (data_at_arr_cs LCS FrameSpecs.CS sh 41 (map vl ws) (row_ptr sp (w_scan s))). unfold t_state.
    entailer!. apply answers_ok_snoc; auto. }
Qed.


