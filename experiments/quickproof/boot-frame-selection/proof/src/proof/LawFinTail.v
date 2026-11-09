(* Law frame_selection_exact: the export leanos_boot_projection_finish from its check of the 64 free words on: its checks follow from the terminal result's word q the model expects (the decoded state's words 1, 2,
   11 and 17, the overlay's status and error, owner 1 and the 64 free words), and the answer moves the law's
   record as the model's finish_done: the next word, or after word 8 the terminal checks. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosFrameSelection.harness.frame_selection_exact.code.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Require Import LeanosFrameSelection.proof.LawProg LeanosFrameSelection.proof.LawDefs LeanosFrameSelection.proof.LawFacts
  LeanosFrameSelection.proof.LawLib LeanosFrameSelection.proof.LawLib2 LeanosFrameSelection.proof.LawRows
  LeanosFrameSelection.proof.LawLib3 LeanosFrameSelection.proof.LawFinStores.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
#[local] Existing Instance LawProg.LCS.



Lemma J_finish_more: forall x q ms me fw m s m', J x (Go (ExpectFinish q ms me fw) m) s -> q + 1 < TERMINAL_WORDS ->
  i_step x = FTerminal -> J x (Go (ExpectFinish (q + 1) ms me fw) m') (set_word s (q + 1)).
Proof.
  intros x q ms me fw m s m' (L & Q & G) Hq F. cbn [go_inv] in G. destruct G as (Ge & Gw & Gq & Gms & Gme & Gf).
  lst_facts L. unfold J. split_and.
  - unfold set_word. apply lst_ok_mk; auto; unfold u32_ok, u64_ok; rep_lia.
  - unfold seq_ok. split; intros G; congruence.
  - cbn [go_inv]. set_unfold; lst_cbn. split_and; auto; lia.
Qed.

Lemma J_finish_last: forall x st m s, lst_ok s -> status_ok st -> i_step x = FTerminal ->
  J x (Return st m) (set_stop s st).
Proof.
  intros x st m s L S F. lst_facts L. pose proof (statuses_u32 st S) as U. unfold J. split_and.
  - unfold set_stop. apply lst_ok_mk; auto; unfold u32_ok, u64_ok, E_NOTHING in *; rep_lia.
  - unfold seq_ok. split; intros G; congruence.
  - unfold ret_inv. set_unfold; lst_cbn. split; reflexivity.
Qed.

Lemma terminal_at: forall q v, field_compatible t_law (DOT _terminal_expect) q ->
  field_at Ews t_law (DOT _terminal_expect) v q = data_at Ews (tarray tulong 9) v (offset_val 2056 q).
Proof. intros. rewrite field_at_data_at, field_compatible_field_address by auto. reflexivity. Qed.

Ltac chk1 :=
  match goal with
  | |- context [if negb (Z.eqb ?a ?b) then _ else _] => destruct (Z.eqb_spec a b); cbn [negb]
  | |- context [if Z.leb ?a ?b then _ else _] => destruct (Z.leb_spec a b)
  | |- context [if Z.eqb ?a ?b then _ else _] => destruct (Z.eqb_spec a b)
  end.
Ltac chk_terminal := unfold terminal_check; cbn [m_terminal with_terminal];
  repeat (first [ reflexivity | solve [ exfalso; lia ] | chk1 ]).

(* The statements after the 64 stores of the local array, and the function's return assertion. *)
Definition fin_rest : statement := ltac:(
  let b := eval cbv delta [f_leanos_boot_projection_finish] beta iota zeta in
    (fn_body f_leanos_boot_projection_finish) in
  match b with
  | context [Ssequence (Ssequence (Sset _b (Econst_int (Int.repr 0) tint)) ?l) ?rest] =>
      exact (Ssequence (Ssequence (Sset _b (Econst_int (Int.repr 0) tint)) l) rest)
  end).

Definition fin_call (x: inputs) (s: lst) : call :=
  Finish (Znth 1 (i_decoded x)) (Znth 2 (i_decoded x)) (w_ms s) (w_me s) (Znth 11 (i_decoded x))
         (Znth 17 (i_decoded x)) 1 (w_word s) (w_free s).

Definition fin_post (gv: globals) (sp: val) (x: inputs) (h: list answer) (s: lst) : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tulong
       (EX v: Z, PROP (u64_ok v) RETURN (vl v)
                 SEP (Ora_law gv (gv _law) (gv _law) sp x (h ++ [(fin_call x s, Word v)])))%argsassert)
    (stackframe_of f_leanos_boot_projection_finish).

Definition Delta_fin : tycontext := func_tycontext f_leanos_boot_projection_finish Vlaw Gfinish nil.

Lemma fin_tail {Espec: OracleKind} gv sp x h s m v_words:
  inputs_ok x -> answers_ok h -> mem_ok m -> i_step x = FTerminal ->
  run x (start x) h = Some (Go (ExpectFinish (w_word s) (w_ms s) (w_me s) (w_free s)) m) ->
  J x (Go (ExpectFinish (w_word s) (w_ms s) (w_me s) (w_free s)) m) s ->
  forall Delta R c, Delta = Delta_fin -> R = fin_post gv sp x h s -> c = fin_rest ->
  semax Delta
    (PROP () LOCAL (temp _m (gv _law); lvar _words (tarray tulong 64) v_words; gvars gv)
     SEP (lfields (gv _law) x sp m s; data_at Tsh (tarray tulong 64) (map vl (w_free s)) v_words)) c R.
Proof.
  intros Ix Ah Mm Fst Hrun HJ Delta R c -> -> ->.
  unfold fin_rest, fin_post, Delta_fin. start_tail.
  assert (Fs: FTerminal = i_step x) by auto.
  assert (Ec: Finish (Znth 1 (i_decoded x)) (Znth 2 (i_decoded x)) (w_ms s) (w_me s) (Znth 11 (i_decoded x))
                (Znth 17 (i_decoded x)) 1 (w_word s) (w_free s) =
              expected x (ExpectFinish (w_word s) (w_ms s) (w_me s) (w_free s)) m) by reflexivity.
  pose proof HJ as (Hs & Hq & Ge). cbn [go_inv] in Ge.
  destruct Ge as (Ge & Gw & Gq & Gms & Gme & Gf).
  lst_facts Hs. inputs_facts Ix. mem_facts Mm.
  rng_at (i_decoded x) [11].
  unfold fin_call.
  unfold lfields. Intros.
  freeze_but [_call; _expect; _verdict; _word; _decoded; _manifest_status; _manifest_error; _free_words;
              _terminal_expect] [v_words] F.
  match goal with |- semax _ (PROPx ?P (LOCALx _ (SEPx ?R))) _ _ =>
    forward_for_simple_bound 64 (EX b: Z, PROPx P (LOCALx [temp _m (gv _law);
      lvar _words (tarray tulong 64) v_words; gvars gv] (SEPx R)))%assert end.
  { entailer!. }
  { forward. forward. forward_call Int.one. { entailer!. rewrite Int64.eq_true. reflexivity. } entailer!. }
  forward_call tt. Intros v.
  forward. vl_temps. forward.
  forward.
  upd_vl.
  assert (Rn: run x (start x) (h ++ [(Finish (Znth 1 (i_decoded x)) (Znth 2 (i_decoded x)) (w_ms s) (w_me s)
                                         (Znth 11 (i_decoded x)) (Znth 17 (i_decoded x)) 1 (w_word s) (w_free s), Word v)]) =
              Some (finish_done x (w_word s) (w_ms s) (w_me s) (w_free s) (with_terminal m (upd_Znth (w_word s) (m_terminal m) v)))).
  { rewrite Ec. rewrite (run_word' x h _ m v Hrun) by (intros c k E; discriminate). reflexivity. }
  unfold finish_done in Rn.
  apply semax_if_seq. forward_if.
  - (* words 0 .. 7: the next word *)
    u64c. assert (Q8: w_word s + 1 < TERMINAL_WORDS) by lia. rewrite (proj2 (Z.ltb_lt _ _) Q8) in Rn.
    forward. forward. forward.
    Exists v. thaw F.
    pose proof (J_finish_more x (w_word s) (w_ms s) (w_me s) (w_free s) m s (with_terminal m (upd_Znth (w_word s) (m_terminal m) v)) HJ Q8
                  (eq_sym Fs)) as HJ'.
    ora_close_tac (Go (ExpectFinish (w_word s + 1) (w_ms s) (w_me s) (w_free s))
                      (with_terminal m (upd_Znth (w_word s) (m_terminal m) v))) (set_word s (w_word s + 1)).
  - (* word 8: the terminal checks *)
    u64c. assert (Q8: TERMINAL_WORDS <= w_word s + 1) by lia. rewrite (proj2 (Z.ltb_ge _ _) Q8) in Rn.
    assert (Lt': Zlength (upd_Znth (w_word s) (m_terminal m) v) = 9) by (rewrite upd_Znth_Zlength; lia).
    assert (Ft': Forall u64_ok (upd_Znth (w_word s) (m_terminal m) v)) by (apply Forall_upd; auto).
    rng_list (upd_Znth (w_word s) (m_terminal m) v) 9.
    assert_PROP (field_compatible t_law (DOT _terminal_expect) (gv _law)) as FCt by entailer!.
    rewrite terminal_at by auto.
    forward.
    forward.
    forward_if (PROP ()
      LOCAL (temp _v (vl v); temp _m (gv _law); lvar _words (tarray tulong 64) v_words; gvars gv)
      SEP (FRZL F; data_at Tsh (tarray tulong 64) (map vl (w_free s)) v_words;
           data_at Ews (tarray tulong 9) (map vl (upd_Znth (w_word s) (m_terminal m) v)) (offset_val 2056 (gv _law));
           field_at Ews t_law (DOT _call) (vi (w_call s)) (gv _law);
           field_at Ews t_law (DOT _expect) (vi E_NOTHING) (gv _law);
           field_at Ews t_law (DOT _verdict) (vi (terminal_check x (with_terminal m (upd_Znth (w_word s) (m_terminal m) v)))) (gv _law);
           field_at Ews t_law (DOT _word) (vl (w_word s)) (gv _law);
           field_at Ews t_law (DOT _decoded) (map vl (i_decoded x)) (gv _law);
           field_at Ews t_law (DOT _manifest_status) (vl (w_ms s)) (gv _law);
           field_at Ews t_law (DOT _manifest_error) (vl (w_me s)) (gv _law);
           field_at Ews t_law (DOT _free_words) (map vl (w_free s)) (gv _law))).
    { u64c. forward_call (gv _law, vi (w_expect s), vi (w_verdict s), S_TERMINAL_VERSION).
      replace (terminal_check x (with_terminal m (upd_Znth (w_word s) (m_terminal m) v))) with S_TERMINAL_VERSION by chk_terminal. entailer!. }
    { u64c. forward.
      forward_if.
      { u64c. forward_call (gv _law, vi (w_expect s), vi (w_verdict s), S_TERMINAL_STATUS).
        replace (terminal_check x (with_terminal m (upd_Znth (w_word s) (m_terminal m) v))) with S_TERMINAL_STATUS by chk_terminal. entailer!. }
      u64c. forward.
      forward_if.
      { u64c. forward_call (gv _law, vi (w_expect s), vi (w_verdict s), S_TERMINAL_ERROR).
        replace (terminal_check x (with_terminal m (upd_Znth (w_word s) (m_terminal m) v))) with S_TERMINAL_ERROR by chk_terminal. entailer!. }
      u64c. forward.
      forward_if.
      { u64c. forward_call (gv _law, vi (w_expect s), vi (w_verdict s), S_TERMINAL_FRAME).
        replace (terminal_check x (with_terminal m (upd_Znth (w_word s) (m_terminal m) v))) with S_TERMINAL_FRAME by chk_terminal. entailer!. }
      u64c. forward.
      forward_if.
      { u64c. forward_call (gv _law, vi (w_expect s), vi (w_verdict s), S_TERMINAL_OWNER).
        replace (terminal_check x (with_terminal m (upd_Znth (w_word s) (m_terminal m) v))) with S_TERMINAL_OWNER by chk_terminal. entailer!. }
      u64c. forward. forward.
      forward_if.
      { u64c. forward_call (gv _law, vi (w_expect s), vi (w_verdict s), S_TERMINAL_ENTRY_COUNT).
        replace (terminal_check x (with_terminal m (upd_Znth (w_word s) (m_terminal m) v))) with S_TERMINAL_ENTRY_COUNT by chk_terminal. entailer!. }
      u64c. forward_call (gv _law, vi (w_expect s), vi (w_verdict s), S_OK).
      replace (terminal_check x (with_terminal m (upd_Znth (w_word s) (m_terminal m) v))) with S_OK by chk_terminal. entailer!. }
    forward.
    Exists v. thaw F. rewrite <- terminal_at by auto.
    assert (Sst: status_ok (terminal_check x (with_terminal m (upd_Znth (w_word s) (m_terminal m) v)))) by checks_ok.
    pose proof (J_finish_last x (terminal_check x (with_terminal m (upd_Znth (w_word s) (m_terminal m) v))) (with_terminal m (upd_Znth (w_word s) (m_terminal m) v)) s Hs Sst (eq_sym Fs)) as HJ'.
    ora_close_tac (Return (terminal_check x (with_terminal m (upd_Znth (w_word s) (m_terminal m) v))) (with_terminal m (upd_Znth (w_word s) (m_terminal m) v))) (set_stop s (terminal_check x (with_terminal m (upd_Znth (w_word s) (m_terminal m) v)))).
Qed.

