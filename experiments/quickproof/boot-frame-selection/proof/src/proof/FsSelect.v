(* The body of boot_frame_select: the scan over the candidates, candidate c at the model's
   Go (ExpectDecode c k f fm) M after the candidates before it (k the scan, f and fm the selection so far, M the
   memory before the step with the states ss so far), each candidate's decoder into row k (decode_done), its
   manifest answer and the consumer's answer (consume_done); the loop's end is next_candidate after candidate
   4095, and each break is select_done. *)
Require Import VST.floyd.proofauto.
Require Import LeanosFrameSelection.frame.code.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Require Import LeanosFrameSelection.proof.InternalSpecs.
Require Import LeanosFrameSelection.proof.FsLemmas.
Require Import LeanosFrameSelection.proof.FsFast.
#[local] Ltac simplify_remove_localdef_temp ::= fast_remove_localdef_temp.
#[local] Existing Instance FrameSpecs.CS.
Local Open Scope Z_scope.

(* ---------- the two rows ---------- *)

(* The states as row k and the other row. *)
Lemma states_split_k (sh: share) (ss: list (list Z)) (sp: val) (k: Z) :
  Zlength ss = 2 -> (k = 0 \/ k = 1) -> field_compatible t_states nil sp ->
  data_at sh t_states (states_val ss) sp =
  (data_at sh t_state (map vl (Znth k ss)) (row_ptr sp k) *
   data_at sh t_state (map vl (Znth (1 - k) ss)) (row_ptr sp (1 - k)))%logic.
Proof.
  intros L K FC. rewrite (states_split sh ss sp L FC).
  assert (P: isptr sp) by (apply field_compatible_isptr in FC; auto).
  destruct K; subst k.
  - change (1 - 0) with 1. rewrite row_ptr0 by auto. reflexivity.
  - change (1 - 1) with 0. rewrite row_ptr0 by auto. apply sepcon_comm.
Qed.

(* Row k rewritten with ws, and the other row: the states with state k ws. *)
Lemma states_join_k (sh: share) (ss: list (list Z)) (sp: val) (k: Z) (ws: list val) (wz: list Z) :
  Zlength ss = 2 -> (k = 0 \/ k = 1) -> field_compatible t_states nil sp -> ws = map vl wz ->
  (data_at sh t_state ws (row_ptr sp k) *
   data_at sh t_state (map vl (Znth (1 - k) ss)) (row_ptr sp (1 - k)))%logic |--
  data_at sh t_states (states_val (upd_Znth k ss wz)) sp.
Proof.
  intros L K FC E. subst ws.
  rewrite (states_split_k sh (upd_Znth k ss wz) sp k) by (rewrite ?Zlength_upd_Znth'; auto).
  rewrite upd_Znth_same by lia. rewrite upd_Znth_diff by lia. apply derives_refl.
Qed.

(* states[scan], as the C computes it. *)
Lemma row_binop (sp: val) (k: Z) : isptr sp -> 0 <= k <= 1 ->
  force_val (sem_binary_operation' Oadd (tptr (tarray tulong 41)) tuint sp (vi k)) = row_ptr sp k.
Proof.
  intros. unfold row_ptr, STATE_BYTES, vi. simpl.
  rewrite sem_add_pi_ptr_special; [ reflexivity | reflexivity | auto | rep_lia ].
Qed.

Lemma with_states_same (m: mem) : with_states m (m_states m) = m.
Proof. destruct m; reflexivity. Qed.

(* ---------- the consumer's answer ---------- *)

Lemma consume_skip (x: inputs) (c k f fm cm v: Z) (m: mem) :
  FRAMES <= v -> consume_done x c k f fm cm v m = next_candidate c k f fm m.
Proof. intros. unfold consume_done. rewrite (proj2 (Z.leb_le _ _) H). reflexivity. Qed.

Lemma consume_first_stop (x: inputs) (c f fm cm v: Z) (m: mem) :
  v < FRAMES -> i_take_next x = 0 -> consume_done x c 0 f fm cm v m = select_done v cm FRAMES m.
Proof. intros. unfold consume_done. rewrite (proj2 (Z.leb_gt _ _) H), H0. reflexivity. Qed.

Lemma consume_first_go (x: inputs) (c f fm cm v: Z) (m: mem) :
  v < FRAMES -> i_take_next x <> 0 -> consume_done x c 0 f fm cm v m = next_candidate c 1 v cm m.
Proof.
  intros. unfold consume_done. rewrite (proj2 (Z.leb_gt _ _) H), (proj2 (Z.eqb_neq _ _) H0). reflexivity.
Qed.

Lemma consume_second (x: inputs) (c f fm cm v: Z) (m: mem) :
  v < FRAMES -> consume_done x c 1 f fm cm v m = select_done f fm v m.
Proof. intros. unfold consume_done. rewrite (proj2 (Z.leb_gt _ _) H). reflexivity. Qed.

Lemma vi_k_eq0 (k: Z) : (k = 0 \/ k = 1) -> Int.repr k = Int.repr 0 -> k = 0.
Proof. intros [-> | ->] E; [ reflexivity | discriminate ]. Qed.

Lemma vi_k_ne0 (k: Z) : (k = 0 \/ k = 1) -> Int.repr k <> Int.repr 0 -> k = 1.
Proof. intros [-> | ->] E; [ contradiction | reflexivity ]. Qed.

Lemma Znth_upd_k (ss: list (list Z)) (k: Z) (ws: list Z) :
  Zlength ss = 2 -> (k = 0 \/ k = 1) -> Znth k (upd_Znth k ss ws) = ws.
Proof. intros. apply upd_Znth_same. lia. Qed.

Lemma body_boot_frame_select (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_boot_frame_select (boot_select_spec Ora).
Proof.
  start_function.
  rename H into HC, H0 into IX.
  destruct (inputs_facts x IX) as (UT & _ & _ & _ & _ & LM & UM & _ & _ & _ & _ & _ & _ & MO).
  pose proof MO as (_ & _ & _ & _ & LS & _).
  assert_PROP (field_compatible t_states nil sp) as FC by entailer!.
  assert (PS: isptr sp) by (apply field_compatible_isptr in FC; auto).
  forward. forward. forward. forward.
  forward_loop (EX c: Z, EX k: Z, EX f: Z, EX fm: Z, EX hs: list answer, EX ss: list (list Z),
    PROP (0 <= c <= FRAMES; k = 0 \/ k = 1; Zlength ss = 2;
          run x (start x) hs = Some (if c <? FRAMES then Go (ExpectDecode c k f fm) (with_states (i_mem x) ss)
                                     else select_done f fm FRAMES (with_states (i_mem x) ss)))
    LOCAL (temp _candidate (vl c); temp _scan (vi k); temp _first (vl f); temp _first_manifest (vl fm);
           temp _second (vl FRAMES); temp _decode decode; temp _context dctx; temp _manifest mp;
           temp _take_next (vi (i_take_next x)); temp _states sp; temp _selected selp;
           temp _selected_manifest smp; temp _next np; temp _decoder_status dsp; gvars gv)
    SEP (func_ptr' (decode_spec Ora) decode; Ora gv dctx sctx sp x hs;
         data_at rsh t_manifest (map vl (i_manifest x)) mp;
         data_at wsh t_states (states_val ss) sp;
         data_at wsh tulong (vl (m_selected (i_mem x))) selp;
         data_at wsh tulong (vl (m_selected_manifest (i_mem x))) smp;
         data_at wsh tulong (vl (m_next (i_mem x))) np;
         data_at wsh tuint (vi (m_decoder (i_mem x))) dsp))%assert
    continue: (EX c: Z, EX k: Z, EX f: Z, EX fm: Z, EX hs: list answer, EX ss: list (list Z),
    PROP (0 <= c < FRAMES; k = 0 \/ k = 1; Zlength ss = 2;
          run x (start x) hs = Some (next_candidate c k f fm (with_states (i_mem x) ss)))
    LOCAL (temp _candidate (vl c); temp _scan (vi k); temp _first (vl f); temp _first_manifest (vl fm);
           temp _second (vl FRAMES); temp _decode decode; temp _context dctx; temp _manifest mp;
           temp _take_next (vi (i_take_next x)); temp _states sp; temp _selected selp;
           temp _selected_manifest smp; temp _next np; temp _decoder_status dsp; gvars gv)
    SEP (func_ptr' (decode_spec Ora) decode; Ora gv dctx sctx sp x hs;
         data_at rsh t_manifest (map vl (i_manifest x)) mp;
         data_at wsh t_states (states_val ss) sp;
         data_at wsh tulong (vl (m_selected (i_mem x))) selp;
         data_at wsh tulong (vl (m_selected_manifest (i_mem x))) smp;
         data_at wsh tulong (vl (m_next (i_mem x))) np;
         data_at wsh tuint (vi (m_decoder (i_mem x))) dsp))%assert
    break: (EX f: Z, EX fm: Z, EX n: Z, EX hs: list answer, EX ss: list (list Z),
    PROP (Zlength ss = 2; run x (start x) hs = Some (select_done f fm n (with_states (i_mem x) ss)))
    LOCAL (temp _first (vl f); temp _first_manifest (vl fm); temp _second (vl n);
           temp _selected selp; temp _selected_manifest smp; temp _next np; gvars gv)
    SEP (func_ptr' (decode_spec Ora) decode; Ora gv dctx sctx sp x hs;
         data_at rsh t_manifest (map vl (i_manifest x)) mp;
         data_at wsh t_states (states_val ss) sp;
         data_at wsh tulong (vl (m_selected (i_mem x))) selp;
         data_at wsh tulong (vl (m_selected_manifest (i_mem x))) smp;
         data_at wsh tulong (vl (m_next (i_mem x))) np;
         data_at wsh tuint (vi (m_decoder (i_mem x))) dsp))%assert.
  { (* the first candidate *)
    forward. Exists 0 0 FRAMES 0 (@nil answer) (m_states (i_mem x)). entailer!.
    rewrite with_states_same. cbn [run]. unfold start. rewrite HC. reflexivity. }
  { (* candidate c *)
    Intros c k f fm hs ss.
    rename H into Lc, H0 into K, H1 into Lss, H2 into R.
    forward_if.
    2: { (* after candidate 4095 *)
      w64. forward. rewrite (proj2 (Z.ltb_ge _ _)) in R by lia.
      Exists f fm FRAMES hs ss. entailer!. }
    w64. rewrite (proj2 (Z.ltb_lt _ _)) in R by lia.
    set (M := with_states (i_mem x) ss) in *.
    forward.
    rewrite row_binop by (auto; lia).
    rewrite (states_split_k wsh ss sp k Lss K FC). Intros.
    forward_call (gv, dctx, sctx, sp, x, hs, c, k, wsh).
    { apply (next_call_go _ _ _ _ R). }
    Intros vret. destruct vret as [st ws]. cbn [fst snd] in *.
    rename H0 into Ust, H1 into Lws, H2 into Uws.
    pose proof (run_decoded x (start x) hs _ M c k st ws R eq_refl) as R1.
    cbn [step reply_value reply_state] in R1. unfold decode_done in R1.
    assert (Lss1: Zlength (upd_Znth k ss ws) = 2) by (rewrite Zlength_upd_Znth'; auto).
    forward_if.
    { (* the decoder rejected the candidate *)
      w64. forward. forward.
      sep_apply (states_join_k wsh ss sp k (map vl ws) ws Lss K FC eq_refl).
      rewrite (proj2 (Z.eqb_neq _ _) H0) in R1.
      Exists (hs ++ [(Decode c k, Decoded st ws)]) S_DECODER (with_decoder (with_state M k ws) st).
      unfold M. cbn [m_states m_selected m_selected_manifest m_next m_decoder with_decoder with_state with_states].
      entailer!. apply returns_return; exact R1. }
    w64. subst st. rewrite Z.eqb_refl in R1.
    do 18 forward.
    forward_call (gv, dctx, sctx, sp, x, hs ++ [(Decode c k, Decoded 0 ws)], c, i_manifest x).
    { apply (next_call_go _ _ _ _ R1). }
    Intros cm. rename H0 into Ucm.
    pose proof (run_word x (start x) _ _ _ cm R1 ltac:(intros; discriminate)) as R2.
    cbn [step reply_value expected] in R2.
    forward.
    do 3 forward.
    assert (E1: Znth k (m_states (with_state M k ws)) = ws) by (apply Znth_with_state; [ exact Lss | lia ]).
    assert (NC2: next_call x ((hs ++ [(Decode c k, Decoded 0 ws)]) ++ [(Candidate c (i_manifest x), Word cm)]) =
                 Some (Consume FRAMES c (Znth 1 ws) (Znth 14 ws) (Znth 15 ws) cm))
      by (rewrite (next_call_go _ _ _ _ R2); cbn [expected]; rewrite E1; reflexivity).
    forward_call (gv, dctx, sctx, sp, x, (hs ++ [(Decode c k, Decoded 0 ws)]) ++ [(Candidate c (i_manifest x), Word cm)],
                  FRAMES, c, Znth 1 ws, Znth 14 ws, Znth 15 ws, cm).
    Intros v. rename H0 into Uv.
    pose proof (run_word x (start x) _ _ _ v R2 ltac:(intros; discriminate)) as R3.
    cbn [step reply_value expected] in R3. rewrite E1 in R3.
    forward.
    sep_apply (states_join_k wsh ss sp k (map vl ws) ws Lss K FC eq_refl).
    forward_if.
    { (* not accepted: the next candidate *)
      w64. forward.
      match type of R3 with run _ _ ?L = _ => Exists c k f fm L (upd_Znth k ss ws) end.
      entailer!.
      rewrite R3, consume_skip by lia. reflexivity. }
    w64.
    forward_if.
    { (* scan 0: the selected frame *)
      w64. subst k.
      forward. forward.
      forward_if.
      { (* take_next 0: the scan stops *)
        w64. forward.
        match type of R3 with run _ _ ?L = _ => Exists v cm FRAMES L (upd_Znth 0 ss ws) end.
        entailer!. rewrite R3, consume_first_stop by auto. reflexivity. }
      w64. forward.
      match type of R3 with run _ _ ?L = _ => Exists c 1 v cm L (upd_Znth 0 ss ws) end.
      entailer!. rewrite R3, consume_first_go by auto. reflexivity. }
    (* scan 1: the next frame *)
    w64. assert (k = 1) by lia. subst k.
    forward. forward.
    match type of R3 with run _ _ ?L = _ => Exists f fm v L (upd_Znth 1 ss ws) end.
    entailer!. rewrite R3, consume_second by lia. reflexivity. }
  { (* the next candidate *)
    Intros c k f fm hs ss.
    forward. Exists (c + 1) k f fm hs ss. entailer!.
    all: first [ match goal with H: run _ _ _ = _ |- _ => rewrite H end; reflexivity
               | unfold vl; rewrite add64_repr; reflexivity ]. }
  (* the records *)
  Intros f fm n hs ss.
  rename H into Lss, H0 into R.
  forward. forward. forward. forward.
  Exists hs S_OK (with_records (with_states (i_mem x) ss) f fm n).
  cbn [m_states m_selected m_selected_manifest m_next m_decoder with_records with_states].
  entailer!.
  apply returns_return; exact R.
Qed.
