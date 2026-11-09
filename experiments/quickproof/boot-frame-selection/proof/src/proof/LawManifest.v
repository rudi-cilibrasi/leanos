(* Law frame_selection_exact: the bodies of the harness's exports leanos_boot_projection_manifest and
   leanos_boot_projection_free against manifest_spec and free_spec Ora_law: their checks follow from the call the
   model expects (block b's overlay word |a| + 1 with the manifest, block b's free word with the usable, blocked and
   reserved words), and each answer moves the law's record as the model's step: the next overlay word or the
   overlay's end (status, error, the reserved word), the next block or the terminal result's word 0. *)
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

Definition manifest_fspec : ident * funspec := manifest_spec Ora_law.

Definition Gmanifest : funspecs := [gp_assert_spec; any_u64_spec; same_manifest_spec].

(* ---------------------------------------------------------------------- *)
(* The record's moves                                                      *)
(* ---------------------------------------------------------------------- *)

(* The overlay's answer v to word w_word s, not the last. *)
Definition s_more (s: lst) (v: Z) : lst :=
  set_word (set_answer s (upd_Znth (w_word s) (w_answer s) v)) (w_word s + 1).

(* The last overlay answer v, after the status st and error er of the block. *)
Definition s_overlay (s: lst) (v st er: Z) : lst :=
  let bad := negb (st =? 1) || negb (er =? 0) in
  set_expect (set_me (set_ms (set_answer s (upd_Znth (w_word s) (w_answer s) v)) (if bad then st else w_ms s))
                     (if bad then er else w_me s)) E_FREE.

Lemma lst_ok_answer: forall s i v, lst_ok s -> 0 <= i < 4 -> u64_ok v -> lst_ok (set_answer s (upd_Znth i (w_answer s) v)).
Proof.
  intros s i v L I V. unfold lst_ok in *; set_unfold; lst_cbn.
  destruct L as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 &
                 A19 & A20).
  split_and; auto. rewrite upd_Znth_Zlength; lia. apply Forall_upd; auto.
Qed.

Lemma J_manifest_more: forall x b ms me fw a m s v,
  J x (Go (ExpectManifest b ms me fw a) m) s -> Zlength a < 2 -> u64_ok v -> i_step x = FTerminal ->
  J x (Go (ExpectManifest b ms me fw (a ++ [v])) m) (s_more s v).
Proof.
  intros x b ms me fw a m s v (L & Q & G) A V F. cbn [go_inv] in G.
  destruct G as (Ge & Gb & Gb' & Gw & Ga & Gs & Gms & Gme & Gfl & Gf).
  lst_facts L. unfold J, s_more. split_and.
  - unfold set_word. apply (lst_ok_mk (set_answer s (upd_Znth (w_word s) (w_answer s) v))); set_unfold; lst_cbn;
      try (apply lst_ok_answer; auto; lia); unfold u32_ok, u64_ok; rep_lia.
  - unfold seq_ok. split; intros G; congruence.
  - cbn [go_inv]. set_unfold; lst_cbn. rewrite Zlength_app, Zlength_cons, Zlength_nil.
    split_and; auto; try lia.
    rewrite Gw. rewrite <- Gs. list_solve.
Qed.

Lemma J_manifest_done: forall x b ms me fw a m s v,
  J x (Go (ExpectManifest b ms me fw a) m) s -> Zlength a = 2 -> u64_ok v -> i_step x = FTerminal ->
  Forall u64_ok a ->
  J x (overlay_done b ms me fw (Znth 0 a) (Znth 1 a) v m) (s_overlay s v (Znth 0 a) (Znth 1 a)).
Proof.
  intros x b ms me fw a m s v (L & Q & G) A V F Fa. cbn [go_inv] in G.
  destruct G as (Ge & Gb & Gb' & Gw & Ga & Gs & Gms & Gme & Gfl & Gf).
  assert (R0: u64_ok (Znth 0 a)) by (apply Forall_u64_Znth; auto; lia).
  assert (R1: u64_ok (Znth 1 a)) by (apply Forall_u64_Znth; auto; lia).
  lst_facts L. unfold J, overlay_done, s_overlay. split_and.
  - unfold set_expect, set_me, set_ms.
    apply (lst_ok_mk (set_answer s (upd_Znth (w_word s) (w_answer s) v))); set_unfold; lst_cbn;
      try (apply lst_ok_answer; auto; lia);
      destruct (negb (Znth 0 a =? 1) || negb (Znth 1 a =? 0))%bool; unfold u32_ok, u64_ok, E_FREE in *; rep_lia.
  - unfold seq_ok. split; intros G; congruence.
  - cbn [go_inv]. set_unfold; lst_cbn. subst ms me. split_and; auto; lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* The bodies                                                              *)
(* ---------------------------------------------------------------------- *)

Lemma body_manifest: semax_body Vlaw Gmanifest f_leanos_boot_projection_manifest manifest_fspec.
Proof.
  start_function.
  match goal with H: next_call _ _ = _ |- _ => rename H into Nc end.
  ora_open p s.
  destruct (next_go x h p _ Hrun Nc) as (g & m & -> & Ec). cbn [mem_of].
  pose proof (progress_of_run x h _ Ix Ah Hrun) as (Fs & _ & Mm & Km).
  destruct (call_manifest x g m b ms q (eq_sym Ec)) as (ms' & me & fw & a & -> & Ems & Eq).
  cbn [stage_step] in Fs.
  pose proof HJ as (Hs & Hq & Ge). cbn [go_inv] in Ge.
  destruct Ge as (Ge & Gb & Gb' & Gw & Ga & Gs & Gms & Gme & Gfl & Gf).
  lst_facts Hs. inputs_facts Ix. mem_facts Mm.
  subst ms q b ms' me fw.
  unfold lfields. Intros.
  freeze_but [_call; _expect; _block; _word; _manifest; _answer; _manifest_status; _manifest_error; _reserved_expect]
    [v_words] F.
  forward.
  if1. if1.
  forward_call Int.one.
  do 18 forward.
  assert (Lm: Zlength (i_manifest x) = Z.of_nat 18) by (rewrite Iml; reflexivity).
  words_fill (i_manifest x) 18%nat.
  forward_call (gv, v_words, i_manifest x, Tsh).
  forward_call Int.one.
  forward_call tt. Intros v.
  assert (Ra: Forall u64_ok a) by (rewrite <- Gs; apply Forall_sublist; auto).
  forward. vl_temps. forward.
  forward.
  rewrite Gw.
  assert (Rn: run x (start x) (h ++ [(Manifest (w_block s) (i_manifest x) (Zlength a + 1), Word v)]) =
              Some (step x (ExpectManifest (w_block s) (w_ms s) (w_me s) (sublist 0 (w_block s) (w_free s)) a) m (Word v))).
  { rewrite Ec. apply (run_word' x h _ m v Hrun). intros c k E; discriminate. }
  unfold step in Rn. cbn [reply_value] in Rn.
  apply semax_if_seq. forward_if.
  - (* words 1 and 2: the next word *)
    u64c. assert (A2: Zlength a < 2) by lia. rewrite (proj2 (Z.ltb_lt _ _) A2) in Rn.
    forward. forward. forward.
    Exists v. thaw F.
    pose proof (J_manifest_more x (w_block s) (w_ms s) (w_me s) (sublist 0 (w_block s) (w_free s)) a m s v HJ A2 ltac:(assumption) (eq_sym Fs)) as HJ'.
    unfold s_more in HJ'. rewrite Gw in HJ'.
    ora_close_tac (Go (ExpectManifest (w_block s) (w_ms s) (w_me s) (sublist 0 (w_block s) (w_free s)) (a ++ [v])) m)
      (set_word (set_answer s (upd_Znth (Zlength a + 1) (w_answer s) v)) (Zlength a + 1 + 1)).
  - (* word 3: the overlay's end *)
    u64c. assert (A2: Zlength a = 2) by lia. rewrite (proj2 (Z.ltb_ge (Zlength a) 2) ltac:(lia)) in Rn.
    assert (W3: w_word s = 3) by lia.
    assert (A0: Znth 1 (upd_Znth (Zlength a + 1) (w_answer s) v) = Znth 0 a)
      by (rewrite upd_Znth_diff by lia; rewrite <- Gs; rewrite Znth_sublist by lia; reflexivity).
    assert (A1: Znth 2 (upd_Znth (Zlength a + 1) (w_answer s) v) = Znth 1 a)
      by (rewrite upd_Znth_diff by lia; rewrite <- Gs; rewrite Znth_sublist by lia; reflexivity).
    assert (A3: Znth 3 (upd_Znth (Zlength a + 1) (w_answer s) v) = v)
      by (replace (Zlength a + 1) with 3 by lia; rewrite upd_Znth_same by lia; reflexivity).
    assert (Lan: Zlength (upd_Znth (Zlength a + 1) (w_answer s) v) = 4) by (rewrite upd_Znth_Zlength; lia).
    assert (A0': Znth 1 (map vl (upd_Znth (Zlength a + 1) (w_answer s) v)) = vl (Znth 0 a))
      by (rewrite Znth_map by lia; rewrite A0; reflexivity).
    assert (A1': Znth 2 (map vl (upd_Znth (Zlength a + 1) (w_answer s) v)) = vl (Znth 1 a))
      by (rewrite Znth_map by lia; rewrite A1; reflexivity).
    assert (A3': Znth 3 (map vl (upd_Znth (Zlength a + 1) (w_answer s) v)) = vl v)
      by (rewrite Znth_map by lia; rewrite A3; reflexivity).
    assert (Ra0: u64_ok (Znth 0 a)) by (apply Forall_u64_Znth; auto; lia).
    assert (Ra1: u64_ok (Znth 1 a)) by (apply Forall_u64_Znth; auto; lia).
    unfold u64_ok in Ra0, Ra1. clear Gs.
    upd_vl.
    forward. rewrite ?A0, ?A0'.
    forward_if (temp _t'5 (Vint (Int.repr (Z.b2z (negb (Znth 0 a =? 1) || negb (Znth 1 a =? 0))%bool)))).
    { destruct (Z.eqb_spec (Znth 0 a) 1) as [E0 | E0]; [ rewrite E0 in *; else_false | ]. forward. entailer!. }
    { destruct (Z.eqb_spec (Znth 0 a) 1) as [E0 | E0]; [ | else_false ].
      forward. rewrite ?A1, ?A1'. forward. entailer!.
      cbn [negb orb]. destruct (Z.eqb_spec (Znth 1 a) 0); cmp_close. }
    forward_if (PROP ()
      LOCAL (temp _v (vl v); temp _m (gv _law); lvar _words (tarray tulong 18) v_words; gvars gv)
      SEP (FRZL F; data_at Tsh (tarray tulong 18) (map vl (i_manifest x)) v_words;
           field_at Ews t_law (DOT _call) (vi (w_call s)) (gv _law);
           field_at Ews t_law (DOT _manifest) (map vl (i_manifest x)) (gv _law);
           field_at Ews t_law (DOT _reserved_expect) (map vl (m_reserved m)) (gv _law);
           field_at Ews t_law (DOT _expect) (vi (w_expect s)) (gv _law);
           field_at Ews t_law (DOT _block) (vl (w_block s)) (gv _law);
           field_at Ews t_law (DOT _word) (vl (Zlength a + 1)) (gv _law);
           field_at Ews t_law (DOT _manifest_status) (vl (if (negb (Znth 0 a =? 1) || negb (Znth 1 a =? 0))%bool then Znth 0 a else w_ms s)) (gv _law);
           field_at Ews t_law (DOT _manifest_error) (vl (if (negb (Znth 0 a =? 1) || negb (Znth 1 a =? 0))%bool then Znth 1 a else w_me s)) (gv _law);
           field_at Ews t_law (DOT _answer) (map vl (upd_Znth (Zlength a + 1) (w_answer s) v)) (gv _law))).
    { forward. rewrite ?A0, ?A0'. forward. forward. rewrite ?A1, ?A1'. forward.
      destruct (negb (Znth 0 a =? 1) || negb (Znth 1 a =? 0))%bool eqn:Bt; cbn [Z.b2z] in *; [ entailer! | else_false ]. }
    { forward. destruct (negb (Znth 0 a =? 1) || negb (Znth 1 a =? 0))%bool eqn:Bt; cbn [Z.b2z] in *; [ else_false | entailer! ]. }
    forward. forward. rewrite ?A3, ?A3'. vl_temps. forward. forward. forward.
    Exists v. thaw F.
    rewrite <- Gw in *.
    pose proof (J_manifest_done x (w_block s) (w_ms s) (w_me s) (sublist 0 (w_block s) (w_free s)) a m s v HJ A2 ltac:(assumption) (eq_sym Fs) Ra) as HJ'.
    unfold overlay_done in Rn, HJ'. unfold s_overlay in HJ'.
    ora_close_tac (Go (ExpectFree (w_block s) (if (negb (Znth 0 a =? 1) || negb (Znth 1 a =? 0))%bool then Znth 0 a else w_ms s) (if (negb (Znth 0 a =? 1) || negb (Znth 1 a =? 0))%bool then Znth 1 a else w_me s) (sublist 0 (w_block s) (w_free s)))
                      (with_reserved m (upd_Znth (w_block s) (m_reserved m) v)))
      (set_expect (set_me (set_ms (set_answer s (upd_Znth (w_word s) (w_answer s) v)) (if (negb (Znth 0 a =? 1) || negb (Znth 1 a =? 0))%bool then Znth 0 a else w_ms s))
                          (if (negb (Znth 0 a =? 1) || negb (Znth 1 a =? 0))%bool then Znth 1 a else w_me s)) E_FREE).
Qed.

