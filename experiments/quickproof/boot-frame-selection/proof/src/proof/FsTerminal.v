(* The body of boot_frame_terminal: the manifest overlay, block b at the model's Go (ExpectManifest b ms me fw nil)
   M after the blocks before it (its three manifest answers, overlay_done, and its free word, free_done: M is the
   memory before the step with the reserved bitmap r so far); the terminal result's words, word q at
   Go (ExpectFinish q ms me fw) M' (finish_done, M' with the terminal result t so far); then the checks of
   terminal_check. *)
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

(* ---------- the overlay's three answers for block b ---------- *)

Lemma manifest_next0 (x: inputs) (p: progress) (h: list answer) (b ms me: Z) (fw: list Z) (m: mem) (v: Z) :
  run x p h = Some (Go (ExpectManifest b ms me fw nil) m) ->
  run x p (h ++ [(Manifest b (i_manifest x) 1, Word v)]) = Some (Go (ExpectManifest b ms me fw [v]) m).
Proof. intros R. exact (run_word x p h _ m v R ltac:(intros; discriminate)). Qed.

Lemma manifest_next1 (x: inputs) (p: progress) (h: list answer) (b ms me: Z) (fw: list Z) (m: mem) (v1 v: Z) :
  run x p h = Some (Go (ExpectManifest b ms me fw [v1]) m) ->
  run x p (h ++ [(Manifest b (i_manifest x) 2, Word v)]) = Some (Go (ExpectManifest b ms me fw [v1; v]) m).
Proof. intros R. exact (run_word x p h _ m v R ltac:(intros; discriminate)). Qed.

Lemma manifest_next2 (x: inputs) (p: progress) (h: list answer) (b ms me: Z) (fw: list Z) (m: mem) (v1 v2 v: Z) :
  run x p h = Some (Go (ExpectManifest b ms me fw [v1; v2]) m) ->
  run x p (h ++ [(Manifest b (i_manifest x) 3, Word v)]) = Some (overlay_done b ms me fw v1 v2 v m).
Proof. intros R. exact (run_word x p h _ m v R ltac:(intros; discriminate)). Qed.

(* The free words as they fill. *)
Lemma upd_fill (a: list Z) (v: Z) (n: Z) :
  Zlength a < n ->
  upd_Znth (Zlength a) (map vl a ++ Zrepeat Vundef (n - Zlength a)) (vl v) =
  map vl (a ++ [v]) ++ Zrepeat Vundef (n - (Zlength a + 1)).
Proof.
  intros. rewrite map_app.
  rewrite upd_Znth_app2 by (rewrite Zlength_map, Zlength_Zrepeat; lia).
  rewrite Zlength_map, Z.sub_diag.
  replace (n - Zlength a) with (1 + (n - (Zlength a + 1))) by lia.
  rewrite <- Zrepeat_app by lia. rewrite upd_Znth_app1 by (rewrite Zlength_Zrepeat; lia).
  rewrite <- app_assoc. f_equal.
Qed.

(* The free words as they fill, block b's at index b. *)
Lemma upd_fill_at (a: list Z) (b: Z) (v: Z) (n: Z) :
  Zlength a = b -> b < n ->
  upd_Znth b (map vl a ++ Zrepeat Vundef (n - b)) (vl v) = map vl (a ++ [v]) ++ Zrepeat Vundef (n - (b + 1)).
Proof. intros <- L. apply upd_fill. exact L. Qed.

(* error != 0, cast to _Bool, as the C computes it. *)
Lemma t4_else (er: Z) : u64_ok er ->
  bool2val (Int64.cmpu Cne (Int64.repr er) (Int64.repr (Int.signed (Int.repr 0)))) =
  vi (if negb (er =? 0) then 1 else 0).
Proof.
  intros U. change (Int.signed (Int.repr 0)) with 0. cbn [Int64.cmpu].
  rewrite eq64_repr by (auto; unfold u64_ok; rep_lia). destruct (er =? 0); reflexivity.
Qed.

Lemma upd_map_vl (i: Z) (l: list Z) (v: Z) :
  upd_Znth i (map vl l) (Vlong (Int64.repr v)) = map vl (upd_Znth i l v).
Proof. apply (upd_Znth_map vl). Qed.

Lemma with_reserved_same (m: mem) : with_reserved m (m_reserved m) = m.
Proof. destruct m; reflexivity. Qed.

Lemma terminal_init (m: mem) (r: list Z) : with_terminal (with_reserved m r) (m_terminal m) = with_reserved m r.
Proof. destruct m; reflexivity. Qed.

(* A return of the checks, with the status of terminal_check. *)
Ltac tret x R :=
  lazymatch type of R with run _ _ ?L = Some (Return _ ?M) =>
    forward; Exists L (terminal_check x M) M; entailer!; post_split;
    first [ apply returns_return; exact R
          | unfold terminal_check; cbn [m_terminal with_terminal with_reserved]; zb; reflexivity ]
  end.

Lemma body_boot_frame_terminal (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_boot_frame_terminal (boot_terminal_spec Ora).
Proof.
  start_function.
  rename H into HC, H0 into IX.
  destruct (inputs_facts x IX) as (_ & _ & _ & _ & _ & LM & UM & LD & UD & LU & UU & LB & UB & MO).
  pose proof MO as (LR & UR & LT & UTm & _).
  forward. forward.
  forward_for_simple_bound 64 (EX b: Z, EX hs: list answer, EX ms: Z, EX me: Z, EX fw: list Z, EX r: list Z,
    PROP (Zlength fw = b; Zlength r = BLOCKS; Forall u64_ok r;
          run x (start x) hs = Some (if b <? BLOCKS then Go (ExpectManifest b ms me fw nil) (with_reserved (i_mem x) r)
                                     else Go (ExpectFinish 0 ms me fw) (with_reserved (i_mem x) r)))
    LOCAL (temp _manifest_status (vl ms); temp _manifest_error (vl me); temp _manifest mp; temp _decoded dp;
           temp _usable up; temp _blocked bp; temp _reserved rp; temp _terminal tp;
           lvar _free_words t_bitmap v_free_words; gvars gv)
    SEP (Ora gv dctx sctx sp x hs; data_at Tsh t_bitmap (map vl fw ++ Zrepeat Vundef (BLOCKS - b)) v_free_words;
         data_at rsh t_manifest (map vl (i_manifest x)) mp;
         data_at rsh t_state (map vl (i_decoded x)) dp;
         data_at rsh t_bitmap (map vl (i_usable x)) up;
         data_at rsh t_bitmap (map vl (i_blocked x)) bp;
         data_at wsh t_bitmap (map vl r) rp;
         data_at wsh t_terminal (map vl (m_terminal (i_mem x))) tp))%assert.
  { (* before block 0 *)
    Exists (@nil answer) 1 0 (@nil Z) (m_reserved (i_mem x)). entailer!.
    all: try (rewrite with_reserved_same; cbn [run]; unfold start; rewrite HC; reflexivity). }
  { (* block i *)
    Intros. rename H into Bi.
    match goal with H: run _ _ hs = _ |- _ => rename H into R end.
    match goal with H: Zlength fw = i |- _ => rename H into Lfw end.
    match goal with H: Zlength r = 64 |- _ => rename H into Lr end.
    match goal with H: Forall u64_ok r |- _ => rename H into Ur end.
    rewrite (proj2 (Z.ltb_lt i 64)) in R by lia.
    do 18 forward.
    forward_call (gv, dctx, sctx, sp, x, hs, i, i_manifest x, 1).
    { apply (next_call_go _ _ _ _ R). }
    Intros st. rename H into Ust.
    forward. deadvars!.
    pose proof (manifest_next0 _ _ _ _ _ _ _ _ st R) as R1.
    do 18 forward.
    forward_call (gv, dctx, sctx, sp, x, hs ++ [(Manifest i (i_manifest x) 1, Word st)], i, i_manifest x, 2).
    { apply (next_call_go _ _ _ _ R1). }
    Intros er. rename H into Uer.
    forward. deadvars!.
    pose proof (manifest_next1 _ _ _ _ _ _ _ _ _ er R1) as R2.
    do 18 forward.
    forward_call (gv, dctx, sctx, sp, x, (hs ++ [(Manifest i (i_manifest x) 1, Word st)])
                                             ++ [(Manifest i (i_manifest x) 2, Word er)], i, i_manifest x, 3).
    { apply (next_call_go _ _ _ _ R2). }
    Intros mask. rename H into Umask.
    forward. deadvars!.
    pose proof (manifest_next2 _ _ _ _ _ _ _ _ _ _ mask R2) as R3. unfold overlay_done in R3.
    remember (negb (st =? 1) || negb (er =? 0))%bool as bad eqn:BAD.
    forward_if (temp _t'4 (vi (if bad then 1 else 0))).
    { forward. w64. subst bad. rewrite (proj2 (Z.eqb_neq st 1)) by lia. cbn [negb orb]. entailer!. }
    { forward. w64. subst bad. rewrite (proj2 (Z.eqb_eq st 1)) by lia. cbn [negb orb].
      rewrite t4_else by auto. entailer!. }
    forward_if [temp _manifest_status (vl (if bad then st else ms));
                temp _manifest_error (vl (if bad then er else me))].
    { destruct bad.
      2: { exfalso. match goal with H: 0 <> 0 |- _ => apply H; reflexivity end. }
      forward. forward. entailer!. }
    { destruct bad.
      1: { exfalso. match goal with H: Int.repr 1 = Int.zero |- _ => exact (Int.one_not_zero H) end. }
      forward. entailer!. }
    forward.
    forward. forward.
    assert (NC: next_call x (((hs ++ [(Manifest i (i_manifest x) 1, Word st)]) ++ [(Manifest i (i_manifest x) 2, Word er)])
                               ++ [(Manifest i (i_manifest x) 3, Word mask)]) =
                Some (Free (Znth i (i_usable x)) (Znth i (i_blocked x)) mask)).
    { rewrite (next_call_go _ _ _ _ R3). cbn [expected m_reserved with_reserved].
      rewrite upd_Znth_same by lia. reflexivity. }
    forward_call (gv, dctx, sctx, sp, x, ((hs ++ [(Manifest i (i_manifest x) 1, Word st)])
                                              ++ [(Manifest i (i_manifest x) 2, Word er)])
                                              ++ [(Manifest i (i_manifest x) 3, Word mask)],
                       Znth i (i_usable x), Znth i (i_blocked x), mask).
    Intros fv. rename H into Ufv.
    pose proof (run_word x (start x) _ _ _ fv R3 ltac:(intros; discriminate)) as R4.
    cbn [step reply_value expected m_reserved with_reserved] in R4.
    rewrite upd_Znth_same in R4 by lia.
    forward.
    rewrite upd_fill_at by (auto; lia).
    rewrite upd_map_vl.
    match type of R4 with run _ _ ?L = _ =>
      Exists L (if bad then st else ms) (if bad then er else me) (fw ++ [fv]) (upd_Znth i r mask) end.
    entailer!.
    post_split; [ rewrite Zlength_app, Zlength_cons, Zlength_nil; lia | rewrite Zlength_upd_Znth'; auto
                | apply Forall_upd_Znth; auto ]. }
  (* the terminal result *)
  Intros hs ms me fw r.
  rename H into Lfw, H0 into Lr, H1 into Ur, H2 into R.
  rewrite Z.ltb_irrefl in R.
  change (Zrepeat Vundef (64 - 64)) with (@nil val). rewrite app_nil_r.
  forward_for_simple_bound 9 (EX q: Z, EX hs1: list answer, EX t: list Z,
    PROP (Zlength t = TERMINAL_WORDS; Forall u64_ok t;
          run x (start x) hs1 =
            Some (if q <? TERMINAL_WORDS
                  then Go (ExpectFinish q ms me fw) (with_terminal (with_reserved (i_mem x) r) t)
                  else Return (terminal_check x (with_terminal (with_reserved (i_mem x) r) t))
                              (with_terminal (with_reserved (i_mem x) r) t)))
    LOCAL (temp _manifest_status (vl ms); temp _manifest_error (vl me); temp _manifest mp; temp _decoded dp;
           temp _usable up; temp _blocked bp; temp _reserved rp; temp _terminal tp;
           lvar _free_words t_bitmap v_free_words; gvars gv)
    SEP (Ora gv dctx sctx sp x hs1; data_at Tsh t_bitmap (map vl fw) v_free_words;
         data_at rsh t_manifest (map vl (i_manifest x)) mp;
         data_at rsh t_state (map vl (i_decoded x)) dp;
         data_at rsh t_bitmap (map vl (i_usable x)) up;
         data_at rsh t_bitmap (map vl (i_blocked x)) bp;
         data_at wsh t_bitmap (map vl r) rp;
         data_at wsh t_terminal (map vl t) tp))%assert.
  { (* before word 0 *)
    Exists hs (m_terminal (i_mem x)). entailer!.
    all: rewrite terminal_init; exact R. }
  { (* word i *)
    Intros. rename H into Qi.
    match goal with H: run _ _ hs1 = _ |- _ => rename H into R1 end.
    match goal with H: Zlength t = 9 |- _ => rename H into Lt end.
    match goal with H: Forall u64_ok t |- _ => rename H into Ut end.
    rewrite (proj2 (Z.ltb_lt i 9)) in R1 by lia.
    do 4 forward.
    do 64 forward.
    forward_call (gv, dctx, sctx, sp, x, hs1, Znth 1 (i_decoded x), Znth 2 (i_decoded x), ms, me,
                       Znth 11 (i_decoded x), Znth 17 (i_decoded x), 1, i, fw).
    { apply (next_call_go _ _ _ _ R1). }
    Intros v. rename H into Uv.
    deadvars!.
    pose proof (run_word x (start x) _ _ _ v R1 ltac:(intros; discriminate)) as R2.
    cbn [step reply_value expected m_terminal with_terminal] in R2.
    forward.
    rewrite ?upd_map_vl, ?(upd_Znth_map vl).
    match type of R2 with run _ _ ?L = _ => Exists L (upd_Znth i t v) end.
    entailer!.
    split; [ rewrite Zlength_upd_Znth'; auto | apply Forall_upd_Znth; auto ]. }
  (* the checks *)
  Intros hs1 t.
  rename H into Lt, H0 into Ut, H1 into R1.
  rewrite Z.ltb_irrefl in R1.
  forward. forward_if. { w64. tret x R1. } w64.
  forward. forward_if. { w64. tret x R1. } w64.
  forward. forward_if. { w64. tret x R1. } w64.
  forward. forward_if. { w64. tret x R1. } w64.
  forward. forward_if. { w64. tret x R1. } w64.
  forward. forward. forward_if. { w64. tret x R1. } w64.
  tret x R1.
Qed.
