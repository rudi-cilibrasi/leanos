(* The body of boot_handoff_decode_candidate: the decoder's reset into states[0] and its checks, the transitions
   over the words decoded, alternating between the two rows until one answers an error, and the authority
   checks of the final state; against Defs.decode_init_done, begin_transition, decode_step_done and
   decode_done. *)
Require Import VST.floyd.proofauto.
Require Import LeanosHandoff.handoff.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.InternalSpecs.
Require Import LeanosHandoff.proof.HdLemmas.
Require Import LeanosHandoff.proof.HdStates.
#[local] Existing Instance HandoffSpecs.CS.
Local Open Scope Z_scope.

Ltac cfail hs M FAIL P HC st :=
  forward; Exists hs st M; rewrite out_current_fail by sne; cbn [m_states m_at with_states];
  entailer!;
  post_split;
  first [ apply returns_return, FAIL; [ unfold decode_init_check, by_call; rewrite P; zb; reflexivity | sne ]
        | unfold keeps; rewrite HC; cbn; repeat split | auto ].

Ltac afail hs M R HC st :=
  forward; Exists hs st M; rewrite out_current_fail by sne; cbn [m_states m_at with_states];
  entailer!;
  post_split;
  first [ apply returns_return; rewrite R; do 2 f_equal; unfold authority_check; zb; reflexivity
        | unfold keeps; rewrite HC; cbn; repeat split | auto ].

Lemma body_boot_handoff_decode_candidate (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_boot_handoff_decode_candidate (boot_candidate_spec Ora).
Proof.
  start_function.
  rename H into HC, H0 into IX, H1 into EF, H2 into LI.
  pose proof IX as IX'. destruct IX' as (UM & UA & UT & UC & _ & _ & _ & LS & FS & _).
  pose proof UM as UM'. pose proof UA as UA'. pose proof UT as UT'. pose proof UC as UC'.
  unfold u32_ok, u64_ok in UM', UA', UT', UC'.
  assert (SO: states_ok (i_states x)) by (split; auto).
  assert (P: projection x = false) by (unfold projection; rewrite HC; reflexivity).
  assert (TG: target x = i_candidate x) by (unfold target; rewrite HC; reflexivity).
  assert (D: decoded x (initial x) = i_info x) by (unfold decoded; rewrite HC; reflexivity).
  assert (R0: run x (start x) [] = Some (Go (ExpectDecodeInit nil) (initial x)))
    by (cbn [run]; unfold start, begin_decode; rewrite HC, P; reflexivity).
  assert_PROP (field_compatible t_states [] sp) as FC by entailer!.
  assert (PS: isptr sp) by (apply field_compatible_isptr in FC; auto).
  rewrite (states_split ssh (i_states x) 0 sp) by auto. Intros.
  forward.
  forward_call (gv, ctx, rctx, x, @nil answer, initial x, row 0 sp, ssh).
  { entailer!. simpl. rewrite TG. unfold row. rewrite isptr_offset_val_zero by auto. reflexivity. }
  Intros vret. destruct vret as [hs a]. cbn [fst snd] in *. rewrite app_nil_l in *.
  match goal with H: run _ _ hs = _ |- _ => rename H into R1 end.
  match goal with H: Zlength a = 41 |- _ => rename H into La end.
  match goal with H: Forall u64_ok a |- _ => rename H into Fa end.
  change (1 - 0) with 1.
  sep_apply (states_put0 ssh (i_states x) a sp LS FC).
  set (ss1 := upd_Znth 0 (i_states x) a) in *.
  assert (SO1: states_ok ss1) by (apply states_ok_upd; auto; lia).
  assert (E0: Znth 0 ss1 = a) by (unfold ss1; rewrite upd_Znth_same by lia; reflexivity).
  assert (FAIL: forall st, decode_init_check x (i_total x) a = st -> st <> S_OK ->
            run x (start x) hs = Some (Return st (with_states (initial x) ss1 0)))
    by (intros; rewrite R1; f_equal; apply decode_init_fail; auto).
  sload. rewrite E0. forward_if.
  { w64. cfail hs (with_states (initial x) ss1 0) FAIL P HC S_AUTHORITY_INIT_VERSION. } w64.
  sload. rewrite E0. forward_if.
  { w64. cfail hs (with_states (initial x) ss1 0) FAIL P HC S_AUTHORITY_INIT_STATUS. } w64.
  sload. rewrite E0. forward_if.
  { w64. cfail hs (with_states (initial x) ss1 0) FAIL P HC S_AUTHORITY_INIT_ERROR. } w64.
  sload. rewrite E0. forward_if.
  { w64. cfail hs (with_states (initial x) ss1 0) FAIL P HC S_AUTHORITY_INIT_IDENTITY. } w64.
  sload. rewrite E0. forward_if.
  { w64. cfail hs (with_states (initial x) ss1 0) FAIL P HC S_AUTHORITY_INIT_EXTENT. } w64.
  sload. rewrite E0. forward_if.
  { w64. cfail hs (with_states (initial x) ss1 0) FAIL P HC S_AUTHORITY_INIT_OFFSET. } w64.
  sload. rewrite E0. forward_if.
  { w64. rewrite <- TG in *. cfail hs (with_states (initial x) ss1 0) FAIL P HC S_AUTHORITY_INIT_TARGET. } w64.
  sload. rewrite E0. forward_if.
  { w64. cfail hs (with_states (initial x) ss1 0) FAIL P HC S_AUTHORITY_INIT_TAG_COUNT. } w64.
  sload. rewrite E0. forward_if.
  { w64. cfail hs (with_states (initial x) ss1 0) FAIL P HC S_AUTHORITY_INIT_ROOT_STATUS. } w64.
  assert (C0: decode_init_check x (i_total x) a = S_OK)
    by (unfold decode_init_check, by_call; rewrite P, TG; zb; reflexivity).
  rewrite decode_init_ok in R1 by auto. change (m_states (initial x)) with (i_states x) in R1. fold ss1 in R1.
  clear FAIL.
  assert (DM: forall ss i, decoded x (with_states (initial x) ss i) = i_info x)
    by (intros; unfold decoded; rewrite HC; reflexivity).
  forward_loop (EX k: Z, EX hs1: list answer, EX ss: list (list Z), EX i: Z,
      PROP (0 <= k; 8 * k <= i_total x; states_ok ss; i = 0 \/ i = 1; Forall u64_ok (Znth i ss);
            run x (start x) hs1 = Some (begin_transition x k (with_states (initial x) ss i)))
      LOCAL (temp _offset (vl (8 * k)); temp _at (vi i); gvars gv; temp _magic (vi (i_magic x));
             temp _info_address (vi (i_address x)); temp _total (vi (i_total x));
             temp _candidate (vl (i_candidate x)); temp _info ip; temp _states sp; temp _current curp)
      SEP (data_at ssh t_states (states_val ss) sp; Ora gv ctx rctx x hs1;
           data_at ish (tarray tulong (i_total x / 8)) (map vl (i_info x)) ip;
           data_at cursh tuint (vi (i_current_record x)) curp))%assert
    continue: (EX k: Z, EX hs1: list answer, EX ss: list (list Z), EX i: Z,
      PROP (0 <= k; 8 * k < i_total x; states_ok ss; i = 0 \/ i = 1; Forall u64_ok (Znth i ss);
            run x (start x) hs1 = Some (begin_transition x (k + 1) (with_states (initial x) ss i)))
      LOCAL (temp _offset (vl (8 * k)); temp _at (vi i); gvars gv; temp _magic (vi (i_magic x));
             temp _info_address (vi (i_address x)); temp _total (vi (i_total x));
             temp _candidate (vl (i_candidate x)); temp _info ip; temp _states sp; temp _current curp)
      SEP (data_at ssh t_states (states_val ss) sp; Ora gv ctx rctx x hs1;
           data_at ish (tarray tulong (i_total x / 8)) (map vl (i_info x)) ip;
           data_at cursh tuint (vi (i_current_record x)) curp))%assert
    break: (EX hs1: list answer, EX ss: list (list Z), EX i: Z,
      PROP (states_ok ss; i = 0 \/ i = 1; Forall u64_ok (Znth i ss);
            run x (start x) hs1 = Some (decode_done x (with_states (initial x) ss i)))
      LOCAL (temp _at (vi i); gvars gv; temp _magic (vi (i_magic x));
             temp _info_address (vi (i_address x)); temp _total (vi (i_total x));
             temp _candidate (vl (i_candidate x)); temp _info ip; temp _states sp; temp _current curp)
      SEP (data_at ssh t_states (states_val ss) sp; Ora gv ctx rctx x hs1;
           data_at ish (tarray tulong (i_total x / 8)) (map vl (i_info x)) ip;
           data_at cursh tuint (vi (i_current_record x)) curp))%assert.
  { forward. Exists 0 hs ss1 0. entailer!; rewrite E0; auto. }
  { Intros k hs1 ss i.
    match goal with H: run _ _ hs1 = _ |- _ => rename H into R end.
    match goal with H: states_ok ss |- _ => rename H into SO2 end.
    match goal with H: i = 0 \/ i = 1 |- _ => rename H into I01 end.
    forward_if.
    2: { w64. rewrite begin_transition_end in R by (cbn; lia).
         forward. Exists hs1 ss i. entailer!. }
    w64. rewrite begin_transition_go in R by (cbn; lia).
    forward.
    rewrite terminal_val by (first [ assumption | destruct EF; rep_lia ]).
    assert (KI: 0 <= 8 * k / 8 < Zlength (i_info x))
      by (rewrite div8, LI; split; [ lia | apply chunk_index; auto; apply EF ]).
    forward.
    rewrite div8 in *.
    rewrite (states_split ssh ss i sp) by (auto; apply SO2). Intros.
    forward_call (gv, ctx, rctx, x, hs1, with_states (initial x) ss i, k, row i sp, ssh, row (1 - i) sp, ssh).
    { entailer!. rewrite DM. simpl. unfold vi, row.
      rewrite sem_add_pi_ptr_special by first [ reflexivity | assumption | simpl; rep_lia ]. reflexivity. }
    { apply (states_ok_row ss i SO2); lia. }
    Intros vret. destruct vret as [hs2 a2]. cbn [fst snd] in *.
    match goal with H: run _ _ (hs1 ++ hs2) = _ |- _ => rename H into R2 end.
    match goal with H: Zlength a2 = 41 |- _ => rename H into La2 end.
    match goal with H: Forall u64_ok a2 |- _ => rename H into Fa2 end.
    forward.
    rewrite vi_sub1 by auto.
    sep_apply (states_put ssh ss i a2 sp ltac:(apply SO2) I01 FC).
    set (ss2 := upd_Znth (1 - i) ss a2) in *.
    assert (SO3: states_ok ss2) by (apply states_ok_upd; auto; lia).
    assert (E1: Znth (1 - i) ss2 = a2) by (apply Znth_upd_this; auto; apply SO2).
    assert (I10: 1 - i = 0 \/ 1 - i = 1) by lia.
    sload. rewrite E1.
    forward_if.
    { (* the transition answered an error *)
      w64. rewrite step_stop in R2 by auto.
      forward. Exists (hs1 ++ hs2) ss2 (1 - i). entailer!; rewrite E1; auto. }
    w64. rewrite step_next in R2 by (rewrite ?P; auto).
    forward.
    Exists k (hs1 ++ hs2) ss2 (1 - i). entailer!; rewrite E1; auto. }
  { (* the next offset *)
    Intros k hs1 ss i.
    forward. Exists (k + 1) hs1 ss i.
    entailer!.
    split; [ destruct EF; apply next8; auto | unfold vl; do 2 f_equal; lia ]. }
  (* the authority checks *)
  Intros hs1 ss i.
  match goal with H: run _ _ hs1 = _ |- _ => rename H into R end.
  match goal with H: states_ok ss |- _ => rename H into SO2 end.
  match goal with H: i = 0 \/ i = 1 |- _ => rename H into I01 end.
  rewrite decode_done_alone in R by auto.
  change (current (with_states (initial x) ss i)) with (Znth i ss) in R.
  change (m_total (with_states (initial x) ss i)) with (i_total x) in R.
  assert (I2: 0 <= i < 2) by lia.
  assert (LI2: Zlength (Znth i ss) = 41) by (apply states_ok_row; auto).
  sload. forward_if. { w64. afail hs1 (with_states (initial x) ss i) R HC S_AUTHORITY_REJECTED_STATUS. } w64.
  sload. forward_if. { w64. afail hs1 (with_states (initial x) ss i) R HC S_AUTHORITY_REJECTED_ERROR. } w64.
  sload. forward_if. { w64. afail hs1 (with_states (initial x) ss i) R HC S_AUTHORITY_REJECTED_OFFSET. } w64.
  sload. forward_if. { w64. afail hs1 (with_states (initial x) ss i) R HC S_AUTHORITY_REJECTED_PHASE. } w64.
  sload. forward_if. { w64. afail hs1 (with_states (initial x) ss i) R HC S_AUTHORITY_REJECTED_TARGET. } w64.
  forward. forward.
  Exists hs1 S_OK (with_states (initial x) ss i).
  rewrite out_current_ok by (rewrite HC; discriminate). cbn [m_states m_at with_states].
  entailer!.
  post_split;
  first [ apply returns_return; rewrite R; do 2 f_equal; unfold authority_check; zb; reflexivity
        | unfold keeps; rewrite HC; cbn; repeat split | auto ].
Qed.
