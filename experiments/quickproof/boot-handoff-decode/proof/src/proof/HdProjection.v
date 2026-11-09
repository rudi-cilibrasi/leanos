(* The body of boot_handoff_decode_projection: the bitmaps zeroed, the decoder's reset into states[0] and its
   checks, the transitions over the words decoded, alternating between the two rows, each accepted entry event
   recorded and projected into the 64 bitmap blocks, and the decoder's final checks; against
   Defs.begin_decode, decode_init_done, begin_transition, decode_step_done, entry_done and decode_done. *)
Require Import VST.floyd.proofauto.
Require Import LeanosHandoff.handoff.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.InternalSpecs.
Require Import LeanosHandoff.proof.HdLemmas.
Require Import LeanosHandoff.proof.HdStates.
Require Import LeanosHandoff.proof.HdFast.
#[local] Ltac simplify_remove_localdef_temp ::= fast_remove_localdef_temp.
#[local] Existing Instance HandoffSpecs.CS.
Local Open Scope Z_scope.

Local Notation PM m u b ss i := (with_states (with_bitmaps m u b zeros) ss i).

Ltac pfail hs ss FAIL PX TG st :=
  forward; Exists hs st zeros zeros zeros ss 0;
  rewrite (proj2 (Z.eqb_neq st S_OK)) by sne;
  entailer!;
  post_split;
  first [ rewrite projection_end_fail by sne; apply FAIL;
          [ unfold decode_init_check, by_call; rewrite PX; rewrite ?TG; zb; reflexivity | sne ]
        | sok | apply mem_ok_with; auto; lia | auto ].

(* A return from the loop's body, its rows joined first: the status st, the model's memory M. *)
Ltac lfail hs u b ss i R st :=
  forward; Exists hs st u b zeros ss i;
  rewrite (proj2 (Z.eqb_neq st S_OK)) by sne;
  entailer!;
  post_split;
  first [ rewrite projection_end_fail by sne; exact R | sok | apply mem_ok_with; auto; lia | auto ].

(* The loads before a call, up to the call. *)
Ltac to_call :=
  repeat lazymatch goal with
  | |- semax _ _ (Ssequence (Scall _ _ _) _) _ => fail
  | |- semax _ _ (Scall _ _ _) _ => fail
  | |- semax _ _ (Ssequence (Ssequence (Scall _ _ _) _) _) _ => fail
  | |- _ => forward
  end.

(* The same, the history read from R after the return (the return may substitute answers it compared). *)
Ltac lfail2 u b ss i R st :=
  forward;
  match type of R with run _ _ (_ ++ ?L) = _ => Exists L st u b zeros ss i end;
  rewrite (proj2 (Z.eqb_neq st S_OK)) by sne;
  entailer!;
  post_split;
  first [ rewrite projection_end_fail by sne; exact R | sok | apply mem_ok_with; auto; lia | auto ].

Lemma body_boot_handoff_decode_projection (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_boot_handoff_decode_projection (decode_projection_spec Ora).
Proof.
  start_function.
  rename H into IX, H0 into PX, H1 into EF, H2 into LD, H3 into MO, H4 into R0.
  pose proof IX as IX'. destruct IX' as (UM & UA & _).
  pose proof UM as UM'. pose proof UA as UA'. unfold u32_ok in UM', UA'.
  assert (UT: u32_ok (m_total m)) by (destruct EF; unfold u32_ok; rep_lia).
  pose proof UT as UT'. unfold u32_ok in UT'.
  pose proof MO as MO'. destruct MO' as (LU & LB & LR & _).
  assert (SO: states_ok (m_states m)) by (apply mem_ok_states; auto).
  unfold t_projection in *.
  Time forward_for_simple_bound 64 (EX w: Z,
    PROP ()
    LOCAL (gvars gv; temp _magic (vi (i_magic x)); temp _info_address (vi (i_address x));
           temp _total (vi (m_total m)); temp _info ip; temp _projection pp; temp _states sp; temp _current curp)
    SEP (func_ptr' (record_spec Ora) record; Ora gv ctx rctx x h;
         data_at ish (tarray tulong (Zlength (decoded x m))) (map vl (decoded x m)) ip;
         data_at psh (Tstruct _boot_projection_storage noattr) (record, (rctx, (up, (bp, rp)))) pp;
         data_at bsh (tarray tulong BLOCKS) (map vl (Zrepeat 0 w ++ sublist w BLOCKS (m_usable m))) up;
         data_at bsh (tarray tulong BLOCKS) (map vl (Zrepeat 0 w ++ sublist w BLOCKS (m_blocked m))) bp;
         data_at bsh (tarray tulong BLOCKS) (map vl (Zrepeat 0 w ++ sublist w BLOCKS (m_reserved m))) rp;
         data_at ssh t_states (states_val (m_states m)) sp; data_at cursh tuint curold curp))%assert.
  { entailer!. rewrite !prefix_start by auto. apply derives_refl. }
  { do 6 forward.
    change (Int.signed (Int.repr 0)) with 0.
    rewrite !prefix_step0 by (rewrite ?Zlength_Zrepeat; lia).
    rewrite !zeros_snoc by lia. entailer!. }
  rewrite !prefix_end'.
  set (m0 := with_bitmaps m zeros zeros zeros).
  assert (R1: run x (start x) h = Some (Go (ExpectDecodeInit nil) m0))
    by (rewrite R0; unfold begin_decode; rewrite PX; reflexivity).
  assert (TG: target x = 0) by (apply target_projection; auto).
  assert_PROP (field_compatible t_states [] sp) as FC by entailer!.
  assert (PS: isptr sp) by (apply field_compatible_isptr in FC; auto).
  rewrite (states_split ssh (m_states m) 0 sp) by (auto; apply SO). Intros.
  forward.
  forward_call (gv, ctx, rctx, x, h, m0, row 0 sp, ssh).
  { entailer!. simpl. rewrite TG. unfold row. rewrite isptr_offset_val_zero by auto. reflexivity. }
  Intros vret. destruct vret as [hs a]. cbn [fst snd] in *.
  match goal with H: run _ _ (h ++ hs) = _ |- _ => rename H into R2 end.
  match goal with H: Zlength a = 41 |- _ => rename H into La end.
  match goal with H: Forall u64_ok a |- _ => rename H into Fa end.
  change (1 - 0) with 1.
  sep_apply (states_put0 ssh (m_states m) a sp ltac:(apply SO) FC).
  set (ss1 := upd_Znth 0 (m_states m) a) in *.
  assert (SO1: states_ok ss1) by (apply states_ok_upd; auto; lia).
  assert (E0: Znth 0 ss1 = a) by (unfold ss1; rewrite upd_Znth_same by (destruct SO; lia); reflexivity).
  assert (FAIL: forall st, decode_init_check x (m_total m) a = st -> st <> S_OK ->
            run x (start x) (h ++ hs) = Some (Return st (with_states m0 ss1 0)))
    by (intros; rewrite R2; f_equal; apply decode_init_fail; auto).
  sload. rewrite E0. forward_if. { w64. pfail hs ss1 FAIL PX TG S_DECODE_INIT_VERSION. } w64.
  sload. rewrite E0. forward_if. { w64. pfail hs ss1 FAIL PX TG S_DECODE_INIT_STATUS. } w64.
  sload. rewrite E0. forward_if. { w64. pfail hs ss1 FAIL PX TG S_DECODE_INIT_ERROR. } w64.
  sload. rewrite E0. forward_if. { w64. pfail hs ss1 FAIL PX TG S_DECODE_INIT_IDENTITY. } w64.
  sload. rewrite E0. forward_if. { w64. pfail hs ss1 FAIL PX TG S_DECODE_INIT_EXTENT. } w64.
  sload. rewrite E0. forward_if. { w64. pfail hs ss1 FAIL PX TG S_DECODE_INIT_OFFSET. } w64.
  sload. rewrite E0. forward_if. { w64. pfail hs ss1 FAIL PX TG S_DECODE_INIT_TARGET. } w64.
  sload. rewrite E0. forward_if. { w64. pfail hs ss1 FAIL PX TG S_DECODE_INIT_TAG_COUNT. } w64.
  sload. rewrite E0. forward_if. { w64. pfail hs ss1 FAIL PX TG S_DECODE_INIT_ROOT_STATUS. } w64.
  assert (C0: decode_init_check x (m_total m) a = S_OK)
    by (unfold decode_init_check, by_call; rewrite PX, TG; zb; reflexivity).
  rewrite decode_init_ok in R2 by auto. change (m_states m0) with (m_states m) in R2. fold ss1 in R2.
  clear FAIL.
  assert (LK: forall k, 0 <= k -> 8 * k < m_total m -> 0 <= 8 * k / 8 < Zlength (decoded x m))
    by (intros k K0 K1; rewrite div8; split; [ lia | pose proof (chunk_index k (m_total m) K0 K1 (proj2 EF)); lia ]).
  forward_loop (EX k: Z, EX hs1: list answer, EX u: list Z, EX b: list Z, EX ss: list (list Z), EX i: Z,
      PROP (0 <= k; 8 * k <= m_total m; Zlength u = BLOCKS; Zlength b = BLOCKS; states_ok ss; i = 0 \/ i = 1;
            Forall u64_ok (Znth i ss);
            run x (start x) (h ++ hs1) = Some (begin_transition x k (PM m u b ss i)))
      LOCAL (temp _offset (vl (8 * k)); temp _at (vi i); gvars gv; temp _magic (vi (i_magic x));
             temp _info_address (vi (i_address x)); temp _total (vi (m_total m)); temp _info ip;
             temp _projection pp; temp _states sp; temp _current curp)
      SEP (func_ptr' (record_spec Ora) record; Ora gv ctx rctx x (h ++ hs1);
           data_at ish (tarray tulong (Zlength (decoded x m))) (map vl (decoded x m)) ip;
           data_at psh (Tstruct _boot_projection_storage noattr) (record, (rctx, (up, (bp, rp)))) pp;
           data_at bsh (tarray tulong BLOCKS) (map vl u) up; data_at bsh (tarray tulong BLOCKS) (map vl b) bp;
           data_at bsh (tarray tulong BLOCKS) (map vl zeros) rp;
           data_at ssh t_states (states_val ss) sp; data_at cursh tuint curold curp))%assert
    continue: (EX k: Z, EX hs1: list answer, EX u: list Z, EX b: list Z, EX ss: list (list Z), EX i: Z,
      PROP (0 <= k; 8 * k < m_total m; Zlength u = BLOCKS; Zlength b = BLOCKS; states_ok ss; i = 0 \/ i = 1;
            Forall u64_ok (Znth i ss);
            run x (start x) (h ++ hs1) = Some (begin_transition x (k + 1) (PM m u b ss i)))
      LOCAL (temp _offset (vl (8 * k)); temp _at (vi i); gvars gv; temp _magic (vi (i_magic x));
             temp _info_address (vi (i_address x)); temp _total (vi (m_total m)); temp _info ip;
             temp _projection pp; temp _states sp; temp _current curp)
      SEP (func_ptr' (record_spec Ora) record; Ora gv ctx rctx x (h ++ hs1);
           data_at ish (tarray tulong (Zlength (decoded x m))) (map vl (decoded x m)) ip;
           data_at psh (Tstruct _boot_projection_storage noattr) (record, (rctx, (up, (bp, rp)))) pp;
           data_at bsh (tarray tulong BLOCKS) (map vl u) up; data_at bsh (tarray tulong BLOCKS) (map vl b) bp;
           data_at bsh (tarray tulong BLOCKS) (map vl zeros) rp;
           data_at ssh t_states (states_val ss) sp; data_at cursh tuint curold curp))%assert
    break: (EX hs1: list answer, EX u: list Z, EX b: list Z, EX ss: list (list Z), EX i: Z,
      PROP (Zlength u = BLOCKS; Zlength b = BLOCKS; states_ok ss; i = 0 \/ i = 1; Forall u64_ok (Znth i ss);
            run x (start x) (h ++ hs1) = Some (decode_done x (PM m u b ss i)))
      LOCAL (temp _at (vi i); gvars gv; temp _magic (vi (i_magic x));
             temp _info_address (vi (i_address x)); temp _total (vi (m_total m)); temp _info ip;
             temp _projection pp; temp _states sp; temp _current curp)
      SEP (func_ptr' (record_spec Ora) record; Ora gv ctx rctx x (h ++ hs1);
           data_at ish (tarray tulong (Zlength (decoded x m))) (map vl (decoded x m)) ip;
           data_at psh (Tstruct _boot_projection_storage noattr) (record, (rctx, (up, (bp, rp)))) pp;
           data_at bsh (tarray tulong BLOCKS) (map vl u) up; data_at bsh (tarray tulong BLOCKS) (map vl b) bp;
           data_at bsh (tarray tulong BLOCKS) (map vl zeros) rp;
           data_at ssh t_states (states_val ss) sp; data_at cursh tuint curold curp))%assert.
  { forward. Exists 0 hs zeros zeros ss1 0. entailer!; rewrite E0; auto. }
  { Intros k hs1 u b ss i. clear R2.
    match goal with H: run _ _ (h ++ hs1) = _ |- _ => rename H into R end.
    match goal with H: states_ok ss |- _ => rename H into SO2 end.
    match goal with H: i = 0 \/ i = 1 |- _ => rename H into I01 end.
    match goal with H: Zlength u = _ |- _ => rename H into Lu end.
    match goal with H: Zlength b = _ |- _ => rename H into Lb end.
    forward_if.
    2: { w64. rewrite begin_transition_end in R by (cbn; lia).
         forward. Exists hs1 u b ss i. entailer!. }
    w64. rewrite begin_transition_go in R by (cbn; lia).
    forward.
    rewrite terminal_val by (first [ assumption | destruct EF; rep_lia ]).
    pose proof (LK k ltac:(lia) ltac:(lia)) as KI.
    forward.
    rewrite div8 in *.
    rewrite (states_split ssh ss i sp) by (auto; apply SO2). Intros.
    forward_call (gv, ctx, rctx, x, h ++ hs1, PM m u b ss i, k, row i sp, ssh, row (1 - i) sp, ssh).
    { entailer!. simpl. unfold vi, row.
      rewrite sem_add_pi_ptr_special by first [ reflexivity | assumption | simpl; rep_lia ]. reflexivity. }
    { apply (states_ok_row ss i SO2); lia. }
    Intros vret. destruct vret as [hs2 a2]. cbn [fst snd] in *. try deadvars!.
    rewrite <- app_assoc in *.
    match goal with H: run _ _ (h ++ hs1 ++ hs2) = _ |- _ => rename H into R2 end.
    match goal with H: Zlength a2 = 41 |- _ => rename H into La2 end.
    match goal with H: Forall u64_ok a2 |- _ => rename H into Fa2 end.
    forward.
    rewrite vi_sub1 by auto.
    forward.
    rewrite row_binop by (auto; lia).
    set (ss2 := upd_Znth (1 - i) ss a2) in *.
    assert (SO3: states_ok ss2) by (apply states_ok_upd; auto; lia).
    assert (E1: Znth (1 - i) ss2 = a2) by (apply Znth_upd_this; auto; apply SO2).
    assert (I10: 1 - i = 0 \/ 1 - i = 1) by lia.
    forward.
    forward_if.
    { (* the transition answered an error *)
      w64. rewrite step_stop in R2 by auto.
      sep_apply (states_put ssh ss i a2 sp ltac:(apply SO2) I01 FC). fold ss2.
      forward. Exists (hs1 ++ hs2) u b ss2 (1 - i). entailer!; rewrite E1; auto. }
    w64.
    forward.
    forward_if.
    { (* an entry event *)
      w64. rewrite step_event in R2 by auto. cbv zeta in R2.
      change (with_states (PM m u b ss i) (upd_Znth (1 - m_at (PM m u b ss i)) (m_states (PM m u b ss i)) a2)
                (1 - m_at (PM m u b ss i))) with (PM m u b ss2 (1 - i)) in R2.
      forward.
      forward_if.
      { w64. assert (EC: event_check a2 = S_PROJECTION_COUNT_ZERO) by (unfold event_check; zb; reflexivity).
        rewrite EC, if_fail in R2 by sne.
        sep_apply (states_put ssh ss i a2 sp ltac:(apply SO2) I01 FC). fold ss2.
        lfail (hs1 ++ hs2) u b ss2 (1 - i) R2 S_PROJECTION_COUNT_ZERO. }
      w64.
      forward.
      forward_if.
      { w64. assert (EC: event_check a2 = S_PROJECTION_COUNT_LARGE) by (unfold event_check; zb; reflexivity).
        rewrite EC, if_fail in R2 by sne.
        sep_apply (states_put ssh ss i a2 sp ltac:(apply SO2) I01 FC). fold ss2.
        lfail (hs1 ++ hs2) u b ss2 (1 - i) R2 S_PROJECTION_COUNT_LARGE. }
      w64.
      assert (EC: event_check a2 = S_OK) by (unfold event_check; zb; reflexivity).
      rewrite EC, Z.eqb_refl in R2.
      forward.
      forward.
      forward.
      forward.
      forward.
      forward.
      forward_call (gv, ctx, rctx, x, h ++ hs1 ++ hs2, Znth 11 a2 - 1, Znth 20 a2, Znth 21 a2, Znth 22 a2).
      { rewrite (next_call_go _ _ _ _ R2). cbn [expected].
        change (current (PM m u b ss2 (1 - i))) with (Znth (1 - i) ss2). rewrite E1. reflexivity. }
      Intros.
      assert (EXR: expected x (ExpectRecord k) (PM m u b ss2 (1 - i)) =
                   Record (Znth 11 a2 - 1) (Znth 20 a2) (Znth 21 a2) (Znth 22 a2))
        by (cbn [expected]; change (current (PM m u b ss2 (1 - i))) with (Znth (1 - i) ss2); rewrite E1; reflexivity).
      pose proof (run_snoc x (start x) (h ++ hs1 ++ hs2) _ _ 0 R2) as R3. rewrite EXR in R3.
      change (step x (ExpectRecord k) (PM m u b ss2 (1 - i)) 0) with (Go (ExpectEntry k 0 []) (PM m u b ss2 (1 - i)))
        in R3.
      rewrite <- !app_assoc in R3. rewrite <- !app_assoc.
      assert (R3': run x (start x) (h ++ hs1 ++ hs2 ++ [(Record (Znth 11 a2 - 1) (Znth 20 a2) (Znth 21 a2) (Znth 22 a2), 0)]) =
                   Some (if 0 <? BLOCKS then Go (ExpectEntry k 0 []) (PM m u b ss2 (1 - i))
                         else begin_transition x (k + 1) (PM m u b ss2 (1 - i)))) by exact R3.
      assert (E1c: forall u0 b0, current (PM m u0 b0 ss2 (1 - i)) = a2) by (intros; exact E1).
      change (current (PM m u b ss i)) with (Znth i ss).
      clear R2 R3.
      rename i into ia.
      forward_for_simple_bound 64 (EX bk: Z, EX hs4: list answer, EX u': list Z, EX b': list Z,
        PROP (Zlength u' = BLOCKS; Zlength b' = BLOCKS;
              run x (start x) (h ++ hs4) =
                Some (if bk <? BLOCKS then Go (ExpectEntry k bk []) (PM m u' b' ss2 (1 - ia))
                      else begin_transition x (k + 1) (PM m u' b' ss2 (1 - ia))))
        LOCAL (temp _state (row (1 - ia) sp); temp _at (vi (1 - ia)); temp _offset (vl (8 * k)); gvars gv;
               temp _magic (vi (i_magic x)); temp _info_address (vi (i_address x)); temp _total (vi (m_total m));
               temp _info ip; temp _projection pp; temp _states sp; temp _current curp)
        SEP (func_ptr' (record_spec Ora) record; Ora gv ctx rctx x (h ++ hs4);
             data_at ish (tarray tulong (Zlength (decoded x m))) (map vl (decoded x m)) ip;
             data_at psh (Tstruct _boot_projection_storage noattr) (record, (rctx, (up, (bp, rp)))) pp;
             data_at bsh (tarray tulong BLOCKS) (map vl u') up; data_at bsh (tarray tulong BLOCKS) (map vl b') bp;
             data_at bsh (tarray tulong BLOCKS) (map vl zeros) rp;
             data_at ssh t_state (map vl (Znth ia ss)) (row ia sp);
             data_at ssh t_state (map vl a2) (row (1 - ia) sp);
             data_at cursh tuint curold curp))%assert.
      { Exists (hs1 ++ hs2 ++ [(Record (Znth 11 a2 - 1) (Znth 20 a2) (Znth 21 a2) (Znth 22 a2), 0)]) u b.
        entailer!. }
      { cbv beta. Intros hs4 u' b'.
        match goal with H: run _ _ (h ++ hs4) = _ |- _ => rename H into R4 end.
        match goal with H: Zlength u' = _ |- _ => rename H into Lu' end.
        match goal with H: Zlength b' = _ |- _ => rename H into Lb' end.
        rewrite (proj2 (Z.ltb_lt i BLOCKS)) in R4 by lia.
        to_call.
        forward_call (gv, ctx, rctx, x, (h ++ hs4), Znth 20 a2, Znth 21 a2, Znth 22 a2, i, Znth i u', Znth i b', 1).
        { apply (entry_call _ _ _ _ _ _ _ R4 (E1c u' b')). }
        Intros v1. try deadvars!.
        assert (R5: run x (start x) ((h ++ hs4) ++ [(Entry (Znth 20 a2) (Znth 21 a2) (Znth 22 a2) i (Znth i u') (Znth i b') 1, v1)]) = Some (Go (ExpectEntry k i [v1]) (PM m u' b' ss2 (1 - ia))))
          by (apply (entry_step _ _ _ _ _ _ _ v1 R4 (E1c u' b')); cbn; lia).
        to_call.
        forward_call (gv, ctx, rctx, x, ((h ++ hs4) ++ [(Entry (Znth 20 a2) (Znth 21 a2) (Znth 22 a2) i (Znth i u') (Znth i b') 1, v1)]), Znth 20 a2, Znth 21 a2, Znth 22 a2, i, Znth i u', Znth i b', 2).
        { apply (entry_call _ _ _ _ _ _ _ R5 (E1c u' b')). }
        Intros v2. try deadvars!.
        assert (R6: run x (start x) (((h ++ hs4) ++ [(Entry (Znth 20 a2) (Znth 21 a2) (Znth 22 a2) i (Znth i u') (Znth i b') 1, v1)]) ++ [(Entry (Znth 20 a2) (Znth 21 a2) (Znth 22 a2) i (Znth i u') (Znth i b') 2, v2)]) = Some (Go (ExpectEntry k i [v1; v2]) (PM m u' b' ss2 (1 - ia))))
          by (apply (entry_step _ _ _ _ _ _ _ v2 R5 (E1c u' b')); cbn; lia).
        to_call.
        forward_call (gv, ctx, rctx, x, (((h ++ hs4) ++ [(Entry (Znth 20 a2) (Znth 21 a2) (Znth 22 a2) i (Znth i u') (Znth i b') 1, v1)]) ++ [(Entry (Znth 20 a2) (Znth 21 a2) (Znth 22 a2) i (Znth i u') (Znth i b') 2, v2)]), Znth 20 a2, Znth 21 a2, Znth 22 a2, i, Znth i u', Znth i b', 3).
        { apply (entry_call _ _ _ _ _ _ _ R6 (E1c u' b')). }
        Intros v3. try deadvars!.
        assert (R7: run x (start x) ((((h ++ hs4) ++ [(Entry (Znth 20 a2) (Znth 21 a2) (Znth 22 a2) i (Znth i u') (Znth i b') 1, v1)]) ++ [(Entry (Znth 20 a2) (Znth 21 a2) (Znth 22 a2) i (Znth i u') (Znth i b') 2, v2)]) ++ [(Entry (Znth 20 a2) (Znth 21 a2) (Znth 22 a2) i (Znth i u') (Znth i b') 3, v3)]) = Some (Go (ExpectEntry k i [v1; v2; v3]) (PM m u' b' ss2 (1 - ia))))
          by (apply (entry_step _ _ _ _ _ _ _ v3 R6 (E1c u' b')); cbn; lia).
        to_call.
        forward_call (gv, ctx, rctx, x, ((((h ++ hs4) ++ [(Entry (Znth 20 a2) (Znth 21 a2) (Znth 22 a2) i (Znth i u') (Znth i b') 1, v1)]) ++ [(Entry (Znth 20 a2) (Znth 21 a2) (Znth 22 a2) i (Znth i u') (Znth i b') 2, v2)]) ++ [(Entry (Znth 20 a2) (Znth 21 a2) (Znth 22 a2) i (Znth i u') (Znth i b') 3, v3)]), Znth 20 a2, Znth 21 a2, Znth 22 a2, i, Znth i u', Znth i b', 4).
        { apply (entry_call _ _ _ _ _ _ _ R7 (E1c u' b')). }
        Intros v4. try deadvars!.
        assert (R8: run x (start x) (((((h ++ hs4) ++ [(Entry (Znth 20 a2) (Znth 21 a2) (Znth 22 a2) i (Znth i u') (Znth i b') 1, v1)]) ++ [(Entry (Znth 20 a2) (Znth 21 a2) (Znth 22 a2) i (Znth i u') (Znth i b') 2, v2)]) ++ [(Entry (Znth 20 a2) (Znth 21 a2) (Znth 22 a2) i (Znth i u') (Znth i b') 3, v3)]) ++ [(Entry (Znth 20 a2) (Znth 21 a2) (Znth 22 a2) i (Znth i u') (Znth i b') 4, v4)]) = Some (entry_done x k i [v1; v2; v3; v4] (PM m u' b' ss2 (1 - ia))))
          by (apply (entry_fin _ _ _ _ _ _ _ v4 R7 (E1c u' b')); reflexivity).
        to_call.
        forward_if.
        { w64. rewrite (entry_done_fail _ _ _ _ _ _ _ _ S_PROJECTION_ENTRY_STATUS) in R8
            by first [ rewrite entry_check4; zb; reflexivity | sne ].
          sep_apply (states_put ssh ss ia a2 sp ltac:(apply SO2) I01 FC). fold ss2.
          rewrite <- !app_assoc in R8. rewrite <- !app_assoc. cbn [app] in R8 |- *.
          lfail2 u' b' ss2 (1 - ia) R8 S_PROJECTION_ENTRY_STATUS. }
        w64.
        forward_if.
        { w64. rewrite (entry_done_fail _ _ _ _ _ _ _ _ S_PROJECTION_ENTRY_ERROR) in R8
            by first [ rewrite entry_check4; zb; reflexivity | sne ].
          sep_apply (states_put ssh ss ia a2 sp ltac:(apply SO2) I01 FC). fold ss2.
          rewrite <- !app_assoc in R8. rewrite <- !app_assoc. cbn [app] in R8 |- *.
          lfail2 u' b' ss2 (1 - ia) R8 S_PROJECTION_ENTRY_ERROR. }
        w64.
        match type of R8 with _ = Some (entry_done _ _ _ ?a _) =>
          assert (EC4: entry_check a = S_OK) by (rewrite entry_check4; zb; reflexivity) end.
        rewrite (entry_done_ok _ _ _ _ _ _ _ _ EC4) in R8.
        do 4 forward.
        rewrite ?upd_Znth_map, ?upd_vl.
        rewrite <- !app_assoc in R8. rewrite <- !app_assoc. cbn [app] in R8 |- *.
        match type of R8 with run _ _ (_ ++ ?L) = _ => Exists L (upd_Znth i u' v3) (upd_Znth i b' v4) end.
        entailer!.
        post_split; first [ exact R8 | rewrite upd_Znth_Zlength by lia; lia | auto ]. }
      cbv beta. Intros hs4 u' b'.
      match goal with H: run _ _ (h ++ hs4) = _ |- _ => rename H into R4 end.
      rewrite Z.ltb_irrefl in R4.
      sep_apply (states_put ssh ss ia a2 sp ltac:(apply SO2) I01 FC). fold ss2.
      Exists k hs4 u' b' ss2 (1 - ia). entailer!; rewrite E1; auto. }
    (* no entry event *)
    w64.
    rewrite step_next in R2 by first [ assumption | rewrite PX; cbn [andb]; apply Z.eqb_neq; assumption ].
    change (with_states (PM m u b ss i) (upd_Znth (1 - m_at (PM m u b ss i)) (m_states (PM m u b ss i)) a2)
              (1 - m_at (PM m u b ss i))) with (PM m u b ss2 (1 - i)) in R2.
    sep_apply (states_put ssh ss i a2 sp ltac:(apply SO2) I01 FC). fold ss2.
    forward.
    Exists k (hs1 ++ hs2) u b ss2 (1 - i). entailer!; rewrite E1; auto. }
  { (* the next offset *)
    Intros k hs1 u b ss i.
    forward. Exists (k + 1) hs1 u b ss i.
    entailer!.
    post_split; first [ destruct EF; apply next8; auto | unfold vl; do 2 f_equal; lia | auto ]. }
  (* the decoder's final checks *)
  Intros hs1 u b ss i.
  match goal with H: run _ _ (h ++ hs1) = _ |- _ => rename H into R end.
  match goal with H: states_ok ss |- _ => rename H into SO2 end.
  match goal with H: i = 0 \/ i = 1 |- _ => rename H into I01 end.
  rewrite decode_done_proj in R by auto.
  change (current (PM m u b ss i)) with (Znth i ss) in R.
  change (m_total (PM m u b ss i)) with (m_total m) in R.
  assert (I2: 0 <= i < 2) by lia.
  assert (LI2: Zlength (Znth i ss) = 41) by (apply states_ok_row; auto).
  sload.
  forward_if (PROP (Znth 2 (Znth i ss) = 0 -> incomplete_check (m_total m) (Znth i ss) = S_OK)
      LOCAL (temp _at (vi i); gvars gv; temp _magic (vi (i_magic x));
             temp _info_address (vi (i_address x)); temp _total (vi (m_total m)); temp _info ip;
             temp _projection pp; temp _states sp; temp _current curp)
      SEP (func_ptr' (record_spec Ora) record; Ora gv ctx rctx x (h ++ hs1);
           data_at ish (tarray tulong (Zlength (decoded x m))) (map vl (decoded x m)) ip;
           data_at psh (Tstruct _boot_projection_storage noattr) (record, (rctx, (up, (bp, rp)))) pp;
           data_at bsh (tarray tulong BLOCKS) (map vl u) up; data_at bsh (tarray tulong BLOCKS) (map vl b) bp;
           data_at bsh (tarray tulong BLOCKS) (map vl zeros) rp;
           data_at ssh t_states (states_val ss) sp; data_at cursh tuint curold curp)).
  { w64.
    match goal with H: Znth 2 (Znth i ss) = 0 |- _ => rewrite (proj2 (Z.eqb_eq _ _) H) in R end.
    sload. forward_if.
    { w64. assert (IC: incomplete_check (m_total m) (Znth i ss) = S_DECODE_INCOMPLETE_STATUS)
        by (unfold incomplete_check; zb; reflexivity).
      rewrite IC, projection_end_fail in R by sne. lfail hs1 u b ss i R S_DECODE_INCOMPLETE_STATUS. }
    w64. sload. forward_if.
    { w64. assert (IC: incomplete_check (m_total m) (Znth i ss) = S_DECODE_INCOMPLETE_OFFSET)
        by (unfold incomplete_check; zb; reflexivity).
      rewrite IC, projection_end_fail in R by sne. lfail hs1 u b ss i R S_DECODE_INCOMPLETE_OFFSET. }
    w64. sload. forward_if.
    { w64. assert (IC: incomplete_check (m_total m) (Znth i ss) = S_DECODE_INCOMPLETE_PHASE)
        by (unfold incomplete_check; zb; reflexivity).
      rewrite IC, projection_end_fail in R by sne. lfail hs1 u b ss i R S_DECODE_INCOMPLETE_PHASE. }
    w64. try forward.
    entailer!; intros; unfold incomplete_check; zb; reflexivity. }
  { w64. forward. entailer!; intros; contradiction. }
  Intros.
  match goal with H: Znth 2 (Znth i ss) = 0 -> _ |- _ => rename H into IC end.
  assert (ST: (if Znth 2 (Znth i ss) =? 0 then incomplete_check (m_total m) (Znth i ss) else S_OK) = S_OK)
    by (destruct (Z.eqb_spec (Znth 2 (Znth i ss)) 0); auto).
  rewrite ST in R.
  forward. forward.
  Exists hs1 S_OK u b zeros ss i. rewrite Z.eqb_refl.
  entailer!.
  post_split; first [ exact R | sok | apply mem_ok_with; auto; lia | auto ].
Qed.
