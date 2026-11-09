(* The body of boot_handoff_stream_copy: the stream reset's seven calls and its checks, then for each chunk the
   read, the transition's nine calls and their checks, the copy's word and the carried state; then the stream's
   final checks and the length written on OK; against Defs.step one answer at a time, up to copy_end. *)
Require Import VST.floyd.proofauto.
Require Import LeanosHandoff.handoff.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.InternalSpecs.
Require Import LeanosHandoff.proof.HdLemmas.
#[local] Existing Instance HandoffSpecs.CS.
Local Open Scope Z_scope.

Lemma stream_init_fail (x: inputs) (a: list Z) (m: mem) (st: Z) :
  stream_init_check x (m_total m) a = st -> st <> S_OK ->
  stream_init_done x a m = copy_end x st (with_copy m (m_copy m)).
Proof.
  intros C N. unfold stream_init_done. rewrite C, with_copy_same, copy_end_fail by auto.
  destruct (Z.eqb_spec st S_OK); [ contradiction | reflexivity ].
Qed.

Lemma stream_init_ok (x: inputs) (a: list Z) (m: mem) :
  stream_init_check x (m_total m) a = S_OK -> stream_init_done x a m = begin_chunk x 0 a (with_copy m (m_copy m)).
Proof. intros C. unfold stream_init_done. rewrite C, with_copy_same. reflexivity. Qed.

Lemma begin_chunk_go (x: inputs) (k: Z) (st: list Z) (m: mem) :
  8 * k < m_total m -> begin_chunk x k st m = Go (ExpectChunk k st) m.
Proof. intros. unfold begin_chunk. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.

Lemma begin_chunk_end (x: inputs) (k: Z) (st: list Z) (m: mem) :
  m_total m <= 8 * k -> begin_chunk x k st m = copy_end x (stream_final (m_total m) st) m.
Proof. intros. unfold begin_chunk. rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity. Qed.

Lemma stream_step_fail (x: inputs) (k cv: Z) (a: list Z) (m: mem) (st: Z) :
  stream_step_check x (m_total m) k cv a = st -> st <> S_OK -> stream_step_done x k cv a m = copy_end x st m.
Proof.
  intros C N. unfold stream_step_done. rewrite C, copy_end_fail by auto.
  destruct (Z.eqb_spec st S_OK); [ contradiction | reflexivity ].
Qed.

Lemma stream_step_ok (x: inputs) (k cv: Z) (a: list Z) (m: mem) :
  stream_step_check x (m_total m) k cv a = S_OK ->
  stream_step_done x k cv a m = begin_chunk x (k + 1) (sublist 0 7 a) (with_copy m (upd_Znth k (m_copy m) cv)).
Proof. intros C. unfold stream_step_done. rewrite C. reflexivity. Qed.

Ltac sfail hs c FAIL st :=
  forward; Exists hs st c; entailer!;
  post_split; first [ apply FAIL; [ unfold stream_step_check; zb; reflexivity | sne ] | sok | auto ].

Ltac ffail hs c R st :=
  forward; Exists hs st c; entailer!;
  post_split; first [ rewrite R; do 2 f_equal; unfold stream_final; zb; reflexivity | sok | auto ].

Ltac ifail hs c FAIL st :=
  forward; Exists hs st c; entailer!;
  post_split; first [ apply FAIL; [ unfold stream_init_check; zb; reflexivity | sne ] | sok | auto ].

Lemma body_boot_handoff_stream_copy (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_boot_handoff_stream_copy (stream_copy_spec Ora).
Proof.
  start_function.
  rename H into IX, H0 into EF, H1 into LC, H2 into R0.
  pose proof IX as IX'. destruct IX' as (UM & UA & _).
  pose proof UM as UM'. pose proof UA as UA'. unfold u32_ok in UM', UA'.
  assert (UT: u32_ok (m_total m)) by (destruct EF; unfold u32_ok; rep_lia).
  pose proof UT as UT'. unfold u32_ok in UT'.
  forward_for_simple_bound 7 (EX q: Z, EX hs: list answer, EX a: list Z,
    PROP (Zlength a = q; Forall u64_ok a;
          run x (start x) (h ++ hs) = Some (if q <? 7 then Go (ExpectStreamInit a) m else stream_init_done x a m))
    LOCAL (lvar _answer (tarray tulong 9) v_answer; lvar _state (tarray tulong 7) v_state;
           temp _read read; temp _context ctx; temp _magic (vi (i_magic x)); temp _info_address (vi (i_address x));
           temp _total (vi (m_total m)); temp _copy cp; temp _length lp; gvars gv)
    SEP (Ora gv ctx rctx x (h ++ hs); data_at Tsh (tarray tulong 7) (map vl a ++ Zrepeat Vundef (7 - q)) v_state;
         data_at_ Tsh (tarray tulong 9) v_answer; func_ptr' (read_spec Ora) read;
         data_at csh (tarray tulong COPY_WORDS) (map vl (m_copy m)) cp; data_at lsh tuint lold lp))%assert.
  - Exists (@nil answer) (@nil Z). rewrite app_nil_r. entailer!.
  - Intros.
    match goal with H: run _ _ (h ++ hs) = _ |- _ => rename H into R end.
    rewrite (proj2 (Z.ltb_lt i 7)) in R by lia.
    forward_call (gv, ctx, rctx, x, h ++ hs, i_magic x, i_address x, m_total m, i_address x, i).
    { rewrite (next_call_go _ _ _ _ R). cbn [expected]. subst i. reflexivity. }
    Intros v.
    forward.
    Exists (hs ++ [(StreamInit (i_magic x) (i_address x) (m_total m) (i_address x) i, v)]) (a ++ [v]).
    entailer!.
    + split; [ rewrite Zlength_app, Zlength_cons, Zlength_nil; lia | ].
      split; [ apply Forall_app; split; auto | ].
      rewrite app_assoc.
      replace (StreamInit (i_magic x) (i_address x) (m_total m) (i_address x) (Zlength a))
        with (expected x (ExpectStreamInit a) m) by reflexivity.
      rewrite (run_snoc _ _ _ _ _ v R). cbn [step].
      rewrite Zlength_app, Zlength_cons, Zlength_nil. reflexivity.
    + rewrite upd_fill by lia. rewrite <- app_assoc. apply derives_refl.
  - Intros hs a.
    match goal with H: run _ _ (h ++ hs) = _ |- _ => rename H into R end.
    rewrite Z.ltb_irrefl in R. change (Zrepeat Vundef (7 - 7)) with (@nil val). rewrite app_nil_r.
    match goal with H: Zlength a = 7 |- _ => rename H into La end.
    match goal with H: Forall u64_ok a |- _ => rename H into Fa end.
    assert (FAIL: forall st, stream_init_check x (m_total m) a = st -> st <> S_OK ->
              run x (start x) (h ++ hs) = Some (copy_end x st (with_copy m (m_copy m))))
      by (intros; rewrite R; f_equal; apply stream_init_fail; auto).
    forward. forward_if. { w64. ifail hs (m_copy m) FAIL S_STREAM_INIT_VERSION. } w64.
    forward. forward_if. { w64. ifail hs (m_copy m) FAIL S_STREAM_INIT_STATUS. } w64.
    forward. forward_if. { w64. ifail hs (m_copy m) FAIL S_STREAM_INIT_ERROR. } w64.
    forward. forward_if. { w64. ifail hs (m_copy m) FAIL S_STREAM_INIT_IDENTITY. } w64.
    forward. forward_if. { w64. ifail hs (m_copy m) FAIL S_STREAM_INIT_EXTENT. } w64.
    forward. forward_if. { w64. ifail hs (m_copy m) FAIL S_STREAM_INIT_OFFSET. } w64.
    assert (C0: stream_init_check x (m_total m) a = S_OK) by (unfold stream_init_check; zb; reflexivity).
    rewrite stream_init_ok in R by auto.
    forward_loop (EX k: Z, EX hs: list answer, EX st: list Z, EX c: list Z,
      PROP (0 <= k; 8 * k <= m_total m; Zlength st = 7; Forall u64_ok st; Zlength c = COPY_WORDS;
            run x (start x) (h ++ hs) = Some (begin_chunk x k st (with_copy m c)))
      LOCAL (temp _offset (vl (8 * k)); lvar _answer (tarray tulong 9) v_answer; lvar _state (tarray tulong 7) v_state;
             temp _read read; temp _context ctx; temp _magic (vi (i_magic x)); temp _info_address (vi (i_address x));
             temp _total (vi (m_total m)); temp _copy cp; temp _length lp; gvars gv)
      SEP (Ora gv ctx rctx x (h ++ hs); data_at Tsh (tarray tulong 7) (map vl st) v_state;
           data_at_ Tsh (tarray tulong 9) v_answer; func_ptr' (read_spec Ora) read;
           data_at csh (tarray tulong COPY_WORDS) (map vl c) cp; data_at lsh tuint lold lp))%assert
    continue: (EX k: Z, EX hs: list answer, EX st: list Z, EX c: list Z,
      PROP (0 <= k; 8 * k < m_total m; Zlength st = 7; Forall u64_ok st; Zlength c = COPY_WORDS;
            run x (start x) (h ++ hs) = Some (begin_chunk x (k + 1) st (with_copy m c)))
      LOCAL (temp _offset (vl (8 * k)); lvar _answer (tarray tulong 9) v_answer; lvar _state (tarray tulong 7) v_state;
             temp _read read; temp _context ctx; temp _magic (vi (i_magic x)); temp _info_address (vi (i_address x));
             temp _total (vi (m_total m)); temp _copy cp; temp _length lp; gvars gv)
      SEP (Ora gv ctx rctx x (h ++ hs); data_at Tsh (tarray tulong 7) (map vl st) v_state;
           data_at_ Tsh (tarray tulong 9) v_answer; func_ptr' (read_spec Ora) read;
           data_at csh (tarray tulong COPY_WORDS) (map vl c) cp; data_at lsh tuint lold lp))%assert
    break: (EX hs: list answer, EX st: list Z, EX c: list Z,
      PROP (Zlength st = 7; Forall u64_ok st; Zlength c = COPY_WORDS;
            run x (start x) (h ++ hs) = Some (copy_end x (stream_final (m_total m) st) (with_copy m c)))
      LOCAL (lvar _answer (tarray tulong 9) v_answer; lvar _state (tarray tulong 7) v_state;
             temp _read read; temp _context ctx; temp _magic (vi (i_magic x)); temp _info_address (vi (i_address x));
             temp _total (vi (m_total m)); temp _copy cp; temp _length lp; gvars gv)
      SEP (Ora gv ctx rctx x (h ++ hs); data_at Tsh (tarray tulong 7) (map vl st) v_state;
           data_at_ Tsh (tarray tulong 9) v_answer; func_ptr' (read_spec Ora) read;
           data_at csh (tarray tulong COPY_WORDS) (map vl c) cp; data_at lsh tuint lold lp))%assert.
    { forward. Exists 0 hs a (m_copy m). entailer!. }
    { Intros k hs1 st c.
      match goal with H: run _ _ (h ++ hs1) = _ |- _ => rename H into R1 end.
      forward_if.
      { (* a chunk *)
        w64.
        rewrite begin_chunk_go in R1 by (cbn; lia).
        forward_call (gv, ctx, rctx, x, h ++ hs1, i_address x + 8 * k).
        { rewrite (next_call_go _ _ _ _ R1). reflexivity. }
        Intros cv.
        forward.
        rewrite terminal_val by (first [ assumption | destruct EF; rep_lia ]).
        assert (TR: 0 <= terminal (m_total m) k <= 1) by apply terminal_range.
        rewrite <- app_assoc.
        assert (R2: run x (start x) (h ++ hs1 ++ [(Read (i_address x + 8 * k), cv)]) =
                    Some (Go (ExpectStreamStep k st cv []) (with_copy m c)))
          by (rewrite app_assoc; apply (run_snoc _ _ _ _ _ cv R1)).
        set (hsr := hs1 ++ [(Read (i_address x + 8 * k), cv)]) in *. clearbody hsr. clear R1.
        forward_for_simple_bound 9 (EX q: Z, EX hs2: list answer, EX a2: list Z,
          PROP (Zlength a2 = q; Forall u64_ok a2;
                run x (start x) (h ++ hsr ++ hs2) =
                  Some (if q <? 9 then Go (ExpectStreamStep k st cv a2) (with_copy m c)
                        else stream_step_done x k cv a2 (with_copy m c)))
          LOCAL (temp _terminal (vl (terminal (m_total m) k)); temp _chunk (vl cv); temp _offset (vl (8 * k));
                 lvar _answer (tarray tulong 9) v_answer; lvar _state (tarray tulong 7) v_state;
                 temp _read read; temp _context ctx; temp _magic (vi (i_magic x));
                 temp _info_address (vi (i_address x)); temp _total (vi (m_total m)); temp _copy cp;
                 temp _length lp; gvars gv)
          SEP (Ora gv ctx rctx x (h ++ hsr ++ hs2); data_at Tsh (tarray tulong 7) (map vl st) v_state;
               data_at Tsh (tarray tulong 9) (map vl a2 ++ Zrepeat Vundef (9 - q)) v_answer;
               func_ptr' (read_spec Ora) read;
               data_at csh (tarray tulong COPY_WORDS) (map vl c) cp; data_at lsh tuint lold lp))%assert.
        { Exists (@nil answer) (@nil Z). rewrite app_nil_r. entailer!. }
        { Intros.
          match goal with H: run _ _ (h ++ hsr ++ hs2) = _ |- _ => rename H into R3 end.
          rewrite (proj2 (Z.ltb_lt i 9)) in R3 by lia.
          do 7 forward.
          forward_call (gv, ctx, rctx, x, h ++ hsr ++ hs2, st, i_address x, 8 * k, 8, cv, terminal (m_total m) k, i).
          { rewrite (next_call_go _ _ _ _ R3). cbn [expected]. subst i. reflexivity. }
          Intros v.
          forward.
          Exists (hs2 ++ [(StreamStep st (i_address x) (8 * k) 8 cv (terminal (m_total m) k) i, v)]) (a2 ++ [v]).
          entailer!.
          + split; [ rewrite Zlength_app, Zlength_cons, Zlength_nil; lia | ].
            split; [ apply Forall_app; split; auto | ].
            rewrite !app_assoc. rewrite app_assoc in R3.
            replace (StreamStep st (i_address x) (8 * k) 8 cv (terminal (m_total m) k) (Zlength a2))
              with (expected x (ExpectStreamStep k st cv a2) (with_copy m c)) by reflexivity.
            rewrite (run_snoc _ _ _ _ _ v R3). cbn [step].
            rewrite Zlength_app, Zlength_cons, Zlength_nil. reflexivity.
          + rewrite upd_fill by lia. rewrite <- !app_assoc. apply derives_refl. }
        Intros hs2 a2.
        match goal with H: run _ _ (h ++ hsr ++ hs2) = _ |- _ => rename H into R3 end.
        rewrite Z.ltb_irrefl in R3. change (Zrepeat Vundef (9 - 9)) with (@nil val). rewrite app_nil_r.
        match goal with H: Zlength a2 = 9 |- _ => rename H into La2 end.
        match goal with H: Forall u64_ok a2 |- _ => rename H into Fa2 end.
        assert (FAIL2: forall st', stream_step_check x (m_total m) k cv a2 = st' -> st' <> S_OK ->
                  run x (start x) (h ++ (hsr ++ hs2)) = Some (copy_end x st' (with_copy m c)))
          by (intros; rewrite R3; f_equal; apply stream_step_fail; auto).
        forward. forward_if. { w64. sfail (hsr ++ hs2) c FAIL2 S_STREAM_STEP_VERSION. } w64.
        forward. forward_if. { w64. sfail (hsr ++ hs2) c FAIL2 S_STREAM_STEP_ERROR. } w64.
        forward. forward_if. { w64. sfail (hsr ++ hs2) c FAIL2 S_STREAM_STEP_IDENTITY. } w64.
        forward. forward_if. { w64. sfail (hsr ++ hs2) c FAIL2 S_STREAM_STEP_EXTENT. } w64.
        forward. forward_if. { w64. sfail (hsr ++ hs2) c FAIL2 S_STREAM_STEP_OFFSET. } w64.
        forward. forward_if. { w64. sfail (hsr ++ hs2) c FAIL2 S_STREAM_STEP_COUNT. } w64.
        forward. forward_if. { w64. sfail (hsr ++ hs2) c FAIL2 S_STREAM_STEP_EXPOSED. } w64.
        forward_if (temp _t'4 (vi (terminal (m_total m) k))).
        { w64. forward. entailer!. replace (terminal (m_total m) k) with 1 by lia. reflexivity. }
        { w64. forward. entailer!. replace (terminal (m_total m) k) with 0 by lia. reflexivity. }
        forward. forward_if. { w64. sfail (hsr ++ hs2) c FAIL2 S_STREAM_STEP_STATUS. } w64.
        assert (C2: stream_step_check x (m_total m) k cv a2 = S_OK) by (unfold stream_step_check; zb; reflexivity).
        rewrite stream_step_ok in R3 by auto. cbn [m_copy with_copy] in R3.
        forward.
        forward.
        { entailer!. rewrite (Z.mul_comm 8 k), Z_div_mult by lia. destruct EF; lia. }
        replace (8 * k / 8) with k by (rewrite Z.mul_comm, Z_div_mult by lia; reflexivity).
        forward_for_simple_bound 7 (EX w: Z,
          PROP ()
          LOCAL (temp _terminal (vl (terminal (m_total m) k)); temp _chunk (vl cv); temp _offset (vl (8 * k));
                 lvar _answer (tarray tulong 9) v_answer; lvar _state (tarray tulong 7) v_state;
                 temp _read read; temp _context ctx; temp _magic (vi (i_magic x));
                 temp _info_address (vi (i_address x)); temp _total (vi (m_total m)); temp _copy cp;
                 temp _length lp; gvars gv)
          SEP (Ora gv ctx rctx x (h ++ hsr ++ hs2);
               data_at Tsh (tarray tulong 7) (map vl (sublist 0 w a2 ++ sublist w 7 st)) v_state;
               data_at Tsh (tarray tulong 9) (map vl a2) v_answer;
               func_ptr' (read_spec Ora) read;
               data_at csh (tarray tulong COPY_WORDS) (upd_Znth k (map vl c) (vl (Znth 7 a2))) cp;
               data_at lsh tuint lold lp))%assert.
        { entailer!. rewrite sublist_nil, sublist_same by lia. apply derives_refl. }
        { forward. forward. entailer!. rewrite carry_step by lia. apply derives_refl. }
        rewrite carry_end by auto.
        Exists k (hsr ++ hs2) (sublist 0 7 a2) (upd_Znth k c cv).
        rewrite H18, upd_Znth_map.
        entailer!.
        post_split; [ rewrite Zlength_sublist by lia; lia | apply Forall_sublist; auto
                    | rewrite upd_Znth_Zlength by (destruct EF; lia); auto ]. }
      { (* the last chunk was read *)
        w64.
        rewrite begin_chunk_end in R1 by (cbn; lia).
        forward. Exists hs1 st c. entailer!. }
    }
    { (* the next offset *)
      Intros k hs1 st c.
      forward. Exists (k + 1) hs1 st c.
      entailer!.
      split; [ destruct EF; apply next8; auto | unfold vl; do 2 f_equal; lia ]. }
    (* the stream's final checks *)
    Intros hs1 st c.
    match goal with H: run _ _ (h ++ hs1) = _ |- _ => rename H into R1 end.
    forward. forward_if. { w64. ffail hs1 c R1 S_STREAM_INCOMPLETE_STATUS. } w64.
    forward. forward_if. { w64. ffail hs1 c R1 S_STREAM_INCOMPLETE_OFFSET. } w64.
    forward. forward.
    Exists hs1 S_OK c. entailer!.
    split; [ rewrite R1; do 2 f_equal; unfold stream_final; zb; reflexivity | sok ].
Qed.
