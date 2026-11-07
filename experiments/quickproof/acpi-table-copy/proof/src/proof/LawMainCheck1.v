(* Law table_copy_exact: main's checks of the header scratch and the two arenas against the law's copies. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosAcpi.harness.table_copy_exact.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawProg LeanosAcpi.proof.LawDefs LeanosAcpi.proof.LawFacts LeanosAcpi.proof.LawLib
  LeanosAcpi.proof.LawLib2 LeanosAcpi.proof.LawModel LeanosAcpi.proof.LawOra LeanosAcpi.proof.LawVerdict
  LeanosAcpi.proof.LawZero LeanosAcpi.proof.LawMainLib LeanosAcpi.proof.LawMainDefs LeanosAcpi.proof.LawMainPure
  LeanosAcpi.proof.LawMainState.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.


Lemma tail_bytes_check {Espec: OracleKind} (TR: tail_ok s_root_check) gv x pl re te s st pub mm mv v_copies v_storage v_result v_madt:
  forall Delta Rp c, Delta = Delta0 -> Rp = Post0 -> c = s_bytes_check ->
  semax Delta (check_pre gv x pl re te s st pub mm mv v_copies v_storage v_result v_madt) c Rp.
Proof.
  intros Delta Rp c -> -> ->.
  unfold s_bytes_check, check_pre. start_tail. Intros.
  match goal with H: J _ _ _ _ _ _ |- _ => rename H into HJ end.
  pose proof HJ as (L & F & R & RI). cbn [mem_of] in F, R.
  pose proof F as (F1 & F2 & F3 & F4 & F5 & F6).
  match goal with I: inputs_ok x |- _ => pose proof I as (_ & _ & _ & I4 & I5 & _) end.
  assert (B2: 0 <= Zlength (m_root mm) <= Int.max_unsigned) by (pose proof (Zlength_nonneg (m_root mm)); lia).
  assert (B3: 0 <= Zlength (m_tables mm) <= Int.max_unsigned) by (pose proof (Zlength_nonneg (m_tables mm)); lia).
  unfold lfields. Intros.
  (* the header scratch *)
  freeze_but2 [_header; _header_expect] [p_header pl] FZ.
  forward_for_simple_bound 36
    (EX i: Z, PROP ()
     LOCAL (temp _status (vi st); temp _m (gv _law); lvar _madt tuint v_madt; lvar _result t_result' v_result;
            lvar _storage t_storage' v_storage; lvar _copies t_slots' v_copies; gvars gv)
     SEP (FRZL FZ; field_at Ews t_law (DOT _header) (p_header pl) (gv _law);
          field_at Ews t_law (DOT _header_expect) (bytes_val (m_header mm)) (gv _law);
          data_at Ews (tarray tuchar 36) (bytes_val (m_header mm)) (p_header pl)))%assert.
  { entailer!. }
  { unfold HEADER_BYTES in F1.
    assert (Rb: 0 <= Znth i (m_header mm) <= 255) by (apply byte_at; auto; lia).
    forward. forward.
    { entailer!. rewrite Znth_bytes_val by lia. apply tc_byte; auto. }
    rewrite Znth_bytes_val by lia.
    forward.
    { entailer!. rewrite Znth_bytes_val by lia. apply tc_byte; auto. }
    rewrite Znth_bytes_val by lia.
    forward_call Int.one.
    { entailer!. simpl. rewrite Int.eq_true. reflexivity. }
    entailer!. }
  thaw FZ.
  (* the root arena *)
  forward.
  freeze_but2 [_root; _root_capacity; _root_expect] [(p_root pl); re] FZ.
  rewrite <- F2.
  forward_loop
    (EX i: Z, PROP (0 <= i <= Zlength (m_root mm))
     LOCAL (temp _i__4 (Vint (Int.repr i)); temp _status (vi st); temp _m (gv _law); lvar _madt tuint v_madt;
            lvar _result t_result' v_result; lvar _storage t_storage' v_storage; lvar _copies t_slots' v_copies; gvars gv)
     SEP (FRZL FZ; field_at Ews t_law (DOT _root) (p_root pl) (gv _law);
          field_at Ews t_law (DOT _root_capacity) (vi (Zlength (m_root mm))) (gv _law); field_at Ews t_law (DOT _root_expect) re (gv _law);
          data_at Ews (tarray tuchar (Zlength (m_root mm))) (bytes_val (m_root mm)) (p_root pl);
          data_at Ews (tarray tuchar (Zlength (m_root mm))) (bytes_val (m_root mm)) re))%assert
    continue:
    (EX i: Z, PROP (0 <= i < Zlength (m_root mm))
     LOCAL (temp _i__4 (Vint (Int.repr i)); temp _status (vi st); temp _m (gv _law); lvar _madt tuint v_madt;
            lvar _result t_result' v_result; lvar _storage t_storage' v_storage; lvar _copies t_slots' v_copies; gvars gv)
     SEP (FRZL FZ; field_at Ews t_law (DOT _root) (p_root pl) (gv _law);
          field_at Ews t_law (DOT _root_capacity) (vi (Zlength (m_root mm))) (gv _law); field_at Ews t_law (DOT _root_expect) re (gv _law);
          data_at Ews (tarray tuchar (Zlength (m_root mm))) (bytes_val (m_root mm)) (p_root pl);
          data_at Ews (tarray tuchar (Zlength (m_root mm))) (bytes_val (m_root mm)) re))%assert
    break:
    (PROP () LOCAL (temp _status (vi st); temp _m (gv _law); lvar _madt tuint v_madt;
            lvar _result t_result' v_result; lvar _storage t_storage' v_storage; lvar _copies t_slots' v_copies; gvars gv) SEP (FRZL FZ; field_at Ews t_law (DOT _root) (p_root pl) (gv _law);
          field_at Ews t_law (DOT _root_capacity) (vi (Zlength (m_root mm))) (gv _law); field_at Ews t_law (DOT _root_expect) re (gv _law);
          data_at Ews (tarray tuchar (Zlength (m_root mm))) (bytes_val (m_root mm)) (p_root pl);
          data_at Ews (tarray tuchar (Zlength (m_root mm))) (bytes_val (m_root mm)) re)).
  { Exists 0. entailer!. }
  { Intros i. unfold vi. forward. forward_if.
    2: { forward. entailer!. }
    wordp.
    assert (Rb: 0 <= Znth i (m_root mm) <= 255) by (apply byte_at; auto; lia).
    forward. forward.
    { entailer!. rewrite Znth_bytes_val by lia. apply tc_byte; auto. }
    rewrite Znth_bytes_val by lia.
    forward. forward.
    { entailer!. rewrite Znth_bytes_val by lia. apply tc_byte; auto. }
    rewrite Znth_bytes_val by lia.
    forward_call Int.one.
    { entailer!. simpl. rewrite Int.eq_true. reflexivity. }
    Exists i. entailer!. }
  { Intros i. forward. Exists (i + 1). entailer!. }
  rewrite F2. thaw FZ.
  (* the table arena *)
  forward.
  freeze_but2 [_tables; _table_capacity; _tables_expect] [(p_tables pl); te] FZ.
  rewrite <- F3.
  forward_loop
    (EX i: Z, PROP (0 <= i <= Zlength (m_tables mm))
     LOCAL (temp _i__5 (Vint (Int.repr i)); temp _status (vi st); temp _m (gv _law); lvar _madt tuint v_madt;
            lvar _result t_result' v_result; lvar _storage t_storage' v_storage; lvar _copies t_slots' v_copies; gvars gv)
     SEP (FRZL FZ; field_at Ews t_law (DOT _tables) (p_tables pl) (gv _law);
          field_at Ews t_law (DOT _table_capacity) (vi (Zlength (m_tables mm))) (gv _law); field_at Ews t_law (DOT _tables_expect) te (gv _law);
          data_at Ews (tarray tuchar (Zlength (m_tables mm))) (bytes_val (m_tables mm)) (p_tables pl);
          data_at Ews (tarray tuchar (Zlength (m_tables mm))) (bytes_val (m_tables mm)) te))%assert
    continue:
    (EX i: Z, PROP (0 <= i < Zlength (m_tables mm))
     LOCAL (temp _i__5 (Vint (Int.repr i)); temp _status (vi st); temp _m (gv _law); lvar _madt tuint v_madt;
            lvar _result t_result' v_result; lvar _storage t_storage' v_storage; lvar _copies t_slots' v_copies; gvars gv)
     SEP (FRZL FZ; field_at Ews t_law (DOT _tables) (p_tables pl) (gv _law);
          field_at Ews t_law (DOT _table_capacity) (vi (Zlength (m_tables mm))) (gv _law); field_at Ews t_law (DOT _tables_expect) te (gv _law);
          data_at Ews (tarray tuchar (Zlength (m_tables mm))) (bytes_val (m_tables mm)) (p_tables pl);
          data_at Ews (tarray tuchar (Zlength (m_tables mm))) (bytes_val (m_tables mm)) te))%assert
    break:
    (PROP () LOCAL (temp _status (vi st); temp _m (gv _law); lvar _madt tuint v_madt;
            lvar _result t_result' v_result; lvar _storage t_storage' v_storage; lvar _copies t_slots' v_copies; gvars gv) SEP (FRZL FZ; field_at Ews t_law (DOT _tables) (p_tables pl) (gv _law);
          field_at Ews t_law (DOT _table_capacity) (vi (Zlength (m_tables mm))) (gv _law); field_at Ews t_law (DOT _tables_expect) te (gv _law);
          data_at Ews (tarray tuchar (Zlength (m_tables mm))) (bytes_val (m_tables mm)) (p_tables pl);
          data_at Ews (tarray tuchar (Zlength (m_tables mm))) (bytes_val (m_tables mm)) te)).
  { Exists 0. entailer!. }
  { Intros i. unfold vi. forward. forward_if.
    2: { forward. entailer!. }
    wordp.
    assert (Rb: 0 <= Znth i (m_tables mm) <= 255) by (apply byte_at; auto; lia).
    forward. forward.
    { entailer!. rewrite Znth_bytes_val by lia. apply tc_byte; auto. }
    rewrite Znth_bytes_val by lia.
    forward. forward.
    { entailer!. rewrite Znth_bytes_val by lia. apply tc_byte; auto. }
    rewrite Znth_bytes_val by lia.
    forward_call Int.one.
    { entailer!. simpl. rewrite Int.eq_true. reflexivity. }
    Exists i. entailer!. }
  { Intros i. forward. Exists (i + 1). entailer!. }
  rewrite F3. thaw FZ.
  eapply semax_pre;
    [ | apply (TR gv x pl re te s st pub mm mv v_copies v_storage v_result v_madt);
        first [ reflexivity | assumption ] ].
  unfold check_pre, lfields. unfold vi, vl. entailer!.
Qed.
