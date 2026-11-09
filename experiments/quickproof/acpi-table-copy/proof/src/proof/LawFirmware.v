(* Law table_copy_exact: the body of the harness's firmware_copy against copy_spec Ora_law: its checks follow
   from the copy the model expects, and the bytes it writes keep the law's record and arenas the model's. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosAcpi.harness.table_copy_exact.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawProg LeanosAcpi.proof.LawDefs LeanosAcpi.proof.LawFacts LeanosAcpi.proof.LawLib
  LeanosAcpi.proof.LawModel LeanosAcpi.proof.LawOra.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Definition Gfw : funspecs := [gp_assert_spec; nondet_u8_spec; nondet_bytes_spec; stop_spec; little_spec].

Ltac split_hyps :=
  repeat match goal with H: _ /\ _ |- _ => destruct H end.

(* The typecheck of p == q with p and q the same valid pointer. *)
Lemma tc_same_ptr: forall (P: mpred) p, (P |-- valid_pointer p) -> P |-- denote_tc_test_eq p p.
Proof.
  intros P p V. apply denote_tc_test_eq_split; [ exact V | exact V ].
Qed.

Lemma body_firmware_copy : semax_body Vlaw Gfw f_firmware_copy firmware_spec.
Proof.
  start_function.
  rename H into Nc.
  unfold Ora_law. Intros p s re te.
  match goal with H: run _ _ _ = Some _ |- _ => rename H into Hrun end.
  match goal with H: J _ _ _ _ _ _ |- _ => rename H into HJ end.
  match goal with H: inputs_ok _ |- _ => rename H into Ix end.
  destruct (next_call_J _ _ _ _ _ _ _ _ Hrun HJ Nc) as (st & m & -> & Ec & G & L & F & R).
  rewrite (holds_run x h st m d len Hrun).
  cbn [mem_of].
  destruct (copy_call x st a d len Ec) as [(g & -> & -> & -> & ->) | (g & len' & -> & -> & -> & ->)].
  - (* the header *)
    try subst ctx.
    cbn [dest_ptr].
    rewrite region_header by (destruct F; auto).
    destruct G as (SI & TI & CI). destruct CI as (C0 & C1).
    pose proof SI as (S1 & S2 & S3 & S4 & S5).
    destruct_lst_ok' L. unfold u32_ok, u64_ok in L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L13, L14, L15, L16, L17, L18,
      L21, L22, L29.
    pose proof F as (F1 & F2 & F3 & F4 & F5 & F6).
    rewrite (data_at_tuchar_cs AcpiSpecs.CS LCS).
    unfold lfields. Intros.
    freeze_but [_kind; _header; _expect; _verdict; _sdt_address; _capacity; _length; _header_expect]
      [p_header pl] FR.
    unfold vi, vl.
    forward.
    forward_call Int.one.
    rewrite C0, S2. unfold E_HEADER.
    forward.
    forward_if (temp _t'1 (Vint (Int.repr 1))).
    { forward. entailer!. }
    { exfalso. lia. }
    forward_call Int.one.
    forward. forward_call Int.one.
    { entailer!. simpl. rewrite Int64.eq_true. reflexivity. }
    forward_call tt. Intros ok. forward.
    forward_if (PROP (False) LOCAL () SEP ()).
    2: { else_false. }
    forward.
    forward_if (temp _t'3 (Vint (Int.repr 1))).
    { forward. entailer!. }
    { exfalso. destruct (p_header pl); try contradiction; simpl in H; try (unfold Ptrofs.eq in H; rewrite zeq_true in H);
      try (apply H; reflexivity). }
    forward_call Int.one.
    forward_if.
    + (* the copy failed *)
      forward_call (gv _law, Vint (Int.repr 0), Vint (Int.repr (w_verdict s)), S_PHYSICAL).
      { unfold u32_ok, S_PHYSICAL; rep_lia. }
      forward.
      assert (Ef: fits (Copy (address_of x g) DHeader HEADER_BYTES) (Copied 0 (m_header m)) = true)
        by (apply fits_copy; auto).
      pose proof (run_snoc x h (Copying g CHeader) m _ _ Hrun Ec Ef) as Hr'.
      assert (Hs: step x (Copying g CHeader) m (Copied 0 (m_header m)) = Return S_PHYSICAL None m).
      { rewrite <- (region_header m F1) at 1. apply step_header_fail; auto. }
      pose proof (J_header_fail x pl re te g m s HJ) as HJ'.
      rewrite (region_header m F1), Hs in HJ'. rewrite Hs in Hr'.
      Exists 0 (m_header m).
      unfold Ora_law. Exists (Return S_PHYSICAL None m) (s_stop s S_PHYSICAL) re te.
      thaw FR. unfold lfields, s_stop. lst_cbn. cbn [mem_of]. unfold vi, vl. rewrite S2.
      rewrite (data_at_tuchar_cs LCS AcpiSpecs.CS sh HEADER_BYTES (bytes_val (m_header m)) (p_header pl)).
      entailer!.
    + (* the header copied *)
      sep_apply (data_at_data_at_ sh (tarray tuchar HEADER_BYTES) (bytes_val (m_header m)) (p_header pl)).
      forward_call (p_header pl, HEADER_BYTES, sh).
      { rewrite if_false by (destruct (p_header pl); try contradiction; discriminate). cancel. }
      all: try (unfold HEADER_BYTES; rep_lia).
      Intros bs. rewrite if_false by (destruct (p_header pl); try contradiction; discriminate).
      change (map (fun b => Vint (Int.repr b)) bs) with (bytes_val bs).
      freeze_but [_header_expect] [p_header pl] FZ.
      forward_for_simple_bound HEADER_BYTES
        (EX i: Z, PROP ()
         LOCAL (temp _ok (Vint (Int.repr ok)); temp _m (gv _law); gvars gv; temp _context (gv _law);
                temp _physical_address (Vlong (Int64.repr (address_of x g)));
                temp _destination (p_header pl); temp _length (Vint (Int.repr HEADER_BYTES)))
         SEP (FRZL FZ;
              field_at Ews t_law (DOT _header_expect) (bytes_val (sublist 0 i bs ++ sublist i HEADER_BYTES (m_header m)))
                (gv _law);
              data_at sh (tarray tuchar HEADER_BYTES) (bytes_val bs) (p_header pl)))%assert.
      { unfold HEADER_BYTES; rep_lia. }
      { entailer!. rewrite sublist_nil, app_nil_l, sublist_same by auto. apply derives_refl. }
      { match goal with H: 0 <= i < HEADER_BYTES |- _ => unfold HEADER_BYTES in H end.
        assert (Rb: 0 <= Znth i bs <= 255) by (apply byte_at; auto; unfold HEADER_BYTES in *; lia).
        forward.
        { entailer!. rewrite Znth_bytes_val by (unfold HEADER_BYTES in *; lia). apply tc_byte; auto. }
        rewrite Znth_bytes_val by (unfold HEADER_BYTES in *; lia).
        forward.
        entailer!. rewrite header_copy_step by (auto; unfold HEADER_BYTES; lia). apply derives_refl. }
      thaw FZ.
      replace (sublist 0 HEADER_BYTES bs ++ sublist HEADER_BYTES HEADER_BYTES (m_header m)) with bs
        by (unfold HEADER_BYTES in *; list_solve).
      forward_call (sh, offset_val 4 (p_header pl), p_header pl, bs, HEADER_BYTES, 4, 4).
      set (len := little (sublist 4 (4 + 4) bs)).
      assert (Lr: 0 <= len < 2 ^ 32).
      { unfold len. pose proof (little_bound (sublist 4 (4 + 4) bs) ltac:(apply Forall_sublist; auto)) as LB.
        rewrite Zlength_sublist in LB by (unfold HEADER_BYTES in *; lia).
        replace (4 + 4 - 4) with 4 in LB by lia. change (256 ^ 4) with (2 ^ 32) in LB. lia. }
      forward_if (temp _t'5 (Vint (Int.repr (Z.b2z ((len <? HEADER_BYTES) || (MAX_SDT_BYTES <? len))%bool)))).
      { forward. entailer!. unfold HEADER_BYTES, MAX_SDT_BYTES. bool_fin. }
      { forward. entailer!. unfold HEADER_BYTES, MAX_SDT_BYTES. bool_fin. }
      forward_if (temp _t'6 (Vint (Int.repr (Z.b2z (hdr_bad x g len))))).
      { forward. entailer!. try b2z_hyp. unfold hdr_bad. rw_bools. reflexivity. }
      { forward. forward. entailer!. try b2z_hyp. unfold hdr_bad. rw_bools. rewrite <- S5. bool_fin. }
      forward_if.
      * (* a length the pipeline does not copy *)
        try b2z_hyp.
        forward_call (gv _law, Vint (Int.repr 0), Vint (Int.repr (w_verdict s)), S_SDT_LENGTH).
        { unfold u32_ok, S_SDT_LENGTH; rep_lia. }
        forward.
        assert (Ef: fits (Copy (address_of x g) DHeader HEADER_BYTES) (Copied ok bs) = true)
          by (apply fits_copy; auto).
        pose proof (run_snoc x h (Copying g CHeader) m _ _ Hrun Ec Ef) as Hr'.
        assert (Nok: ok <> 0) by (wordc; auto).
        rewrite (step_header_bad x g m ok bs Nok) in Hr' by auto.
        pose proof (J_header_bad x pl re te g m s ok bs HJ Nok ltac:(assumption) ltac:(assumption) ltac:(auto)) as HJ'.
        rewrite (step_header_bad x g m ok bs Nok) in HJ' by auto.
        Exists ok bs.
        unfold Ora_law. Exists (Return S_SDT_LENGTH None (write m DHeader bs)) (s_stop s S_SDT_LENGTH) re te.
        thaw FR. unfold lfields, s_stop. lst_cbn. cbn [mem_of write m_header m_root m_tables]. unfold vi, vl.
        rewrite S2.
        rewrite (data_at_tuchar_cs LCS AcpiSpecs.CS sh HEADER_BYTES (bytes_val bs) (p_header pl)).
        entailer!.
      * (* the body's length *)
        try b2z_hyp.
        forward. forward. forward.
        assert (Ef: fits (Copy (address_of x g) DHeader HEADER_BYTES) (Copied ok bs) = true)
          by (apply fits_copy; auto).
        pose proof (run_snoc x h (Copying g CHeader) m _ _ Hrun Ec Ef) as Hr'.
        assert (Nok: ok <> 0) by (wordc; auto).
        rewrite (step_header_ok x g m ok bs Nok) in Hr' by auto.
        pose proof (J_header_ok x pl re te g m s ok bs HJ Nok ltac:(assumption) ltac:(assumption) ltac:(auto)) as HJ'.
        rewrite (step_header_ok x g m ok bs Nok) in HJ' by auto.
        Exists ok bs.
        unfold Ora_law. Exists (Go (Copying g (CBody len)) (write m DHeader bs)) (set_expect (set_length s len) E_BODY) re te.
        thaw FR. unfold lfields. lst_cbn. cbn [mem_of write m_header m_root m_tables]. unfold vi, vl.
        rewrite S2.
        rewrite (data_at_tuchar_cs LCS AcpiSpecs.CS sh HEADER_BYTES (bytes_val bs) (p_header pl)).
        entailer!.
        rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia. apply derives_refl.
  - (* the body *)
    try subst ctx.
    destruct G as (SI & TI & CI). destruct CI as (C0 & C1 & C2 & C3). subst len'.
    pose proof SI as (S1 & S2 & S3 & S4 & S5).
    destruct_lst_ok' L. unfold u32_ok, u64_ok in L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L13, L14, L15, L16, L17, L18,
      L21, L22, L29.
    pose proof F as (F1 & F2 & F3 & F4 & F5 & F6).
    unfold len_ok, HEADER_BYTES, MAX_SDT_BYTES in C3. destruct C3 as ((C3a & C3b) & C3c).
    assert (O: 0 <= cursor_of g) by (destruct g; simpl; [ lia | unfold tgt_inv, tab_inv in TI; lia ]).
    assert (Fit: cursor_of g + (w_length s) <= base_cap x g) by (rewrite capacity_base in C3c; lia).
    assert (LB: Zlength (base_mem m g) = base_cap x g) by (apply base_cap_fit; auto).
    pose proof (dest_ptr_isptr pl g H4 H5) as Pd.
    rewrite (data_at_tuchar_cs AcpiSpecs.CS LCS).
    sep_apply (arrays_to_base x m re te g).
    unfold lfields. Intros.
    assert_PROP (field_compatible (tarray tuchar (base_cap x g)) nil (base_exp re te g)) as FCb by entailer!.
    freeze_but [_kind; _expect; _verdict; _sdt_address; _capacity; _length; _destination; _destination_expect;
                _byte; _word] [dest_ptr pl (dest_of g); base_exp re te g] FR.
    unfold vi, vl. rewrite C0, S2, S3, S4, S5. unfold E_BODY.
    forward.
    forward_call Int.one.
    forward.
    forward_if (temp _t'1 (Vint (Int.repr 1))).
    { exfalso. lia. }
    { forward. forward. entailer!. }
    forward_call Int.one.
    forward. forward_call Int.one.
    { entailer!. simpl. rewrite Int64.eq_true. reflexivity. }
    forward_call tt. Intros ok. forward.
    match goal with |- semax _ ?Pre _ _ => forward_if Pre end.
    { exfalso. lia. }
    { forward. entailer!. }
    forward.
    forward_if (temp _t'7 (Vint (Int.repr 1))).
    { forward. forward. entailer!. }
    { exfalso. destruct (dest_ptr pl (dest_of g)); try contradiction; simpl in H;
      try (unfold Ptrofs.eq in H; rewrite zeq_true in H); try (apply H; reflexivity). }
    forward_call Int.one.
    forward.
    forward_if (temp _t'8 (Vint (Int.repr 1))).
    { forward. entailer!. bool_fin. }
    { exfalso. wordc. lia. }
    forward_call Int.one.
    forward_if.
    + (* the copy failed *)
      forward_call (gv _law, Vint (Int.repr 1), Vint (Int.repr (w_verdict s)), S_PHYSICAL).
      { unfold u32_ok, S_PHYSICAL; rep_lia. }
      forward.
      assert (Ef: fits (Copy (address_of x g) (dest_of g) (w_length s)) (Copied 0 (region m (dest_of g) (w_length s))) = true).
      { apply fits_copy. rewrite region_base, Zlength_sublist; lia. }
      pose proof (run_snoc x h (Copying g (CBody (w_length s))) m _ _ Hrun Ec Ef) as Hr'.
      rewrite step_body_fail in Hr' by lia.
      pose proof (J_body_fail x pl re te g (w_length s) m s HJ) as HJ'.
      rewrite step_body_fail in HJ' by lia.
      Exists 0 (region m (dest_of g) (w_length s)).
      unfold Ora_law. Exists (Return S_PHYSICAL None m) (s_stop s S_PHYSICAL) re te.
      thaw FR. sep_apply (arrays_unbase x m re te g).
      unfold lfields, s_stop. lst_cbn. cbn [mem_of]. unfold vi, vl. rewrite S2, S3, S4, S5.
      rewrite (data_at_tuchar_cs LCS AcpiSpecs.CS sh (w_length s) (bytes_val (region m (dest_of g) (w_length s))) (dest_ptr pl (dest_of g))).
      entailer!.
      split; [ rewrite region_base, Zlength_sublist; lia | ].
      rewrite region_base. apply Forall_sublist. destruct g; simpl; auto.
    + (* the body copied *)
      sep_apply (data_at_data_at_ sh (tarray tuchar (w_length s)) (bytes_val (region m (dest_of g) (w_length s))) (dest_ptr pl (dest_of g))).
      forward_call (dest_ptr pl (dest_of g), (w_length s), sh).
      { rewrite if_false by (destruct (dest_ptr pl (dest_of g)); try contradiction; discriminate). cancel. }
      all: try rep_lia.
      Intros bs. rewrite if_false by (destruct (dest_ptr pl (dest_of g)); try contradiction; discriminate).
      change (map (fun b => Vint (Int.repr b)) bs) with (bytes_val bs).
      rewrite (dexp_split g re te (base_cap x g) (base_mem m g) (w_length s)) by (auto; lia). Intros.
      freeze_but [_destination_expect] [dest_ptr pl (dest_of g); dexp_of re te g] FZ.
      forward_for_simple_bound (w_length s)
        (EX i: Z, PROP ()
         LOCAL (temp _ok (Vint (Int.repr ok)); temp _m (gv _law); gvars gv; temp _context (gv _law);
                temp _physical_address (Vlong (Int64.repr (address_of x g)));
                temp _destination (dest_ptr pl (dest_of g)); temp _length (Vint (Int.repr (w_length s))))
         SEP (FRZL FZ; field_at Ews t_law (DOT _destination_expect) (dexp_of re te g) (gv _law);
              data_at sh (tarray tuchar (w_length s)) (bytes_val bs) (dest_ptr pl (dest_of g));
              data_at Ews (tarray tuchar (w_length s))
                (bytes_val (sublist 0 i bs ++ sublist i (w_length s)
                              (sublist (cursor_of g) (cursor_of g + (w_length s)) (base_mem m g))))
                (dexp_of re te g)))%assert.
      { entailer!. rewrite sublist_nil, app_nil_l.
        rewrite (sublist_same 0 (w_length s)); [ apply derives_refl | reflexivity | ].
        rewrite Zlength_sublist; lia. }
      { assert (Rb: 0 <= Znth i bs <= 255) by (apply byte_at; auto; lia).
        forward. forward.
        { entailer!. rewrite Znth_bytes_val by lia. apply tc_byte; auto. }
        rewrite Znth_bytes_val by lia.
        forward.
        entailer!. rewrite body_copy_step by (rewrite ?Zlength_sublist; auto; lia). apply derives_refl. }
      thaw FZ.
      replace (sublist 0 (w_length s) bs ++ sublist (w_length s) (w_length s) (sublist (cursor_of g) (cursor_of g + (w_length s)) (base_mem m g))) with bs
        by list_solve.
      assert (DJ := dexp_join g re te (base_cap x g) (base_mem m g) (w_length s) bs Pre O ltac:(lia) ltac:(lia) LB
                      ltac:(assumption) FCb).
      sep_apply (derives_refl' _ _ DJ). clear DJ.
      forward. forward. forward. forward.
      assert (Ef: fits (Copy (address_of x g) (dest_of g) (w_length s)) (Copied ok bs) = true) by (apply fits_copy; auto).
      pose proof (run_snoc x h (Copying g (CBody (w_length s))) m _ _ Hrun Ec Ef) as Hr'.
      assert (Nok: ok <> 0) by (wordc; auto).
      rewrite (step_body_ok x g (w_length s) m ok bs Nok) in Hr'.
      pose proof (J_body_ok x pl re te g (w_length s) m s ok bs HJ Nok ltac:(assumption) ltac:(assumption)) as HJ'.
      rewrite (step_body_ok x g (w_length s) m ok bs Nok) in HJ'.
      Exists ok bs.
      unfold Ora_law. Exists (Go (Copying g (CChunk (w_length s) bs (cursor_of g) 0 nil)) (write m (dest_of g) bs))
        (set_expect (set_word (set_byte s 0) 0) E_STREAM) re te.
      thaw FR.
      rewrite <- (base_write m g bs), <- (other_write x m re te g bs).
      sep_apply (arrays_unbase x (write m (dest_of g) bs) re te g).
      unfold lfields. lst_cbn. cbn [mem_of]. unfold vi, vl. rewrite S2, S3, S4, S5.
      replace (m_header (write m (dest_of g) bs)) with (m_header m) by (destruct g; reflexivity).
      rewrite (data_at_tuchar_cs LCS AcpiSpecs.CS sh (w_length s) (bytes_val bs) (dest_ptr pl (dest_of g))).
      entailer!.
Qed.
