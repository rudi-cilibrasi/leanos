(* Law table_copy_exact: main's checks of the 256 copy slots against the law's records. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosAcpi.harness.table_copy_exact.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawProg LeanosAcpi.proof.LawDefs LeanosAcpi.proof.LawFacts LeanosAcpi.proof.LawLib
  LeanosAcpi.proof.LawLib2 LeanosAcpi.proof.LawModel LeanosAcpi.proof.LawOra LeanosAcpi.proof.LawVerdict
  LeanosAcpi.proof.LawZero LeanosAcpi.proof.LawMainLib LeanosAcpi.proof.LawMainDefs LeanosAcpi.proof.LawMainPure
  LeanosAcpi.proof.LawMainModel LeanosAcpi.proof.LawMainCmp LeanosAcpi.proof.LawMainCmp2 LeanosAcpi.proof.LawMainCmp3
  LeanosAcpi.proof.LawMainState.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Lemma add_bytes_vi: forall p o, isptr p -> 0 <= o <= Int.max_unsigned ->
  force_val (sem_add_ptr_int tuchar Unsigned p (vi o)) = offset_val o p.
Proof. intros. apply add_bytes; auto. Qed.

Lemma eval_add_bytes_vi: forall p o, isptr p -> 0 <= o <= Int.max_unsigned ->
  eval_binop Oadd (tptr tuchar) tuint p (vi o) = offset_val o p.
Proof. intros. apply eval_add_bytes; auto. Qed.

(* A load from the copy slot whose value Zt names: its typecheck, then the loaded value. *)
Ltac fz Zt :=
  forward;
  lazymatch goal with
  | |- semax _ _ _ _ => try (rewrite Zt; cbv beta iota)
  | _ => entailer!; rewrite Zt; simpl; auto
  end.

Lemma tail_slots_check {Espec: OracleKind} (TS: tail_ok s_status_check): tail_ok s_slots_check.
Proof.
  intros gv x pl re te s st pub mm mv v_copies v_storage v_result v_madt Delta Rp c -> -> ->.
  unfold s_slots_check, check_pre. start_tail. Intros.
  match goal with H: J _ _ _ _ _ _ |- _ => rename H into HJ end.
  match goal with H: eok _ _ |- _ => rename H into EO end.
  pose proof HJ as (L & F & R & RI). cbn [mem_of] in F, R. pose proof F as (F1 & F2 & F3 & F4 & F5 & F6).
  pose proof R as (R1 & R2 & R3 & R4 & R5). pose proof EO as [E1 E2].
  destruct_lst_ok' L. unfold u32_ok, u64_ok in *.
  match goal with I: inputs_ok x |- _ => pose proof I as (I1 & I2 & _ & I4 & I5 & _) end.
  unfold u64_ok in I1, I2. unfold MAX_ENTRIES in *.
  unfold lfields. Intros.
  assert_PROP (isptr (p_tables pl)) as Ppt by entailer!.
  assert_PROP (Zlength (slots_val pl mm (Zrepeat zsdt 256)) = 256) as Lsl by (unfold t_slots' in *; entailer!).
  pose proof (slots_val_len pl mm Lsl) as Lm. unfold MAX_ENTRIES in Lm.
  freeze_but2 [_tables; _addresses; _ended; _offsets; _lengths; _finals] [v_copies; p_tables pl] FR.
  forward_for_simple_bound 256
    (EX t: Z, PROP () LOCAL (temp _status (vi st); temp _m (gv _law); lvar _madt tuint v_madt; lvar _result t_result' v_result;
            lvar _storage t_storage' v_storage; lvar _copies t_slots' v_copies; gvars gv) SEP (FRZL FR; field_at Ews t_law (DOT _tables) (p_tables pl) (gv _law);
          field_at Ews t_law (DOT _addresses) (map vl (w_addresses s)) (gv _law);
          field_at Ews t_law (DOT _ended) (vi (w_ended s)) (gv _law);
          field_at Ews t_law (DOT _offsets) (map vi (w_offsets s)) (gv _law);
          field_at Ews t_law (DOT _lengths) (map vi (w_lengths s)) (gv _law);
          field_at Ews t_law (DOT _finals) (map vl (w_finals s)) (gv _law);
          data_at Ews (tarray tuchar (table_capacity x)) (bytes_val (m_tables mm)) (p_tables pl);
          data_at Tsh t_slots' (slots_val pl mm (Zrepeat zsdt 256)) v_copies))%assert.
  { entailer!. }
  { forward. forward_if.
    - (* a copy the pipeline wrote *)
      wordp.
      pose proof (Forall_Znth' _ _ i E2 ltac:(lia)) as Eo. rewrite (R4 i ltac:(lia)) in Eo. unfold slot_of in Eo.
      cbn [s_offset] in Eo.
      assert (Zt: Znth i (slots_val pl mm (Zrepeat zsdt 256)) = sdt_val (p_tables pl) (slot_of s i)).
      { pose proof (slots_val_at pl mm i ltac:(unfold MAX_ENTRIES; lia) ltac:(unfold MAX_ENTRIES; lia)) as Z0.
        unfold MAX_ENTRIES in Z0. unfold zsdt. rewrite Z0.
        replace (i <? Zlength (m_slots mm)) with true by (symmetry; apply Z.ltb_lt; lia).
        rewrite (R4 i ltac:(lia)). reflexivity. }
      assert (Zt': Znth i (slots_val pl mm (Zrepeat zsdt 256)) =
        (vl (Znth i (w_addresses s)), (offset_val (Znth i (w_offsets s)) (p_tables pl),
         (vi (Znth i (w_lengths s)), vi (Znth i (w_finals s) mod 2 ^ 32))))) by (rewrite Zt; reflexivity).
      clear Zt. rename Zt' into Zt0.
      assert (Zt': forall d, @Znth _ d i (slots_val pl mm (Zrepeat zsdt 256)) =
        (vl (Znth i (w_addresses s)), (offset_val (Znth i (w_offsets s)) (p_tables pl),
         (vi (Znth i (w_lengths s)), vi (Znth i (w_finals s) mod 2 ^ 32))))).
      { intros d. rewrite <- Zt0. apply Znth_default_irrel. rewrite Lsl. lia. }
      fz Zt'. forward.
      forward_if (temp _t'29 (vi 1)).
      + fz Zt'. forward. forward. forward.
        { entailer!. rewrite add_bytes_vi by (auto; rep_lia).
          apply (bytes_test_eq Ews (table_capacity x) (bytes_val (m_tables mm)) (p_tables pl));
            [ apply writable_readable, writable_Ews | lia | lia | cancel ]. }
        entailer!. rewrite ?add_bytes_vi, ?eval_add_bytes_vi by (auto; rep_lia).
        first [ rewrite cmp_bytes_same by auto; reflexivity | rewrite if_true by reflexivity; reflexivity ].
      + else_false.
      + forward_if (temp _t'30 (vi 1)).
        * fz Zt'. forward. forward. entailer!. rewrite Int.eq_true. reflexivity.
        * else_false.
        * forward_if (temp _t'31 (vi 1)).
          -- fz Zt'. forward. forward. entailer!. rewrite repr_mod32, loword_repr, Int.eq_true. reflexivity.
          -- else_false.
          -- forward_call Int.one. entailer!.
    - (* a slot it did not *)
      wordp.
      assert (Zt': Znth i (slots_val pl mm (Zrepeat zsdt 256)) = (vl 0, (nullval, (vi 0, vi 0)))).
      { pose proof (slots_val_at pl mm i ltac:(unfold MAX_ENTRIES; lia) ltac:(unfold MAX_ENTRIES; lia)) as Z0.
        unfold MAX_ENTRIES in Z0. unfold zsdt. rewrite Z0.
        replace (i <? Zlength (m_slots mm)) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      rename Zt' into Zt0.
      assert (Zt': forall d, @Znth _ d i (slots_val pl mm (Zrepeat zsdt 256)) = (vl 0, (nullval, (vi 0, vi 0)))).
      { intros d. rewrite <- Zt0. apply Znth_default_irrel. rewrite Lsl. lia. }
      fz Zt'.
      forward_if (temp _t'32 (vi 1)).
      + fz Zt'. forward. entailer!.
      + else_false.
      + forward_if (temp _t'33 (vi 1)).
        * fz Zt'. forward. entailer!.
        * else_false.
        * forward_if (temp _t'34 (vi 1)).
          -- fz Zt'. forward. entailer!.
          -- else_false.
          -- forward_call Int.one. entailer!.
  }
  thaw FR.
  eapply semax_pre;
    [ | apply (TS gv x pl re te s st pub mm mv v_copies v_storage v_result v_madt);
        first [ reflexivity | assumption ] ].
  unfold check_pre, lfields. unfold vi, vl. entailer!.
Qed.
