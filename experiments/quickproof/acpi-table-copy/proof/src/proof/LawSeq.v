(* Law table_copy_exact: the body of the harness's copy sequence export against sequence_spec Ora_law: its checks
   follow from the call the model expects (sequence_call), and the answer it records keeps J (LawModel). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env.
Require Import LeanosAcpi.harness.table_copy_exact.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawProg LeanosAcpi.proof.LawDefs LeanosAcpi.proof.LawFacts LeanosAcpi.proof.LawLib
  LeanosAcpi.proof.LawModel LeanosAcpi.proof.LawOra LeanosAcpi.proof.LawLib2 LeanosAcpi.proof.LawExp2.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Ltac addr := repeat match goal with E: context [Int.add (Int.repr _) (Int.repr _)] |- _ => rewrite add_repr in E end.

Definition Gseq : funspecs := [gp_assert_spec; any_u64_spec; stop_spec; begin_table_spec].

Lemma body_sequence : semax_body Vlaw Gseq f_leanos_boot_machine_acpi_copy_sequence_step_query
  (sequence_spec Ora_law).
Proof.
  start_function.
  rename H into Nc.
  unfold Ora_law. Intros p s re te.
  match goal with H: run _ _ _ = Some _ |- _ => rename H into Hrun end.
  match goal with H: J _ _ _ _ _ _ |- _ => rename H into HJ end.
  match goal with H: inputs_ok _ |- _ => rename H into Ix end.
  try subst ctx.
  destruct (next_call_J _ _ _ _ _ _ _ _ Hrun HJ Nc) as (st & m & -> & Ec & G & L & F & R).
  destruct (sequence_call x st _ _ _ _ _ _ Ec) as (l & cur & -> & -> & -> & -> & -> & -> & ->).
  cbn [mem_of] in *.
  pose proof G as (TB & G1 & G2 & G3 & G4 & G5 & G6).
  pose proof TB as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10).
  destruct_lst_ok' L. unfold u32_ok, u64_ok in L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L13, L14, L15, L16, L17, L18,
      L21, L22, L29.
  unfold MAX_ENTRIES in *.
  pose proof (Zlength_nonneg cur) as Lc0.
  unfold lfields. Intros.
  freeze_but [_expect; _word; _ordinal; _count; _table; _answer; _verdict] (@nil val) FR.
  unfold vi, vl. rewrite G1, G2, T1, T5, T9. unfold E_SEQUENCE.
  forward.
  forward.
  forward_if (temp _t'1 (Vint (Int.repr 1))).
  { repeat forward. all: (entailer!; bool_fin). }
  { exfalso. wordp. lia. }
  forward_call Int.one.
  forward.
  forward_if (temp _t'2 (Vint (Int.repr 1))).
  { repeat forward. all: (entailer!; bool_fin). }
  { exfalso. wordp. lia. }
  forward_if (temp _t'3 (Vint (Int.repr 1))).
  { repeat forward. all: (entailer!; bool_fin). }
  { exfalso. wordp. lia. }
  forward_call Int.one.
  forward_if (temp _t'4 (Vint (Int.repr 1))).
  { forward. forward.
    forward_if (temp _t'5 (Vint (Int.repr (if l_entry l + 1 =? Zlength (l_addresses l) then 1 else 0)))).
    { forward. entailer!. wordp. rewrite (proj2 (Z.eqb_eq _ _)) by lia. reflexivity. }
    { forward. entailer!. wordp. rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity. }
    forward. entailer!. destruct (l_entry l + 1 =? Zlength (l_addresses l)); reflexivity. }
  { exfalso. wordp. lia. }
  forward_call Int.one.
  forward_call tt. Intros v.
  forward. forward. forward.
  unfold vl. rewrite (upd_Znth_map (fun v => Vlong (Int64.repr v))).
  assert (Rv: u64_ok v) by auto.
  pose proof (run_snoc x h (Sequencing l cur) m _ (Word v) Hrun Ec (fits_word_seq _ _ _ _ _ _ v)) as Hr'.
  pose proof (seq_step_bytes x l cur m (Word v)) as (B1 & B2 & B3).
  destruct (Z_lt_ge_dec (Zlength cur) 2) as [Lt | Ge].
  - (* a word before the last *)
    forward_if (PROP (False) LOCAL () SEP ()).
    { forward. forward. forward.
      pose proof (J_seq_more x pl re te l cur m s v HJ Lt Rv) as HJ'.
      Exists v. unfold Ora_law.
      Exists (step x (Sequencing l cur) m (Word v))
        (set_word (set_answer s (upd_Znth (Zlength cur) (w_answer s) v)) (Zlength cur + 1)) re te.
      rewrite B1, B2, B3. thaw FR. unfold lfields. lst_cbn. unfold vi, vl.
      rewrite ?G1, ?T1, ?T5, ?T9. unfold E_SEQUENCE. entailer!. }
    { exfalso. wordp. lia. }
  - (* the last word *)
    assert (Lc2: Zlength cur = 2) by lia.
    match goal with |- semax _ ?Pre _ _ => forward_if Pre end.
    { exfalso. wordp. lia. }
    { forward. entailer!. }
    assert (Ea: upd_Znth (Zlength cur) (w_answer s) v = cur ++ [v] ++ sublist 3 5 (w_answer s))
      by (apply seq_answers; auto).
    rewrite Ea.
    assert (Fc: Forall u64_ok cur) by (rewrite <- G3; apply Forall_sublist; auto).
    assert (Z0: Znth 0 (cur ++ [v] ++ sublist 3 5 (w_answer s)) = Znth 0 (cur ++ [v])) by list_solve.
    assert (Z1: Znth 1 (cur ++ [v] ++ sublist 3 5 (w_answer s)) = Znth 1 (cur ++ [v])) by list_solve.
    assert (Z2: Znth 2 (cur ++ [v] ++ sublist 3 5 (w_answer s)) = Znth 2 (cur ++ [v])) by list_solve.
    assert (Fa: Forall u64_ok (cur ++ [v])) by (apply Forall_app; split; auto).
    assert (R0: 0 <= Znth 0 (cur ++ [v]) <= Int64.max_unsigned) by (apply (Forall_Znth' _ _ 0 Fa); list_solve).
    assert (R1: 0 <= Znth 1 (cur ++ [v]) <= Int64.max_unsigned) by (apply (Forall_Znth' _ _ 1 Fa); list_solve).
    assert (R2: 0 <= Znth 2 (cur ++ [v]) <= Int64.max_unsigned) by (apply (Forall_Znth' _ _ 2 Fa); list_solve).
    forward. rewrite Z0.
    forward_if (temp _t'7 (Vint (Int.repr (Z.b2z (negb (Znth 0 (cur ++ [v]) =? 1) || negb (Znth 1 (cur ++ [v]) =? 0)))))).
    { repeat forward. all: (entailer!; bool_fin). }
    { forward. rewrite Z1. forward. entailer!. bool_fin. }
    forward_if (temp _t'8 (Vint (Int.repr (Z.b2z (seq_bad l (cur ++ [v])))))).
    { forward. entailer!. try b2z_hyp. unfold seq_bad. rwb. reflexivity. }
    { forward. rewrite Z2. forward. forward. entailer!. try b2z_hyp. unfold seq_bad. rwb. cbn [orb]. bool_fin. }
    forward_if.
    + (* rejected *)
      try b2z_hyp.
      forward_call (gv _law, Vint (Int.repr 3), Vint (Int.repr (w_verdict s)), S_SEQUENCE).
      all: try (unfold u32_ok, S_SEQUENCE; rep_lia).
      pose proof (J_seq_reject x pl re te l cur m s v HJ Lc2 Rv ltac:(auto)) as HJ'. rewrite Ea in HJ'.
      forward. Exists v.
      unfold Ora_law. Exists (step x (Sequencing l cur) m (Word v))
        (s_stop (set_answer s (upd_Znth (Zlength cur) (w_answer s) v)) S_SEQUENCE) re te.
      rewrite B1, B2, B3. thaw FR. unfold lfields, s_stop. lst_cbn. rewrite Ea. unfold vi, vl.
      rewrite ?G1, ?G2, ?T1, ?T5, ?T9. unfold E_SEQUENCE. entailer!.
    + (* accepted *)
      try b2z_hyp.
      forward. rewrite Z2. forward.
      forward. forward.
      thaw FR.
      forward_if (PROP () LOCAL (temp _v (Vlong (Int64.repr v)))
                  SEP (Ora_law gv (gv _law) pl x
                         (h ++ [(Sequence (l_ordinal l) (Zlength (l_addresses l)) (l_entry l) 1
                                   (if l_entry l + 1 =? Zlength (l_addresses l) then 1 else 0) (Zlength cur + 1),
                                 Word v)]))).
      * (* the last table *)
        forward_call (gv _law, Vint (Int.repr 3), Vint (Int.repr (w_verdict s)), VERDICT_TABLES).
        all: try (unfold u32_ok, VERDICT_TABLES; rep_lia).
        assert (Ll: l_entry l + 1 = Zlength (l_addresses l)) by (addr; wordp; lia).
        pose proof (J_seq_last x pl re te l cur m s v HJ Lc2 Rv ltac:(auto) Ll) as HJ'. rewrite Ea in HJ'.
        unfold Ora_law. Exists (step x (Sequencing l cur) m (Word v))
          (s_stop (set_word_ordinal (set_answer s (upd_Znth (Zlength cur) (w_answer s) v)) (Znth 2 (cur ++ [v])))
             VERDICT_TABLES) re te.
        rewrite B1, B2, B3. unfold lfields, s_stop. lst_cbn. rewrite Ea. unfold vi, vl.
        rewrite ?G1, ?G2, ?T1, ?T5, ?T9. unfold E_SEQUENCE. entailer!.
      * (* the next table *)
        assert (Ll: l_entry l + 1 < Zlength (l_addresses l)) by (addr; wordp; lia).
        assert (Rcap: table_capacity x <= Int.max_unsigned) by (destruct Ix as (_ & _ & _ & _ & I5 & _); auto).
        forward.
        forward_call (gv _law, l_entry l + 1, w_arena s, table_capacity x, p_tables pl, te, w_addresses s, w_offsets s,
                      Vint (Int.repr (w_is_root s)), Vint (Int.repr (l_entry l)), Vlong (Int64.repr (w_sdt_address s)),
                      w_dest s, w_dexp s, Vint (Int.repr (w_capacity s)), Vlong (Int64.repr (w_cursor s)),
                      Vlong (Int64.repr (w_byte s)), Vint (Int.repr (Zlength cur)), Vint (Int.repr 3),
                      Vint (Int.repr (w_verdict s))).
        all: try (unfold u32_ok in *; repeat split; auto; rep_lia).
        pose proof (J_seq_next x pl re te l cur m s v HJ Lc2 Rv Ix ltac:(auto) Ll) as HJ'. rewrite Ea in HJ'.
        unfold Ora_law. Exists (step x (Sequencing l cur) m (Word v))
          (bt_state x pl te (set_word_ordinal (set_answer s (upd_Znth (Zlength cur) (w_answer s) v)) (Znth 2 (cur ++ [v])))
             (l_entry l + 1)) re te.
        rewrite B1, B2, B3.
        unfold bt_state in *.
        assert (Ew1: w_arena (set_word_ordinal (set_answer s (upd_Znth (Zlength cur) (w_answer s) v)) (Znth 2 (cur ++ [v])))
                     = w_arena s) by reflexivity.
        assert (Ew2: w_arena (set_word_ordinal (set_answer s (cur ++ [v] ++ sublist 3 5 (w_answer s))) (Znth 2 (cur ++ [v])))
                     = w_arena s) by reflexivity.
        rewrite Ew1. rewrite Ew2 in HJ'.
        destruct (table_capacity x <=? w_arena s) eqn:Eb.
        -- unfold s_stop in HJ'. unfold lfields, s_stop. lst_cbn. rewrite Ea. unfold vi, vl.
           rewrite ?G1, ?G2, ?T1, ?T5, ?T9. unfold E_SEQUENCE. entailer!.
        -- unfold lfields. lst_cbn. rewrite Ea. unfold vi, vl. rewrite ?G1, ?G2, ?T1, ?T5, ?T9. unfold E_SEQUENCE.
           entailer!.
      * forward. Exists v. entailer!.
Qed.
