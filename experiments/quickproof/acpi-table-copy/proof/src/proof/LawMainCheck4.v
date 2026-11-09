(* Law table_copy_exact: main's last checks: the result's table count and MADT by the status, the first offset,
   and the law's records tiling the table arena. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosAcpi.harness.table_copy_exact.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawProg LeanosAcpi.proof.LawDefs LeanosAcpi.proof.LawFacts LeanosAcpi.proof.LawLib
  LeanosAcpi.proof.LawLib2 LeanosAcpi.proof.LawModel LeanosAcpi.proof.LawOra LeanosAcpi.proof.LawVerdict
  LeanosAcpi.proof.LawZero LeanosAcpi.proof.LawMainLib LeanosAcpi.proof.LawMainDefs LeanosAcpi.proof.LawMainPure
  LeanosAcpi.proof.LawMainModel LeanosAcpi.proof.LawMainCmp LeanosAcpi.proof.LawMainCmp2
  LeanosAcpi.proof.LawMainState.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

(* main's return: its locals freed. *)
Ltac main_return :=
  unfold t_slots', t_storage', t_result' in *;
  Exists (Int.repr 0);
  repeat match goal with
  | |- ?L |-- ?Q =>
      match L with context [data_at ?sh ?t ?v ?p] =>
        match Q with context [data_at_ sh t p] => sep_apply (data_at_data_at_ sh t v p) end end
  end;
  entailer!.

Ltac dead := exfalso; match goal with Hf: ?a <> ?a |- _ => exact (Hf eq_refl) end.

Lemma tail_status_check {Espec: OracleKind}: tail_ok s_status_check.
Proof.
  intros gv x pl re te s st pub mm mv v_copies v_storage v_result v_madt Delta Rp c -> -> ->.
  unfold s_status_check, check_pre. start_tail. Intros.
  match goal with H: J _ _ _ _ _ _ |- _ => rename H into HJ end.
  match goal with H: st = S_OK -> _ |- _ => rename H into HO end.
  pose proof HJ as (L & F & R & RI). cbn [mem_of] in F, R. pose proof RI as (RI1 & RI2 & RI3).
  destruct_lst_ok' L. unfold u32_ok, u64_ok in *.
  (* the status's range, and nothing published off OK *)
  assert (Sr: 0 <= st <= Int.max_unsigned /\ (st <> S_OK -> pub = None)).
  { destruct (Z.eq_dec (w_verdict s) VERDICT_TABLES) as [Hv | Hv].
    - destruct (RI2 Hv) as (_ & _ & _ & _ & C5 & C6). unfold select_madt in *.
      destruct (select_from (m_tables mm) (m_slots mm) 0 None) as [st' | i] eqn:Sel; cbn [stat] in C5; subst st.
      + pose proof (select_from_small _ _ _ _ _ Sel). split; [ rep_lia | auto ].
      + split; [ unfold S_OK; rep_lia | intros C; contradiction C; reflexivity ].
    - destruct (RI3 Hv) as (C1 & C2 & C3). split; [ subst st; lia | auto ]. }
  destruct Sr as [Sr Pn].
  unfold lfields. Intros.
  forward_if.
  - assert (Hn: st <> S_OK) by (unfold S_OK; exact H).
    rewrite (Pn Hn).
    change (result_val pl v_copies mm None zroot zentries (vi 0) nullval) with
      (match m_root_copy mm with Some sd => sdt_val (p_root pl) sd | None => zroot end,
       (match m_entries mm with Some (count, w) => entries_val (p_root pl) count w | None => zentries end,
        (vi 0, nullval))).
    forward.
    forward_if (temp _t'35 (vi 1)).
    + forward. forward. entailer!.
    + dead.
    + forward_call Int.one. forward. main_return.
  - assert (Ho: st = S_OK) by (unfold S_OK; lia).
    destruct (HO Ho) as (i & Pi & Mi). subst pub mv.
    assert (Hv: w_verdict s = VERDICT_TABLES).
    { destruct (Z.eq_dec (w_verdict s) VERDICT_TABLES) as [Hv | Hv]; [ exact Hv | ].
      destruct (RI3 Hv) as (_ & C & _). contradiction. }
    destruct (RI2 Hv) as (C1 & C2 & C3 & C4 & C5 & C6).
    assert (Si: select_madt mm = inr i).
    { destruct (select_madt mm) as [st' | j]; [ discriminate | injection C6 as E; subst; reflexivity ]. }
    pose proof (select_madt_range mm i Si) as Ri.
    pose proof (tile_at x s mm R C3 C4) as TA.
    destruct (TA 0 ltac:(lia)) as (_ & _ & _ & _ & _ & _ & O0). specialize (O0 eq_refl).
    unfold MAX_ENTRIES in *.
    change (result_val pl v_copies mm (Some (w_count s, i)) zroot zentries (vi 0) nullval) with
      (match m_root_copy mm with Some sd => sdt_val (p_root pl) sd | None => zroot end,
       (match m_entries mm with Some (count, w) => entries_val (p_root pl) count w | None => zentries end,
        (vi (w_count s), offset_val (SDT_BYTES * i) v_copies))).
    forward. forward.
    forward_if (temp _t'36 (vi 1)).
    + forward. forward. forward.
      { entailer!. rewrite add_copies by (auto; rep_lia). apply (copies_test_eq (slots_val pl mm (Zrepeat zsdt 256))); [ lia | unfold t_slots'; cancel ]. }
      entailer!. rewrite add_copies by (auto; rep_lia). rewrite if_true by reflexivity. reflexivity.
    + else_false.
    + forward_call Int.one.
      forward.
      forward_call Int.one. { entailer!. rewrite O0. reflexivity. }
      freeze_but2 [_table_capacity; _count; _offsets; _lengths; _finals] (@nil val) FR.
      forward.
      forward_loop
        (EX t: Z, PROP (0 <= t <= w_count s) LOCAL (temp _t__2 (vi t); temp _status (vi st); temp _m (gv _law); lvar _madt tuint v_madt; lvar _result t_result' v_result;
            lvar _storage t_storage' v_storage; lvar _copies t_slots' v_copies; gvars gv) SEP (FRZL FR; field_at Ews t_law (DOT _table_capacity) (vi (table_capacity x)) (gv _law);
          field_at Ews t_law (DOT _count) (vi (w_count s)) (gv _law);
          field_at Ews t_law (DOT _offsets) (map vi (w_offsets s)) (gv _law);
          field_at Ews t_law (DOT _lengths) (map vi (w_lengths s)) (gv _law);
          field_at Ews t_law (DOT _finals) (map vl (w_finals s)) (gv _law)))%assert
        continue:
        (EX t: Z, PROP (0 <= t < w_count s) LOCAL (temp _t__2 (vi t); temp _status (vi st); temp _m (gv _law); lvar _madt tuint v_madt; lvar _result t_result' v_result;
            lvar _storage t_storage' v_storage; lvar _copies t_slots' v_copies; gvars gv) SEP (FRZL FR; field_at Ews t_law (DOT _table_capacity) (vi (table_capacity x)) (gv _law);
          field_at Ews t_law (DOT _count) (vi (w_count s)) (gv _law);
          field_at Ews t_law (DOT _offsets) (map vi (w_offsets s)) (gv _law);
          field_at Ews t_law (DOT _lengths) (map vi (w_lengths s)) (gv _law);
          field_at Ews t_law (DOT _finals) (map vl (w_finals s)) (gv _law)))%assert
        break:
        (PROP () LOCAL (temp _status (vi st); temp _m (gv _law); lvar _madt tuint v_madt; lvar _result t_result' v_result;
            lvar _storage t_storage' v_storage; lvar _copies t_slots' v_copies; gvars gv) SEP (FRZL FR; field_at Ews t_law (DOT _table_capacity) (vi (table_capacity x)) (gv _law);
          field_at Ews t_law (DOT _count) (vi (w_count s)) (gv _law);
          field_at Ews t_law (DOT _offsets) (map vi (w_offsets s)) (gv _law);
          field_at Ews t_law (DOT _lengths) (map vi (w_lengths s)) (gv _law);
          field_at Ews t_law (DOT _finals) (map vl (w_finals s)) (gv _law))).
      { Exists 0. entailer!. }
      { Intros t. forward. forward_if.
        2: { forward. entailer!. }
        wordp.
        destruct (TA t ltac:(lia)) as (A1 & A2 & A3 & A4 & A5 & A6 & _).
        forward.
        forward_call (Znth t (w_lengths s)). { split; [ unfold HEADER_BYTES in A6; lia | lia ]. }
        forward. forward. forward.
        set (o := Znth t (w_offsets s)) in *. set (ln := Znth t (w_lengths s)) in *.
        pose proof (padded_range ln ltac:(unfold HEADER_BYTES in A6; lia)) as (P1 & P2).
        assert (Eb: 0 <= o + padded ln <= Int.max_unsigned) by (match goal with I: inputs_ok x |- _ =>
          pose proof I as (_ & _ & _ & _ & I5 & _) end; lia).
        rewrite (Int.unsigned_repr o) by rep_lia. rewrite (Int.unsigned_repr (padded ln)) by rep_lia.
        rewrite add64_repr'.
        forward_if (temp _t'38 (vi 1)).
        + forward. forward. entailer!. wordp.
          match goal with I: inputs_ok x |- _ => pose proof I as (_ & _ & _ & _ & I5 & _) end.
          specialize (A3 ltac:(lia)). bool_fin.
        + rewrite ?add32_repr' in *. wordp. assert (Ti: 0 <= t + 1 < Zlength (w_offsets s)) by lia.
          forward.
          forward. entailer!.
          specialize (A2 ltac:(lia)). rewrite ?Znth_map by lia. fold o ln. rewrite A2. bool_fin.
        + forward_call Int.one.
          forward.
          forward_call Int.one.
          { entailer!.
            assert (Fb: 0 <= Znth t (w_finals s) <= Int64.max_unsigned) by (apply (Forall_Znth' _ _ t L28); lia).
            rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia.
            rewrite Int.unsigned_repr_eq. change Int.modulus with (2 ^ 32). rewrite A1. rewrite Int64.eq_true.
            reflexivity. }
          Exists t. entailer!. }
      { Intros t. forward. Exists (t + 1). entailer!. }
      forward. thaw FR. main_return.
Qed.
