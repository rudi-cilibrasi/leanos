(* Law table_copy_exact: main from the call of acpi_pipeline to its check of the header scratch: the law's oracle
   handed over, the call, the expected verdict (madt_verdict on VERDICT_TABLES), the status check. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosAcpi.harness.table_copy_exact.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawProg LeanosAcpi.proof.LawDefs LeanosAcpi.proof.LawFacts LeanosAcpi.proof.LawLib
  LeanosAcpi.proof.LawLib2 LeanosAcpi.proof.LawModel LeanosAcpi.proof.LawOra LeanosAcpi.proof.LawVerdict
  LeanosAcpi.proof.LawZero LeanosAcpi.proof.LawMainLib LeanosAcpi.proof.LawMainDefs LeanosAcpi.proof.LawMainPure
  LeanosAcpi.proof.LawMainModel LeanosAcpi.proof.LawMainState LeanosAcpi.proof.LawMainCheck1.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Lemma tail_call {Espec: OracleKind} (TR: tail_ok s_root_check) gv x pl re te s v_copies v_storage v_result v_madt:
  inputs_ok x -> J x pl re te (start x) s ->
  isptr (p_header pl) -> isptr (p_root pl) -> isptr (p_tables pl) -> isptr re -> isptr te ->
  forall Delta Rp c, Delta = Delta0 -> Rp = Post0 -> c = s_call ->
  semax Delta (call_pre gv x pl re te s v_copies v_storage v_result v_madt) c Rp.
Proof.
  intros Ix HJ Pph Ppr Ppt Pre Pte Delta Rp c -> -> ->.
  unfold s_call, call_pre. start_tail.
  make_func_ptr _firmware_copy.
  assert (OI: (lfields (gv _law) x pl re te (i_header x) s *
               data_at Ews (tarray tuchar (root_capacity x)) (bytes_val (i_root x)) re *
               data_at Ews (tarray tuchar (table_capacity x)) (bytes_val (i_tables x)) te)%logic
              |-- Ora_law gv (gv _law) pl x nil).
  { pose proof (ora_intro gv pl x nil (start x) s re te Ix eq_refl HJ Pph Ppr Ppt Pre Pte) as O.
    rewrite mem_of_start in O. exact O. }
  unfold lfields in OI |- *. Intros. forward. forward.
  sep_apply OI. clear OI.
  rewrite (data_at_tuchar_cs LCS AcpiSpecs.CS Ews 36), (data_at_tuchar_cs LCS AcpiSpecs.CS Ews (root_capacity x)),
    (data_at_tuchar_cs LCS AcpiSpecs.CS Ews (table_capacity x)).
  rewrite storage_cs, result_cs, slots_cs.
  unfold sl1, sl2, sl3.
  forward_call (gv, gv _firmware_copy, gv _law, x, pl, Ews, v_storage, Tsh, v_copies, Tsh, Zrepeat zsdt 256,
                v_result, zroot, zentries, vi 0, nullval).
  Intros vret. destruct vret as [[[h st] pub] mm]. cbn [fst snd] in *.
  forward.
  unfold Ora_law. Intros p s' re' te'.
  match goal with H: pipeline x h = Some _ |- _ => rename H into Hp end.
  match goal with H: run x (start x) h = Some p |- _ => rename H into Hrun end.
  assert (Ep: p = Return st pub mm).
  { unfold pipeline in Hp. rewrite Hrun in Hp. destruct p as [g mg | st' pub' mg]; [ discriminate | ].
    inversion Hp; subst; reflexivity. }
  subst p. cbn [mem_of].
  match goal with H: J x pl re' te' (Return st pub mm) s' |- _ => rename H into HJ' end.
  pose proof HJ' as (L & F & R & RI). cbn [mem_of] in F, R. pose proof RI as (RI1 & RI2 & RI3).
  pose proof (pipeline_published x h st pub mm Hp) as PP.
  rewrite <- !(data_at_tuchar_cs LCS AcpiSpecs.CS). rewrite <- storage_cs, <- result_cs, <- slots_cs.
  unfold lfields. Intros.
  freeze_but2 [_expect; _verdict; _count; _tables_expect; _offsets; _lengths] [te'; v_madt] FR.
  unfold vi, vl.
  forward. forward_call Int.one. { rewrite RI1. entailer!. }
  forward.
  forward.
  forward_if (EX mv: val,
    PROP (st = S_OK -> exists i, pub = Some (w_count s', i) /\ mv = vi i)
    LOCAL (temp _t'17 (vi st); temp _status (Vint (Int.repr st)); temp _m (gv _law); lvar _madt tuint v_madt;
           lvar _result t_result' v_result; lvar _storage t_storage' v_storage; lvar _copies t_slots' v_copies;
           gvars gv)
    SEP (FRZL FR; field_at Ews t_law (DOT _expect) (Vint (Int.repr (w_expect s'))) (gv _law);
         field_at Ews t_law (DOT _verdict) (Vint (Int.repr (w_verdict s'))) (gv _law);
         field_at Ews t_law (DOT _count) (Vint (Int.repr (w_count s'))) (gv _law);
         field_at Ews t_law (DOT _tables_expect) te' (gv _law);
         field_at Ews t_law (DOT _offsets) (map vi (w_offsets s')) (gv _law);
         field_at Ews t_law (DOT _lengths) (map vi (w_lengths s')) (gv _law);
         data_at Ews (tarray tuchar (table_capacity x)) (bytes_val (m_tables mm)) te';
         data_at Tsh tuint mv v_madt))%assert.
  - (* every table was copied: the MADT selection *)
    destruct_lst_ok' L. unfold u32_ok, u64_ok in L2.
    wordp. match goal with E: w_verdict s' = 255 |- _ => rename E into Hv end.
    destruct (RI2 Hv) as (C1 & C2 & C3 & C4 & C5 & C6).
    rewrite C1.
    forward_call (gv _law, te', m_tables mm, table_capacity x, m_slots mm, w_offsets s', w_lengths s', v_madt,
                  Vint (Int.repr 0)).
    { pose proof (verdict_slots x s' mm R C3 C4) as VS.
      destruct F as (F1 & F2 & F3 & F4 & F5 & F6). destruct Ix as (_ & _ & _ & _ & I5 & _).
      repeat split; auto; try (rewrite <- C1; unfold MAX_ENTRIES in *; lia);
      match goal with t: Z, Ht: 0 <= ?t < Zlength (m_slots mm) |- _ =>
        destruct (VS t Ht) as (V1 & V2 & V3 & V4 & V5); first [ exact V1 | exact V2 | lia ] end. }
    Intros mv. forward.
    Exists mv. entailer!.
    + unfold select_madt in *.
      destruct (select_from (m_tables mm) (m_slots mm) 0 None) as [st' | i] eqn:Sel.
      * exfalso. apply (select_from_inl _ _ _ _ _ Sel). auto.
      * exists i. split; [ reflexivity | auto ].
    + rewrite C1. apply derives_refl.
  - (* the verdict *)
    destruct_lst_ok' L. unfold u32_ok, u64_ok in L2.
    wordp. match goal with E: w_verdict s' <> 255 |- _ => rename E into Hv end.
    destruct (RI3 Hv) as (C1 & C2 & C3).
    forward. forward.
    Exists (Vint (Int.repr 0)). entailer!.
    all: try (split; [ intros; contradiction | rewrite C1; reflexivity ]).
  - Intros mv. forward.
    forward_call Int.one.
    { entailer!. simpl. rewrite Int.eq_true. reflexivity. }
    thaw FR. pose proof (run_eok x h st pub mm Hrun) as EO.
    eapply semax_pre;
      [ | apply (tail_bytes_check TR gv x pl re' te' s' st pub mm mv v_copies v_storage v_result v_madt);
          first [ reflexivity | assumption ] ].
    unfold check_pre, lfields. unfold vi, vl. entailer!.
Qed.
