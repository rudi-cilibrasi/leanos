(* Law table_copy_exact: main's checks of the result's root and entries against the law's record. *)
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
  LeanosAcpi.proof.LawMainCmp3 LeanosAcpi.proof.LawMainState.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

(* A comparison of equal words, decided. *)
Ltac eqc := entailer!; try (rewrite ?repr_mod32, ?loword_repr, ?Int.eq_true; reflexivity).

Lemma tail_root_check {Espec: OracleKind} (TS: tail_ok s_slots_check): tail_ok s_root_check.
Proof.
  intros gv x pl re te s st pub mm mv v_copies v_storage v_result v_madt Delta Rp c -> -> ->.
  unfold s_root_check, check_pre. start_tail. Intros.
  match goal with H: J _ _ _ _ _ _ |- _ => rename H into HJ end.
  match goal with H: eok _ _ |- _ => rename H into EO end.
  pose proof HJ as (L & F & R & RI). cbn [mem_of] in F, R. pose proof F as (F1 & F2 & F3 & F4 & F5 & F6).
  pose proof R as (R1 & R2 & R3 & R4 & R5). pose proof EO as [E1 E2].
  destruct_lst_ok' L. unfold u32_ok, u64_ok in *.
  match goal with I: inputs_ok x |- _ => pose proof I as (I1 & I2 & _ & I4 & I5 & _) end.
  unfold u64_ok in I1, I2.
  unfold lfields. Intros.
  assert_PROP (isptr (p_root pl)) as Ppr by entailer!.
  unfold result_val, zroot, zentries.
  (* the result's root *)
  forward.
  forward_if (temp _t'77 (vi (w_root_done s))).
  - destruct (m_root_copy mm) as [sd | ] eqn:Erc; [ | rewrite R1 in *; else_false ].
    destruct R1 as [Rd Esd]. subst sd.
    assert (Cap: HEADER_BYTES <= root_capacity x) by (apply E1; left; first [ discriminate | rewrite Erc; discriminate ]).
    unfold sdt_val; cbn [s_address s_offset s_length s_next].
    forward. forward.
    forward_if (temp _t'19 (vi 1)).
    + forward. forward. forward.
      { entailer!. rewrite ?isptr_offset_val_zero by auto.
        apply (arr_test_eq0 Ews tuchar (root_capacity x) (bytes_val (m_root mm)) (p_root pl));
          [ apply readable_nonidentity, writable_readable, writable_Ews | simpl; lia
          | unfold HEADER_BYTES in Cap; lia | cancel ]. }
      entailer!. rewrite ?isptr_offset_val_zero by auto.
      first [ rewrite cmp_ptr_same by auto; reflexivity | rewrite if_true by reflexivity; reflexivity ].
    + else_false.
    + forward_if (temp _t'20 (vi 1)).
      * forward. forward. forward. eqc.
      * else_false.
      * forward_if (temp _t'21 (vi 1)).
        -- forward. forward. forward. eqc.
        -- else_false.
        -- forward_call Int.one. entailer!.
  - destruct (m_root_copy mm) as [sd | ] eqn:Erc; [ destruct R1 as [Rd _]; rewrite Rd in *; else_false | ].
    forward.
    forward_if (temp _t'22 (vi 1)).
    + forward. forward. eqc.
    + else_false.
    + forward_if (temp _t'23 (vi 1)).
      * forward. forward. eqc.
      * else_false.
      * forward_if (temp _t'24 (vi 1)).
        -- forward. forward. eqc.
        -- else_false.
        -- forward_call Int.one. entailer!.
  - (* the result's entries *)
    forward.
    forward_if (temp _t'67 (vi (w_entries_done s))).
    + destruct (m_entries mm) as [[cnt w] | ] eqn:Een; [ | rewrite R2 in *; else_false ].
      destruct R2 as (Ed & Ec & Ew). subst cnt w.
      assert (Cap: HEADER_BYTES <= root_capacity x) by (apply E1; right; first [ discriminate | rewrite Een; discriminate ]).
      unfold entries_val. forward. forward.
      forward_if (temp _t'25 (vi 1)).
      { entailer!. rewrite ?add_bytes by (auto; rep_lia). unfold HEADER_BYTES.
        apply (bytes_test_eq Ews (root_capacity x) (bytes_val (m_root mm)) (p_root pl));
          [ apply writable_readable, writable_Ews | unfold HEADER_BYTES in Cap; lia | unfold HEADER_BYTES in Cap; lia
          | cancel ]. }
      * forward. forward. forward. eqc.
      * exfalso.
        match goal with
        | Hf: offset_val _ _ <> _ |- _ => rewrite add_bytes in Hf by (auto; rep_lia); apply Hf; reflexivity
        end.
      * forward_if (temp _t'26 (vi 1)).
        -- forward. forward. forward. eqc.
        -- else_false.
        -- forward_call Int.one. entailer!.
    + destruct (m_entries mm) as [[cnt w] | ] eqn:Een; [ destruct R2 as (Ed & _); rewrite Ed in *; else_false | ].
      forward.
      forward_if (temp _t'27 (vi 1)).
      * forward. forward. eqc.
      * else_false.
      * forward_if (temp _t'28 (vi 1)).
        -- forward. forward. eqc.
        -- else_false.
        -- forward_call Int.one. entailer!.
    + eapply semax_pre;
        [ | apply (TS gv x pl re te s st pub mm mv v_copies v_storage v_result v_madt);
            first [ reflexivity | assumption ] ].
      unfold check_pre, lfields, result_val, zroot, zentries. unfold vi, vl. entailer!.
Qed.
