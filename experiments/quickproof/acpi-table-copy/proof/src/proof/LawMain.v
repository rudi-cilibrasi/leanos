(* Law table_copy_exact: the body of the harness's main, up to its nondet_bytes of the header scratch; the rest is
   the tail lemmas (LawMainBytes, ...). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosAcpi.harness.table_copy_exact.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.LawProg LeanosAcpi.proof.LawDefs LeanosAcpi.proof.LawFacts LeanosAcpi.proof.LawLib
  LeanosAcpi.proof.LawLib2 LeanosAcpi.proof.LawOra LeanosAcpi.proof.LawZero LeanosAcpi.proof.LawMainLib
  LeanosAcpi.proof.LawMainDefs LeanosAcpi.proof.LawMainState LeanosAcpi.proof.LawMainBytes.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Lemma law_glob: forall gv, headptr (gv _law) ->
  globvar2pred gv (_law, v_law) |-- (lfields (gv _law) x0 pl0 nullval nullval hx0 s0 * TT)%logic.
Proof.
  intros gv [b H]. unfold globvar2pred. simpl. rewrite sepcon_emp. rewrite H.
  assert (FC: field_compatible t_law nil (Vptr b Ptrofs.zero)).
  { apply headptr_field_compatible; try (exists b; reflexivity);
      first [ reflexivity | exact I | (vm_compute; reflexivity) | (apply la_env_cs_sound; reflexivity) ]. }
  exact (law_zero b FC).
Qed.

(* Freeze every SEP item but mem_mgr, the results of malloc and the law's fields in L. *)
Ltac keep_main x L :=
  lazymatch x with
  | field_at _ _ (StructField ?f :: nil) _ _ => lazymatch L with context [f] => constr:(true) | _ => constr:(false) end
  | mem_mgr _ => constr:(true)
  | mres _ _ => constr:(true)
  | _ => constr:(false)
  end.
Ltac idx_main R L i :=
  lazymatch R with
  | nil => constr:(@nil Z)
  | ?x :: ?R' =>
      let rest := idx_main R' L (Z.succ i) in
      let k := keep_main x L in
      lazymatch k with true => rest | false => let i' := eval cbn in i in constr:(i' :: rest) end
  end.
Ltac freeze_main L F :=
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    let I := idx_main R L 0 in freeze_tac I F
  end.

Lemma body_main (TR: forall Espec: OracleKind, @tail_ok Espec s_root_check): forall p, QPprog_vars p = main_vars -> semax_body Vmain Gmain f_main (_main, main_spec_std p).
Proof.
  intros p Hp. start_function. rewrite Hp.
  assert_PROP (headptr (gv _law) /\ headptr (gv sl1) /\ headptr (gv sl2) /\ headptr (gv sl3)) as HP by entailer!.
  destruct HP as (H1 & H2 & H3 & H4).
  unfold globvars2pred, main_vars. simpl map. cbn [fold_right].
  sep_apply (lit_xsdt gv H3). sep_apply (lit_apic gv H2). sep_apply (lit_rsdt gv H4). sep_apply (law_glob gv H1).
  sep_apply (create_mem_mgr gv).
  unfold lfields. Intros.
  freeze_main [_kind; _address; _root_capacity; _table_capacity; _header; _root; _tables; _root_expect; _tables_expect] FR.
  forward.
  forward_call tt. Intros k. forward.
  forward_call tt. Intros ad. forward.
  forward_call tt. Intros rc. forward.
  forward_call tt. Intros tc. forward.
  forward_call (tarray tuchar 36, gv). { simpl. rep_lia. }
  Intros ph. change (if eq_dec ph nullval then emp else _) with (mres (tarray tuchar 36) ph). forward.
  forward. forward_call (tarray tuchar rc, gv). { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros pr. change (if eq_dec pr nullval then emp else _) with (mres (tarray tuchar rc) pr). forward.
  forward. forward_call (tarray tuchar tc, gv). { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros pt. change (if eq_dec pt nullval then emp else _) with (mres (tarray tuchar tc) pt). forward.
  forward. forward_call (tarray tuchar rc, gv). { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros re. change (if eq_dec re nullval then emp else _) with (mres (tarray tuchar rc) re). forward.
  forward. forward_call (tarray tuchar tc, gv). { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros te. change (if eq_dec te nullval then emp else _) with (mres (tarray tuchar tc) te). forward.
  assert_PROP (is_pointer_or_null ph) as Nph by (unfold mres; destruct (eq_dec ph nullval); entailer!).
  assert_PROP (is_pointer_or_null pr) as Npr by (unfold mres; destruct (eq_dec pr nullval); entailer!).
  assert_PROP (is_pointer_or_null pt) as Npt by (unfold mres; destruct (eq_dec pt nullval); entailer!).
  assert_PROP (is_pointer_or_null re) as Nre by (unfold mres; destruct (eq_dec re nullval); entailer!).
  assert_PROP (is_pointer_or_null te) as Nte by (unfold mres; destruct (eq_dec te nullval); entailer!).
  forward.
  forward_if (temp _t'10 (Vint (Int.repr (Z.b2z (isnul ph || isnul pr))))).
  { apply (mres_tc' (tarray tuchar 36) ph _ TT). cancel. }
  { forward. entailer!. }
  { forward. forward.
    { entailer!. apply (mres_tc' (tarray tuchar rc) pr _ TT). cancel. }
    entailer!. rewrite null_test2 by auto. rewrite (isnul_false ph) by auto. reflexivity. }
  forward_if (temp _t'11 (Vint (Int.repr (Z.b2z (isnul ph || isnul pr || isnul pt))))).
  { try b2z_hyp. forward. entailer!. rw_bools. reflexivity. }
  { try b2z_hyp. forward. forward.
    { entailer!. apply (mres_tc' (tarray tuchar tc) pt _ TT). cancel. }
    entailer!. rewrite null_test2 by auto. rw_bools. reflexivity. }
  forward_if (temp _t'12 (Vint (Int.repr (Z.b2z (isnul ph || isnul pr || isnul pt || isnul re))))).
  { try b2z_hyp. forward. entailer!. rw_bools. reflexivity. }
  { try b2z_hyp. forward. forward.
    { entailer!. apply (mres_tc' (tarray tuchar rc) re _ TT). cancel. }
    entailer!. rewrite null_test2 by auto. rw_bools. reflexivity. }
  forward_if (temp _t'13 (Vint (Int.repr (Z.b2z (isnul ph || isnul pr || isnul pt || isnul re || isnul te))))).
  { try b2z_hyp. forward. entailer!. rw_bools. reflexivity. }
  { try b2z_hyp. forward. forward.
    { entailer!. apply (mres_tc' (tarray tuchar tc) te _ TT). cancel. }
    entailer!. rewrite null_test2 by auto. rw_bools. reflexivity. }
  forward_if (PROP ((isnul ph || isnul pr || isnul pt || isnul re || isnul te)%bool = false)
              LOCAL (temp _m (gv _law); lvar _madt tuint v_madt;
                     lvar _result (Tstruct _acpi_table_copy_result noattr) v_result;
                     lvar _storage (Tstruct _acpi_table_copy_storage noattr) v_storage;
                     lvar _copies (tarray (Tstruct _copied_acpi_sdt noattr) 256) v_copies; gvars gv)
              SEP (mem_mgr gv; mres (tarray tuchar tc) te; mres (tarray tuchar rc) re; mres (tarray tuchar tc) pt;
                   mres (tarray tuchar rc) pr; mres (tarray tuchar 36) ph; FRZL FR;
                   field_at Ews t_law (DOT _kind) (vl k) (gv _law); field_at Ews t_law (DOT _address) (vl ad) (gv _law);
                   field_at Ews t_law (DOT _header) ph (gv _law); field_at Ews t_law (DOT _root) pr (gv _law);
                   field_at Ews t_law (DOT _tables) pt (gv _law);
                   field_at Ews t_law (DOT _root_capacity) (Vint (Int.repr rc)) (gv _law);
                   field_at Ews t_law (DOT _table_capacity) (Vint (Int.repr tc)) (gv _law);
                   field_at Ews t_law (DOT _root_expect) re (gv _law);
                   field_at Ews t_law (DOT _tables_expect) te (gv _law))).
  { rewrite (FRZL_ax FR). unfold FR, abbreviate. simpl fold_right_sepcon. Intros.
    forward. Exists (Int.repr 0). entailer!. }
  { try b2z_hyp. forward. entailer!. }
  Intros. repeat rewrite orb_false_iff in H7. destruct H7 as [[[[Eh Er] Et] Ee] Ex].
  rewrite (mres_ptr _ ph Eh), (mres_ptr _ pr Er), (mres_ptr _ pt Et), (mres_ptr _ re Ee), (mres_ptr _ te Ex).
  Intros. thaw FR.
  assert_PROP (isptr ph /\ isptr pr /\ isptr pt /\ isptr re /\ isptr te) as PP by entailer!.
  destruct PP as (Pph & Ppr & Ppt & Pre & Pte).
  eapply semax_pre;
    [ | apply (tail_bytes (TR _) gv k ad rc tc ph pr pt re te v_copies v_storage v_result v_madt);
        first [ reflexivity | assumption | auto ] ].
  unfold lfields2. entailer!.
Qed.
