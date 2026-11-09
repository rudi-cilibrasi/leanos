(* Law table_copy_exact: main's pointer comparisons as VST leaves them (the copies array, at the law's compspecs). *)
Require Import VST.floyd.proofauto.
Require Import LeanosAcpi.harness.table_copy_exact.code.
Require Import LeanosAcpi.proof.Defs LeanosAcpi.proof.AcpiSpecs LeanosAcpi.proof.LawProg LeanosAcpi.proof.LawMainCmp.
#[local] Existing Instance LawProg.LCS.
Local Open Scope Z_scope.

Lemma cmp_ptr_same: forall t q, isptr q -> force_val (sem_cast tint tbool (eval_binop Oeq (tptr t) (tptr t) q q)) = vi 1.
Proof.
  intros t q P. destruct q; try contradiction.
  unfold eval_binop, force_val2, sem_binary_operation'. simpl.
  rewrite !andb_false_r. cbn [orb].
  unfold Val.cmplu_bool. destruct (eq_block b b); [ | congruence ]. simpl.
  rewrite cmp_same by exact P. reflexivity.
Qed.

Lemma copies_test_eq: forall (v: reptype (tarray (Tstruct _copied_acpi_sdt noattr) 256)) p i P, 0 <= i <= 256 ->
  P |-- data_at Tsh (tarray (Tstruct _copied_acpi_sdt noattr) 256) v p * TT ->
  P |-- denote_tc_test_eq (offset_val (SDT_BYTES * i) p) (offset_val (SDT_BYTES * i) p).
Proof.
  intros v p i P I D. replace SDT_BYTES with (sizeof (Tstruct _copied_acpi_sdt noattr)) by reflexivity.
  apply (arr_test_eq' Tsh (Tstruct _copied_acpi_sdt noattr) 256 v p i P);
    first [ apply top_share_nonidentity | exact D | (simpl; lia) | lia ].
Qed.

Lemma add_copies: forall p i, isptr p -> 0 <= i <= Int.max_unsigned ->
  force_val (sem_add_ptr_int (Tstruct _copied_acpi_sdt noattr) Unsigned p (vi i)) = offset_val (SDT_BYTES * i) p.
Proof.
  intros p i P I. destruct p; try contradiction.
  unfold sem_add_ptr_int. simpl. unfold offset_val. f_equal. f_equal.
  unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by auto. rewrite ptrofs_mul_repr. reflexivity.
Qed.
