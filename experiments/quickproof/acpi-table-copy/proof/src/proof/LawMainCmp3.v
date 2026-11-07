(* Law table_copy_exact: main's comparisons of byte pointers (a copy's bytes, an arena from an offset on). *)
Require Import VST.floyd.proofauto.
Require Import LeanosAcpi.harness.table_copy_exact.code.
Require Import LeanosAcpi.proof.Defs LeanosAcpi.proof.AcpiSpecs LeanosAcpi.proof.LawProg LeanosAcpi.proof.LawMainCmp.
#[local] Existing Instance LawProg.LCS.
Local Open Scope Z_scope.

Lemma bytes_test_eq: forall sh n (v: reptype (tarray tuchar n)) p o P, readable_share sh -> 0 <= o <= n -> 0 < n ->
  P |-- data_at sh (tarray tuchar n) v p * TT -> P |-- denote_tc_test_eq (offset_val o p) (offset_val o p).
Proof.
  intros sh n v p o P Sh O N D.
  pose proof (arr_test_eq' sh tuchar n v p o P (readable_nonidentity Sh) ltac:(simpl; lia) O N D) as T.
  simpl sizeof in T. rewrite Z.mul_1_l in T. exact T.
Qed.

Lemma add_bytes: forall p o, isptr p -> 0 <= o <= Int.max_unsigned ->
  force_val (sem_add_ptr_int tuchar Unsigned p (Vint (Int.repr o))) = offset_val o p.
Proof.
  intros p o P O. destruct p; try contradiction.
  unfold sem_add_ptr_int. simpl. unfold offset_val. f_equal. f_equal.
  unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by auto. rewrite ptrofs_mul_repr. f_equal. lia.
Qed.

Lemma eval_add_bytes: forall p o, isptr p -> 0 <= o <= Int.max_unsigned ->
  eval_binop Oadd (tptr tuchar) tuint p (Vint (Int.repr o)) = offset_val o p.
Proof.
  intros p o P O. destruct p; try contradiction.
  unfold eval_binop, force_val2, sem_binary_operation'. simpl.
  unfold sem_add_ptr_int. simpl. unfold offset_val. f_equal. f_equal.
  unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by auto. rewrite ptrofs_mul_repr. f_equal. lia.
Qed.

Lemma cmp_bytes_same: forall q, isptr q ->
  force_val (sem_cast tint tbool (eval_binop Oeq (tptr tuchar) (tptr tuchar) q q)) = Vint (Int.repr 1).
Proof.
  intros q P. destruct q; try contradiction.
  unfold eval_binop, force_val2, sem_binary_operation'. simpl.
  rewrite cmp_same by exact P. reflexivity.
Qed.
