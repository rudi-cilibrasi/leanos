(* Law enumeration_exact: the pointers the harness computes as `array + index` (&d->seen[k],
   &snapshot.headers[k]), as VST's field addresses. *)
Require Import VST.floyd.proofauto.
Require Import LeanosEnum.harness.enumeration_exact.code.
Require Import LeanosEnum.proof.LawProg LeanosEnum.proof.LawSpecs.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Lemma seen_addr: forall ctx k, field_compatible t_device (DOT _seen) ctx -> 0 <= k < 16 ->
  force_val (sem_binary_operation' Oadd (tarray (Tstruct _pci_enumeration_header noattr) 16) tuint
     (eval_field (Tstruct _device noattr) _seen ctx) (Vint (Int.repr k))) =
  field_address t_device [ArraySubsc k; StructField _seen] ctx.
Proof.
  intros ctx k FC Hk.
  assert (FC': field_compatible t_device [ArraySubsc k; StructField _seen] ctx).
  { apply field_compatible_cons. simpl. split; [ lia | exact FC ]. }
  rewrite field_address_offset by exact FC'.
  destruct FC as [Pc _]. destruct ctx; try contradiction.
  unfold eval_field. simpl.
  f_equal. rewrite Ptrofs.add_assoc. f_equal.
  unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by rep_lia.
  rewrite ptrofs_mul_repr, ptrofs_add_repr. reflexivity.
Qed.

Lemma headers_addr: forall p k,
  field_compatible (Tstruct _pci_enumeration_snapshot noattr) (DOT _headers) p -> 0 <= k < 16 ->
  force_val (sem_binary_operation' Oadd (tarray (Tstruct _pci_enumeration_header noattr) 16) tuint
     (eval_field (Tstruct _pci_enumeration_snapshot noattr) _headers p) (Vint (Int.repr k))) =
  field_address (Tstruct _pci_enumeration_snapshot noattr) [ArraySubsc k; StructField _headers] p.
Proof.
  intros p k FC Hk.
  assert (FC': field_compatible (Tstruct _pci_enumeration_snapshot noattr) [ArraySubsc k; StructField _headers] p).
  { apply field_compatible_cons. simpl. split; [ lia | exact FC ]. }
  rewrite field_address_offset by exact FC'.
  destruct FC as [Pc _]. destruct p; try contradiction.
  unfold eval_field. simpl.
  f_equal. rewrite Ptrofs.add_assoc. f_equal.
  unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by rep_lia.
  rewrite ptrofs_mul_repr, ptrofs_add_repr. reflexivity.
Qed.
