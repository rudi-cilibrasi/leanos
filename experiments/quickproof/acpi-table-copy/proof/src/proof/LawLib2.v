(* Law table_copy_exact: more tactics the proofs of the harness's functions share. *)
Require Import VST.floyd.proofauto.
Require Import LeanosAcpi.proof.LawLib.
Local Open Scope Z_scope.

(* The boolean comparisons of the context as facts. *)
Ltac cmp_props :=
  repeat match goal with
  | E: (_ <? _) = true |- _ => apply Z.ltb_lt in E
  | E: (_ <? _) = false |- _ => apply Z.ltb_ge in E
  | E: (_ <=? _) = true |- _ => apply Z.leb_le in E
  | E: (_ <=? _) = false |- _ => apply Z.leb_gt in E
  | E: (_ =? _) = true |- _ => apply Z.eqb_eq in E
  | E: (_ =? _) = false |- _ => apply Z.eqb_neq in E
  end.

Ltac wordp := wordc; cmp_props.
