(* The body of acpi_pipeline, the unit's wrapper: one call of acpi_copy_root_and_tables with the same arguments. *)
Require Import VST.floyd.proofauto.
Require Import LeanosAcpi.acpi.code.
Require Import LeanosAcpi.proof.Defs.
Require Import LeanosAcpi.proof.AcpiSpecs.
Require Import LeanosAcpi.proof.InternalSpecs.
#[local] Existing Instance AcpiSpecs.CS.
Local Open Scope Z_scope.

Lemma body_acpi_pipeline (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_acpi_pipeline (pipeline_spec Ora).
Proof.
  start_function.
  forward_call (gv, copy, ctx, x, pl, sh, sp, ssh, copies, osh, sold, res, rroot, rentries, rcount, rmadt).
  Intros vret. destruct vret as [[[h st] pub] m]. cbn [fst snd] in *.
  forward.
  Exists h st pub m. entailer!.
Qed.
