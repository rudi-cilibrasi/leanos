(* Law table_copy_exact: the compspecs of the whole program of the law (the harness linked with the acpi unit,
   built exactly as src/contracts/table_copy_exact.v builds whole_prog), so that the harness's functions are
   proved under the compspecs of the theorem itself. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require QuickProof.Link.
Require LeanosAcpi.units.Acpi.
Require LeanosAcpi.harness.table_copy_exact.code.
Require LeanosAcpi.proof.AcpiSpecs.

Module Harness.
  #[local] Instance CS : compspecs. make_compspecs LeanosAcpi.harness.table_copy_exact.code.prog. Defined.
  Definition qp := ltac:(QPprog LeanosAcpi.harness.table_copy_exact.code.prog).
End Harness.

Definition law_prog := ltac:(QPlink_progs Harness.qp Acpi.qp).
Definition law_comps := ltac:(let x := eval vm_compute in (prog_composites law_prog) in exact x).
Definition law_cprog : Clight.program := Clightdefs.mkprogram law_comps nil nil 1%positive Logic.I.
#[export] Instance LCS : compspecs. make_compspecs law_cprog. Defined.
#[export] Instance LCR : change_composite_env AcpiSpecs.CS LCS. make_cs_preserve AcpiSpecs.CS LCS. Defined.
