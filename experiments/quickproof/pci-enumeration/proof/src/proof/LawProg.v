(* Law enumeration_exact: the compspecs of the whole program of the law (the harness linked with the enum unit,
   built exactly as src/contracts/enumeration_exact.v builds whole_prog), so that the harness's functions
   (device_read, main) are proved under the compspecs of the theorem itself. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require QuickProof.Link.
Require LeanosEnum.units.Enum.
Require LeanosEnum.harness.enumeration_exact.code.
Require LeanosEnum.proof.EnumSpecs.

Module Harness.
  #[local] Instance CS : compspecs. make_compspecs LeanosEnum.harness.enumeration_exact.code.prog. Defined.
  Definition qp := ltac:(QPprog LeanosEnum.harness.enumeration_exact.code.prog).
End Harness.

Definition law_prog := ltac:(QPlink_progs Harness.qp Enum.qp).
Definition law_comps := ltac:(let x := eval vm_compute in (prog_composites law_prog) in exact x).
Definition law_cprog : Clight.program := Clightdefs.mkprogram law_comps nil nil 1%positive Logic.I.
#[export] Instance LCS : compspecs. make_compspecs law_cprog. Defined.
#[export] Instance LCR : change_composite_env EnumSpecs.CS LCS. make_cs_preserve EnumSpecs.CS LCS. Defined.
