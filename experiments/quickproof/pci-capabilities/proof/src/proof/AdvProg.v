(* Law capabilities_adversarial: the compspecs of the whole program of the law (the harness linked with the caps
   unit, built exactly as src/contracts/capabilities_adversarial.v builds whole_prog), so that the harness's
   functions (device_read, named_pointer, main) are proved under the compspecs of the theorem itself. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require QuickProof.Link.
Require LeanosCaps.units.Caps.
Require LeanosCaps.harness.capabilities_adversarial.code.
Require LeanosCaps.proof.CapsSpecs.

Module Harness.
  #[local] Instance CS : compspecs. make_compspecs LeanosCaps.harness.capabilities_adversarial.code.prog. Defined.
  Definition qp := ltac:(QPprog LeanosCaps.harness.capabilities_adversarial.code.prog).
End Harness.

Definition law_prog := ltac:(QPlink_progs Harness.qp Caps.qp).
Definition law_comps := ltac:(let x := eval vm_compute in (prog_composites law_prog) in exact x).
Definition law_cprog : Clight.program := Clightdefs.mkprogram law_comps nil nil 1%positive Logic.I.
#[export] Instance LCS : compspecs. make_compspecs law_cprog. Defined.
#[export] Instance LCR : change_composite_env CapsSpecs.CS LCS. make_cs_preserve CapsSpecs.CS LCS. Defined.
