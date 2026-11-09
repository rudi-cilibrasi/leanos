(* The body proofs of the unit's functions, for every device predicate, under the names the contracts use.
   The proofs are in ScanProof.v. *)
Require Import VST.floyd.proofauto.
Require Import LeanosEnum.enum.code.
Require Import LeanosEnum.proof.Defs.
Require Import LeanosEnum.proof.EnumSpecs.
Require LeanosEnum.proof.ScanProof.
#[local] Existing Instance EnumSpecs.CS.

Lemma body_pci_enumeration_finish (Dev: val -> list answer -> mpred) :
  semax_body Vprog (Gprog Dev) f_pci_enumeration_finish finish_spec.
Proof. exact (ScanProof.body_pci_enumeration_finish Dev). Qed.
Lemma body_pci_enumerate_segment (Dev: val -> list answer -> mpred) :
  semax_body Vprog (Gprog Dev) f_pci_enumerate_segment (enum_spec Dev).
Proof. exact (ScanProof.body_pci_enumerate_segment Dev). Qed.
Lemma body_enum_scan (Dev: val -> list answer -> mpred) :
  semax_body Vprog (Gprog Dev) f_enum_scan (enum_scan_spec Dev).
Proof. exact (ScanProof.body_enum_scan Dev). Qed.
