(* The body proofs of the unit's functions, for every device predicate, under the names the contracts use.
   The proofs are in CollectProof.v. *)
Require Import VST.floyd.proofauto.
Require Import LeanosCaps.caps.code.
Require Import LeanosCaps.proof.Defs.
Require Import LeanosCaps.proof.CapsSpecs.
Require LeanosCaps.proof.CollectProof.
#[local] Existing Instance CapsSpecs.CS.

Lemma body_pci_capability_finish (Dev: val -> Z * Z * Z -> list answer -> mpred) :
  semax_body Vprog (Gprog Dev) f_pci_capability_finish finish_spec.
Proof. exact (CollectProof.body_pci_capability_finish Dev). Qed.
Lemma body_pci_collect_capabilities (Dev: val -> Z * Z * Z -> list answer -> mpred) :
  semax_body Vprog (Gprog Dev) f_pci_collect_capabilities (collect_spec Dev).
Proof. exact (CollectProof.body_pci_collect_capabilities Dev). Qed.
Lemma body_caps_collect (Dev: val -> Z * Z * Z -> list answer -> mpred) :
  semax_body Vprog (Gprog Dev) f_caps_collect (caps_collect_spec Dev).
Proof. exact (CollectProof.body_caps_collect Dev). Qed.
