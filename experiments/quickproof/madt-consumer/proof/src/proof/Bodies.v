(* The body proofs of the unit's functions, for every oracle predicate, under the names the contracts use: a
   re-export of BindProof.v (the consumer's proof against the model of Defs.v, with its lemmas in BindLemmas.v). *)
Require Import VST.floyd.proofauto.
Require Import LeanosMadt.madt.code.
Require Import LeanosMadt.proof.Defs.
Require Import LeanosMadt.proof.MadtSpecs.
Require LeanosMadt.proof.BindProof.
#[local] Existing Instance MadtSpecs.CS.

Lemma body_qotom_bsp_publish (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_qotom_bsp_publish publish_spec.
Proof. exact (BindProof.body_qotom_bsp_publish Ora). Qed.
Lemma body_qotom_bind_validated_madt_entries (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_qotom_bind_validated_madt_entries (bind_spec Ora).
Proof. exact (BindProof.body_qotom_bind_validated_madt_entries Ora). Qed.
Lemma body_madt_bind (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_madt_bind (madt_bind_spec Ora).
Proof. exact (BindProof.body_madt_bind Ora). Qed.
