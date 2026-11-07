(* The body proofs of the unit's functions, for every oracle predicate, under the names the contract uses: the
   contract's G lists Gprog at the law's oracle, and proves each body with entry_shared (body_X Ora_law).
   This file re-exports the proofs: EnvelopeProof.v, EntriesProof.v, ResultProof.v and AdmissionProof.v (the
   header's functions, lemmas in BodyLemmas.v) and WrapperProofs.v (the wrappers main calls). *)
Require Import VST.floyd.proofauto.
Require Import LeanosMadtAdmission.madt_admission.code.
Require Import LeanosMadtAdmission.proof.Defs.
Require Import LeanosMadtAdmission.proof.MgaSpecs.
Require Import LeanosMadtAdmission.proof.InternalSpecs.
Require LeanosMadtAdmission.proof.EnvelopeProof.
Require LeanosMadtAdmission.proof.EntriesProof.
Require LeanosMadtAdmission.proof.ResultProof.
Require LeanosMadtAdmission.proof.AdmissionProof.
Require LeanosMadtAdmission.proof.WrapperProofs.
#[local] Existing Instance MgaSpecs.CS.

(* The header's functions. *)
Lemma body_madt_generated_envelope (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_madt_generated_envelope (generated_envelope_spec Ora).
Proof. exact (EnvelopeProof.body_madt_generated_envelope Ora). Qed.
Lemma body_madt_generated_entries (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_madt_generated_entries (generated_entries_spec Ora).
Proof. exact (EntriesProof.body_madt_generated_entries Ora). Qed.
Lemma body_madt_topology_admission_result (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_madt_topology_admission_result (topology_result_spec Ora).
Proof. exact (ResultProof.body_madt_topology_admission_result Ora). Qed.
Lemma body_madt_generated_admission (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_madt_generated_admission (generated_admission_spec Ora).
Proof. exact (AdmissionProof.body_madt_generated_admission Ora). Qed.

(* The wrappers main calls. *)
Lemma body_madt_envelope (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_madt_envelope (envelope_spec Ora).
Proof. exact (WrapperProofs.body_madt_envelope Ora). Qed.
Lemma body_madt_entries (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_madt_entries (entries_spec Ora).
Proof. exact (WrapperProofs.body_madt_entries Ora). Qed.
Lemma body_madt_result (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_madt_result (result_spec Ora).
Proof. exact (WrapperProofs.body_madt_result Ora). Qed.
Lemma body_madt_admission (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_madt_admission (admission_spec Ora).
Proof. exact (WrapperProofs.body_madt_admission Ora). Qed.
