(* The body proofs of the unit's functions, for every oracle predicate, under the names the contract uses: the
   contract's G lists Gprog at the law's oracle (the exports' specifications are those of the harness's
   functions of the same names; the read and the record are the harness's bootloader_read and
   projection_record, through HandoffSpecs.read_spec and record_spec), and proves each body with
   entry_shared (body_X Ora_law).  Each is proved in an Hd*.v file: HdExtent.v (boot_handoff_extent), HdCopy.v
   (boot_handoff_stream_copy), HdReset.v (boot_decode_reset), HdTransition.v (boot_decode_transition),
   HdProjection.v (boot_handoff_decode_projection), HdCandidate.v (boot_handoff_decode_candidate), HdProject.v
   (boot_handoff_project) and HdWrap.v (the five wrappers); with the lemmas of HdLemmas.v and HdStates.v and the
   faster LOCAL simplification of HdFast.v. *)
Require Import VST.floyd.proofauto.
Require Import LeanosHandoff.handoff.code.
Require Import LeanosHandoff.proof.Defs.
Require Import LeanosHandoff.proof.HandoffSpecs.
Require Import LeanosHandoff.proof.InternalSpecs.
Require LeanosHandoff.proof.HdExtent LeanosHandoff.proof.HdCopy LeanosHandoff.proof.HdReset
        LeanosHandoff.proof.HdTransition LeanosHandoff.proof.HdProjection LeanosHandoff.proof.HdCandidate
        LeanosHandoff.proof.HdProject LeanosHandoff.proof.HdWrap.
#[local] Existing Instance HandoffSpecs.CS.

(* The header's functions. *)
Lemma body_boot_handoff_extent (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_boot_handoff_extent (boot_extent_spec Ora).
Proof. exact (HdExtent.body_boot_handoff_extent Ora). Qed.
Lemma body_boot_handoff_stream_copy (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_boot_handoff_stream_copy (stream_copy_spec Ora).
Proof. exact (HdCopy.body_boot_handoff_stream_copy Ora). Qed.
Lemma body_boot_decode_reset (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_boot_decode_reset (decode_reset_spec Ora).
Proof. exact (HdReset.body_boot_decode_reset Ora). Qed.
Lemma body_boot_decode_transition (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_boot_decode_transition (decode_transition_spec Ora).
Proof. exact (HdTransition.body_boot_decode_transition Ora). Qed.
Lemma body_boot_handoff_decode_projection (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_boot_handoff_decode_projection (decode_projection_spec Ora).
Proof. exact (HdProjection.body_boot_handoff_decode_projection Ora). Qed.
Lemma body_boot_handoff_decode_candidate (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_boot_handoff_decode_candidate (boot_candidate_spec Ora).
Proof. exact (HdCandidate.body_boot_handoff_decode_candidate Ora). Qed.
Lemma body_boot_handoff_project (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_boot_handoff_project (boot_project_spec Ora).
Proof. exact (HdProject.body_boot_handoff_project Ora). Qed.

(* The wrappers main calls. *)
Lemma body_handoff_extent (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_handoff_extent (extent_spec Ora).
Proof. exact (HdWrap.body_handoff_extent Ora). Qed.
Lemma body_handoff_copy (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_handoff_copy (copy_spec Ora).
Proof. exact (HdWrap.body_handoff_copy Ora). Qed.
Lemma body_handoff_projection (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_handoff_projection (projection_spec Ora).
Proof. exact (HdWrap.body_handoff_projection Ora). Qed.
Lemma body_handoff_candidate (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_handoff_candidate (candidate_spec Ora).
Proof. exact (HdWrap.body_handoff_candidate Ora). Qed.
Lemma body_handoff_project (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_handoff_project (project_spec Ora).
Proof. exact (HdWrap.body_handoff_project Ora). Qed.
