(* The body proofs of the unit's functions, for every oracle predicate, under the names the contract uses: the
   contract's G lists Gprog at the law's oracle (the exports' specifications are those of the harness's functions
   of the same names; the decoder and the scrub are the harness's law_decode and law_scrub, through
   FrameSpecs.decode_spec and scrub_spec), and proves each body with entry_shared (body_X Ora_law).  Each is
   proved in an Fs*.v file: FsTerminal.v (boot_frame_terminal), FsSelect.v (boot_frame_select), FsChecks.v
   (boot_frame_cross_check, boot_frame_scrub_selected and boot_frame_publication_check), FsPublication.v
   (boot_frame_publication_result), FsRescan.v (boot_frame_rescan) and FsWrap.v (the seven wrappers); with the
   lemmas and tactics of FsLemmas.v and the faster LOCAL simplification of FsFast.v. *)
Require Import VST.floyd.proofauto.
Require Import LeanosFrameSelection.frame.code.
Require Import LeanosFrameSelection.proof.Defs.
Require Import LeanosFrameSelection.proof.FrameSpecs.
Require Import LeanosFrameSelection.proof.InternalSpecs.
Require LeanosFrameSelection.proof.FsTerminal LeanosFrameSelection.proof.FsSelect
        LeanosFrameSelection.proof.FsChecks LeanosFrameSelection.proof.FsPublication
        LeanosFrameSelection.proof.FsRescan LeanosFrameSelection.proof.FsWrap.
#[local] Existing Instance FrameSpecs.CS.

(* The header's functions. *)
Lemma body_boot_frame_terminal (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_boot_frame_terminal (boot_terminal_spec Ora).
Proof. exact (FsTerminal.body_boot_frame_terminal Ora). Qed.
Lemma body_boot_frame_select (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_boot_frame_select (boot_select_spec Ora).
Proof. exact (FsSelect.body_boot_frame_select Ora). Qed.
Lemma body_boot_frame_cross_check (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_boot_frame_cross_check (boot_cross_check_spec Ora).
Proof. exact (FsChecks.body_boot_frame_cross_check Ora). Qed.
Lemma body_boot_frame_scrub_selected (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_boot_frame_scrub_selected (boot_scrub_selected_spec Ora).
Proof. exact (FsChecks.body_boot_frame_scrub_selected Ora). Qed.
Lemma body_boot_frame_publication_result (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_boot_frame_publication_result (boot_publication_result_spec Ora).
Proof. exact (FsPublication.body_boot_frame_publication_result Ora). Qed.
Lemma body_boot_frame_publication_check (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_boot_frame_publication_check (boot_publication_check_spec Ora).
Proof. exact (FsChecks.body_boot_frame_publication_check Ora). Qed.
Lemma body_boot_frame_rescan (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_boot_frame_rescan (boot_rescan_spec Ora).
Proof. exact (FsRescan.body_boot_frame_rescan Ora). Qed.

(* The wrappers main calls. *)
Lemma body_frame_terminal (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_frame_terminal (frame_terminal_spec Ora).
Proof. exact (FsWrap.body_frame_terminal Ora). Qed.
Lemma body_frame_select (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_frame_select (frame_select_spec Ora).
Proof. exact (FsWrap.body_frame_select Ora). Qed.
Lemma body_frame_cross_check (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_frame_cross_check (frame_cross_check_spec Ora).
Proof. exact (FsWrap.body_frame_cross_check Ora). Qed.
Lemma body_frame_scrub_selected (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_frame_scrub_selected (frame_scrub_selected_spec Ora).
Proof. exact (FsWrap.body_frame_scrub_selected Ora). Qed.
Lemma body_frame_publication_result (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_frame_publication_result (frame_publication_result_spec Ora).
Proof. exact (FsWrap.body_frame_publication_result Ora). Qed.
Lemma body_frame_publication_check (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_frame_publication_check (frame_publication_check_spec Ora).
Proof. exact (FsWrap.body_frame_publication_check Ora). Qed.
Lemma body_frame_rescan (Ora: ORA) :
  semax_body Vprog (Gprog Ora) f_frame_rescan (frame_rescan_spec Ora).
Proof. exact (FsWrap.body_frame_rescan Ora). Qed.
