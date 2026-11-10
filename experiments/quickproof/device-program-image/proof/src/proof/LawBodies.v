(* Law image_exact: the body proofs of the harness's functions and of main, under the law's compspecs
   (LawProg.LCS) and context (LawSpecs.Glaw).  The contract moves each into the law's program with
   QuickProof.Assembly.entry_shared (main through semax_body_main_std).

   PHASE 1: the statements are final; the bodies are proved in phase 2 (src/proof/NOTES.md lists the
   obligations).  Each Admitted below is to be replaced by `exact <File>.body_<f>.` of a phase-2 file. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env QuickProof.Assembly.
Require Import LeanosDeviceProgramImage.harness.image_exact.code.
Require LeanosDeviceProgramImage.device_program.code.
Require Import LeanosDeviceProgramImage.proof.Defs.
Require Import LeanosDeviceProgramImage.proof.LawProg LeanosDeviceProgramImage.proof.LawSpecs.
Require LeanosDeviceProgramImage.proof.LawSmall LeanosDeviceProgramImage.proof.LawPol
  LeanosDeviceProgramImage.proof.LawCheck LeanosDeviceProgramImage.proof.LawCheckPol
  LeanosDeviceProgramImage.proof.LawRead LeanosDeviceProgramImage.proof.LawCase
  LeanosDeviceProgramImage.proof.LawAdm LeanosDeviceProgramImage.proof.LawMain
  LeanosDeviceProgramImage.proof.LawStart.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

(* The global variables of the law's program, as main_spec_std's globvars2pred lists them. *)
Definition law_vars : list (ident * globvar type) :=
  [(_wifi_scratch, LeanosDeviceProgramImage.device_program.code.v_wifi_scratch); (_law, v_law)].

Lemma law_prog_vars : QPprog_vars law_prog = law_vars.
Proof. vm_compute. reflexivity. Qed.

Lemma body_word_at : semax_body Vlaw Glaw f_word_at word_at_spec.
Proof. exact LeanosDeviceProgramImage.proof.LawSmall.body_word_at. Qed.
Lemma body_read_image : semax_body Vlaw Glaw f_read_image read_image_spec.
Proof. exact LeanosDeviceProgramImage.proof.LawRead.body_read_image. Qed.
Lemma body_any_target : semax_body Vlaw Glaw f_any_target any_target_spec.
Proof. exact LeanosDeviceProgramImage.proof.LawSmall.body_any_target. Qed.
Lemma body_any_u64 : semax_body Vlaw Glaw f_any_u64 any_u64_spec.
Proof. exact LeanosDeviceProgramImage.proof.LawSmall.body_any_u64. Qed.
Lemma body_any_policy : semax_body Vlaw Glaw f_any_policy any_policy_spec.
Proof. exact LeanosDeviceProgramImage.proof.LawPol.body_any_policy. Qed.
Lemma body_copy_policy : semax_body Vlaw Glaw f_copy_policy copy_policy_spec.
Proof. exact LeanosDeviceProgramImage.proof.LawPol.body_copy_policy. Qed.
Lemma body_same_target : semax_body Vlaw Glaw f_same_target same_target_spec.
Proof. exact LeanosDeviceProgramImage.proof.LawSmall.body_same_target. Qed.
Lemma body_same_desc : semax_body Vlaw Glaw f_same_desc same_desc_spec.
Proof. exact LeanosDeviceProgramImage.proof.LawSmall.body_same_desc. Qed.
Lemma body_check_policy : semax_body Vlaw Glaw f_check_policy check_policy_spec.
Proof. exact LeanosDeviceProgramImage.proof.LawCheckPol.body_check_policy. Qed.
Lemma body_declares_sink : semax_body Vlaw Glaw f_declares_sink declares_sink_spec.
Proof. exact LeanosDeviceProgramImage.proof.LawCheck.body_declares_sink. Qed.
Lemma body_declares_desc : semax_body Vlaw Glaw f_declares_desc declares_desc_spec.
Proof. exact LeanosDeviceProgramImage.proof.LawCheck.body_declares_desc. Qed.
Lemma body_within : semax_body Vlaw Glaw f_within law_within_spec.
Proof. exact LeanosDeviceProgramImage.proof.LawCheck.body_within. Qed.
Lemma body_header_case : semax_body Vlaw Glaw f_header_case header_case_spec.
Proof. exact LeanosDeviceProgramImage.proof.LawCase.body_header_case. Qed.
Lemma body_start_case : semax_body Vlaw Glaw f_start_case start_case_spec.
Proof. exact LeanosDeviceProgramImage.proof.LawStart.body_start_case. Qed.
Lemma body_admission_case : semax_body Vlaw Glaw f_admission_case admission_case_spec.
Proof. exact LeanosDeviceProgramImage.proof.LawAdm.body_admission_case. Qed.

(* main, for any program with the law's global variables (the contract instantiates p with whole_prog). *)
Lemma body_main : forall p, QPprog_vars p = law_vars -> semax_body Vlaw Glaw f_main (_main, main_spec_std p).
Proof. intros p Hp. apply LeanosDeviceProgramImage.proof.LawMain.body_main. rewrite Hp. reflexivity. Qed.
