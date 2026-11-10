(* The body proofs of the unit's functions, under the names the contract uses: one semax_body per function, in the
   unit's compspecs (Specs.CS) and context (Specs.Gprog).  The contract moves each into the law's program with
   QuickProof.Assembly.entry_shared.

   The statements are those of phase 1, unchanged.  The proofs: the helpers in BodyHelpers.v (wifi_le32,
   wifi_desc_limit) and BodyLookup.v (wifi_is_sink, wifi_has_desc); the admission in BodyAdmit.v
   (wifi_policy_within), BodyShape.v (wifi_service_admitted) and BodySource.v (wifi_source_admitted), with the
   policy object split around one descriptor in BodyPolicy.v; the header in HdHead.v and its tails HdTarget.v,
   HdV3.v, HdSinks.v, HdDescs.v and HdLoop.v (HdDefs.v, HdArith.v: the tails' statements, joins and arithmetic);
   wifi_start in BodyStart.v, with BodyVm.v (struct wifi_vm by fields) and BodyScratch.v (the scratch loop); the
   six wrappers in BodyWrap.v. *)
Require Import VST.floyd.proofauto.
Require Import LeanosDeviceProgramImage.device_program.code.
Require Import LeanosDeviceProgramImage.proof.Specs.
Require LeanosDeviceProgramImage.proof.BodyWrap.
Require LeanosDeviceProgramImage.proof.BodyHelpers.
Require LeanosDeviceProgramImage.proof.BodyLookup.
Require LeanosDeviceProgramImage.proof.BodyAdmit.
Require LeanosDeviceProgramImage.proof.BodyShape.
Require LeanosDeviceProgramImage.proof.BodySource.
Require LeanosDeviceProgramImage.proof.HdHead.
Require LeanosDeviceProgramImage.proof.BodyStart.
#[local] Existing Instance Specs.CS.

(* The helpers. *)
Lemma body_wifi_le32 : semax_body Vprog Gprog f_wifi_le32 le32_spec.
Proof. exact BodyHelpers.body_wifi_le32. Qed.
Lemma body_wifi_desc_limit : semax_body Vprog Gprog f_wifi_desc_limit desc_limit_spec.
Proof. exact BodyHelpers.body_wifi_desc_limit. Qed.
Lemma body_wifi_has_desc : semax_body Vprog Gprog f_wifi_has_desc has_desc_spec.
Proof. exact BodyLookup.body_wifi_has_desc. Qed.
Lemma body_wifi_is_sink : semax_body Vprog Gprog f_wifi_is_sink is_sink_spec.
Proof. exact BodyLookup.body_wifi_is_sink. Qed.

(* The admission. *)
Lemma body_wifi_policy_within : semax_body Vprog Gprog f_wifi_policy_within policy_within_spec.
Proof. exact BodyAdmit.body_wifi_policy_within. Qed.
Lemma body_wifi_service_admitted : semax_body Vprog Gprog f_wifi_service_admitted service_admitted_spec.
Proof. exact BodyShape.body_wifi_service_admitted. Qed.
Lemma body_wifi_source_admitted : semax_body Vprog Gprog f_wifi_source_admitted source_admitted_spec.
Proof. exact BodySource.body_wifi_source_admitted. Qed.

(* The parser. *)
Lemma body_wifi_image_header : semax_body Vprog Gprog f_wifi_image_header image_header_spec.
Proof. exact HdHead.body_wifi_image_header. Qed.
Lemma body_wifi_start : semax_body Vprog Gprog f_wifi_start wifi_start_spec.
Proof. exact BodyStart.body_wifi_start. Qed.

(* The wrappers (BodyWrap.v). *)
Lemma body_dp_header : semax_body Vprog Gprog f_dp_header dp_header_spec.
Proof. exact BodyWrap.body_dp_header. Qed.
Lemma body_dp_start : semax_body Vprog Gprog f_dp_start dp_start_spec.
Proof. exact BodyWrap.body_dp_start. Qed.
Lemma body_dp_within : semax_body Vprog Gprog f_dp_within dp_within_spec.
Proof. exact BodyWrap.body_dp_within. Qed.
Lemma body_dp_service : semax_body Vprog Gprog f_dp_service dp_service_spec.
Proof. exact BodyWrap.body_dp_service. Qed.
Lemma body_dp_source : semax_body Vprog Gprog f_dp_source dp_source_spec.
Proof. exact BodyWrap.body_dp_source. Qed.
Lemma body_dp_scratch : semax_body Vprog Gprog f_dp_scratch dp_scratch_spec.
Proof. exact BodyWrap.body_dp_scratch. Qed.
