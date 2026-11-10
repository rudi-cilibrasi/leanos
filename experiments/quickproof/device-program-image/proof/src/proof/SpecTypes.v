(* Sanity checks of the phase-1 statements (no Admitted): every specification has the C type of its function
   (semax_body requires it, and an Admitted body would hide a mismatch), and the law's contexts are without
   repetition. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Env QuickProof.Assembly.
Require LeanosDeviceProgramImage.device_program.code LeanosDeviceProgramImage.harness.image_exact.code.
Require LeanosDeviceProgramImage.proof.Specs LeanosDeviceProgramImage.proof.LawSpecs.
Module U := LeanosDeviceProgramImage.device_program.code.
Module H := LeanosDeviceProgramImage.harness.image_exact.code.
Module S := LeanosDeviceProgramImage.proof.Specs.
Module L := LeanosDeviceProgramImage.proof.LawSpecs.

Definition ty_ok (spec: ident * funspec) (f: function) : Prop :=
  typesig_of_funspec (snd spec) = (map snd (fn_params f), fn_return f) /\
  callingconvention_of_funspec (snd spec) = fn_callconv f.

Ltac ty := split; reflexivity.

Lemma ty_unit:
  ty_ok S.le32_spec U.f_wifi_le32 /\ ty_ok S.desc_limit_spec U.f_wifi_desc_limit /\
  ty_ok S.has_desc_spec U.f_wifi_has_desc /\ ty_ok S.is_sink_spec U.f_wifi_is_sink /\
  ty_ok S.policy_within_spec U.f_wifi_policy_within /\ ty_ok S.service_admitted_spec U.f_wifi_service_admitted /\
  ty_ok S.source_admitted_spec U.f_wifi_source_admitted /\ ty_ok S.image_header_spec U.f_wifi_image_header /\
  ty_ok S.wifi_start_spec U.f_wifi_start /\ ty_ok S.dp_header_spec U.f_dp_header /\
  ty_ok S.dp_start_spec U.f_dp_start /\ ty_ok S.dp_within_spec U.f_dp_within /\
  ty_ok S.dp_service_spec U.f_dp_service /\ ty_ok S.dp_source_spec U.f_dp_source /\
  ty_ok S.dp_scratch_spec U.f_dp_scratch.
Proof. repeat split; reflexivity. Qed.

Lemma ty_law:
  ty_ok L.word_at_spec H.f_word_at /\ ty_ok L.read_image_spec H.f_read_image /\
  ty_ok L.any_target_spec H.f_any_target /\ ty_ok L.any_u64_spec H.f_any_u64 /\
  ty_ok L.any_policy_spec H.f_any_policy /\ ty_ok L.copy_policy_spec H.f_copy_policy /\
  ty_ok L.same_target_spec H.f_same_target /\ ty_ok L.same_desc_spec H.f_same_desc /\
  ty_ok L.check_policy_spec H.f_check_policy /\ ty_ok L.declares_sink_spec H.f_declares_sink /\
  ty_ok L.declares_desc_spec H.f_declares_desc /\ ty_ok L.law_within_spec H.f_within /\
  ty_ok L.header_case_spec H.f_header_case /\ ty_ok L.start_case_spec H.f_start_case /\
  ty_ok L.admission_case_spec H.f_admission_case.
Proof. repeat split; reflexivity. Qed.

Lemma norepet_unit: compute_list_norepet (map fst S.Vprog ++ map fst S.Gprog) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma norepet_law: compute_list_norepet (map fst L.Vlaw ++ map fst L.Glaw) = true.
Proof. vm_compute. reflexivity. Qed.
