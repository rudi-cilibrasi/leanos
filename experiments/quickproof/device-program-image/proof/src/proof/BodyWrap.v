(* The body proofs of the six wrappers of patch/device_program_unit.c: each forwards its arguments to the function
   of wifi-exec.h with the same specification (dp_scratch returns the address of wifi_scratch). *)
Require Import VST.floyd.proofauto.
Require Import LeanosDeviceProgramImage.device_program.code.
Require Import LeanosDeviceProgramImage.proof.Specs.
#[local] Existing Instance Specs.CS.

Lemma body_dp_scratch : semax_body Vprog Gprog f_dp_scratch dp_scratch_spec.
Proof. start_function. forward. Qed.

Lemma body_dp_header : semax_body Vprog Gprog f_dp_header dp_header_spec.
Proof.
  start_function.
  forward_call (sh, image, bs, tsh, tp, psh, pp, P0, hsh, hp).
  Intros vret. destruct vret as [[tv pv] hv]. simpl fst in *; simpl snd in *.
  forward.
  Exists tv pv hv. entailer!.
Qed.

Lemma body_dp_start : semax_body Vprog Gprog f_dp_start dp_start_spec.
Proof.
  start_function.
  forward_call (gv, sh, image, bs, wsh, vmp, V0, ssh, sc).
  Intros vret. destruct vret as [vv sc']. simpl fst in *; simpl snd in *.
  forward.
  Exists vv sc'. entailer!.
Qed.

Lemma body_dp_within : semax_body Vprog Gprog f_dp_within dp_within_spec.
Proof. start_function. forward_call (psh, pp, P, msh, mp, M). forward. Qed.

Lemma body_dp_service : semax_body Vprog Gprog f_dp_service dp_service_spec.
Proof.
  start_function. forward_call (tsh, tp, T, psh, pp, P, wsh, wp, W, msh, mp, M). forward.
Qed.

Lemma body_dp_source : semax_body Vprog Gprog f_dp_source dp_source_spec.
Proof. start_function. forward_call (tsh, tp, T, psh, pp, P, msh, mp, M). forward. Qed.
