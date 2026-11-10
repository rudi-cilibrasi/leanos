(* The body of wifi_image_header: the length and magic test, the version, the policy's scalars zeroed, the
   version-1 return; from the version-2/3 test on, HdTarget (then HdV3, HdSinks, HdDescs, HdLoop). *)
Require Import VST.floyd.proofauto.
Require Import LeanosDeviceProgramImage.device_program.code.
Require Import LeanosDeviceProgramImage.proof.Specs.
Require Import LeanosDeviceProgramImage.proof.BodyHelpers.
Require Import LeanosDeviceProgramImage.proof.BodyLookup.
Require Import LeanosDeviceProgramImage.proof.BodyPolicy.
Require Import LeanosDeviceProgramImage.proof.BodyAdmit.
Require Import LeanosDeviceProgramImage.proof.HdDefs.
Require Import LeanosDeviceProgramImage.proof.HdTarget.
#[local] Existing Instance Specs.CS.
Local Open Scope Z_scope.

Lemma body_wifi_image_header : semax_body Vprog Gprog f_wifi_image_header image_header_spec.
Proof.
  start_function.
  rename H into IOK, H0 into PW.
  pose proof IOK as (LB & U8).
  assert_PROP (field_compatible (tarray tuchar (Zlength bs)) [] image) as FCi by entailer!.
  assert (PI: isptr image) by (destruct FCi; auto).
  assert (W: forall k, u32_ok (le32 bs k)) by (intros; apply le32_range; auto).
  pose proof (Zlength_nonneg bs) as L0.
  assert (Wr: forall k, 0 <= le32 bs k <= Int.max_unsigned) by (intros; apply W).
  rewrite !data_at__eq.
  assert_PROP (field_compatible t_policy [] pp) as FCp by entailer!.
  fif_t _t'1 (Vint (Int.repr (Z.b2z ((Zlength bs <? 16) || negb (le32 bs 0 =? MAGIC))%bool))).
  { forward. entailer!. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
  { forward_call (sh, image, bs, 0). forward. entailer!.
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [orb]. cmp_join. }
  forward_if.
  { assert (D: decode bs = None) by (unfold decode; cbv zeta; destruct ((Zlength bs <? 16) || negb (le32 bs 0 =? MAGIC))%bool; [ reflexivity | discriminate ]).
    hd_bad D. }
  rename H into C0. bprop. rename H into C0a, H0 into C0b.
  forward_call (sh, image, bs, 4).
  rewrite (policy_val_eq P0), pol_fields by auto. Intros.
  do 9 forward.
  fif_p (le32 bs 4 <> 1).
  { (* version 1 *)
    do 7 forward.
    repr_facts Wr.
    assert (D: decode bs = Some (bcm_target, no_policy, 16)) by dec_solve.
    hd_ret.
    unfold header_post, header_status. rewrite D. rewrite pol_store_none by auto.
    split; [ repeat split; reflexivity | reflexivity ]. }
  { forward. entailer!. }
  Intros. rename H into C1.
  eapply semax_pre; [ | apply (hd_target sh image bs tsh tp psh pp P0 hsh hp); first [ reflexivity | assumption ] ].
  entailer!.
Qed.
