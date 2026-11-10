(* Law image_exact: the body of the law's read_image. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import LeanosDeviceProgramImage.harness.image_exact.code.
Require Import LeanosDeviceProgramImage.proof.Defs.
Require Import LeanosDeviceProgramImage.proof.LawProg LeanosDeviceProgramImage.proof.LawSpecs
  LeanosDeviceProgramImage.proof.LawLib LeanosDeviceProgramImage.proof.LawSplit
  LeanosDeviceProgramImage.proof.LawReadDefs LeanosDeviceProgramImage.proof.LawReadTail
  LeanosDeviceProgramImage.proof.LawReadV23.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Lemma body_read_image : semax_body Vlaw Glaw f_read_image read_image_spec.
Proof.
  start_function.
  pose proof H as IM. destruct H as [Hlen F].
  forward.
  match goal with |- context [temp _p (offset_val ?e r)] => replace e with 32 by (vm_compute; reflexivity) end.
  assert_PROP (field_compatible t_law_image nil r) as FCr by entailer!.
  rewrite data_at__eq, li_default_eq. unfold li_default. rewrite ri_rep_eq by auto. unfold ri_rep, pol_fields. Intros.
  forward. forward.
  forward_if (temp _t'1 (Vint (Int.repr (Z.b2z ((Zlength bs <? 16) || negb (le32 bs 0 =? MAGIC)))))).
  { forward. entailer!. bfix. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
  { bfix. forward_call (sh, b, bs, 0).
    forward. entailer!. bfix.
    assert (W0: u32_ok (le32 bs 0)) by (apply le32_range; auto).
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. simpl orb.
    unfold MAGIC. rewrite <- (Int_eq_u32 (le32 bs 0) 1179211596) by (auto; unfold u32_ok; rep_lia).
    destruct (Int.eq _ _); reflexivity. }
  forward_if.
  { bfix. ri_ret FCr.

    assert (D: decode bs = None).
    { apply dec_bad_head. destruct (Z.ltb_spec (Zlength bs) 16); [ left; auto | right ].
      destruct (Z.eqb_spec (le32 bs 0) MAGIC); simpl in *; congruence. }
    unfold reading_ok, header_status, start_status, start. rewrite D. auto. }
  assert (HD: hd_ok bs).
  { apply orb_false_iff in H as [H1 H2]. apply Z.ltb_ge in H1. apply negb_false_iff, Z.eqb_eq in H2. split; auto. }
  pose proof HD as [HD1 HD2]. forward_call (sh, b, bs, 4).
  forward. forward. forward. forward. forward. forward. forward. forward. forward.
  forward.
  forward_if (ri_join sh b bs wsh r).
  - forward. forward. forward. forward. forward. forward.
    Exists bcm_target no_policy 16 (Zrepeat Vundef 8) (Zrepeat udesc 16).
    unfold ri_rep, pol_fields. entailer!.
    assert (W4: u32_ok (le32 bs 4)) by (apply le32_range; auto).
    bfix. apply dec_v1; auto.
  - eapply semax_pre; [ | apply ri_v23; auto ].
    unfold ri_pre23, ri_rep, pol_fields. entailer!.
  - apply ri_tail; auto.
Qed.
