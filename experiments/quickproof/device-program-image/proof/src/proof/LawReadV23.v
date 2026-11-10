(* Law image_exact: read_image for versions other than 1: the version, length and target checks, the target, and
   (LawReadV3) the version-3 policy. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import LeanosDeviceProgramImage.harness.image_exact.code.
Require Import LeanosDeviceProgramImage.proof.Defs.
Require Import LeanosDeviceProgramImage.proof.LawProg LeanosDeviceProgramImage.proof.LawSpecs
  LeanosDeviceProgramImage.proof.LawLib LeanosDeviceProgramImage.proof.LawSplit
  LeanosDeviceProgramImage.proof.LawFacts LeanosDeviceProgramImage.proof.LawReadDefs
  LeanosDeviceProgramImage.proof.LawReadV3.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Local Opaque Z.shiftr Z.land.

Ltac iops := rewrite ?shru_u32, ?and_u32, ?modu_u32 in * by (first [ assumption | unfold u32_ok in *; rep_lia ]).

Lemma ri_v23 {Espec: OracleKind}: forall sh b bs wsh r,
  readable_share sh -> writable_share wsh -> image_ok bs -> field_compatible t_law_image nil r ->
  semax ri_delta (ri_pre23 sh b bs wsh r) s_v23 (overridePost (ri_join sh b bs wsh r) (ri_post sh b bs wsh r)).
Proof.
  intros sh b bs wsh r SH WSH IM FCr.
  start_part. unfold ri_pre23. Intros.
  rename H into HD, H0 into V1. pose proof IM as [Hlen F]. pose proof HD as [HD1 HD2].
  assert (Wv: u32_ok (le32 bs 4)) by (apply le32_range; auto).
  unfold ri_rep, pol_fields. Intros.
  forward_if (temp _t'4 (Vint (Int.repr (Z.b2z (negb (le32 bs 4 =? 2) && negb (le32 bs 4 =? 3)))))).
  { forward. entailer!. bfix. bdec. }
  { forward. entailer!. bfix. bdec. }
  forward_if.
  { bfix. ri_ret FCr.
    apply andb_true_iff in H as [A B]. apply negb_true_iff, Z.eqb_neq in A. apply negb_true_iff, Z.eqb_neq in B.
    assert (D: decode bs = None) by (apply dec_bad_version; auto).
    unfold reading_ok, header_status, start_status, start. rewrite D. auto. }
  assert (V23: le32 bs 4 = 2 \/ le32 bs 4 = 3).
  { bfix. apply andb_false_iff in H as [A|A]; apply negb_false_iff, Z.eqb_eq in A; auto. }
  clear H.
  forward_if (temp _t'5 (Vint (Int.repr (if le32 bs 4 =? 2 then 32 else 68)))).
  { forward. entailer!. bfix. destruct (Z.eqb_spec (le32 bs 4) 2); [ reflexivity | congruence ]. }
  { forward. entailer!. bfix. destruct (Z.eqb_spec (le32 bs 4) 2); [ congruence | reflexivity ]. }
  set (L := if le32 bs 4 =? 2 then 32 else 68) in *.
  assert (HL: L = 32 \/ L = 68) by (unfold L; destruct (le32 bs 4 =? 2); auto).
  forward_if.
  { try rewrite !Int.unsigned_repr in H by (destruct HL; rep_lia). ri_ret FCr.
    assert (D: decode bs = None) by (apply dec_short23; auto).
    unfold reading_ok, header_status, start_status, start. rewrite D. auto. }
  try rewrite !Int.unsigned_repr in H by (destruct HL; rep_lia).
  assert (L32: 32 <= Zlength bs) by (destruct HL; lia).
  assert (V23ok: v23_ok bs) by (split; [ auto | split; [ auto | unfold L in H; lia ] ]).
  clear H.
  forward_call (sh, b, bs, 16).
  forward_call (sh, b, bs, 24).
  forward_call (sh, b, bs, 28).
  assert (W: forall k, u32_ok (le32 bs k)) by (intros; apply le32_range; auto).
  pose proof (W 16) as W16. pose proof (W 24) as W24. pose proof (W 28) as W28.
  set (bdf := le32 bs 16) in *. set (w := le32 bs 24) in *. set (w28 := le32 bs 28) in *.
  assert (WB: u32_ok (bar_of w28)) by (unfold bar_of; destruct (w28 =? 0); auto; unfold u32_ok; rep_lia).
  forward_if (temp _bar (Vint (Int.repr (bar_of w28)))).
  { forward. entailer!. bfix. unfold bar_of. destruct (Z.eqb_spec w28 0); [ reflexivity | congruence ]. }
  { forward. entailer!. bfix. unfold bar_of. destruct (Z.eqb_spec w28 0); [ congruence | reflexivity ]. }
  assert (S24: u32_ok (Z.shiftr bdf 24)) by (apply shiftr_u32; unfold u32_ok in *; lia).
  assert (S13: u32_ok (Z.shiftr bdf 13)) by (apply shiftr_u32; unfold u32_ok in *; lia).
  assert (S3: u32_ok (Z.shiftr bdf 3)) by (apply shiftr_u32; unfold u32_ok in *; lia).
  assert (A13: u32_ok (Z.land (Z.shiftr bdf 13) 7)) by (apply land_u32; unfold u32_ok in *; lia).
  assert (A3: u32_ok (Z.land (Z.shiftr bdf 3) 31)) by (apply land_u32; unfold u32_ok in *; lia).
  forward_if (temp _t'9 (Vint (Int.repr (Z.b2z (negb (Z.shiftr bdf 24 =? 0) ||
                                                negb (Z.land (Z.shiftr bdf 13) 7 =? 0))%bool)))).
  { forward. entailer!. iops. bfix. bdec. }
  { forward. entailer!. iops. bfix. bdec. }
  forward_if (temp _t'10 (Vint (Int.repr (Z.b2z (negb (bdf_ok bdf)))))).
  { forward. entailer!. rewrite <- bdf_law by (unfold u32_ok in *; rep_lia). bfix. bdec. }
  { forward. entailer!. rewrite <- bdf_law by (unfold u32_ok in *; rep_lia). iops. bfix. bdec. }
  forward_if.
  { bfix. ri_ret FCr.
    assert (D: decode bs = None).
    { apply dec_bad_target; auto. rewrite target_ok_eq. fold bdf. bsplit. rewrite H. reflexivity. }
    unfold reading_ok, header_status, start_status, start. rewrite D. auto. }
  bfix. bsplit. rename H into BDF.
  forward_if (temp _t'11 (Vint (Int.repr (Z.b2z ((bar_of w28 <? 16) || (36 <? bar_of w28))%bool)))).
  { forward. entailer!. bfix. bdec. }
  { forward. entailer!. bfix. bdec. }
  assert (M4: u32_ok (bar_of w28 mod 4)) by (pose proof (Z.mod_pos_bound (bar_of w28) 4); unfold u32_ok; rep_lia).
  forward_if (temp _t'12 (Vint (Int.repr (Z.b2z (negb (bar_ok (bar_of w28))))))).
  { forward. entailer!. rewrite <- bar_law. bfix. bdec. }
  { forward. entailer!. rewrite <- bar_law. iops. bfix. bdec. }
  forward_if.
  { bfix. ri_ret FCr.
    assert (D: decode bs = None).
    { apply dec_bad_target; auto. rewrite target_ok_eq. fold bdf w28. bsplit. rewrite BDF, H. reflexivity. }
    unfold reading_ok, header_status, start_status, start. rewrite D. auto. }
  bfix. bsplit. rename H into BAR.
  forward_if (temp _t'13 (Vint (Int.repr (Z.b2z ((w =? 0) || (65536 <? w))%bool)))).
  { forward. entailer!. bfix. bdec. }
  { forward. entailer!. bfix. bdec. }
  assert (M512: u32_ok (w mod 512)) by (pose proof (Z.mod_pos_bound w 512); unfold u32_ok; rep_lia).
  forward_if (temp _t'14 (Vint (Int.repr (Z.b2z (negb (window_ok w)))))).
  { forward. entailer!. rewrite <- window_law. bfix. bdec. }
  { forward. entailer!. rewrite <- window_law. iops. bfix. bdec. }
  forward_if.
  { bfix. ri_ret FCr.
    assert (D: decode bs = None).
    { apply dec_bad_target; auto. rewrite target_ok_eq. fold bdf w w28. bsplit. rewrite BDF, BAR, H.
      reflexivity. }
    unfold reading_ok, header_status, start_status, start. rewrite D. auto. }
  bfix. bsplit. rename H into WIN.
  assert (TOK: target_ok bs = true) by (rewrite target_ok_eq; fold bdf w w28; rewrite BDF, BAR, WIN; reflexivity).
  unfold tg_undef.
  forward. forward. forward.
  forward_call (sh, b, bs, 20). forward.
  forward. forward. forward.
  assert (S16: u32_ok (Z.shiftr bdf 16)) by (apply shiftr_u32; unfold u32_ok in *; lia).
  assert (S8: u32_ok (Z.shiftr bdf 8)) by (apply shiftr_u32; unfold u32_ok in *; lia).
  iops.
  rewrite <- (bus_law bdf) by (auto; unfold u32_ok in *; rep_lia).
  assert (TV: (Vint (Int.repr (Z.land (Z.shiftr bdf 16) 255)), (Vint (Int.repr (Z.land (Z.shiftr bdf 8) 31)),
     (Vint (Int.repr (Z.land bdf 7)), (Vint (Int.repr (le32 bs 20)), (Vint (Int.repr w),
      Vint (Int.repr (bar_of w28))))))) = target_val (target_of bs)) by reflexivity.
  rewrite TV.
  forward_if.
  - eapply semax_pre; [ | apply ri_v3; auto ].
    unfold ri_pre3, ri_rep, pol_fields. entailer!. bfix. split; [ exact V23ok | split; auto ].
  - forward. unfold ri_join.
    Exists (target_of bs) no_policy 32 (Zrepeat Vundef 8) (Zrepeat udesc 16).
    unfold no_policy;
      cbn [pl_present pl_dma pl_window pl_cfg_read pl_cfg_write pl_cmd_clear pl_cmd_set pl_sink_count
           pl_sinks pl_desc_count pl_descs].
    simpl map. rewrite !app_nil_l. unfold z32, z64, ri_rep, pol_fields.
    entailer!.
    bfix. apply dec_v2; auto. destruct V23; auto; congruence.
Qed.
