(* Law image_exact: the law's state struct law: the law's reading of the image (m->want.t, m->want.pol) as its
   own objects (header_case and start_case pass their addresses), and the compspecs conversion from the law's
   compspecs to the unit's (the calls of the unit's functions). *)
Require Import VST.floyd.proofauto.
Require Import LeanosDeviceProgramImage.harness.image_exact.code.
Require Import LeanosDeviceProgramImage.proof.Defs.
Require LeanosDeviceProgramImage.proof.Specs.
Require Import LeanosDeviceProgramImage.proof.LawProg LeanosDeviceProgramImage.proof.LawSpecs.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

#[export] Instance LCR' : change_composite_env LCS LeanosDeviceProgramImage.proof.Specs.CS.
  make_cs_preserve LCS LeanosDeviceProgramImage.proof.Specs.CS. Defined.

Definition lv_t (lv: law_t) : target_t := fst (snd (snd (snd (snd (snd lv))))).
Definition lv_pol (lv: law_t) : policy_t := fst (snd (snd (snd (snd (snd (snd lv)))))).

Lemma want_t_focus: forall sh (lv: law_t) m,
  data_at sh t_law lv m |--
  data_at sh t_target (lv_t lv) (field_address t_law (DOT _want DOT _t) m) *
  (data_at sh t_target (lv_t lv) (field_address t_law (DOT _want DOT _t) m) -* data_at sh t_law lv m).
Proof.
  intros sh lv m.
  unfold data_at at 1 4.
  eapply derives_trans.
  - eapply nested_field_ramif' with (gfs1 := [StructField _t; StructField _want]).
    + apply JMeq_refl.
    + simpl. repeat split; auto; unfold in_members; simpl; repeat (first [ left; reflexivity | right ]).
  - simpl app. rewrite field_at_data_at.
    apply sepcon_derives; [ apply derives_refl | ].
    apply allp_left with (lv_t lv). apply allp_left with (lv_t lv).
    rewrite prop_imp by apply JMeq_refl.
    apply wand_derives.
    + rewrite field_at_data_at. apply derives_refl.
    + apply derives_refl'. f_equal.
      destruct lv as (a1 & a2 & a3 & a4 & a5 & a6 & a7 & a8 & a9 & a10). reflexivity.
Qed.

Lemma want_pol_focus: forall sh (lv: law_t) m,
  data_at sh t_law lv m |--
  data_at sh t_policy (lv_pol lv) (field_address t_law (DOT _want DOT _pol) m) *
  (data_at sh t_policy (lv_pol lv) (field_address t_law (DOT _want DOT _pol) m) -* data_at sh t_law lv m).
Proof.
  intros sh lv m.
  unfold data_at at 1 4.
  eapply derives_trans.
  - eapply nested_field_ramif' with (gfs1 := [StructField _pol; StructField _want]).
    + apply JMeq_refl.
    + simpl. repeat split; auto; unfold in_members; simpl; repeat (first [ left; reflexivity | right ]).
  - simpl app. rewrite field_at_data_at.
    apply sepcon_derives; [ apply derives_refl | ].
    apply allp_left with (lv_pol lv). apply allp_left with (lv_pol lv).
    rewrite prop_imp by apply JMeq_refl.
    apply wand_derives.
    + rewrite field_at_data_at. apply derives_refl.
    + apply derives_refl'. f_equal.
      destruct lv as (a1 & a2 & a3 & a4 & a5 & a6 & a7 & a8 & a9 & a10). reflexivity.
Qed.

(* &m->want.t and &m->want.pol as the harness computes them. *)
Lemma want_t_addr: forall m, field_compatible t_target nil (field_address t_law (DOT _want DOT _t) m) ->
  field_address t_law (DOT _want DOT _t) m = offset_val 24 m.
Proof.
  intros m FC. unfold field_address in *.
  destruct (field_compatible_dec t_law (DOT _want DOT _t) m) as [Y|N].
  - reflexivity.
  - destruct FC as [F _]. simpl in F. contradiction.
Qed.

Lemma want_pol_addr: forall m, field_compatible t_policy nil (field_address t_law (DOT _want DOT _pol) m) ->
  field_address t_law (DOT _want DOT _pol) m = offset_val 48 m.
Proof.
  intros m FC. unfold field_address in *.
  destruct (field_compatible_dec t_law (DOT _want DOT _pol) m) as [Y|N].
  - reflexivity.
  - destruct FC as [F _]. simpl in F. contradiction.
Qed.

(* The objects the law passes to the unit, at the unit's compspecs. *)
Lemma tg_cs: forall sh (v: target_t) p,
  @data_at LCS sh t_target v p = @data_at LeanosDeviceProgramImage.proof.Specs.CS sh t_target v p.
Proof.
  intros. apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite LCS _ LCR'); [ apply JMeq_refl | reflexivity ].
Qed.

Lemma tg_cs_: forall sh p,
  @data_at_ LCS sh t_target p = @data_at_ LeanosDeviceProgramImage.proof.Specs.CS sh t_target p.
Proof. intros. apply (f_equal (fun f => f p)). apply (@data_at__change_composite LCS _ LCR'). reflexivity. Qed.

Lemma pol_cs: forall sh (v: policy_t) p,
  @data_at LCS sh t_policy v p = @data_at LeanosDeviceProgramImage.proof.Specs.CS sh t_policy v p.
Proof.
  intros. apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite LCS _ LCR'); [ apply JMeq_refl | reflexivity ].
Qed.

Lemma vm_cs: forall sh (v: vm_t) p,
  @data_at LCS sh t_vm v p = @data_at LeanosDeviceProgramImage.proof.Specs.CS sh t_vm v p.
Proof.
  intros. apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite LCS _ LCR'); [ apply JMeq_refl | reflexivity ].
Qed.

Lemma u32_cs: forall sh (v: val) p,
  @data_at LCS sh tuint v p = @data_at LeanosDeviceProgramImage.proof.Specs.CS sh tuint v p.
Proof.
  intros. apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite LCS _ LCR'); [ apply JMeq_refl | reflexivity ].
Qed.

Lemma u32_cs_: forall sh p,
  @data_at_ LCS sh tuint p = @data_at_ LeanosDeviceProgramImage.proof.Specs.CS sh tuint p.
Proof. intros. apply (f_equal (fun f => f p)). apply (@data_at__change_composite LCS _ LCR'). reflexivity. Qed.

Lemma bytes_cs: forall sh n (v: list val) p,
  @data_at LCS sh (tarray tuchar n) v p = @data_at LeanosDeviceProgramImage.proof.Specs.CS sh (tarray tuchar n) v p.
Proof.
  intros. apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite LCS _ LCR'); [ apply JMeq_refl | reflexivity ].
Qed.
