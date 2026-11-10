(* Law image_exact: the bodies of header_case and admission_case. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import LeanosDeviceProgramImage.harness.image_exact.code.
Require Import LeanosDeviceProgramImage.proof.Defs.
Require LeanosDeviceProgramImage.proof.Specs.
Require Import LeanosDeviceProgramImage.proof.LawProg LeanosDeviceProgramImage.proof.LawSpecs
  LeanosDeviceProgramImage.proof.LawLib LeanosDeviceProgramImage.proof.LawLaw.
Local Open Scope Z_scope.
#[local] Existing Instance LawProg.LCS.

Lemma header_status_range: forall bs, 0 <= header_status bs <= 2.
Proof. intros. unfold header_status. destruct (decode bs); unfold BAD; lia. Qed.

Lemma header_status_ok: forall bs, header_status bs = 0 -> exists T P H, decode bs = Some (T, P, H).
Proof.
  intros bs E. unfold header_status in E. destruct (decode bs) as [[[T P] H]|]; [ eauto | discriminate ].
Qed.

Local Opaque decode le32 header_status start_status start.

Ltac unfocus :=
  match goal with |- context [?A -* ?B] => sep_apply (modus_ponens_wand A B) end.

Lemma target_eqb_refl: forall T, target_eqb T T = true.
Proof. intros. unfold target_eqb. rewrite !Z.eqb_refl. reflexivity. Qed.

Lemma body_header_case : semax_body Vlaw Glaw f_header_case header_case_spec.
Proof.
  start_function.
  destruct lv as (cl & len & cp & st & hl & tv & pv & nv & blv & sst).
  match goal with Hr: law_reads _ _ |- _ => destruct Hr as [Elen RO] end. subst len.
  forward_call (Tsh, v_t). Intros T.
  forward_call (Tsh, v_pol, false). Intros P0.
  forward_call (Tsh, v_prior, Tsh, v_pol, P0).
  forward_call. Intros h0. forward.
  forward.
  sep_apply (data_at_data_at_ Tsh t_target (target_val T) v_t).
  sep_apply (data_at_data_at_ Tsh tuint (Vint (Int.repr h0)) v_header_len).
  rewrite tg_cs_, u32_cs_, (pol_cs Tsh (policy_val P0) v_pol), (bytes_cs ish (Zlength bs)).
  forward_call (ish, image, bs, Tsh, v_t, Tsh, v_pol, P0, Tsh, v_header_len).
  Intros vret. destruct vret as [[tvo pvo] hvo]. simpl fst in *; simpl snd in *.
  change S.t_target with t_target. change S.t_policy with t_policy.
  rewrite <- tg_cs, <- pol_cs, <- u32_cs, <- bytes_cs.
  destruct RO as (Est & Esst & RD). subst st.
  pose proof (header_status_range bs) as HSR.
  forward.
  forward.
  forward_call (Int.repr 1).
  { entailer!. rewrite Int.eq_true. reflexivity. }
  forward_if.
  - bfix.
    match goal with Hh: header_status bs = 0 |- _ => destruct (header_status_ok bs Hh) as (T' & P' & H' & D) end.
    unfold S.header_post in H3. rewrite D in H3. destruct H3 as (-> & -> & ->).
    rewrite D in RD. destruct RD as (Ehl & Etv & PD & Env & Eblv). subst hl tv.
    destruct H as [Hlen F].
    pose proof (decode_wf bs T' P' H' F D) as (TW & PW & HR).
    assert_PROP (field_compatible t_law (DOT _want DOT _t) m /\ field_compatible t_law (DOT _want DOT _pol) m)
      as FCtp by (entailer!; split; auto with field_compatible).
    destruct FCtp as [FCt FCp].
    match goal with |- context [data_at msh t_law ?lv m] => sep_apply (want_t_focus msh lv m) end.
    unfold lv_t; simpl fst; simpl snd. Intros.
    forward_call (Tsh, v_t, T', msh, field_address t_law (DOT _want DOT _t) m, T').
    rewrite target_eqb_refl. unfocus.
    forward_call (Int.repr 1).
    forward. forward.
    forward_call (Int.repr 1).
    { entailer!. rewrite Int.eq_true. reflexivity. }
    match goal with |- context [data_at msh t_law ?lv m] => sep_apply (want_pol_focus msh lv m) end.
    unfold lv_pol; simpl fst; simpl snd. Intros.
    forward_call (Tsh, v_pol, msh, field_address t_law (DOT _want DOT _pol) m, pv, Tsh, v_prior, P', P0).
    unfocus.
    try_clean_up_stackframe.
    sep_apply (data_at_data_at_ Tsh t_policy (policy_val P0) v_prior).
    sep_apply (data_at_data_at_ Tsh t_policy (policy_val (store P' P0)) v_pol).
    sep_apply (data_at_data_at_ Tsh t_target (target_val T') v_t).
    sep_apply (data_at_data_at_ Tsh tuint (Vint (Int.repr H')) v_header_len).
    go_lower. cancel.
  - forward. clear RD H3.
    sep_apply (data_at_data_at_ Tsh t_target tvo v_t). sep_apply (data_at_data_at_ Tsh t_policy pvo v_pol).
    sep_apply (data_at_data_at_ Tsh tuint hvo v_header_len).
    try_clean_up_stackframe.
    sep_apply (data_at_data_at_ Tsh t_policy (policy_val P0) v_prior).
    go_lower. cancel.
Qed.
